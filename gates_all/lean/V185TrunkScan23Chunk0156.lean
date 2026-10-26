import V185TrunkScan23Chunk0155

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_922242 : List Nat := [3, 4, 3, 1, 1, 2, 2, 1, 6]
def baseStart_922242 : Nat := 118140960795 + 922242 * 2 ^ 59
def prefixEnd_922242 : Nat := 4983230072969 + 3 ^ 40 * 922242 * 2
def baseEnd_922242 : Nat := 52617047307098439737077

theorem tailTrace_922242 : CollatzResearch.WordTrace tailWord_922242 prefixEnd_922242 52617047307098439737077 := by
  unfold tailWord_922242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8409232281220553809746245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22424619416588143492656653 8409232281220553809746245)
  ·
    refine ⟨1576731052728853839327421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8409232281220553809746245 1576731052728853839327421)
    ·
      refine ⟨591274144773320189747783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1576731052728853839327421 591274144773320189747783)
      ·
        refine ⟨886911217159980284621675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591274144773320189747783 886911217159980284621675)
        ·
          refine ⟨1330366825739970426932513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886911217159980284621675 1330366825739970426932513)
          ·
            refine ⟨997775119304977820199385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1330366825739970426932513 997775119304977820199385)
            ·
              refine ⟨748331339478733365149539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997775119304977820199385 748331339478733365149539)
              ·
                refine ⟨1122497009218100047724309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748331339478733365149539 1122497009218100047724309)
                ·
                  refine ⟨52617047307098439737077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1122497009218100047724309 52617047307098439737077)
                  ·
                    rfl

theorem cell23_922242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_922242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922242 prefixEnd_922242 := by exact prefixLift 922242
  have htrace : WordTrace (prefixWord ++ tailWord_922242) baseStart_922242 baseEnd_922242 := by
    simpa [prefixWord, tailWord_922242, baseEnd_922242] using wordTrace_append hprefix tailTrace_922242
  have hstable : (prefixWord ++ tailWord_922242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922242).length < 2 ^ (prefixWord ++ tailWord_922242).sum := by decide
  have hdescent : baseEnd_922242 < baseStart_922242 := by decide
  rcases family_descends (prefixWord ++ tailWord_922242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922244 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_922244 : Nat := 118140960795 + 922244 * 2 ^ 59
def prefixEnd_922244 : Nat := 4983230072969 + 3 ^ 40 * 922244 * 2
def baseEnd_922244 : Nat := 473554452725194949808683

theorem tailTrace_922244 : CollatzResearch.WordTrace tailWord_922244 prefixEnd_922244 473554452725194949808683 := by
  unfold tailWord_922244
  simp only [CollatzResearch.WordTrace]
  refine ⟨16818501035437484790278893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22424668047249979720371857 16818501035437484790278893)
  ·
    refine ⟨6306937888289056796354585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16818501035437484790278893 6306937888289056796354585)
    ·
      refine ⟨4730203416216792597265939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6306937888289056796354585 4730203416216792597265939)
      ·
        refine ⟨7095305124325188895898909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4730203416216792597265939 7095305124325188895898909)
        ·
          refine ⟨2660739421621945835962091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7095305124325188895898909 2660739421621945835962091)
          ·
            refine ⟨3991109132432918753943137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660739421621945835962091 3991109132432918753943137)
            ·
              refine ⟨2993331849324689065457353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3991109132432918753943137 2993331849324689065457353)
              ·
                refine ⟨2244998886993516799093015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2993331849324689065457353 2244998886993516799093015)
                ·
                  refine ⟨3367498330490275198639523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244998886993516799093015 3367498330490275198639523)
                  ·
                    refine ⟨5051247495735412797959285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3367498330490275198639523 5051247495735412797959285)
                    ·
                      refine ⟨473554452725194949808683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5051247495735412797959285 473554452725194949808683)
                      ·
                        rfl

theorem cell23_922244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_922244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922244 prefixEnd_922244 := by exact prefixLift 922244
  have htrace : WordTrace (prefixWord ++ tailWord_922244) baseStart_922244 baseEnd_922244 := by
    simpa [prefixWord, tailWord_922244, baseEnd_922244] using wordTrace_append hprefix tailTrace_922244
  have hstable : (prefixWord ++ tailWord_922244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922244).length < 2 ^ (prefixWord ++ tailWord_922244).sum := by decide
  have hdescent : baseEnd_922244 < baseStart_922244 := by decide
  rcases family_descends (prefixWord ++ tailWord_922244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922247 : List Nat := [1, 1, 4, 2, 1, 2, 4, 8]
def baseStart_922247 : Nat := 118140960795 + 922247 * 2 ^ 59
def prefixEnd_922247 : Nat := 4983230072969 + 3 ^ 40 * 922247 * 2
def baseEnd_922247 : Nat := 17539110858042905113747

theorem tailTrace_922247 : CollatzResearch.WordTrace tailWord_922247 prefixEnd_922247 17539110858042905113747 := by
  unfold tailWord_922247
  simp only [CollatzResearch.WordTrace]
  refine ⟨33637111489864101092916995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22424740993242734061944663 33637111489864101092916995)
  ·
    refine ⟨50455667234796151639375493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33637111489864101092916995 50455667234796151639375493)
    ·
      refine ⟨9460437606524278432382905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50455667234796151639375493 9460437606524278432382905)
      ·
        refine ⟨7095328204893208824287179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9460437606524278432382905 7095328204893208824287179)
        ·
          refine ⟨10642992307339813236430769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7095328204893208824287179 10642992307339813236430769)
          ·
            refine ⟨7982244230504859927323077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10642992307339813236430769 7982244230504859927323077)
            ·
              refine ⟨1496670793219661236373077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7982244230504859927323077 1496670793219661236373077)
              ·
                refine ⟨17539110858042905113747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1496670793219661236373077 17539110858042905113747)
                ·
                  rfl

theorem cell23_922247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 8].length) (baseStart_922247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922247 prefixEnd_922247 := by exact prefixLift 922247
  have htrace : WordTrace (prefixWord ++ tailWord_922247) baseStart_922247 baseEnd_922247 := by
    simpa [prefixWord, tailWord_922247, baseEnd_922247] using wordTrace_append hprefix tailTrace_922247
  have hstable : (prefixWord ++ tailWord_922247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922247).length < 2 ^ (prefixWord ++ tailWord_922247).sum := by decide
  have hdescent : baseEnd_922247 < baseStart_922247 := by decide
  rcases family_descends (prefixWord ++ tailWord_922247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922254 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_922254 : Nat := 118140960795 + 922254 * 2 ^ 59
def prefixEnd_922254 : Nat := 4983230072969 + 3 ^ 40 * 922254 * 2
def baseEnd_922254 : Nat := 473559587531739910683637

theorem tailTrace_922254 : CollatzResearch.WordTrace tailWord_922254 prefixEnd_922254 473559587531739910683637 := by
  unfold tailWord_922254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4204670850104842661052727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22424911200559160858947877 4204670850104842661052727)
  ·
    refine ⟨6307006275157263991579091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4204670850104842661052727 6307006275157263991579091)
    ·
      refine ⟨9460509412735895987368637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6307006275157263991579091 9460509412735895987368637)
      ·
        refine ⟨3547691029775960995263239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9460509412735895987368637 3547691029775960995263239)
        ·
          refine ⟨5321536544663941492894859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3547691029775960995263239 5321536544663941492894859)
          ·
            refine ⟨7982304816995912239342289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321536544663941492894859 7982304816995912239342289)
            ·
              refine ⟨5986728612746934179506717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7982304816995912239342289 5986728612746934179506717)
              ·
                refine ⟨2245023229780100317315019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5986728612746934179506717 2245023229780100317315019)
                ·
                  refine ⟨3367534844670150475972529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2245023229780100317315019 3367534844670150475972529)
                  ·
                    refine ⟨2525651133502612856979397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3367534844670150475972529 2525651133502612856979397)
                    ·
                      refine ⟨473559587531739910683637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2525651133502612856979397 473559587531739910683637)
                      ·
                        rfl

theorem cell23_922254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_922254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922254 prefixEnd_922254 := by exact prefixLift 922254
  have htrace : WordTrace (prefixWord ++ tailWord_922254) baseStart_922254 baseEnd_922254 := by
    simpa [prefixWord, tailWord_922254, baseEnd_922254] using wordTrace_append hprefix tailTrace_922254
  have hstable : (prefixWord ++ tailWord_922254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922254).length < 2 ^ (prefixWord ++ tailWord_922254).sum := by decide
  have hdescent : baseEnd_922254 < baseStart_922254 := by decide
  rcases family_descends (prefixWord ++ tailWord_922254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922258 : List Nat := [3, 2, 3, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_922258 : Nat := 118140960795 + 922258 * 2 ^ 59
def prefixEnd_922258 : Nat := 4983230072969 + 3 ^ 40 * 922258 * 2
def baseEnd_922258 : Nat := 473561641454357895033619

theorem tailTrace_922258 : CollatzResearch.WordTrace tailWord_922258 prefixEnd_922258 473561641454357895033619 := by
  unfold tailWord_922258
  simp only [CollatzResearch.WordTrace]
  refine ⟨8409378173206062492891857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22425008461882833314378285 8409378173206062492891857)
  ·
    refine ⟨6307033629904546869668893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8409378173206062492891857 6307033629904546869668893)
    ·
      refine ⟨2365137611214205076125835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6307033629904546869668893 2365137611214205076125835)
      ·
        refine ⟨3547706416821307614188753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365137611214205076125835 3547706416821307614188753)
        ·
          refine ⟨2660779812615980710641565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3547706416821307614188753 2660779812615980710641565)
          ·
            refine ⟨997792429730992766490587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2660779812615980710641565 997792429730992766490587)
            ·
              refine ⟨1496688644596489149735881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997792429730992766490587 1496688644596489149735881)
              ·
                refine ⟨1122516483447366862301911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1496688644596489149735881 1122516483447366862301911)
                ·
                  refine ⟨1683774725171050293452867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122516483447366862301911 1683774725171050293452867)
                  ·
                    refine ⟨2525662087756575440179301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1683774725171050293452867 2525662087756575440179301)
                    ·
                      refine ⟨473561641454357895033619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2525662087756575440179301 473561641454357895033619)
                      ·
                        rfl

theorem cell23_922258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_922258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922258 prefixEnd_922258 := by exact prefixLift 922258
  have htrace : WordTrace (prefixWord ++ tailWord_922258) baseStart_922258 baseEnd_922258 := by
    simpa [prefixWord, tailWord_922258, baseEnd_922258] using wordTrace_append hprefix tailTrace_922258
  have hstable : (prefixWord ++ tailWord_922258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922258).length < 2 ^ (prefixWord ++ tailWord_922258).sum := by decide
  have hdescent : baseEnd_922258 < baseStart_922258 := by decide
  rcases family_descends (prefixWord ++ tailWord_922258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922291 : List Nat := [1, 1, 1, 2, 3, 4, 1, 4, 2, 1, 3]
def baseStart_922291 : Nat := 118140960795 + 922291 * 2 ^ 59
def prefixEnd_922291 : Nat := 4983230072969 + 3 ^ 40 * 922291 * 2
def baseEnd_922291 : Nat := 473578586315956265920967

theorem tailTrace_922291 : CollatzResearch.WordTrace tailWord_922291 prefixEnd_922291 473578586315956265920967 := by
  unfold tailWord_922291
  simp only [CollatzResearch.WordTrace]
  refine ⟨33638716301704696607518727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22425810867803131071679151 33638716301704696607518727)
  ·
    refine ⟨50458074452557044911278091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33638716301704696607518727 50458074452557044911278091)
    ·
      refine ⟨75687111678835567366917137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50458074452557044911278091 75687111678835567366917137)
      ·
        refine ⟨56765333759126675525187853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75687111678835567366917137 56765333759126675525187853)
        ·
          refine ⟨21287000159672503321945445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56765333759126675525187853 21287000159672503321945445)
          ·
            refine ⟨3991312529938594372864771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21287000159672503321945445 3991312529938594372864771)
            ·
              refine ⟨5986968794907891559297157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3991312529938594372864771 5986968794907891559297157)
              ·
                refine ⟨1122556649045229667368217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5986968794907891559297157 1122556649045229667368217)
                ·
                  refine ⟨841917486783922250526163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1122556649045229667368217 841917486783922250526163)
                  ·
                    refine ⟨1262876230175883375789245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 841917486783922250526163 1262876230175883375789245)
                    ·
                      refine ⟨473578586315956265920967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1262876230175883375789245 473578586315956265920967)
                      ·
                        rfl

theorem cell23_922291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 1, 3].length) (baseStart_922291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922291 prefixEnd_922291 := by exact prefixLift 922291
  have htrace : WordTrace (prefixWord ++ tailWord_922291) baseStart_922291 baseEnd_922291 := by
    simpa [prefixWord, tailWord_922291, baseEnd_922291] using wordTrace_append hprefix tailTrace_922291
  have hstable : (prefixWord ++ tailWord_922291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922291).length < 2 ^ (prefixWord ++ tailWord_922291).sum := by decide
  have hdescent : baseEnd_922291 < baseStart_922291 := by decide
  rcases family_descends (prefixWord ++ tailWord_922291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922301 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 3, 3, 2]
def baseStart_922301 : Nat := 118140960795 + 922301 * 2 ^ 59
def prefixEnd_922301 : Nat := 4983230072969 + 3 ^ 40 * 922301 * 2
def baseEnd_922301 : Nat := 473583721122501226795921

theorem tailTrace_922301 : CollatzResearch.WordTrace tailWord_922301 prefixEnd_922301 473583721122501226795921 := by
  unfold tailWord_922301
  simp only [CollatzResearch.WordTrace]
  refine ⟨33639081031668468315382757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22426054021112312210255171 33639081031668468315382757)
  ·
    refine ⟨6307327693437837809134267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33639081031668468315382757 6307327693437837809134267)
    ·
      refine ⟨9460991540156756713701401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6307327693437837809134267 9460991540156756713701401)
      ·
        refine ⟨7095743655117567535276051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9460991540156756713701401 7095743655117567535276051)
        ·
          refine ⟨10643615482676351302914077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7095743655117567535276051 10643615482676351302914077)
          ·
            refine ⟨3991355806003631738592779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10643615482676351302914077 3991355806003631738592779)
            ·
              refine ⟨5987033709005447607889169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3991355806003631738592779 5987033709005447607889169)
              ·
                refine ⟨4490275281754085705916877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5987033709005447607889169 4490275281754085705916877)
                ·
                  refine ⟨1683853230657782139718829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4490275281754085705916877 1683853230657782139718829)
                  ·
                    refine ⟨631444961496668302394561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1683853230657782139718829 631444961496668302394561)
                    ·
                      refine ⟨473583721122501226795921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 631444961496668302394561 473583721122501226795921)
                      ·
                        rfl

theorem cell23_922301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_922301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922301 prefixEnd_922301 := by exact prefixLift 922301
  have htrace : WordTrace (prefixWord ++ tailWord_922301) baseStart_922301 baseEnd_922301 := by
    simpa [prefixWord, tailWord_922301, baseEnd_922301] using wordTrace_append hprefix tailTrace_922301
  have hstable : (prefixWord ++ tailWord_922301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922301).length < 2 ^ (prefixWord ++ tailWord_922301).sum := by decide
  have hdescent : baseEnd_922301 < baseStart_922301 := by decide
  rcases family_descends (prefixWord ++ tailWord_922301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922308 : List Nat := [2, 3, 3, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_922308 : Nat := 118140960795 + 922308 * 2 ^ 59
def prefixEnd_922308 : Nat := 4983230072969 + 3 ^ 40 * 922308 * 2
def baseEnd_922308 : Nat := 473587315487082699408389

theorem tailTrace_922308 : CollatzResearch.WordTrace tailWord_922308 prefixEnd_922308 473587315487082699408389 := by
  unfold tailWord_922308
  simp only [CollatzResearch.WordTrace]
  refine ⟨16819668171321554255443789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22426224228428739007258385 16819668171321554255443789)
  ·
    refine ⟨6307375564245582845791421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16819668171321554255443789 6307375564245582845791421)
    ·
      refine ⟨2365265836592093567171783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6307375564245582845791421 2365265836592093567171783)
      ·
        refine ⟨3547898754888140350757675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365265836592093567171783 3547898754888140350757675)
        ·
          refine ⟨5321848132332210526136513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3547898754888140350757675 5321848132332210526136513)
          ·
            refine ⟨3991386099249157894602385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5321848132332210526136513 3991386099249157894602385)
            ·
              refine ⟨2993539574436868420951789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3991386099249157894602385 2993539574436868420951789)
              ·
                refine ⟨1122577340413825657856921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2993539574436868420951789 1122577340413825657856921)
                ·
                  refine ⟨841933005310369243392691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1122577340413825657856921 841933005310369243392691)
                  ·
                    refine ⟨1262899507965553865089037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 841933005310369243392691 1262899507965553865089037)
                    ·
                      refine ⟨473587315487082699408389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1262899507965553865089037 473587315487082699408389)
                      ·
                        rfl

theorem cell23_922308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_922308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922308 prefixEnd_922308 := by exact prefixLift 922308
  have htrace : WordTrace (prefixWord ++ tailWord_922308) baseStart_922308 baseEnd_922308 := by
    simpa [prefixWord, tailWord_922308, baseEnd_922308] using wordTrace_append hprefix tailTrace_922308
  have hstable : (prefixWord ++ tailWord_922308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922308).length < 2 ^ (prefixWord ++ tailWord_922308).sum := by decide
  have hdescent : baseEnd_922308 < baseStart_922308 := by decide
  rcases family_descends (prefixWord ++ tailWord_922308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922335 : List Nat := [1, 1, 2, 3, 2, 5, 2, 1, 1, 3, 2]
def baseStart_922335 : Nat := 118140960795 + 922335 * 2 ^ 59
def prefixEnd_922335 : Nat := 4983230072969 + 3 ^ 40 * 922335 * 2
def baseEnd_922335 : Nat := 473601179464754093770765

theorem tailTrace_922335 : CollatzResearch.WordTrace tailWord_922335 prefixEnd_922335 473601179464754093770765 := by
  unfold tailWord_922335
  simp only [CollatzResearch.WordTrace]
  refine ⟨33640321113545292122120459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22426880742363528081413639 33640321113545292122120459)
  ·
    refine ⟨50460481670317938183180689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33640321113545292122120459 50460481670317938183180689)
    ·
      refine ⟨37845361252738453637385517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50460481670317938183180689 37845361252738453637385517)
      ·
        refine ⟨14192010469776920114019569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37845361252738453637385517 14192010469776920114019569)
        ·
          refine ⟨10644007852332690085514677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14192010469776920114019569 10644007852332690085514677)
          ·
            refine ⟨997875736156189695517001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10644007852332690085514677 997875736156189695517001)
            ·
              refine ⟨748406802117142271637751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997875736156189695517001 748406802117142271637751)
              ·
                refine ⟨1122610203175713407456627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748406802117142271637751 1122610203175713407456627)
                ·
                  refine ⟨1683915304763570111184941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122610203175713407456627 1683915304763570111184941)
                  ·
                    refine ⟨631468239286338791694353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1683915304763570111184941 631468239286338791694353)
                    ·
                      refine ⟨473601179464754093770765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 631468239286338791694353 473601179464754093770765)
                      ·
                        rfl

theorem cell23_922335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_922335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922335 prefixEnd_922335 := by exact prefixLift 922335
  have htrace : WordTrace (prefixWord ++ tailWord_922335) baseStart_922335 baseEnd_922335 := by
    simpa [prefixWord, tailWord_922335, baseEnd_922335] using wordTrace_append hprefix tailTrace_922335
  have hstable : (prefixWord ++ tailWord_922335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922335).length < 2 ^ (prefixWord ++ tailWord_922335).sum := by decide
  have hdescent : baseEnd_922335 < baseStart_922335 := by decide
  rcases family_descends (prefixWord ++ tailWord_922335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922354 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 7]
def baseStart_922354 : Nat := 118140960795 + 922354 * 2 ^ 59
def prefixEnd_922354 : Nat := 4983230072969 + 3 ^ 40 * 922354 * 2
def baseEnd_922354 : Nat := 52623437288576613270353

theorem tailTrace_922354 : CollatzResearch.WordTrace tailWord_922354 prefixEnd_922354 52623437288576613270353 := by
  unfold tailWord_922354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8410253525119114591765529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22427342733650972244708077 8410253525119114591765529)
  ·
    refine ⟨6307690143839335943824147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8410253525119114591765529 6307690143839335943824147)
    ·
      refine ⟨9461535215759003915736221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6307690143839335943824147 9461535215759003915736221)
      ·
        refine ⟨3548075705909626468401083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9461535215759003915736221 3548075705909626468401083)
        ·
          refine ⟨5322113558864439702601625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3548075705909626468401083 5322113558864439702601625)
          ·
            refine ⟨3991585169148329776951219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5322113558864439702601625 3991585169148329776951219)
            ·
              refine ⟨5987377753722494665426829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3991585169148329776951219 5987377753722494665426829)
              ·
                refine ⟨2245266657645935499535061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5987377753722494665426829 2245266657645935499535061)
                ·
                  refine ⟨52623437288576613270353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2245266657645935499535061 52623437288576613270353)
                  ·
                    rfl

theorem cell23_922354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_922354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922354 prefixEnd_922354 := by exact prefixLift 922354
  have htrace : WordTrace (prefixWord ++ tailWord_922354) baseStart_922354 baseEnd_922354 := by
    simpa [prefixWord, tailWord_922354, baseEnd_922354] using wordTrace_append hprefix tailTrace_922354
  have hstable : (prefixWord ++ tailWord_922354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922354).length < 2 ^ (prefixWord ++ tailWord_922354).sum := by decide
  have hdescent : baseEnd_922354 < baseStart_922354 := by decide
  rcases family_descends (prefixWord ++ tailWord_922354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922365 : List Nat := [1, 4, 1, 1, 1, 1, 7, 1, 2, 2, 2]
def baseStart_922365 : Nat := 118140960795 + 922365 * 2 ^ 59
def prefixEnd_922365 : Nat := 4983230072969 + 3 ^ 40 * 922365 * 2
def baseEnd_922365 : Nat := 473616583884388976395627

theorem tailTrace_922365 : CollatzResearch.WordTrace tailWord_922365 prefixEnd_922365 473616583884388976395627 := by
  unfold tailWord_922365
  simp only [CollatzResearch.WordTrace]
  refine ⟨33641415303436607245712549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22427610202291071497141699 33641415303436607245712549)
  ·
    refine ⟨6307765369394363858571103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33641415303436607245712549 6307765369394363858571103)
    ·
      refine ⟨9461648054091545787856655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6307765369394363858571103 9461648054091545787856655)
      ·
        refine ⟨14192472081137318681784983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9461648054091545787856655 14192472081137318681784983)
        ·
          refine ⟨21288708121705978022677475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14192472081137318681784983 21288708121705978022677475)
          ·
            refine ⟨31933062182558967034016213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21288708121705978022677475 31933062182558967034016213)
            ·
              refine ⟨748431144903725789859755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31933062182558967034016213 748431144903725789859755)
              ·
                refine ⟨1122646717355588684789633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748431144903725789859755 1122646717355588684789633)
                ·
                  refine ⟨841985038016691513592225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1122646717355588684789633 841985038016691513592225)
                  ·
                    refine ⟨631488778512518635194169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 841985038016691513592225 631488778512518635194169)
                    ·
                      refine ⟨473616583884388976395627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 631488778512518635194169 473616583884388976395627)
                      ·
                        rfl

theorem cell23_922365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_922365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922365 prefixEnd_922365 := by exact prefixLift 922365
  have htrace : WordTrace (prefixWord ++ tailWord_922365) baseStart_922365 baseEnd_922365 := by
    simpa [prefixWord, tailWord_922365, baseEnd_922365] using wordTrace_append hprefix tailTrace_922365
  have hstable : (prefixWord ++ tailWord_922365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922365).length < 2 ^ (prefixWord ++ tailWord_922365).sum := by decide
  have hdescent : baseEnd_922365 < baseStart_922365 := by decide
  rcases family_descends (prefixWord ++ tailWord_922365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922394 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_922394 : Nat := 118140960795 + 922394 * 2 ^ 59
def prefixEnd_922394 : Nat := 4983230072969 + 3 ^ 40 * 922394 * 2
def baseEnd_922394 : Nat := 473631474823369362932993

theorem tailTrace_922394 : CollatzResearch.WordTrace tailWord_922394 prefixEnd_922394 473631474823369362932993 := by
  unfold tailWord_922394
  simp only [CollatzResearch.WordTrace]
  refine ⟨8410618255082886299629559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22428315346887696799012157 8410618255082886299629559)
  ·
    refine ⟨12615927382624329449444339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8410618255082886299629559 12615927382624329449444339)
    ·
      refine ⟨18923891073936494174166509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12615927382624329449444339 18923891073936494174166509)
      ·
        refine ⟨7096459152726185315312441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18923891073936494174166509 7096459152726185315312441)
        ·
          refine ⟨5322344364544638986484331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7096459152726185315312441 5322344364544638986484331)
          ·
            refine ⟨7983516546816958479726497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5322344364544638986484331 7983516546816958479726497)
            ·
              refine ⟨5987637410112718859794873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7983516546816958479726497 5987637410112718859794873)
              ·
                refine ⟨4490728057584539144846155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5987637410112718859794873 4490728057584539144846155)
                ·
                  refine ⟨6736092086376808717269233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4490728057584539144846155 6736092086376808717269233)
                  ·
                    refine ⟨5052069064782606537951925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6736092086376808717269233 5052069064782606537951925)
                    ·
                      refine ⟨473631474823369362932993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5052069064782606537951925 473631474823369362932993)
                      ·
                        rfl

theorem cell23_922394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_922394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922394 prefixEnd_922394 := by exact prefixLift 922394
  have htrace : WordTrace (prefixWord ++ tailWord_922394) baseStart_922394 baseEnd_922394 := by
    simpa [prefixWord, tailWord_922394, baseEnd_922394] using wordTrace_append hprefix tailTrace_922394
  have hstable : (prefixWord ++ tailWord_922394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922394).length < 2 ^ (prefixWord ++ tailWord_922394).sum := by decide
  have hdescent : baseEnd_922394 < baseStart_922394 := by decide
  rcases family_descends (prefixWord ++ tailWord_922394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922441 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 2, 2, 3]
def baseStart_922441 : Nat := 118140960795 + 922441 * 2 ^ 59
def prefixEnd_922441 : Nat := 4983230072969 + 3 ^ 40 * 922441 * 2
def baseEnd_922441 : Nat := 473655608414130679045277

theorem tailTrace_922441 : CollatzResearch.WordTrace tailWord_922441 prefixEnd_922441 473655608414130679045277 := by
  unfold tailWord_922441
  simp only [CollatzResearch.WordTrace]
  refine ⟨33644187251161272225479177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22429458167440848150319451 33644187251161272225479177)
  ·
    refine ⟨25233140438370954169109383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33644187251161272225479177 25233140438370954169109383)
    ·
      refine ⟨37849710657556431253664075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25233140438370954169109383 37849710657556431253664075)
      ·
        refine ⟨56774565986334646880496113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37849710657556431253664075 56774565986334646880496113)
        ·
          refine ⟨42580924489750985160372085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56774565986334646880496113 42580924489750985160372085)
          ·
            refine ⟨3991961670914154858784883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42580924489750985160372085 3991961670914154858784883)
            ·
              refine ⟨5987942506371232288177325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3991961670914154858784883 5987942506371232288177325)
              ·
                refine ⟨2245478439889212108066497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5987942506371232288177325 2245478439889212108066497)
                ·
                  refine ⟨1684108829916909081049873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2245478439889212108066497 1684108829916909081049873)
                  ·
                    refine ⟨1263081622437681810787405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1684108829916909081049873 1263081622437681810787405)
                    ·
                      refine ⟨473655608414130679045277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1263081622437681810787405 473655608414130679045277)
                      ·
                        rfl

theorem cell23_922441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 2, 3].length) (baseStart_922441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922441 prefixEnd_922441 := by exact prefixLift 922441
  have htrace : WordTrace (prefixWord ++ tailWord_922441) baseStart_922441 baseEnd_922441 := by
    simpa [prefixWord, tailWord_922441, baseEnd_922441] using wordTrace_append hprefix tailTrace_922441
  have hstable : (prefixWord ++ tailWord_922441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922441).length < 2 ^ (prefixWord ++ tailWord_922441).sum := by decide
  have hdescent : baseEnd_922441 < baseStart_922441 := by decide
  rcases family_descends (prefixWord ++ tailWord_922441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922464 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 6]
def baseStart_922464 : Nat := 118140960795 + 922464 * 2 ^ 59
def prefixEnd_922464 : Nat := 4983230072969 + 3 ^ 40 * 922464 * 2
def baseEnd_922464 : Nat := 473667418469184089057671

theorem tailTrace_922464 : CollatzResearch.WordTrace tailWord_922464 prefixEnd_922464 473667418469184089057671 := by
  unfold tailWord_922464
  simp only [CollatzResearch.WordTrace]
  refine ⟨16822513065038973576783223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22430017420051964769044297 16822513065038973576783223)
  ·
    refine ⟨25233769597558460365174835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16822513065038973576783223 25233769597558460365174835)
    ·
      refine ⟨37850654396337690547762253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25233769597558460365174835 37850654396337690547762253)
      ·
        refine ⟨14193995398626633955410845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37850654396337690547762253 14193995398626633955410845)
        ·
          refine ⟨5322748274484987733279067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14193995398626633955410845 5322748274484987733279067)
          ·
            refine ⟨7984122411727481599918601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5322748274484987733279067 7984122411727481599918601)
            ·
              refine ⟨5988091808795611199938951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7984122411727481599918601 5988091808795611199938951)
              ·
                refine ⟨8982137713193416799908427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5988091808795611199938951 8982137713193416799908427)
                ·
                  refine ⟨13473206569790125199862641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8982137713193416799908427 13473206569790125199862641)
                  ·
                    refine ⟨10104904927342593899896981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13473206569790125199862641 10104904927342593899896981)
                    ·
                      refine ⟨473667418469184089057671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10104904927342593899896981 473667418469184089057671)
                      ·
                        rfl

theorem cell23_922464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_922464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922464 prefixEnd_922464 := by exact prefixLift 922464
  have htrace : WordTrace (prefixWord ++ tailWord_922464) baseStart_922464 baseEnd_922464 := by
    simpa [prefixWord, tailWord_922464, baseEnd_922464] using wordTrace_append hprefix tailTrace_922464
  have hstable : (prefixWord ++ tailWord_922464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922464).length < 2 ^ (prefixWord ++ tailWord_922464).sum := by decide
  have hdescent : baseEnd_922464 < baseStart_922464 := by decide
  rcases family_descends (prefixWord ++ tailWord_922464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922505 : List Nat := [1, 2, 1, 1, 5, 2, 1, 5, 1, 1, 3]
def baseStart_922505 : Nat := 118140960795 + 922505 * 2 ^ 59
def prefixEnd_922505 : Nat := 4983230072969 + 3 ^ 40 * 922505 * 2
def baseEnd_922505 : Nat := 473688471176018428644983

theorem tailTrace_922505 : CollatzResearch.WordTrace tailWord_922505 prefixEnd_922505 473688471176018428644983 := by
  unfold tailWord_922505
  simp only [CollatzResearch.WordTrace]
  refine ⟨33646521522929411155808969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22431014348619607437205979 33646521522929411155808969)
  ·
    refine ⟨25234891142197058366856727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33646521522929411155808969 25234891142197058366856727)
    ·
      refine ⟨37852336713295587550285091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25234891142197058366856727 37852336713295587550285091)
      ·
        refine ⟨56778505069943381325427637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37852336713295587550285091 56778505069943381325427637)
        ·
          refine ⟨5322984850307191999258841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56778505069943381325427637 5322984850307191999258841)
          ·
            refine ⟨3992238637730393999444131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5322984850307191999258841 3992238637730393999444131)
            ·
              refine ⟨5988357956595590999166197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992238637730393999444131 5988357956595590999166197)
              ·
                refine ⟨561408558430836656171831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5988357956595590999166197 561408558430836656171831)
                ·
                  refine ⟨842112837646254984257747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561408558430836656171831 842112837646254984257747)
                  ·
                    refine ⟨1263169256469382476386621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 842112837646254984257747 1263169256469382476386621)
                    ·
                      refine ⟨473688471176018428644983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1263169256469382476386621 473688471176018428644983)
                      ·
                        rfl

theorem cell23_922505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 1, 1, 3].length) (baseStart_922505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922505 prefixEnd_922505 := by exact prefixLift 922505
  have htrace : WordTrace (prefixWord ++ tailWord_922505) baseStart_922505 baseEnd_922505 := by
    simpa [prefixWord, tailWord_922505, baseEnd_922505] using wordTrace_append hprefix tailTrace_922505
  have hstable : (prefixWord ++ tailWord_922505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922505).length < 2 ^ (prefixWord ++ tailWord_922505).sum := by decide
  have hdescent : baseEnd_922505 < baseStart_922505 := by decide
  rcases family_descends (prefixWord ++ tailWord_922505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922508 : List Nat := [2, 2, 1, 2, 1, 2, 6, 1, 1, 5]
def baseStart_922508 : Nat := 118140960795 + 922508 * 2 ^ 59
def prefixEnd_922508 : Nat := 4983230072969 + 3 ^ 40 * 922508 * 2
def baseEnd_922508 : Nat := 157896670539327305635823

theorem tailTrace_922508 : CollatzResearch.WordTrace tailWord_922508 prefixEnd_922508 157896670539327305635823 := by
  unfold tailWord_922508
  simp only [CollatzResearch.WordTrace]
  refine ⟨16823315470959271334084089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22431087294612361778778785 16823315470959271334084089)
  ·
    refine ⟨12617486603219453500563067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16823315470959271334084089 12617486603219453500563067)
    ·
      refine ⟨18926229904829180250844601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12617486603219453500563067 18926229904829180250844601)
      ·
        refine ⟨14194672428621885188133451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18926229904829180250844601 14194672428621885188133451)
        ·
          refine ⟨21292008642932827782200177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14194672428621885188133451 21292008642932827782200177)
          ·
            refine ⟨15969006482199620836650133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21292008642932827782200177 15969006482199620836650133)
            ·
              refine ⟨748547178853107226717975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15969006482199620836650133 748547178853107226717975)
              ·
                refine ⟨1122820768279660840076963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748547178853107226717975 1122820768279660840076963)
                ·
                  refine ⟨1684231152419491260115445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122820768279660840076963 1684231152419491260115445)
                  ·
                    refine ⟨157896670539327305635823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1684231152419491260115445 157896670539327305635823)
                    ·
                      rfl

theorem cell23_922508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_922508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922508 prefixEnd_922508 := by exact prefixLift 922508
  have htrace : WordTrace (prefixWord ++ tailWord_922508) baseStart_922508 baseEnd_922508 := by
    simpa [prefixWord, tailWord_922508, baseEnd_922508] using wordTrace_append hprefix tailTrace_922508
  have hstable : (prefixWord ++ tailWord_922508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922508).length < 2 ^ (prefixWord ++ tailWord_922508).sum := by decide
  have hdescent : baseEnd_922508 < baseStart_922508 := by decide
  rcases family_descends (prefixWord ++ tailWord_922508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922531 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 3]
def baseStart_922531 : Nat := 118140960795 + 922531 * 2 ^ 59
def prefixEnd_922531 : Nat := 4983230072969 + 3 ^ 40 * 922531 * 2
def baseEnd_922531 : Nat := 473701821673035326919863

theorem tailTrace_922531 : CollatzResearch.WordTrace tailWord_922531 prefixEnd_922531 473701821673035326919863 := by
  unfold tailWord_922531
  simp only [CollatzResearch.WordTrace]
  refine ⟨33647469820835217596255447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22431646547223478397503631 33647469820835217596255447)
  ·
    refine ⟨50471204731252826394383171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33647469820835217596255447 50471204731252826394383171)
    ·
      refine ⟨75706807096879239591574757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50471204731252826394383171 75706807096879239591574757)
      ·
        refine ⟨14195026330664857423420267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75706807096879239591574757 14195026330664857423420267)
        ·
          refine ⟨21292539495997286135130401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14195026330664857423420267 21292539495997286135130401)
          ·
            refine ⟨15969404621997964601347801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21292539495997286135130401 15969404621997964601347801)
            ·
              refine ⟨11977053466498473451010851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15969404621997964601347801 11977053466498473451010851)
              ·
                refine ⟨17965580199747710176516277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11977053466498473451010851 17965580199747710176516277)
                ·
                  refine ⟨1684273143726347829048401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17965580199747710176516277 1684273143726347829048401)
                  ·
                    refine ⟨1263204857794760871786301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1684273143726347829048401 1263204857794760871786301)
                    ·
                      refine ⟨473701821673035326919863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1263204857794760871786301 473701821673035326919863)
                      ·
                        rfl

theorem cell23_922531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_922531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922531 prefixEnd_922531 := by exact prefixLift 922531
  have htrace : WordTrace (prefixWord ++ tailWord_922531) baseStart_922531 baseEnd_922531 := by
    simpa [prefixWord, tailWord_922531, baseEnd_922531] using wordTrace_append hprefix tailTrace_922531
  have hstable : (prefixWord ++ tailWord_922531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922531).length < 2 ^ (prefixWord ++ tailWord_922531).sum := by decide
  have hdescent : baseEnd_922531 < baseStart_922531 := by decide
  rcases family_descends (prefixWord ++ tailWord_922531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922545 : List Nat := [1, 2, 2, 4, 3, 1, 2, 2, 1, 1, 4]
def baseStart_922545 : Nat := 118140960795 + 922545 * 2 ^ 59
def prefixEnd_922545 : Nat := 4983230072969 + 3 ^ 40 * 922545 * 2
def baseEnd_922545 : Nat := 473709010402198272144799

theorem tailTrace_922545 : CollatzResearch.WordTrace tailWord_922545 prefixEnd_922545 473709010402198272144799 := by
  unfold tailWord_922545
  simp only [CollatzResearch.WordTrace]
  refine ⟨33647980442784497987265089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22431986961856331991510059 33647980442784497987265089)
  ·
    refine ⟨25235985332088373490448817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33647980442784497987265089 25235985332088373490448817)
    ·
      refine ⟨18926988999066280117836613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25235985332088373490448817 18926988999066280117836613)
      ·
        refine ⟨3548810437324927522094365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18926988999066280117836613 3548810437324927522094365)
        ·
          refine ⟨1330803913996847820785387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3548810437324927522094365 1330803913996847820785387)
          ·
            refine ⟨1996205870995271731178081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330803913996847820785387 1996205870995271731178081)
            ·
              refine ⟨1497154403246453798383561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1996205870995271731178081 1497154403246453798383561)
              ·
                refine ⟨1122865802434840348787671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497154403246453798383561 1122865802434840348787671)
                ·
                  refine ⟨1684298703652260523181507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122865802434840348787671 1684298703652260523181507)
                  ·
                    refine ⟨2526448055478390784772261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1684298703652260523181507 2526448055478390784772261)
                    ·
                      refine ⟨473709010402198272144799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2526448055478390784772261 473709010402198272144799)
                      ·
                        rfl

theorem cell23_922545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_922545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922545 prefixEnd_922545 := by exact prefixLift 922545
  have htrace : WordTrace (prefixWord ++ tailWord_922545) baseStart_922545 baseEnd_922545 := by
    simpa [prefixWord, tailWord_922545, baseEnd_922545] using wordTrace_append hprefix tailTrace_922545
  have hstable : (prefixWord ++ tailWord_922545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922545).length < 2 ^ (prefixWord ++ tailWord_922545).sum := by decide
  have hdescent : baseEnd_922545 < baseStart_922545 := by decide
  rcases family_descends (prefixWord ++ tailWord_922545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922551 : List Nat := [1, 1, 3, 1, 3, 1, 6, 7]
def baseStart_922551 : Nat := 118140960795 + 922551 * 2 ^ 59
def prefixEnd_922551 : Nat := 4983230072969 + 3 ^ 40 * 922551 * 2
def baseEnd_922551 : Nat := 17544892269856490691473

theorem tailTrace_922551 : CollatzResearch.WordTrace tailWord_922551 prefixEnd_922551 17544892269856490691473 := by
  unfold tailWord_922551
  simp only [CollatzResearch.WordTrace]
  refine ⟨33648199280762761011983507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22432132853841840674655671 33648199280762761011983507)
  ·
    refine ⟨50472298921144141517975261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33648199280762761011983507 50472298921144141517975261)
    ·
      refine ⟨18927112095429053069240723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50472298921144141517975261 18927112095429053069240723)
      ·
        refine ⟨28390668143143579603861085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18927112095429053069240723 28390668143143579603861085)
        ·
          refine ⟨10646500553678842351447907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28390668143143579603861085 10646500553678842351447907)
          ·
            refine ⟨15969750830518263527171861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10646500553678842351447907 15969750830518263527171861)
            ·
              refine ⟨748582070180543602836181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15969750830518263527171861 748582070180543602836181)
              ·
                refine ⟨17544892269856490691473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 748582070180543602836181 17544892269856490691473)
                ·
                  rfl

theorem cell23_922551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 7].length) (baseStart_922551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922551 prefixEnd_922551 := by exact prefixLift 922551
  have htrace : WordTrace (prefixWord ++ tailWord_922551) baseStart_922551 baseEnd_922551 := by
    simpa [prefixWord, tailWord_922551, baseEnd_922551] using wordTrace_append hprefix tailTrace_922551
  have hstable : (prefixWord ++ tailWord_922551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922551).length < 2 ^ (prefixWord ++ tailWord_922551).sum := by decide
  have hdescent : baseEnd_922551 < baseStart_922551 := by decide
  rcases family_descends (prefixWord ++ tailWord_922551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922568 : List Nat := [2, 1, 3, 1, 6, 1, 9]
def baseStart_922568 : Nat := 118140960795 + 922568 * 2 ^ 59
def prefixEnd_922568 : Nat := 4983230072969 + 3 ^ 40 * 922568 * 2
def baseEnd_922568 : Nat := 5848405190830267680953

theorem tailTrace_922568 : CollatzResearch.WordTrace tailWord_922568 prefixEnd_922568 5848405190830267680953 := by
  unfold tailWord_922568
  simp only [CollatzResearch.WordTrace]
  refine ⟨16824409660850586457676179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22432546214467448610234905 16824409660850586457676179)
  ·
    refine ⟨25236614491275879686514269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16824409660850586457676179 25236614491275879686514269)
    ·
      refine ⟨9463730434228454882442851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25236614491275879686514269 9463730434228454882442851)
      ·
        refine ⟨14195595651342682323664277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9463730434228454882442851 14195595651342682323664277)
        ·
          refine ⟨665418546156688233921763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14195595651342682323664277 665418546156688233921763)
          ·
            refine ⟨998127819235032350882645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665418546156688233921763 998127819235032350882645)
            ·
              refine ⟨5848405190830267680953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 998127819235032350882645 5848405190830267680953)
              ·
                rfl

theorem cell23_922568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 9].length) (baseStart_922568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922568 prefixEnd_922568 := by exact prefixLift 922568
  have htrace : WordTrace (prefixWord ++ tailWord_922568) baseStart_922568 baseEnd_922568 := by
    simpa [prefixWord, tailWord_922568, baseEnd_922568] using wordTrace_append hprefix tailTrace_922568
  have hstable : (prefixWord ++ tailWord_922568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922568).length < 2 ^ (prefixWord ++ tailWord_922568).sum := by decide
  have hdescent : baseEnd_922568 < baseStart_922568 := by decide
  rcases family_descends (prefixWord ++ tailWord_922568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922573 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_922573 : Nat := 118140960795 + 922573 * 2 ^ 59
def prefixEnd_922573 : Nat := 4983230072969 + 3 ^ 40 * 922573 * 2
def baseEnd_922573 : Nat := 473723387860524162594671

theorem tailTrace_922573 : CollatzResearch.WordTrace tailWord_922573 prefixEnd_922573 473723387860524162594671 := by
  unfold tailWord_922573
  simp only [CollatzResearch.WordTrace]
  refine ⟨33649001686683058769284373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22432667791122039179522915 33649001686683058769284373)
  ·
    refine ⟨1577296954063268379810205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33649001686683058769284373 1577296954063268379810205)
    ·
      refine ⟨591486357773725642428827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1577296954063268379810205 591486357773725642428827)
      ·
        refine ⟨887229536660588463643241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591486357773725642428827 887229536660588463643241)
        ·
          refine ⟨665422152495441347732431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 887229536660588463643241 665422152495441347732431)
          ·
            refine ⟨998133228743162021598647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665422152495441347732431 998133228743162021598647)
            ·
              refine ⟨1497199843114743032397971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998133228743162021598647 1497199843114743032397971)
              ·
                refine ⟨2245799764672114548596957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497199843114743032397971 2245799764672114548596957)
                ·
                  refine ⟨842174911752042955723859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2245799764672114548596957 842174911752042955723859)
                  ·
                    refine ⟨1263262367628064433585789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 842174911752042955723859 1263262367628064433585789)
                    ·
                      refine ⟨473723387860524162594671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1263262367628064433585789 473723387860524162594671)
                      ·
                        rfl

theorem cell23_922573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_922573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922573 prefixEnd_922573 := by exact prefixLift 922573
  have htrace : WordTrace (prefixWord ++ tailWord_922573) baseStart_922573 baseEnd_922573 := by
    simpa [prefixWord, tailWord_922573, baseEnd_922573] using wordTrace_append hprefix tailTrace_922573
  have hstable : (prefixWord ++ tailWord_922573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922573).length < 2 ^ (prefixWord ++ tailWord_922573).sum := by decide
  have hdescent : baseEnd_922573 < baseStart_922573 := by decide
  rcases family_descends (prefixWord ++ tailWord_922573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922595 : List Nat := [1, 1, 1, 6, 1, 1, 3, 3, 2, 1, 3]
def baseStart_922595 : Nat := 118140960795 + 922595 * 2 ^ 59
def prefixEnd_922595 : Nat := 4983230072969 + 3 ^ 40 * 922595 * 2
def baseEnd_922595 : Nat := 473734684434923076519569

theorem tailTrace_922595 : CollatzResearch.WordTrace tailWord_922595 prefixEnd_922595 473734684434923076519569 := by
  unfold tailWord_922595
  simp only [CollatzResearch.WordTrace]
  refine ⟨33649804092603356526585239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22433202728402237684390159 33649804092603356526585239)
  ·
    refine ⟨50474706138905034789877859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33649804092603356526585239 50474706138905034789877859)
    ·
      refine ⟨75712059208357552184816789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50474706138905034789877859 75712059208357552184816789)
      ·
        refine ⟨3549002775391760258663287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75712059208357552184816789 3549002775391760258663287)
        ·
          refine ⟨5323504163087640387994931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3549002775391760258663287 5323504163087640387994931)
          ·
            refine ⟨7985256244631460581992397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5323504163087640387994931 7985256244631460581992397)
            ·
              refine ⟨2994471091736797718247149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7985256244631460581992397 2994471091736797718247149)
              ·
                refine ⟨1122926659401299144342681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2994471091736797718247149 1122926659401299144342681)
                ·
                  refine ⟨842194994550974358257011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1122926659401299144342681 842194994550974358257011)
                  ·
                    refine ⟨1263292491826461537385517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 842194994550974358257011 1263292491826461537385517)
                    ·
                      refine ⟨473734684434923076519569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1263292491826461537385517 473734684434923076519569)
                      ·
                        rfl

theorem cell23_922595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_922595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922595 prefixEnd_922595 := by exact prefixLift 922595
  have htrace : WordTrace (prefixWord ++ tailWord_922595) baseStart_922595 baseEnd_922595 := by
    simpa [prefixWord, tailWord_922595, baseEnd_922595] using wordTrace_append hprefix tailTrace_922595
  have hstable : (prefixWord ++ tailWord_922595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922595).length < 2 ^ (prefixWord ++ tailWord_922595).sum := by decide
  have hdescent : baseEnd_922595 < baseStart_922595 := by decide
  rcases family_descends (prefixWord ++ tailWord_922595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922638 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_922638 : Nat := 118140960795 + 922638 * 2 ^ 59
def prefixEnd_922638 : Nat := 4983230072969 + 3 ^ 40 * 922638 * 2
def baseEnd_922638 : Nat := 473756764103066408281871

theorem tailTrace_922638 : CollatzResearch.WordTrace tailWord_922638 prefixEnd_922638 473756764103066408281871 := by
  unfold tailWord_922638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4206421553930946858800071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22434248287631716580267045 4206421553930946858800071)
  ·
    refine ⟨6309632330896420288200107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4206421553930946858800071 6309632330896420288200107)
    ·
      refine ⟨9464448496344630432300161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6309632330896420288200107 9464448496344630432300161)
      ·
        refine ⟨7098336372258472824225121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9464448496344630432300161 7098336372258472824225121)
        ·
          refine ⟨5323752279193854618168841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7098336372258472824225121 5323752279193854618168841)
          ·
            refine ⟨3992814209395390963626631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5323752279193854618168841 3992814209395390963626631)
            ·
              refine ⟨5989221314093086445439947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992814209395390963626631 5989221314093086445439947)
              ·
                refine ⟨8983831971139629668159921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5989221314093086445439947 8983831971139629668159921)
                ·
                  refine ⟨6737873978354722251119941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8983831971139629668159921 6737873978354722251119941)
                  ·
                    refine ⟨1263351370941510422084989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6737873978354722251119941 1263351370941510422084989)
                    ·
                      refine ⟨473756764103066408281871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1263351370941510422084989 473756764103066408281871)
                      ·
                        rfl

theorem cell23_922638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_922638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922638 prefixEnd_922638 := by exact prefixLift 922638
  have htrace : WordTrace (prefixWord ++ tailWord_922638) baseStart_922638 baseEnd_922638 := by
    simpa [prefixWord, tailWord_922638, baseEnd_922638] using wordTrace_append hprefix tailTrace_922638
  have hstable : (prefixWord ++ tailWord_922638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922638).length < 2 ^ (prefixWord ++ tailWord_922638).sum := by decide
  have hdescent : baseEnd_922638 < baseStart_922638 := by decide
  rcases family_descends (prefixWord ++ tailWord_922638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922648 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 2, 2, 4]
def baseStart_922648 : Nat := 118140960795 + 922648 * 2 ^ 59
def prefixEnd_922648 : Nat := 4983230072969 + 3 ^ 40 * 922648 * 2
def baseEnd_922648 : Nat := 473761898909611369156825

theorem tailTrace_922648 : CollatzResearch.WordTrace tailWord_922648 prefixEnd_922648 473761898909611369156825 := by
  unfold tailWord_922648
  simp only [CollatzResearch.WordTrace]
  refine ⟨16825868580705673289132299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22434491440940897718843065 16825868580705673289132299)
  ·
    refine ⟨25238802871058509933698449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16825868580705673289132299 25238802871058509933698449)
    ·
      refine ⟨18929102153293882450273837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25238802871058509933698449 18929102153293882450273837)
      ·
        refine ⟨7098413307485205918852689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18929102153293882450273837 7098413307485205918852689)
        ·
          refine ⟨5323809980613904439139517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7098413307485205918852689 5323809980613904439139517)
          ·
            refine ⟨1996428742730214164677319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5323809980613904439139517 1996428742730214164677319)
            ·
              refine ⟨2994643114095321247015979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996428742730214164677319 2994643114095321247015979)
              ·
                refine ⟨4491964671142981870523969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2994643114095321247015979 4491964671142981870523969)
                ·
                  refine ⟨3368973503357236402892977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4491964671142981870523969 3368973503357236402892977)
                  ·
                    refine ⟨2526730127517927302169733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3368973503357236402892977 2526730127517927302169733)
                    ·
                      refine ⟨473761898909611369156825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2526730127517927302169733 473761898909611369156825)
                      ·
                        rfl

theorem cell23_922648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_922648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922648 prefixEnd_922648 := by exact prefixLift 922648
  have htrace : WordTrace (prefixWord ++ tailWord_922648) baseStart_922648 baseEnd_922648 := by
    simpa [prefixWord, tailWord_922648, baseEnd_922648] using wordTrace_append hprefix tailTrace_922648
  have hstable : (prefixWord ++ tailWord_922648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922648).length < 2 ^ (prefixWord ++ tailWord_922648).sum := by decide
  have hdescent : baseEnd_922648 < baseStart_922648 := by decide
  rcases family_descends (prefixWord ++ tailWord_922648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922652 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_922652 : Nat := 118140960795 + 922652 * 2 ^ 59
def prefixEnd_922652 : Nat := 4983230072969 + 3 ^ 40 * 922652 * 2
def baseEnd_922652 : Nat := 473763952832229353506807

theorem tailTrace_922652 : CollatzResearch.WordTrace tailWord_922652 prefixEnd_922652 473763952832229353506807 := by
  unfold tailWord_922652
  simp only [CollatzResearch.WordTrace]
  refine ⟨16825941526698427630705105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22434588702264570174273473 16825941526698427630705105)
  ·
    refine ⟨12619456145023820723028829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16825941526698427630705105 12619456145023820723028829)
    ·
      refine ⟨4732296054383932771135811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12619456145023820723028829 4732296054383932771135811)
      ·
        refine ⟨7098444081575899156703717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4732296054383932771135811 7098444081575899156703717)
        ·
          refine ⟨1330958265295481091881947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7098444081575899156703717 1330958265295481091881947)
          ·
            refine ⟨1996437397943221637822921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330958265295481091881947 1996437397943221637822921)
            ·
              refine ⟨1497328048457416228367191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1996437397943221637822921 1497328048457416228367191)
              ·
                refine ⟨2245992072686124342550787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497328048457416228367191 2245992072686124342550787)
                ·
                  refine ⟨3368988109029186513826181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2245992072686124342550787 3368988109029186513826181)
                  ·
                    refine ⟨631685270442972471342409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3368988109029186513826181 631685270442972471342409)
                    ·
                      refine ⟨473763952832229353506807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 631685270442972471342409 473763952832229353506807)
                      ·
                        rfl

theorem cell23_922652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_922652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922652 prefixEnd_922652 := by exact prefixLift 922652
  have htrace : WordTrace (prefixWord ++ tailWord_922652) baseStart_922652 baseEnd_922652 := by
    simpa [prefixWord, tailWord_922652, baseEnd_922652] using wordTrace_append hprefix tailTrace_922652
  have hstable : (prefixWord ++ tailWord_922652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922652).length < 2 ^ (prefixWord ++ tailWord_922652).sum := by decide
  have hdescent : baseEnd_922652 < baseStart_922652 := by decide
  rcases family_descends (prefixWord ++ tailWord_922652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922658 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 7]
def baseStart_922658 : Nat := 118140960795 + 922658 * 2 ^ 59
def prefixEnd_922658 : Nat := 4983230072969 + 3 ^ 40 * 922658 * 2
def baseEnd_922658 : Nat := 52640781524017370003531

theorem tailTrace_922658 : CollatzResearch.WordTrace tailWord_922658 prefixEnd_922658 52640781524017370003531 := by
  unfold tailWord_922658
  simp only [CollatzResearch.WordTrace]
  refine ⟨8413025472843779571532157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22434734594250078857419085 8413025472843779571532157)
  ·
    refine ⟨3154884552316417339324559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8413025472843779571532157 3154884552316417339324559)
    ·
      refine ⟨4732326828474626008986839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3154884552316417339324559 4732326828474626008986839)
      ·
        refine ⟨7098490242711939013480259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4732326828474626008986839 7098490242711939013480259)
        ·
          refine ⟨10647735364067908520220389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7098490242711939013480259 10647735364067908520220389)
          ·
            refine ⟨1996450380762732847541323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10647735364067908520220389 1996450380762732847541323)
            ·
              refine ⟨2994675571144099271311985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996450380762732847541323 2994675571144099271311985)
              ·
                refine ⟨2246006678358074453483989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2994675571144099271311985 2246006678358074453483989)
                ·
                  refine ⟨52640781524017370003531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2246006678358074453483989 52640781524017370003531)
                  ·
                    rfl

theorem cell23_922658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_922658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922658 prefixEnd_922658 := by exact prefixLift 922658
  have htrace : WordTrace (prefixWord ++ tailWord_922658) baseStart_922658 baseEnd_922658 := by
    simpa [prefixWord, tailWord_922658, baseEnd_922658] using wordTrace_append hprefix tailTrace_922658
  have hstable : (prefixWord ++ tailWord_922658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922658).length < 2 ^ (prefixWord ++ tailWord_922658).sum := by decide
  have hdescent : baseEnd_922658 < baseStart_922658 := by decide
  rcases family_descends (prefixWord ++ tailWord_922658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922686 : List Nat := [4, 2, 1, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_922686 : Nat := 118140960795 + 922686 * 2 ^ 59
def prefixEnd_922686 : Nat := 4983230072969 + 3 ^ 40 * 922686 * 2
def baseEnd_922686 : Nat := 473781411174482220481651

theorem tailTrace_922686 : CollatzResearch.WordTrace tailWord_922686 prefixEnd_922686 473781411174482220481651 := by
  unfold tailWord_922686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4206640391909209883518489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22435415423515786045431941 4206640391909209883518489)
  ·
    refine ⟨3154980293931907412638867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4206640391909209883518489 3154980293931907412638867)
    ·
      refine ⟨4732470440897861118958301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3154980293931907412638867 4732470440897861118958301)
      ·
        refine ⟨1774676415336697919609363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4732470440897861118958301 1774676415336697919609363)
        ·
          refine ⟨2662014623005046879414045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1774676415336697919609363 2662014623005046879414045)
          ·
            refine ⟨998255483626892579780267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2662014623005046879414045 998255483626892579780267)
            ·
              refine ⟨1497383225440338869670401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998255483626892579780267 1497383225440338869670401)
              ·
                refine ⟨1123037419080254152252801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497383225440338869670401 1123037419080254152252801)
                ·
                  refine ⟨842278064310190614189601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1123037419080254152252801 842278064310190614189601)
                  ·
                    refine ⟨631708548232642960642201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 842278064310190614189601 631708548232642960642201)
                    ·
                      refine ⟨473781411174482220481651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 631708548232642960642201 473781411174482220481651)
                      ·
                        rfl

theorem cell23_922686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_922686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922686 prefixEnd_922686 := by exact prefixLift 922686
  have htrace : WordTrace (prefixWord ++ tailWord_922686) baseStart_922686 baseEnd_922686 := by
    simpa [prefixWord, tailWord_922686, baseEnd_922686] using wordTrace_append hprefix tailTrace_922686
  have hstable : (prefixWord ++ tailWord_922686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922686).length < 2 ^ (prefixWord ++ tailWord_922686).sum := by decide
  have hdescent : baseEnd_922686 < baseStart_922686 := by decide
  rcases family_descends (prefixWord ++ tailWord_922686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922708 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_922708 : Nat := 118140960795 + 922708 * 2 ^ 59
def prefixEnd_922708 : Nat := 4983230072969 + 3 ^ 40 * 922708 * 2
def baseEnd_922708 : Nat := 473792707748881134406549

theorem tailTrace_922708 : CollatzResearch.WordTrace tailWord_922708 prefixEnd_922708 473792707748881134406549 := by
  unfold tailWord_922708
  simp only [CollatzResearch.WordTrace]
  refine ⟨16826962770596988412724389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22435950360795984550299185 16826962770596988412724389)
  ·
    refine ⟨3155055519486935327385823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16826962770596988412724389 3155055519486935327385823)
    ·
      refine ⟨4732583279230402991078735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3155055519486935327385823 4732583279230402991078735)
      ·
        refine ⟨7098874918845604486618103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4732583279230402991078735 7098874918845604486618103)
        ·
          refine ⟨10648312378268406729927155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7098874918845604486618103 10648312378268406729927155)
          ·
            refine ⟨15972468567402610094890733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10648312378268406729927155 15972468567402610094890733)
            ·
              refine ⟨5989675712775978785584025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15972468567402610094890733 5989675712775978785584025)
              ·
                refine ⟨4492256784581984089188019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5989675712775978785584025 4492256784581984089188019)
                ·
                  refine ⟨6738385176872976133782029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4492256784581984089188019 6738385176872976133782029)
                  ·
                    refine ⟨2526894441327366050168261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6738385176872976133782029 2526894441327366050168261)
                    ·
                      refine ⟨473792707748881134406549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2526894441327366050168261 473792707748881134406549)
                      ·
                        rfl

theorem cell23_922708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_922708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922708 prefixEnd_922708 := by exact prefixLift 922708
  have htrace : WordTrace (prefixWord ++ tailWord_922708) baseStart_922708 baseEnd_922708 := by
    simpa [prefixWord, tailWord_922708, baseEnd_922708] using wordTrace_append hprefix tailTrace_922708
  have hstable : (prefixWord ++ tailWord_922708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922708).length < 2 ^ (prefixWord ++ tailWord_922708).sum := by decide
  have hdescent : baseEnd_922708 < baseStart_922708 := by decide
  rcases family_descends (prefixWord ++ tailWord_922708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922748 : List Nat := [2, 2, 2, 1, 1, 3, 2, 4, 6]
def baseStart_922748 : Nat := 118140960795 + 922748 * 2 ^ 59
def prefixEnd_922748 : Nat := 4983230072969 + 3 ^ 40 * 922748 * 2
def baseEnd_922748 : Nat := 52645916330562330878485

theorem tailTrace_922748 : CollatzResearch.WordTrace tailWord_922748 prefixEnd_922748 52645916330562330878485 := by
  unfold tailWord_922748
  simp only [CollatzResearch.WordTrace]
  refine ⟨16827692230524531828452449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22436922974032709104603265 16827692230524531828452449)
  ·
    refine ⟨12620769172893398871339337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16827692230524531828452449 12620769172893398871339337)
    ·
      refine ⟨9465576879670049153504503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12620769172893398871339337 9465576879670049153504503)
      ·
        refine ⟨14198365319505073730256755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9465576879670049153504503 14198365319505073730256755)
        ·
          refine ⟨21297547979257610595385133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14198365319505073730256755 21297547979257610595385133)
          ·
            refine ⟨7986580492221603973269425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21297547979257610595385133 7986580492221603973269425)
            ·
              refine ⟨5989935369166202979952069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7986580492221603973269425 5989935369166202979952069)
              ·
                refine ⟨1123112881718663058741013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5989935369166202979952069 1123112881718663058741013)
                ·
                  refine ⟨52645916330562330878485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1123112881718663058741013 52645916330562330878485)
                  ·
                    rfl

theorem cell23_922748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 6].length) (baseStart_922748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922748 prefixEnd_922748 := by exact prefixLift 922748
  have htrace : WordTrace (prefixWord ++ tailWord_922748) baseStart_922748 baseEnd_922748 := by
    simpa [prefixWord, tailWord_922748, baseEnd_922748] using wordTrace_append hprefix tailTrace_922748
  have hstable : (prefixWord ++ tailWord_922748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922748).length < 2 ^ (prefixWord ++ tailWord_922748).sum := by decide
  have hdescent : baseEnd_922748 < baseStart_922748 := by decide
  rcases family_descends (prefixWord ++ tailWord_922748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922802 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2]
def baseStart_922802 : Nat := 118140960795 + 922802 * 2 ^ 59
def prefixEnd_922802 : Nat := 4983230072969 + 3 ^ 40 * 922802 * 2
def baseEnd_922802 : Nat := 473840974930403766631117

theorem tailTrace_922802 : CollatzResearch.WordTrace tailWord_922802 prefixEnd_922802 473840974930403766631117 := by
  unfold tailWord_922802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8414338500713357719842665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22438236001902287252913773 8414338500713357719842665)
  ·
    refine ⟨6310753875535018289881999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8414338500713357719842665 6310753875535018289881999)
    ·
      refine ⟨9466130813302527434822999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6310753875535018289881999 9466130813302527434822999)
      ·
        refine ⟨14199196219953791152234499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9466130813302527434822999 14199196219953791152234499)
        ·
          refine ⟨21298794329930686728351749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14199196219953791152234499 21298794329930686728351749)
          ·
            refine ⟨3993523936862003761565953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21298794329930686728351749 3993523936862003761565953)
            ·
              refine ⟨2995142952646502821174465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3993523936862003761565953 2995142952646502821174465)
              ·
                refine ⟨2246357214484877115880849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2995142952646502821174465 2246357214484877115880849)
                ·
                  refine ⟨1684767910863657836910637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2246357214484877115880849 1684767910863657836910637)
                  ·
                    refine ⟨631787966573871688841489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1684767910863657836910637 631787966573871688841489)
                    ·
                      refine ⟨473840974930403766631117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 631787966573871688841489 473840974930403766631117)
                      ·
                        rfl

theorem cell23_922802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_922802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922802 prefixEnd_922802 := by exact prefixLift 922802
  have htrace : WordTrace (prefixWord ++ tailWord_922802) baseStart_922802 baseEnd_922802 := by
    simpa [prefixWord, tailWord_922802, baseEnd_922802] using wordTrace_append hprefix tailTrace_922802
  have hstable : (prefixWord ++ tailWord_922802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922802).length < 2 ^ (prefixWord ++ tailWord_922802).sum := by decide
  have hdescent : baseEnd_922802 < baseStart_922802 := by decide
  rcases family_descends (prefixWord ++ tailWord_922802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922809 : List Nat := [1, 2, 1, 4, 1, 4, 1, 4, 1, 1, 3]
def baseStart_922809 : Nat := 118140960795 + 922809 * 2 ^ 59
def prefixEnd_922809 : Nat := 4983230072969 + 3 ^ 40 * 922809 * 2
def baseEnd_922809 : Nat := 473844569294985239243585

theorem tailTrace_922809 : CollatzResearch.WordTrace tailWord_922809 prefixEnd_922809 473844569294985239243585 := by
  unfold tailWord_922809
  simp only [CollatzResearch.WordTrace]
  refine ⟨33657609313828071074875481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22438406209218714049916987 33657609313828071074875481)
  ·
    refine ⟨25243206985371053306156611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33657609313828071074875481 25243206985371053306156611)
    ·
      refine ⟨37864810478056579959234917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25243206985371053306156611 37864810478056579959234917)
      ·
        refine ⟨7099651964635608742356547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37864810478056579959234917 7099651964635608742356547)
        ·
          refine ⟨10649477946953413113534821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7099651964635608742356547 10649477946953413113534821)
          ·
            refine ⟨1996777115053764958787779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10649477946953413113534821 1996777115053764958787779)
            ·
              refine ⟨2995165672580647438181669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996777115053764958787779 2995165672580647438181669)
              ·
                refine ⟨561593563608871394659063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2995165672580647438181669 561593563608871394659063)
                ·
                  refine ⟨842390345413307091988595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561593563608871394659063 842390345413307091988595)
                  ·
                    refine ⟨1263585518119960637982893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 842390345413307091988595 1263585518119960637982893)
                    ·
                      refine ⟨473844569294985239243585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1263585518119960637982893 473844569294985239243585)
                      ·
                        rfl

theorem cell23_922809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_922809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922809 prefixEnd_922809 := by exact prefixLift 922809
  have htrace : WordTrace (prefixWord ++ tailWord_922809) baseStart_922809 baseEnd_922809 := by
    simpa [prefixWord, tailWord_922809, baseEnd_922809] using wordTrace_append hprefix tailTrace_922809
  have hstable : (prefixWord ++ tailWord_922809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922809).length < 2 ^ (prefixWord ++ tailWord_922809).sum := by decide
  have hdescent : baseEnd_922809 < baseStart_922809 := by decide
  rcases family_descends (prefixWord ++ tailWord_922809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922849 : List Nat := [1, 2, 3, 1, 3, 4, 2, 1, 1, 1, 4]
def baseStart_922849 : Nat := 118140960795 + 922849 * 2 ^ 59
def prefixEnd_922849 : Nat := 4983230072969 + 3 ^ 40 * 922849 * 2
def baseEnd_922849 : Nat := 473865108521165082743401

theorem tailTrace_922849 : CollatzResearch.WordTrace tailWord_922849 prefixEnd_922849 473865108521165082743401 := by
  unfold tailWord_922849
  simp only [CollatzResearch.WordTrace]
  refine ⟨33659068233683157906331601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22439378822455438604221067 33659068233683157906331601)
  ·
    refine ⟨25244301175262368429748701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33659068233683157906331601 25244301175262368429748701)
    ·
      refine ⟨9466612940723388161155763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25244301175262368429748701 9466612940723388161155763)
      ·
        refine ⟨14199919411085082241733645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9466612940723388161155763 14199919411085082241733645)
        ·
          refine ⟨5324969779156905840650117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14199919411085082241733645 5324969779156905840650117)
          ·
            refine ⟨998431833591919845121897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5324969779156905840650117 998431833591919845121897)
            ·
              refine ⟨748823875193939883841423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998431833591919845121897 748823875193939883841423)
              ·
                refine ⟨1123235812790909825762135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748823875193939883841423 1123235812790909825762135)
                ·
                  refine ⟨1684853719186364738643203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123235812790909825762135 1684853719186364738643203)
                  ·
                    refine ⟨2527280578779547107964805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1684853719186364738643203 2527280578779547107964805)
                    ·
                      refine ⟨473865108521165082743401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2527280578779547107964805 473865108521165082743401)
                      ·
                        rfl

theorem cell23_922849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_922849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922849 prefixEnd_922849 := by exact prefixLift 922849
  have htrace : WordTrace (prefixWord ++ tailWord_922849) baseStart_922849 baseEnd_922849 := by
    simpa [prefixWord, tailWord_922849, baseEnd_922849] using wordTrace_append hprefix tailTrace_922849
  have hstable : (prefixWord ++ tailWord_922849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922849).length < 2 ^ (prefixWord ++ tailWord_922849).sum := by decide
  have hdescent : baseEnd_922849 < baseStart_922849 := by decide
  rcases family_descends (prefixWord ++ tailWord_922849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922855 : List Nat := [1, 1, 5, 3, 2, 1, 10]
def baseStart_922855 : Nat := 118140960795 + 922855 * 2 ^ 59
def prefixEnd_922855 : Nat := 4983230072969 + 3 ^ 40 * 922855 * 2
def baseEnd_922855 : Nat := 5850224560556692089733

theorem tailTrace_922855 : CollatzResearch.WordTrace tailWord_922855 prefixEnd_922855 5850224560556692089733 := by
  unfold tailWord_922855
  simp only [CollatzResearch.WordTrace]
  refine ⟨33659287071661420931050019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22439524714440947287366679 33659287071661420931050019)
  ·
    refine ⟨50488930607492131396575029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33659287071661420931050019 50488930607492131396575029)
    ·
      refine ⟨4733337244452387318428909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50488930607492131396575029 4733337244452387318428909)
      ·
        refine ⟨1775001466669645244410841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4733337244452387318428909 1775001466669645244410841)
        ·
          refine ⟨1331251100002233933308131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1775001466669645244410841 1331251100002233933308131)
          ·
            refine ⟨1996876650003350899962197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331251100002233933308131 1996876650003350899962197)
            ·
              refine ⟨5850224560556692089733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1996876650003350899962197 5850224560556692089733)
              ·
                rfl

theorem cell23_922855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 10].length) (baseStart_922855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922855 prefixEnd_922855 := by exact prefixLift 922855
  have htrace : WordTrace (prefixWord ++ tailWord_922855) baseStart_922855 baseEnd_922855 := by
    simpa [prefixWord, tailWord_922855, baseEnd_922855] using wordTrace_append hprefix tailTrace_922855
  have hstable : (prefixWord ++ tailWord_922855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922855).length < 2 ^ (prefixWord ++ tailWord_922855).sum := by decide
  have hdescent : baseEnd_922855 < baseStart_922855 := by decide
  rcases family_descends (prefixWord ++ tailWord_922855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922866 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 3, 2, 2]
def baseStart_922866 : Nat := 118140960795 + 922866 * 2 ^ 59
def prefixEnd_922866 : Nat := 4983230072969 + 3 ^ 40 * 922866 * 2
def baseEnd_922866 : Nat := 473873837692291516230823

theorem tailTrace_922866 : CollatzResearch.WordTrace tailWord_922866 prefixEnd_922866 473873837692291516230823 := by
  unfold tailWord_922866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8414922068655392452425113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22439792183081046539800301 8414922068655392452425113)
  ·
    refine ⟨6311191551491544339318835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8414922068655392452425113 6311191551491544339318835)
    ·
      refine ⟨9466787327237316508978253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6311191551491544339318835 9466787327237316508978253)
      ·
        refine ⟨3550045247713993690866845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9466787327237316508978253 3550045247713993690866845)
        ·
          refine ⟨1331266967892747634075067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3550045247713993690866845 1331266967892747634075067)
          ·
            refine ⟨1996900451839121451112601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331266967892747634075067 1996900451839121451112601)
            ·
              refine ⟨1497675338879341088334451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1996900451839121451112601 1497675338879341088334451)
              ·
                refine ⟨2246513008319011632501677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497675338879341088334451 2246513008319011632501677)
                ·
                  refine ⟨842442378119629362188129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2246513008319011632501677 842442378119629362188129)
                  ·
                    refine ⟨631831783589722021641097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 842442378119629362188129 631831783589722021641097)
                    ·
                      refine ⟨473873837692291516230823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 631831783589722021641097 473873837692291516230823)
                      ·
                        rfl

theorem cell23_922866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_922866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922866 prefixEnd_922866 := by exact prefixLift 922866
  have htrace : WordTrace (prefixWord ++ tailWord_922866) baseStart_922866 baseEnd_922866 := by
    simpa [prefixWord, tailWord_922866, baseEnd_922866] using wordTrace_append hprefix tailTrace_922866
  have hstable : (prefixWord ++ tailWord_922866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922866).length < 2 ^ (prefixWord ++ tailWord_922866).sum := by decide
  have hdescent : baseEnd_922866 < baseStart_922866 := by decide
  rcases family_descends (prefixWord ++ tailWord_922866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922962 : List Nat := [3, 2, 2, 1, 1, 1, 1, 7, 5]
def baseStart_922962 : Nat := 118140960795 + 922962 * 2 ^ 59
def prefixEnd_922962 : Nat := 4983230072969 + 3 ^ 40 * 922962 * 2
def baseEnd_922962 : Nat := 52658125759458126736709

theorem tailTrace_922962 : CollatzResearch.WordTrace tailWord_922962 prefixEnd_922962 52658125759458126736709 := by
  unfold tailWord_922962
  simp only [CollatzResearch.WordTrace]
  refine ⟨8415797420568444551298785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22442126454849185470130093 8415797420568444551298785)
  ·
    refine ⟨6311848065426333413474089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8415797420568444551298785 6311848065426333413474089)
    ·
      refine ⟨4733886049069750060105567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6311848065426333413474089 4733886049069750060105567)
      ·
        refine ⟨7100829073604625090158351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4733886049069750060105567 7100829073604625090158351)
        ·
          refine ⟨10651243610406937635237527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7100829073604625090158351 10651243610406937635237527)
          ·
            refine ⟨15976865415610406452856291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10651243610406937635237527 15976865415610406452856291)
            ·
              refine ⟨23965298123415609679284437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15976865415610406452856291 23965298123415609679284437)
              ·
                refine ⟨561686674767553351858229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23965298123415609679284437 561686674767553351858229)
                ·
                  refine ⟨52658125759458126736709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 561686674767553351858229 52658125759458126736709)
                  ·
                    rfl

theorem cell23_922962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_922962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922962 prefixEnd_922962 := by exact prefixLift 922962
  have htrace : WordTrace (prefixWord ++ tailWord_922962) baseStart_922962 baseEnd_922962 := by
    simpa [prefixWord, tailWord_922962, baseEnd_922962] using wordTrace_append hprefix tailTrace_922962
  have hstable : (prefixWord ++ tailWord_922962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922962).length < 2 ^ (prefixWord ++ tailWord_922962).sum := by decide
  have hdescent : baseEnd_922962 < baseStart_922962 := by decide
  rcases family_descends (prefixWord ++ tailWord_922962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922979 : List Nat := [1, 1, 1, 5, 2, 2, 4, 2, 5]
def baseStart_922979 : Nat := 118140960795 + 922979 * 2 ^ 59
def prefixEnd_922979 : Nat := 4983230072969 + 3 ^ 40 * 922979 * 2
def baseEnd_922979 : Nat := 52659095667361063790867

theorem tailTrace_922979 : CollatzResearch.WordTrace tailWord_922979 prefixEnd_922979 52659095667361063790867 := by
  unfold tailWord_922979
  simp only [CollatzResearch.WordTrace]
  refine ⟨33663809723212190108563991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22442539815474793405709327 33663809723212190108563991)
  ·
    refine ⟨50495714584818285162845987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33663809723212190108563991 50495714584818285162845987)
    ·
      refine ⟨75743571877227427744268981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50495714584818285162845987 75743571877227427744268981)
      ·
        refine ⟨7100959863490071351025217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75743571877227427744268981 7100959863490071351025217)
        ·
          refine ⟨5325719897617553513268913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7100959863490071351025217 5325719897617553513268913)
          ·
            refine ⟨3994289923213165134951685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5325719897617553513268913 3994289923213165134951685)
            ·
              refine ⟨748929360602468462803441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3994289923213165134951685 748929360602468462803441)
              ·
                refine ⟨561697020451851347102581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748929360602468462803441 561697020451851347102581)
                ·
                  refine ⟨52659095667361063790867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 561697020451851347102581 52659095667361063790867)
                  ·
                    rfl

theorem cell23_922979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 5].length) (baseStart_922979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922979 prefixEnd_922979 := by exact prefixLift 922979
  have htrace : WordTrace (prefixWord ++ tailWord_922979) baseStart_922979 baseEnd_922979 := by
    simpa [prefixWord, tailWord_922979, baseEnd_922979] using wordTrace_append hprefix tailTrace_922979
  have hstable : (prefixWord ++ tailWord_922979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922979).length < 2 ^ (prefixWord ++ tailWord_922979).sum := by decide
  have hdescent : baseEnd_922979 < baseStart_922979 := by decide
  rcases family_descends (prefixWord ++ tailWord_922979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923012 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_923012 : Nat := 118140960795 + 923012 * 2 ^ 59
def prefixEnd_923012 : Nat := 4983230072969 + 3 ^ 40 * 923012 * 2
def baseEnd_923012 : Nat := 473948805867847945005151

theorem tailTrace_923012 : CollatzResearch.WordTrace tailWord_923012 prefixEnd_923012 473948805867847945005151 := by
  unfold tailWord_923012
  simp only [CollatzResearch.WordTrace]
  refine ⟨16832506666046318372257645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22443342221395091163010193 16832506666046318372257645)
  ·
    refine ⟨6312189999767369389596617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16832506666046318372257645 6312189999767369389596617)
    ·
      refine ⟨4734142499825527042197463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6312189999767369389596617 4734142499825527042197463)
      ·
        refine ⟨7101213749738290563296195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4734142499825527042197463 7101213749738290563296195)
        ·
          refine ⟨10651820624607435844944293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7101213749738290563296195 10651820624607435844944293)
          ·
            refine ⟨1997216367113894220927055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10651820624607435844944293 1997216367113894220927055)
            ·
              refine ⟨2995824550670841331390583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997216367113894220927055 2995824550670841331390583)
              ·
                refine ⟨4493736826006261997085875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995824550670841331390583 4493736826006261997085875)
                ·
                  refine ⟨6740605239009392995628813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493736826006261997085875 6740605239009392995628813)
                  ·
                    refine ⟨2527726964628522373360805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6740605239009392995628813 2527726964628522373360805)
                    ·
                      refine ⟨473948805867847945005151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2527726964628522373360805 473948805867847945005151)
                      ·
                        rfl

theorem cell23_923012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_923012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923012 prefixEnd_923012 := by exact prefixLift 923012
  have htrace : WordTrace (prefixWord ++ tailWord_923012) baseStart_923012 baseEnd_923012 := by
    simpa [prefixWord, tailWord_923012, baseEnd_923012] using wordTrace_append hprefix tailTrace_923012
  have hstable : (prefixWord ++ tailWord_923012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923012).length < 2 ^ (prefixWord ++ tailWord_923012).sum := by decide
  have hdescent : baseEnd_923012 < baseStart_923012 := by decide
  rcases family_descends (prefixWord ++ tailWord_923012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923039 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 3, 4]
def baseStart_923039 : Nat := 118140960795 + 923039 * 2 ^ 59
def prefixEnd_923039 : Nat := 4983230072969 + 3 ^ 40 * 923039 * 2
def baseEnd_923039 : Nat := 157987556615173113122509

theorem tailTrace_923039 : CollatzResearch.WordTrace tailWord_923039 prefixEnd_923039 157987556615173113122509 := by
  unfold tailWord_923039
  simp only [CollatzResearch.WordTrace]
  refine ⟨33665998102994820355748171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22443998735329880237165447 33665998102994820355748171)
  ·
    refine ⟨50498997154492230533622257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33665998102994820355748171 50498997154492230533622257)
    ·
      refine ⟨37874247865869172900216693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50498997154492230533622257 37874247865869172900216693)
      ·
        refine ⟨3550710737425234959395315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37874247865869172900216693 3550710737425234959395315)
        ·
          refine ⟨5326066106137852439092973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3550710737425234959395315 5326066106137852439092973)
          ·
            refine ⟨1997274789801694664659865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5326066106137852439092973 1997274789801694664659865)
            ·
              refine ⟨1497956092351270998494899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1997274789801694664659865 1497956092351270998494899)
              ·
                refine ⟨2246934138526906497742349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497956092351270998494899 2246934138526906497742349)
                ·
                  refine ⟨842600301947589936653381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2246934138526906497742349 842600301947589936653381)
                  ·
                    refine ⟨157987556615173113122509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 842600301947589936653381 157987556615173113122509)
                    ·
                      rfl

theorem cell23_923039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 4].length) (baseStart_923039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923039 prefixEnd_923039 := by exact prefixLift 923039
  have htrace : WordTrace (prefixWord ++ tailWord_923039) baseStart_923039 baseEnd_923039 := by
    simpa [prefixWord, tailWord_923039, baseEnd_923039] using wordTrace_append hprefix tailTrace_923039
  have hstable : (prefixWord ++ tailWord_923039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923039).length < 2 ^ (prefixWord ++ tailWord_923039).sum := by decide
  have hdescent : baseEnd_923039 < baseStart_923039 := by decide
  rcases family_descends (prefixWord ++ tailWord_923039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923096 : List Nat := [2, 1, 2, 2, 2, 1, 2, 6, 1, 1, 3]
def baseStart_923096 : Nat := 118140960795 + 923096 * 2 ^ 59
def prefixEnd_923096 : Nat := 4983230072969 + 3 ^ 40 * 923096 * 2
def baseEnd_923096 : Nat := 473991938242825616354765

theorem tailTrace_923096 : CollatzResearch.WordTrace tailWord_923096 prefixEnd_923096 473991938242825616354765 := by
  unfold tailWord_923096
  simp only [CollatzResearch.WordTrace]
  refine ⟨16834038531894159545286571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22445384709192212727048761 16834038531894159545286571)
  ·
    refine ⟨25251057797841239317929857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16834038531894159545286571 25251057797841239317929857)
    ·
      refine ⟨18938293348380929488447393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25251057797841239317929857 18938293348380929488447393)
      ·
        refine ⟨14203720011285697116335545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18938293348380929488447393 14203720011285697116335545)
        ·
          refine ⟨10652790008464272837251659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14203720011285697116335545 10652790008464272837251659)
          ·
            refine ⟨15979185012696409255877489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10652790008464272837251659 15979185012696409255877489)
            ·
              refine ⟨11984388759522306941908117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15979185012696409255877489 11984388759522306941908117)
              ·
                refine ⟨561768223102608137901943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11984388759522306941908117 561768223102608137901943)
                ·
                  refine ⟨842652334653912206852915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561768223102608137901943 842652334653912206852915)
                  ·
                    refine ⟨1263978501980868310279373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 842652334653912206852915 1263978501980868310279373)
                    ·
                      refine ⟨473991938242825616354765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1263978501980868310279373 473991938242825616354765)
                      ·
                        rfl

theorem cell23_923096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_923096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923096 prefixEnd_923096 := by exact prefixLift 923096
  have htrace : WordTrace (prefixWord ++ tailWord_923096) baseStart_923096 baseEnd_923096 := by
    simpa [prefixWord, tailWord_923096, baseEnd_923096] using wordTrace_append hprefix tailTrace_923096
  have hstable : (prefixWord ++ tailWord_923096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923096).length < 2 ^ (prefixWord ++ tailWord_923096).sum := by decide
  have hdescent : baseEnd_923096 < baseStart_923096 := by decide
  rcases family_descends (prefixWord ++ tailWord_923096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923112 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 1, 6]
def baseStart_923112 : Nat := 118140960795 + 923112 * 2 ^ 59
def prefixEnd_923112 : Nat := 4983230072969 + 3 ^ 40 * 923112 * 2
def baseEnd_923112 : Nat := 158000051311099184584897

theorem tailTrace_923112 : CollatzResearch.WordTrace tailWord_923112 prefixEnd_923112 158000051311099184584897 := by
  unfold tailWord_923112
  simp only [CollatzResearch.WordTrace]
  refine ⟨16834330315865176911577795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22445773754486902548770393 16834330315865176911577795)
  ·
    refine ⟨25251495473797765367366693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16834330315865176911577795 25251495473797765367366693)
    ·
      refine ⟨4734655401337081006381255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25251495473797765367366693 4734655401337081006381255)
      ·
        refine ⟨7101983102005621509571883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4734655401337081006381255 7101983102005621509571883)
        ·
          refine ⟨10652974653008432264357825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7101983102005621509571883 10652974653008432264357825)
          ·
            refine ⟨7989730989756324198268369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10652974653008432264357825 7989730989756324198268369)
            ·
              refine ⟨5992298242317243148701277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7989730989756324198268369 5992298242317243148701277)
              ·
                refine ⟨2247111840868966180762979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5992298242317243148701277 2247111840868966180762979)
                ·
                  refine ⟨3370667761303449271144469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247111840868966180762979 3370667761303449271144469)
                  ·
                    refine ⟨158000051311099184584897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3370667761303449271144469 158000051311099184584897)
                    ·
                      rfl

theorem cell23_923112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_923112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923112 prefixEnd_923112 := by exact prefixLift 923112
  have htrace : WordTrace (prefixWord ++ tailWord_923112) baseStart_923112 baseEnd_923112 := by
    simpa [prefixWord, tailWord_923112, baseEnd_923112] using wordTrace_append hprefix tailTrace_923112
  have hstable : (prefixWord ++ tailWord_923112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923112).length < 2 ^ (prefixWord ++ tailWord_923112).sum := by decide
  have hdescent : baseEnd_923112 < baseStart_923112 := by decide
  rcases family_descends (prefixWord ++ tailWord_923112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923119 : List Nat := [1, 1, 2, 1, 4, 1, 5, 2, 1, 1, 4]
def baseStart_923119 : Nat := 118140960795 + 923119 * 2 ^ 59
def prefixEnd_923119 : Nat := 4983230072969 + 3 ^ 40 * 923119 * 2
def baseEnd_923119 : Nat := 474003748297879026367159

theorem tailTrace_923119 : CollatzResearch.WordTrace tailWord_923119 prefixEnd_923119 474003748297879026367159 := by
  unfold tailWord_923119
  simp only [CollatzResearch.WordTrace]
  refine ⟨33668915942704994018660411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22445943961803329345773607 33668915942704994018660411)
  ·
    refine ⟨50503373914057491027990617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33668915942704994018660411 50503373914057491027990617)
    ·
      refine ⟨37877530435543118270992963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50503373914057491027990617 37877530435543118270992963)
      ·
        refine ⟨56816295653314677406489445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37877530435543118270992963 56816295653314677406489445)
        ·
          refine ⟨10653055434996502013716771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56816295653314677406489445 10653055434996502013716771)
          ·
            refine ⟨15979583152494753020575157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10653055434996502013716771 15979583152494753020575157)
            ·
              refine ⟨1498085920546383095678921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15979583152494753020575157 1498085920546383095678921)
              ·
                refine ⟨1123564440409787321759191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1498085920546383095678921 1123564440409787321759191)
                ·
                  refine ⟨1685346660614680982638787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123564440409787321759191 1685346660614680982638787)
                  ·
                    refine ⟨2528019990922021473958181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1685346660614680982638787 2528019990922021473958181)
                    ·
                      refine ⟨474003748297879026367159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2528019990922021473958181 474003748297879026367159)
                      ·
                        rfl

theorem cell23_923119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 1, 4].length) (baseStart_923119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923119 prefixEnd_923119 := by exact prefixLift 923119
  have htrace : WordTrace (prefixWord ++ tailWord_923119) baseStart_923119 baseEnd_923119 := by
    simpa [prefixWord, tailWord_923119, baseEnd_923119] using wordTrace_append hprefix tailTrace_923119
  have hstable : (prefixWord ++ tailWord_923119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923119).length < 2 ^ (prefixWord ++ tailWord_923119).sum := by decide
  have hdescent : baseEnd_923119 < baseStart_923119 := by decide
  rcases family_descends (prefixWord ++ tailWord_923119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923132 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_923132 : Nat := 118140960795 + 923132 * 2 ^ 59
def prefixEnd_923132 : Nat := 4983230072969 + 3 ^ 40 * 923132 * 2
def baseEnd_923132 : Nat := 474010423546387475504599

theorem tailTrace_923132 : CollatzResearch.WordTrace tailWord_923132 prefixEnd_923132 474010423546387475504599 := by
  unfold tailWord_923132
  simp only [CollatzResearch.WordTrace]
  refine ⟨16834695045828948619441825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22446260061105264825922433 16834695045828948619441825)
  ·
    refine ⟨12626021284371711464581369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16834695045828948619441825 12626021284371711464581369)
    ·
      refine ⟨9469515963278783598436027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12626021284371711464581369 9469515963278783598436027)
      ·
        refine ⟨14204273944918175397654041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9469515963278783598436027 14204273944918175397654041)
        ·
          refine ⟨10653205458688631548240531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14204273944918175397654041 10653205458688631548240531)
          ·
            refine ⟨15979808188032947322360797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10653205458688631548240531 15979808188032947322360797)
            ·
              refine ⟨5992428070512355245885299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15979808188032947322360797 5992428070512355245885299)
              ·
                refine ⟨8988642105768532868827949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5992428070512355245885299 8988642105768532868827949)
                ·
                  refine ⟨3370740789663199825810481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8988642105768532868827949 3370740789663199825810481)
                  ·
                    refine ⟨2528055592247399869357861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3370740789663199825810481 2528055592247399869357861)
                    ·
                      refine ⟨474010423546387475504599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2528055592247399869357861 474010423546387475504599)
                      ·
                        rfl

theorem cell23_923132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_923132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923132 prefixEnd_923132 := by exact prefixLift 923132
  have htrace : WordTrace (prefixWord ++ tailWord_923132) baseStart_923132 baseEnd_923132 := by
    simpa [prefixWord, tailWord_923132, baseEnd_923132] using wordTrace_append hprefix tailTrace_923132
  have hstable : (prefixWord ++ tailWord_923132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923132).length < 2 ^ (prefixWord ++ tailWord_923132).sum := by decide
  have hdescent : baseEnd_923132 < baseStart_923132 := by decide
  rcases family_descends (prefixWord ++ tailWord_923132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923146 : List Nat := [3, 1, 2, 2, 2, 3, 2, 2, 2, 4]
def baseStart_923146 : Nat := 118140960795 + 923146 * 2 ^ 59
def prefixEnd_923146 : Nat := 4983230072969 + 3 ^ 40 * 923146 * 2
def baseEnd_923146 : Nat := 158005870758516806909845

theorem tailTrace_923146 : CollatzResearch.WordTrace tailWord_923146 prefixEnd_923146 158005870758516806909845 := by
  unfold tailWord_923146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8417475178401794407473323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22446600475738118419928861 8417475178401794407473323)
  ·
    refine ⟨12626212767602691611209985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8417475178401794407473323 12626212767602691611209985)
    ·
      refine ⟨9469659575702018708407489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12626212767602691611209985 9469659575702018708407489)
      ·
        refine ⟨7102244681776514031305617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9469659575702018708407489 7102244681776514031305617)
        ·
          refine ⟨5326683511332385523479213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7102244681776514031305617 5326683511332385523479213)
          ·
            refine ⟨1997506316749644571304705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5326683511332385523479213 1997506316749644571304705)
            ·
              refine ⟨1498129737562233428478529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1997506316749644571304705 1498129737562233428478529)
              ·
                refine ⟨1123597303171675071358897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1498129737562233428478529 1123597303171675071358897)
                ·
                  refine ⟨842697977378756303519173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1123597303171675071358897 842697977378756303519173)
                  ·
                    refine ⟨158005870758516806909845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 842697977378756303519173 158005870758516806909845)
                    ·
                      rfl

theorem cell23_923146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_923146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923146 prefixEnd_923146 := by exact prefixLift 923146
  have htrace : WordTrace (prefixWord ++ tailWord_923146) baseStart_923146 baseEnd_923146 := by
    simpa [prefixWord, tailWord_923146, baseEnd_923146] using wordTrace_append hprefix tailTrace_923146
  have hstable : (prefixWord ++ tailWord_923146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923146).length < 2 ^ (prefixWord ++ tailWord_923146).sum := by decide
  have hdescent : baseEnd_923146 < baseStart_923146 := by decide
  rcases family_descends (prefixWord ++ tailWord_923146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923147 : List Nat := [1, 1, 1, 1, 9, 1, 2, 2, 1, 1, 3]
def baseStart_923147 : Nat := 118140960795 + 923147 * 2 ^ 59
def prefixEnd_923147 : Nat := 4983230072969 + 3 ^ 40 * 923147 * 2
def baseEnd_923147 : Nat := 474018125756204916817031

theorem tailTrace_923147 : CollatzResearch.WordTrace tailWord_923147 prefixEnd_923147 474018125756204916817031 := by
  unfold tailWord_923147
  simp only [CollatzResearch.WordTrace]
  refine ⟨33669937186603554800679695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22446624791069036533786463 33669937186603554800679695)
  ·
    refine ⟨50504905779905332201019543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33669937186603554800679695 50504905779905332201019543)
    ·
      refine ⟨75757358669857998301529315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50504905779905332201019543 75757358669857998301529315)
      ·
        refine ⟨113636038004786997452293973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75757358669857998301529315 113636038004786997452293973)
        ·
          refine ⟨665836160184298813197035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 113636038004786997452293973 665836160184298813197035)
          ·
            refine ⟨998754240276448219795553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665836160184298813197035 998754240276448219795553)
            ·
              refine ⟨749065680207336164846665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998754240276448219795553 749065680207336164846665)
              ·
                refine ⟨561799260155502123634999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749065680207336164846665 561799260155502123634999)
                ·
                  refine ⟨842698890233253185452499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561799260155502123634999 842698890233253185452499)
                  ·
                    refine ⟨1264048335349879778178749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 842698890233253185452499 1264048335349879778178749)
                    ·
                      refine ⟨474018125756204916817031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1264048335349879778178749 474018125756204916817031)
                      ·
                        rfl

theorem cell23_923147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 1, 1, 3].length) (baseStart_923147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923147 prefixEnd_923147 := by exact prefixLift 923147
  have htrace : WordTrace (prefixWord ++ tailWord_923147) baseStart_923147 baseEnd_923147 := by
    simpa [prefixWord, tailWord_923147, baseEnd_923147] using wordTrace_append hprefix tailTrace_923147
  have hstable : (prefixWord ++ tailWord_923147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923147).length < 2 ^ (prefixWord ++ tailWord_923147).sum := by decide
  have hdescent : baseEnd_923147 < baseStart_923147 := by decide
  rcases family_descends (prefixWord ++ tailWord_923147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923153 : List Nat := [1, 2, 2, 1, 1, 2, 5, 4, 1, 2, 2]
def baseStart_923153 : Nat := 118140960795 + 923153 * 2 ^ 59
def prefixEnd_923153 : Nat := 4983230072969 + 3 ^ 40 * 923153 * 2
def baseEnd_923153 : Nat := 474021206640131893342003

theorem tailTrace_923153 : CollatzResearch.WordTrace tailWord_923153 prefixEnd_923153 474021206640131893342003 := by
  unfold tailWord_923153
  simp only [CollatzResearch.WordTrace]
  refine ⟨33670156024581817825398113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22446770683054545216932075 33670156024581817825398113)
  ·
    refine ⟨25252617018436363369048585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33670156024581817825398113 25252617018436363369048585)
    ·
      refine ⟨18939462763827272526786439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25252617018436363369048585 18939462763827272526786439)
      ·
        refine ⟨28409194145740908790179659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18939462763827272526786439 28409194145740908790179659)
        ·
          refine ⟨42613791218611363185269489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28409194145740908790179659 42613791218611363185269489)
          ·
            refine ⟨31960343413958522388952117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42613791218611363185269489 31960343413958522388952117)
            ·
              refine ⟨2996282195058611473964261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31960343413958522388952117 2996282195058611473964261)
              ·
                refine ⟨561802911573489651368299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2996282195058611473964261 561802911573489651368299)
                ·
                  refine ⟨842704367360234477052449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561802911573489651368299 842704367360234477052449)
                  ·
                    refine ⟨632028275520175857789337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 842704367360234477052449 632028275520175857789337)
                    ·
                      refine ⟨474021206640131893342003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632028275520175857789337 474021206640131893342003)
                      ·
                        rfl

theorem cell23_923153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 1, 2, 2].length) (baseStart_923153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923153 prefixEnd_923153 := by exact prefixLift 923153
  have htrace : WordTrace (prefixWord ++ tailWord_923153) baseStart_923153 baseEnd_923153 := by
    simpa [prefixWord, tailWord_923153, baseEnd_923153] using wordTrace_append hprefix tailTrace_923153
  have hstable : (prefixWord ++ tailWord_923153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923153).length < 2 ^ (prefixWord ++ tailWord_923153).sum := by decide
  have hdescent : baseEnd_923153 < baseStart_923153 := by decide
  rcases family_descends (prefixWord ++ tailWord_923153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923169 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_923169 : Nat := 118140960795 + 923169 * 2 ^ 59
def prefixEnd_923169 : Nat := 4983230072969 + 3 ^ 40 * 923169 * 2
def baseEnd_923169 : Nat := 474029422330603830741929

theorem tailTrace_923169 : CollatzResearch.WordTrace tailWord_923169 prefixEnd_923169 474029422330603830741929 := by
  unfold tailWord_923169
  simp only [CollatzResearch.WordTrace]
  refine ⟨33670739592523852557980561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22447159728349235038653707 33670739592523852557980561)
  ·
    refine ⟨25253054694392889418485421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33670739592523852557980561 25253054694392889418485421)
    ·
      refine ⟨9469895510397333531932033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25253054694392889418485421 9469895510397333531932033)
      ·
        refine ⟨7102421632798000148949025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9469895510397333531932033 7102421632798000148949025)
        ·
          refine ⟨5326816224598500111711769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7102421632798000148949025 5326816224598500111711769)
          ·
            refine ⟨3995112168448875083783827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5326816224598500111711769 3995112168448875083783827)
            ·
              refine ⟨5992668252673312625675741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3995112168448875083783827 5992668252673312625675741)
              ·
                refine ⟨2247250594752492234628403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5992668252673312625675741 2247250594752492234628403)
                ·
                  refine ⟨3370875892128738351942605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247250594752492234628403 3370875892128738351942605)
                  ·
                    refine ⟨1264078459548276881978477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3370875892128738351942605 1264078459548276881978477)
                    ·
                      refine ⟨474029422330603830741929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1264078459548276881978477 474029422330603830741929)
                      ·
                        rfl

theorem cell23_923169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_923169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923169 prefixEnd_923169 := by exact prefixLift 923169
  have htrace : WordTrace (prefixWord ++ tailWord_923169) baseStart_923169 baseEnd_923169 := by
    simpa [prefixWord, tailWord_923169, baseEnd_923169] using wordTrace_append hprefix tailTrace_923169
  have hstable : (prefixWord ++ tailWord_923169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923169).length < 2 ^ (prefixWord ++ tailWord_923169).sum := by decide
  have hdescent : baseEnd_923169 < baseStart_923169 := by decide
  rcases family_descends (prefixWord ++ tailWord_923169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923176 : List Nat := [2, 1, 5, 2, 2, 1, 3, 7]
def baseStart_923176 : Nat := 118140960795 + 923176 * 2 ^ 59
def prefixEnd_923176 : Nat := 4983230072969 + 3 ^ 40 * 923176 * 2
def baseEnd_923176 : Nat := 17556778396117974198311

theorem tailTrace_923176 : CollatzResearch.WordTrace tailWord_923176 prefixEnd_923176 17556778396117974198311 := by
  unfold tailWord_923176
  simp only [CollatzResearch.WordTrace]
  refine ⟨16835497451749246376742691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22447329935665661835656921 16835497451749246376742691)
  ·
    refine ⟨25253246177623869565114037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16835497451749246376742691 25253246177623869565114037)
    ·
      refine ⟨2367491829152237771729441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25253246177623869565114037 2367491829152237771729441)
      ·
        refine ⟨1775618871864178328797081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2367491829152237771729441 1775618871864178328797081)
        ·
          refine ⟨1331714153898133746597811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1775618871864178328797081 1331714153898133746597811)
          ·
            refine ⟨1997571230847200619896717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331714153898133746597811 1997571230847200619896717)
            ·
              refine ⟨749089211567700232461269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1997571230847200619896717 749089211567700232461269)
              ·
                refine ⟨17556778396117974198311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 749089211567700232461269 17556778396117974198311)
                ·
                  rfl

theorem cell23_923176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 7].length) (baseStart_923176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923176 prefixEnd_923176 := by exact prefixLift 923176
  have htrace : WordTrace (prefixWord ++ tailWord_923176) baseStart_923176 baseEnd_923176 := by
    simpa [prefixWord, tailWord_923176, baseEnd_923176] using wordTrace_append hprefix tailTrace_923176
  have hstable : (prefixWord ++ tailWord_923176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923176).length < 2 ^ (prefixWord ++ tailWord_923176).sum := by decide
  have hdescent : baseEnd_923176 < baseStart_923176 := by decide
  rcases family_descends (prefixWord ++ tailWord_923176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923209 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 3, 4, 2]
def baseStart_923209 : Nat := 118140960795 + 923209 * 2 ^ 59
def prefixEnd_923209 : Nat := 4983230072969 + 3 ^ 40 * 923209 * 2
def baseEnd_923209 : Nat := 474049961556783674241745

theorem tailTrace_923209 : CollatzResearch.WordTrace tailWord_923209 prefixEnd_923209 474049961556783674241745 := by
  unfold tailWord_923209
  simp only [CollatzResearch.WordTrace]
  refine ⟨33672198512378939389436681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22448132341585959592957787 33672198512378939389436681)
  ·
    refine ⟨25254148884284204542077511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33672198512378939389436681 25254148884284204542077511)
    ·
      refine ⟨37881223326426306813116267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25254148884284204542077511 37881223326426306813116267)
      ·
        refine ⟨56821834989639460219674401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37881223326426306813116267 56821834989639460219674401)
        ·
          refine ⟨42616376242229595164755801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56821834989639460219674401 42616376242229595164755801)
          ·
            refine ⟨31962282181672196373566851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42616376242229595164755801 31962282181672196373566851)
            ·
              refine ⟨47943423272508294560350277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31962282181672196373566851 47943423272508294560350277)
              ·
                refine ⟨8989391863595305230065677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47943423272508294560350277 8989391863595305230065677)
                ·
                  refine ⟨3371021948848239461274629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8989391863595305230065677 3371021948848239461274629)
                  ·
                    refine ⟨632066615409044898988993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3371021948848239461274629 632066615409044898988993)
                    ·
                      refine ⟨474049961556783674241745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632066615409044898988993 474049961556783674241745)
                      ·
                        rfl

theorem cell23_923209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 4, 2].length) (baseStart_923209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923209 prefixEnd_923209 := by exact prefixLift 923209
  have htrace : WordTrace (prefixWord ++ tailWord_923209) baseStart_923209 baseEnd_923209 := by
    simpa [prefixWord, tailWord_923209, baseEnd_923209] using wordTrace_append hprefix tailTrace_923209
  have hstable : (prefixWord ++ tailWord_923209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923209).length < 2 ^ (prefixWord ++ tailWord_923209).sum := by decide
  have hdescent : baseEnd_923209 < baseStart_923209 := by decide
  rcases family_descends (prefixWord ++ tailWord_923209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923246 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_923246 : Nat := 118140960795 + 923246 * 2 ^ 59
def prefixEnd_923246 : Nat := 4983230072969 + 3 ^ 40 * 923246 * 2
def baseEnd_923246 : Nat := 474068960341000029479075

theorem tailTrace_923246 : CollatzResearch.WordTrace tailWord_923246 prefixEnd_923246 474068960341000029479075 := by
  unfold tailWord_923246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4209193501655611838566699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22449032008829929805689061 4209193501655611838566699)
  ·
    refine ⟨6313790252483417757850049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4209193501655611838566699 6313790252483417757850049)
    ·
      refine ⟨4735342689362563318387537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6313790252483417757850049 4735342689362563318387537)
      ·
        refine ⟨3551507017021922488790653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4735342689362563318387537 3551507017021922488790653)
        ·
          refine ⟨1331815131383220933296495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3551507017021922488790653 1331815131383220933296495)
          ·
            refine ⟨1997722697074831399944743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331815131383220933296495 1997722697074831399944743)
            ·
              refine ⟨2996584045612247099917115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997722697074831399944743 2996584045612247099917115)
              ·
                refine ⟨4494876068418370649875673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2996584045612247099917115 4494876068418370649875673)
                ·
                  refine ⟨3371157051313777987406755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4494876068418370649875673 3371157051313777987406755)
                  ·
                    refine ⟨5056735576970666981110133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3371157051313777987406755 5056735576970666981110133)
                    ·
                      refine ⟨474068960341000029479075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5056735576970666981110133 474068960341000029479075)
                      ·
                        rfl

theorem cell23_923246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_923246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923246 prefixEnd_923246 := by exact prefixLift 923246
  have htrace : WordTrace (prefixWord ++ tailWord_923246) baseStart_923246 baseEnd_923246 := by
    simpa [prefixWord, tailWord_923246, baseEnd_923246] using wordTrace_append hprefix tailTrace_923246
  have hstable : (prefixWord ++ tailWord_923246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923246).length < 2 ^ (prefixWord ++ tailWord_923246).sum := by decide
  have hdescent : baseEnd_923246 < baseStart_923246 := by decide
  rcases family_descends (prefixWord ++ tailWord_923246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923296 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 2, 5]
def baseStart_923296 : Nat := 118140960795 + 923296 * 2 ^ 59
def prefixEnd_923296 : Nat := 4983230072969 + 3 ^ 40 * 923296 * 2
def baseEnd_923296 : Nat := 158031544791241611284615

theorem tailTrace_923296 : CollatzResearch.WordTrace tailWord_923296 prefixEnd_923296 158031544791241611284615 := by
  unfold tailWord_923296
  simp only [CollatzResearch.WordTrace]
  refine ⟨16837685831531876623926871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22450247775375835498569161 16837685831531876623926871)
  ·
    refine ⟨25256528747297814935890307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16837685831531876623926871 25256528747297814935890307)
    ·
      refine ⟨37884793120946722403835461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25256528747297814935890307 37884793120946722403835461)
      ·
        refine ⟨7103398710177510450719149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37884793120946722403835461 7103398710177510450719149)
        ·
          refine ⟨2663774516316566419019681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7103398710177510450719149 2663774516316566419019681)
          ·
            refine ⟨1997830887237424814264761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2663774516316566419019681 1997830887237424814264761)
            ·
              refine ⟨1498373165428068610698571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1997830887237424814264761 1498373165428068610698571)
              ·
                refine ⟨2247559748142102916047857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1498373165428068610698571 2247559748142102916047857)
                ·
                  refine ⟨1685669811106577187035893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2247559748142102916047857 1685669811106577187035893)
                  ·
                    refine ⟨158031544791241611284615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1685669811106577187035893 158031544791241611284615)
                    ·
                      rfl

theorem cell23_923296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 2, 5].length) (baseStart_923296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923296 prefixEnd_923296 := by exact prefixLift 923296
  have htrace : WordTrace (prefixWord ++ tailWord_923296) baseStart_923296 baseEnd_923296 := by
    simpa [prefixWord, tailWord_923296, baseEnd_923296] using wordTrace_append hprefix tailTrace_923296
  have hstable : (prefixWord ++ tailWord_923296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923296).length < 2 ^ (prefixWord ++ tailWord_923296).sum := by decide
  have hdescent : baseEnd_923296 < baseStart_923296 := by decide
  rcases family_descends (prefixWord ++ tailWord_923296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923317 : List Nat := [1, 3, 3, 3, 3, 1, 2, 2, 5]
def baseStart_923317 : Nat := 118140960795 + 923317 * 2 ^ 59
def prefixEnd_923317 : Nat := 4983230072969 + 3 ^ 40 * 923317 * 2
def baseEnd_923317 : Nat := 52678379718607694632361

theorem tailTrace_923317 : CollatzResearch.WordTrace tailWord_923317 prefixEnd_923317 52678379718607694632361 := by
  unfold tailWord_923317
  simp only [CollatzResearch.WordTrace]
  refine ⟨33676137595987673834368205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22450758397325115889578803 33676137595987673834368205)
  ·
    refine ⟨12628551598495377687888077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33676137595987673834368205 12628551598495377687888077)
    ·
      refine ⟨4735706849435766632958029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12628551598495377687888077 4735706849435766632958029)
      ·
        refine ⟨1775890068538412487359261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4735706849435766632958029 1775890068538412487359261)
        ·
          refine ⟨665958775701904682759723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1775890068538412487359261 665958775701904682759723)
          ·
            refine ⟨998938163552857024139585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665958775701904682759723 998938163552857024139585)
            ·
              refine ⟨749203622664642768104689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998938163552857024139585 749203622664642768104689)
              ·
                refine ⟨561902716998482076078517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749203622664642768104689 561902716998482076078517)
                ·
                  refine ⟨52678379718607694632361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 561902716998482076078517 52678379718607694632361)
                  ·
                    rfl

theorem cell23_923317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 5].length) (baseStart_923317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923317 prefixEnd_923317 := by exact prefixLift 923317
  have htrace : WordTrace (prefixWord ++ tailWord_923317) baseStart_923317 baseEnd_923317 := by
    simpa [prefixWord, tailWord_923317, baseEnd_923317] using wordTrace_append hprefix tailTrace_923317
  have hstable : (prefixWord ++ tailWord_923317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923317).length < 2 ^ (prefixWord ++ tailWord_923317).sum := by decide
  have hdescent : baseEnd_923317 < baseStart_923317 := by decide
  rcases family_descends (prefixWord ++ tailWord_923317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923350 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_923350 : Nat := 118140960795 + 923350 * 2 ^ 59
def prefixEnd_923350 : Nat := 4983230072969 + 3 ^ 40 * 923350 * 2
def baseEnd_923350 : Nat := 474122362329067622578597

theorem tailTrace_923350 : CollatzResearch.WordTrace tailWord_923350 prefixEnd_923350 474122362329067622578597 := by
  unfold tailWord_923350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104833825304257529394969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22451560803245413646879669 2104833825304257529394969)
  ·
    refine ⟨1578625368978193147046227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2104833825304257529394969 1578625368978193147046227)
    ·
      refine ⟨2367938053467289720569341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1578625368978193147046227 2367938053467289720569341)
      ·
        refine ⟨887976770050233645213503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2367938053467289720569341 887976770050233645213503)
        ·
          refine ⟨1331965155075350467820255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887976770050233645213503 1331965155075350467820255)
          ·
            refine ⟨1997947732613025701730383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331965155075350467820255 1997947732613025701730383)
            ·
              refine ⟨2996921598919538552595575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997947732613025701730383 2996921598919538552595575)
              ·
                refine ⟨4495382398379307828893363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2996921598919538552595575 4495382398379307828893363)
                ·
                  refine ⟨6743073597568961743340045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4495382398379307828893363 6743073597568961743340045)
                  ·
                    refine ⟨2528652599088360653752517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6743073597568961743340045 2528652599088360653752517)
                    ·
                      refine ⟨474122362329067622578597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2528652599088360653752517 474122362329067622578597)
                      ·
                        rfl

theorem cell23_923350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_923350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923350 prefixEnd_923350 := by exact prefixLift 923350
  have htrace : WordTrace (prefixWord ++ tailWord_923350) baseStart_923350 baseEnd_923350 := by
    simpa [prefixWord, tailWord_923350, baseEnd_923350] using wordTrace_append hprefix tailTrace_923350
  have hstable : (prefixWord ++ tailWord_923350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923350).length < 2 ^ (prefixWord ++ tailWord_923350).sum := by decide
  have hdescent : baseEnd_923350 < baseStart_923350 := by decide
  rcases family_descends (prefixWord ++ tailWord_923350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923353 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 2, 2, 3]
def baseStart_923353 : Nat := 118140960795 + 923353 * 2 ^ 59
def prefixEnd_923353 : Nat := 4983230072969 + 3 ^ 40 * 923353 * 2
def baseEnd_923353 : Nat := 474123902771031110841083

theorem tailTrace_923353 : CollatzResearch.WordTrace tailWord_923353 prefixEnd_923353 474123902771031110841083 := by
  unfold tailWord_923353
  simp only [CollatzResearch.WordTrace]
  refine ⟨33677450623857251982678713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22451633749238167988452475 33677450623857251982678713)
  ·
    refine ⟨25258087967892938987009035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33677450623857251982678713 25258087967892938987009035)
    ·
      refine ⟨37887131951839408480513553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25258087967892938987009035 37887131951839408480513553)
      ·
        refine ⟨28415348963879556360385165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37887131951839408480513553 28415348963879556360385165)
        ·
          refine ⟨10655755861454833635144437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28415348963879556360385165 10655755861454833635144437)
          ·
            refine ⟨998977112011390653294791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10655755861454833635144437 998977112011390653294791)
            ·
              refine ⟨1498465668017085979942187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998977112011390653294791 1498465668017085979942187)
              ·
                refine ⟨2247698502025628969913281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1498465668017085979942187 2247698502025628969913281)
                ·
                  refine ⟨1685773876519221727434961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2247698502025628969913281 1685773876519221727434961)
                  ·
                    refine ⟨1264330407389416295576221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1685773876519221727434961 1264330407389416295576221)
                    ·
                      refine ⟨474123902771031110841083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1264330407389416295576221 474123902771031110841083)
                      ·
                        rfl

theorem cell23_923353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_923353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923353 prefixEnd_923353 := by exact prefixLift 923353
  have htrace : WordTrace (prefixWord ++ tailWord_923353) baseStart_923353 baseEnd_923353 := by
    simpa [prefixWord, tailWord_923353, baseEnd_923353] using wordTrace_append hprefix tailTrace_923353
  have hstable : (prefixWord ++ tailWord_923353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923353).length < 2 ^ (prefixWord ++ tailWord_923353).sum := by decide
  have hdescent : baseEnd_923353 < baseStart_923353 := by decide
  rcases family_descends (prefixWord ++ tailWord_923353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923373 : List Nat := [1, 5, 1, 2, 1, 4, 1, 2, 6]
def baseStart_923373 : Nat := 118140960795 + 923373 * 2 ^ 59
def prefixEnd_923373 : Nat := 4983230072969 + 3 ^ 40 * 923373 * 2
def baseEnd_923373 : Nat := 52681574709346781398999

theorem tailTrace_923373 : CollatzResearch.WordTrace tailWord_923373 prefixEnd_923373 52681574709346781398999 := by
  unfold tailWord_923373
  simp only [CollatzResearch.WordTrace]
  refine ⟨33678180083784795398406773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22452120055856530265604515 33678180083784795398406773)
  ·
    refine ⟨3157329382854824568600635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33678180083784795398406773 3157329382854824568600635)
    ·
      refine ⟨4735994074282236852900953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3157329382854824568600635 4735994074282236852900953)
      ·
        refine ⟨3551995555711677639675715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4735994074282236852900953 3551995555711677639675715)
        ·
          refine ⟨5327993333567516459513573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3551995555711677639675715 5327993333567516459513573)
          ·
            refine ⟨998998750043909336158795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5327993333567516459513573 998998750043909336158795)
            ·
              refine ⟨1498498125065864004238193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998998750043909336158795 1498498125065864004238193)
              ·
                refine ⟨1123873593799398003178645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1498498125065864004238193 1123873593799398003178645)
                ·
                  refine ⟨52681574709346781398999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1123873593799398003178645 52681574709346781398999)
                  ·
                    rfl

theorem cell23_923373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_923373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923373 prefixEnd_923373 := by exact prefixLift 923373
  have htrace : WordTrace (prefixWord ++ tailWord_923373) baseStart_923373 baseEnd_923373 := by
    simpa [prefixWord, tailWord_923373, baseEnd_923373] using wordTrace_append hprefix tailTrace_923373
  have hstable : (prefixWord ++ tailWord_923373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923373).length < 2 ^ (prefixWord ++ tailWord_923373).sum := by decide
  have hdescent : baseEnd_923373 < baseStart_923373 := by decide
  rcases family_descends (prefixWord ++ tailWord_923373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923389 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_923389 : Nat := 118140960795 + 923389 * 2 ^ 59
def prefixEnd_923389 : Nat := 4983230072969 + 3 ^ 40 * 923389 * 2
def baseEnd_923389 : Nat := 474142388074592969990917

theorem tailTrace_923389 : CollatzResearch.WordTrace tailWord_923389 prefixEnd_923389 474142388074592969990917 := by
  unfold tailWord_923389
  simp only [CollatzResearch.WordTrace]
  refine ⟨33678763651726830130989221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22452509101151220087326147 33678763651726830130989221)
  ·
    refine ⟨6314768184698780649560479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33678763651726830130989221 6314768184698780649560479)
    ·
      refine ⟨9472152277048170974340719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6314768184698780649560479 9472152277048170974340719)
      ·
        refine ⟨14208228415572256461511079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9472152277048170974340719 14208228415572256461511079)
        ·
          refine ⟨21312342623358384692266619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14208228415572256461511079 21312342623358384692266619)
          ·
            refine ⟨31968513935037577038399929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21312342623358384692266619 31968513935037577038399929)
            ·
              refine ⟨23976385451278182778799947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31968513935037577038399929 23976385451278182778799947)
              ·
                refine ⟨35964578176917274168199921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23976385451278182778799947 35964578176917274168199921)
                ·
                  refine ⟨26973433632687955626149941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35964578176917274168199921 26973433632687955626149941)
                  ·
                    refine ⟨2528759403064495839951557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26973433632687955626149941 2528759403064495839951557)
                    ·
                      refine ⟨474142388074592969990917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2528759403064495839951557 474142388074592969990917)
                      ·
                        rfl

theorem cell23_923389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_923389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923389 prefixEnd_923389 := by exact prefixLift 923389
  have htrace : WordTrace (prefixWord ++ tailWord_923389) baseStart_923389 baseEnd_923389 := by
    simpa [prefixWord, tailWord_923389, baseEnd_923389] using wordTrace_append hprefix tailTrace_923389
  have hstable : (prefixWord ++ tailWord_923389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923389).length < 2 ^ (prefixWord ++ tailWord_923389).sum := by decide
  have hdescent : baseEnd_923389 < baseStart_923389 := by decide
  rcases family_descends (prefixWord ++ tailWord_923389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923390 : List Nat := [4, 2, 2, 1, 3, 1, 3, 1, 6]
def baseStart_923390 : Nat := 118140960795 + 923390 * 2 ^ 59
def prefixEnd_923390 : Nat := 4983230072969 + 3 ^ 40 * 923390 * 2
def baseEnd_923390 : Nat := 52682544617249718453157

theorem tailTrace_923390 : CollatzResearch.WordTrace tailWord_923390 prefixEnd_923390 52682544617249718453157 := by
  unfold tailWord_923390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4209850015590400912721953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22452533416482138201183749 4209850015590400912721953)
  ·
    refine ⟨3157387511692800684541465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4209850015590400912721953 3157387511692800684541465)
    ·
      refine ⟨2368040633769600513406099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3157387511692800684541465 2368040633769600513406099)
      ·
        refine ⟨3552060950654400770109149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368040633769600513406099 3552060950654400770109149)
        ·
          refine ⟨1332022856495400288790931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3552060950654400770109149 1332022856495400288790931)
          ·
            refine ⟨1998034284743100433186397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332022856495400288790931 1998034284743100433186397)
            ·
              refine ⟨749262856778662662444899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1998034284743100433186397 749262856778662662444899)
              ·
                refine ⟨1123894285167993993667349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 749262856778662662444899 1123894285167993993667349)
                ·
                  refine ⟨52682544617249718453157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1123894285167993993667349 52682544617249718453157)
                  ·
                    rfl

theorem cell23_923390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_923390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923390 prefixEnd_923390 := by exact prefixLift 923390
  have htrace : WordTrace (prefixWord ++ tailWord_923390) baseStart_923390 baseEnd_923390 := by
    simpa [prefixWord, tailWord_923390, baseEnd_923390] using wordTrace_append hprefix tailTrace_923390
  have hstable : (prefixWord ++ tailWord_923390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923390).length < 2 ^ (prefixWord ++ tailWord_923390).sum := by decide
  have hdescent : baseEnd_923390 < baseStart_923390 := by decide
  rcases family_descends (prefixWord ++ tailWord_923390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923406 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_923406 : Nat := 118140960795 + 923406 * 2 ^ 59
def prefixEnd_923406 : Nat := 4983230072969 + 3 ^ 40 * 923406 * 2
def baseEnd_923406 : Nat := 474151117245719403478339

theorem tailTrace_923406 : CollatzResearch.WordTrace tailWord_923406 prefixEnd_923406 474151117245719403478339 := by
  unfold tailWord_923406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4209922961583155254294759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22452922461776828022905381 4209922961583155254294759)
  ·
    refine ⟨6314884442374732881442139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4209922961583155254294759 6314884442374732881442139)
    ·
      refine ⟨9472326663562099322163209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6314884442374732881442139 9472326663562099322163209)
      ·
        refine ⟨7104244997671574491622407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9472326663562099322163209 7104244997671574491622407)
        ·
          refine ⟨10656367496507361737433611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7104244997671574491622407 10656367496507361737433611)
          ·
            refine ⟨15984551244761042606150417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10656367496507361737433611 15984551244761042606150417)
            ·
              refine ⟨11988413433570781954612813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15984551244761042606150417 11988413433570781954612813)
              ·
                refine ⟨4495655037589043232979805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11988413433570781954612813 4495655037589043232979805)
                ·
                  refine ⟨1685870639095891212367427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4495655037589043232979805 1685870639095891212367427)
                  ·
                    refine ⟨2528805958643836818551141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1685870639095891212367427 2528805958643836818551141)
                    ·
                      refine ⟨474151117245719403478339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2528805958643836818551141 474151117245719403478339)
                      ·
                        rfl

theorem cell23_923406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_923406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923406 prefixEnd_923406 := by exact prefixLift 923406
  have htrace : WordTrace (prefixWord ++ tailWord_923406) baseStart_923406 baseEnd_923406 := by
    simpa [prefixWord, tailWord_923406, baseEnd_923406] using wordTrace_append hprefix tailTrace_923406
  have hstable : (prefixWord ++ tailWord_923406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923406).length < 2 ^ (prefixWord ++ tailWord_923406).sum := by decide
  have hdescent : baseEnd_923406 < baseStart_923406 := by decide
  rcases family_descends (prefixWord ++ tailWord_923406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923409 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_923409 : Nat := 118140960795 + 923409 * 2 ^ 59
def prefixEnd_923409 : Nat := 4983230072969 + 3 ^ 40 * 923409 * 2
def baseEnd_923409 : Nat := 474152657687682891740825

theorem tailTrace_923409 : CollatzResearch.WordTrace tailWord_923409 prefixEnd_923409 474152657687682891740825 := by
  unfold tailWord_923409
  simp only [CollatzResearch.WordTrace]
  refine ⟨33679493111654373546717281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22452995407769582364478187 33679493111654373546717281)
  ·
    refine ⟨25259619833740780160037961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33679493111654373546717281 25259619833740780160037961)
    ·
      refine ⟨18944714875305585120028471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25259619833740780160037961 18944714875305585120028471)
      ·
        refine ⟨28417072312958377680042707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18944714875305585120028471 28417072312958377680042707)
        ·
          refine ⟨42625608469437566520064061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28417072312958377680042707 42625608469437566520064061)
          ·
            refine ⟨15984603176039087445024023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42625608469437566520064061 15984603176039087445024023)
            ·
              refine ⟨23976904764058631167536035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15984603176039087445024023 23976904764058631167536035)
              ·
                refine ⟨35965357146087946751304053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23976904764058631167536035 35965357146087946751304053)
                ·
                  refine ⟨3371752232445745007934755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35965357146087946751304053 3371752232445745007934755)
                  ·
                    refine ⟨5057628348668617511902133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3371752232445745007934755 5057628348668617511902133)
                    ·
                      refine ⟨474152657687682891740825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5057628348668617511902133 474152657687682891740825)
                      ·
                        rfl

theorem cell23_923409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_923409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923409 prefixEnd_923409 := by exact prefixLift 923409
  have htrace : WordTrace (prefixWord ++ tailWord_923409) baseStart_923409 baseEnd_923409 := by
    simpa [prefixWord, tailWord_923409, baseEnd_923409] using wordTrace_append hprefix tailTrace_923409
  have hstable : (prefixWord ++ tailWord_923409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923409).length < 2 ^ (prefixWord ++ tailWord_923409).sum := by decide
  have hdescent : baseEnd_923409 < baseStart_923409 := by decide
  rcases family_descends (prefixWord ++ tailWord_923409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923410 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_923410 : Nat := 118140960795 + 923410 * 2 ^ 59
def prefixEnd_923410 : Nat := 4983230072969 + 3 ^ 40 * 923410 * 2
def baseEnd_923410 : Nat := 474153171168337387828321

theorem tailTrace_923410 : CollatzResearch.WordTrace tailWord_923410 prefixEnd_923410 474153171168337387828321 := by
  unfold tailWord_923410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8419882396162687679375921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22453019723100500478335789 8419882396162687679375921)
  ·
    refine ⟨6314911797122015759531941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8419882396162687679375921 6314911797122015759531941)
    ·
      refine ⟨1184045961960377954912239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6314911797122015759531941 1184045961960377954912239)
      ·
        refine ⟨1776068942940566932368359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1184045961960377954912239 1776068942940566932368359)
        ·
          refine ⟨2664103414410850398552539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1776068942940566932368359 2664103414410850398552539)
          ·
            refine ⟨3996155121616275597828809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664103414410850398552539 3996155121616275597828809)
            ·
              refine ⟨2997116341212206698371607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3996155121616275597828809 2997116341212206698371607)
              ·
                refine ⟨4495674511818310047557411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997116341212206698371607 4495674511818310047557411)
                ·
                  refine ⟨6743511767727465071336117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4495674511818310047557411 6743511767727465071336117)
                  ·
                    refine ⟨632204228224449850437761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6743511767727465071336117 632204228224449850437761)
                    ·
                      refine ⟨474153171168337387828321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632204228224449850437761 474153171168337387828321)
                      ·
                        rfl

theorem cell23_923410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_923410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923410 prefixEnd_923410 := by exact prefixLift 923410
  have htrace : WordTrace (prefixWord ++ tailWord_923410) baseStart_923410 baseEnd_923410 := by
    simpa [prefixWord, tailWord_923410, baseEnd_923410] using wordTrace_append hprefix tailTrace_923410
  have hstable : (prefixWord ++ tailWord_923410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923410).length < 2 ^ (prefixWord ++ tailWord_923410).sum := by decide
  have hdescent : baseEnd_923410 < baseStart_923410 := by decide
  rcases family_descends (prefixWord ++ tailWord_923410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923416 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 4, 4]
def baseStart_923416 : Nat := 118140960795 + 923416 * 2 ^ 59
def prefixEnd_923416 : Nat := 4983230072969 + 3 ^ 40 * 923416 * 2
def baseEnd_923416 : Nat := 158052084017421454784431

theorem tailTrace_923416 : CollatzResearch.WordTrace tailWord_923416 prefixEnd_923416 158052084017421454784431 := by
  unfold tailWord_923416
  simp only [CollatzResearch.WordTrace]
  refine ⟨16839874211314506871111051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22453165615086009161481401 16839874211314506871111051)
  ·
    refine ⟨25259811316971760306666577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16839874211314506871111051 25259811316971760306666577)
    ·
      refine ⟨18944858487728820229999933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25259811316971760306666577 18944858487728820229999933)
      ·
        refine ⟨7104321932898307586249975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18944858487728820229999933 7104321932898307586249975)
        ·
          refine ⟨10656482899347461379374963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7104321932898307586249975 10656482899347461379374963)
          ·
            refine ⟨15984724349021192069062445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10656482899347461379374963 15984724349021192069062445)
            ·
              refine ⟨5994271630882947025898417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15984724349021192069062445 5994271630882947025898417)
              ·
                refine ⟨4495703723162210269423813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5994271630882947025898417 4495703723162210269423813)
                ·
                  refine ⟨842944448092914425516965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4495703723162210269423813 842944448092914425516965)
                  ·
                    refine ⟨158052084017421454784431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 842944448092914425516965 158052084017421454784431)
                    ·
                      rfl

theorem cell23_923416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_923416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923416 prefixEnd_923416 := by exact prefixLift 923416
  have htrace : WordTrace (prefixWord ++ tailWord_923416) baseStart_923416 baseEnd_923416 := by
    simpa [prefixWord, tailWord_923416, baseEnd_923416] using wordTrace_append hprefix tailTrace_923416
  have hstable : (prefixWord ++ tailWord_923416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923416).length < 2 ^ (prefixWord ++ tailWord_923416).sum := by decide
  have hdescent : baseEnd_923416 < baseStart_923416 := by decide
  rcases family_descends (prefixWord ++ tailWord_923416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923429 : List Nat := [1, 3, 1, 2, 3, 2, 11]
def baseStart_923429 : Nat := 118140960795 + 923429 * 2 ^ 59
def prefixEnd_923429 : Nat := 4983230072969 + 3 ^ 40 * 923429 * 2
def baseEnd_923429 : Nat := 5853863300009540907293

theorem tailTrace_923429 : CollatzResearch.WordTrace tailWord_923429 prefixEnd_923429 5853863300009540907293 := by
  unfold tailWord_923429
  simp only [CollatzResearch.WordTrace]
  refine ⟨33680222571581916962445341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22453481714387944641630227 33680222571581916962445341)
  ·
    refine ⟨12630083464343218860917003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33680222571581916962445341 12630083464343218860917003)
    ·
      refine ⟨18945125196514828291375505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12630083464343218860917003 18945125196514828291375505)
      ·
        refine ⟨14208843897386121218531629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18945125196514828291375505 14208843897386121218531629)
        ·
          refine ⟨5328316461519795456949361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14208843897386121218531629 5328316461519795456949361)
          ·
            refine ⟨3996237346139846592712021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5328316461519795456949361 3996237346139846592712021)
            ·
              refine ⟨5853863300009540907293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3996237346139846592712021 5853863300009540907293)
              ·
                rfl

theorem cell23_923429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 11].length) (baseStart_923429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923429 prefixEnd_923429 := by exact prefixLift 923429
  have htrace : WordTrace (prefixWord ++ tailWord_923429) baseStart_923429 baseEnd_923429 := by
    simpa [prefixWord, tailWord_923429, baseEnd_923429] using wordTrace_append hprefix tailTrace_923429
  have hstable : (prefixWord ++ tailWord_923429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923429).length < 2 ^ (prefixWord ++ tailWord_923429).sum := by decide
  have hdescent : baseEnd_923429 < baseStart_923429 := by decide
  rcases family_descends (prefixWord ++ tailWord_923429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923450 : List Nat := [3, 1, 1, 1, 5, 1, 4, 1, 2, 4]
def baseStart_923450 : Nat := 118140960795 + 923450 * 2 ^ 59
def prefixEnd_923450 : Nat := 4983230072969 + 3 ^ 40 * 923450 * 2
def baseEnd_923450 : Nat := 158057903464839077109379

theorem tailTrace_923450 : CollatzResearch.WordTrace tailWord_923450 prefixEnd_923450 158057903464839077109379 := by
  unfold tailWord_923450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8420247126126459387239951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22453992336337225032639869 8420247126126459387239951)
  ·
    refine ⟨12630370689189689080859927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8420247126126459387239951 12630370689189689080859927)
    ·
      refine ⟨18945556033784533621289891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12630370689189689080859927 18945556033784533621289891)
      ·
        refine ⟨28418334050676800431934837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18945556033784533621289891 28418334050676800431934837)
        ·
          refine ⟨2664218817250950040493891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28418334050676800431934837 2664218817250950040493891)
          ·
            refine ⟨3996328225876425060740837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664218817250950040493891 3996328225876425060740837)
            ·
              refine ⟨749311542351829698888907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3996328225876425060740837 749311542351829698888907)
              ·
                refine ⟨1123967313527744548333361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 749311542351829698888907 1123967313527744548333361)
                ·
                  refine ⟨842975485145808411250021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1123967313527744548333361 842975485145808411250021)
                  ·
                    refine ⟨158057903464839077109379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 842975485145808411250021 158057903464839077109379)
                    ·
                      rfl

theorem cell23_923450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_923450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923450 prefixEnd_923450 := by exact prefixLift 923450
  have htrace : WordTrace (prefixWord ++ tailWord_923450) baseStart_923450 baseEnd_923450 := by
    simpa [prefixWord, tailWord_923450, baseEnd_923450] using wordTrace_append hprefix tailTrace_923450
  have hstable : (prefixWord ++ tailWord_923450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923450).length < 2 ^ (prefixWord ++ tailWord_923450).sum := by decide
  have hdescent : baseEnd_923450 < baseStart_923450 := by decide
  rcases family_descends (prefixWord ++ tailWord_923450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923473 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 1, 3, 3]
def baseStart_923473 : Nat := 118140960795 + 923473 * 2 ^ 59
def prefixEnd_923473 : Nat := 4983230072969 + 3 ^ 40 * 923473 * 2
def baseEnd_923473 : Nat := 474185520449570641340531

theorem tailTrace_923473 : CollatzResearch.WordTrace tailWord_923473 prefixEnd_923473 474185520449570641340531 := by
  unfold tailWord_923473
  simp only [CollatzResearch.WordTrace]
  refine ⟨33681827383422512477047073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22454551588948341651364715 33681827383422512477047073)
  ·
    refine ⟨25261370537566884357785305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33681827383422512477047073 25261370537566884357785305)
    ·
      refine ⟨18946027903175163268338979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25261370537566884357785305 18946027903175163268338979)
      ·
        refine ⟨28419041854762744902508469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18946027903175163268338979 28419041854762744902508469)
        ·
          refine ⟨2664285173884007334610169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28419041854762744902508469 2664285173884007334610169)
          ·
            refine ⟨1998213880413005500957627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2664285173884007334610169 1998213880413005500957627)
            ·
              refine ⟨2997320820619508251436441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998213880413005500957627 2997320820619508251436441)
              ·
                refine ⟨2247990615464631188577331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2997320820619508251436441 2247990615464631188577331)
                ·
                  refine ⟨3371985923196946782865997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247990615464631188577331 3371985923196946782865997)
                  ·
                    refine ⟨1264494721198855043574749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3371985923196946782865997 1264494721198855043574749)
                    ·
                      refine ⟨474185520449570641340531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1264494721198855043574749 474185520449570641340531)
                      ·
                        rfl

theorem cell23_923473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_923473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923473 prefixEnd_923473 := by exact prefixLift 923473
  have htrace : WordTrace (prefixWord ++ tailWord_923473) baseStart_923473 baseEnd_923473 := by
    simpa [prefixWord, tailWord_923473, baseEnd_923473] using wordTrace_append hprefix tailTrace_923473
  have hstable : (prefixWord ++ tailWord_923473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923473).length < 2 ^ (prefixWord ++ tailWord_923473).sum := by decide
  have hdescent : baseEnd_923473 < baseStart_923473 := by decide
  rcases family_descends (prefixWord ++ tailWord_923473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923491 : List Nat := [1, 1, 1, 5, 4, 2, 2, 2, 1, 2, 2]
def baseStart_923491 : Nat := 118140960795 + 923491 * 2 ^ 59
def prefixEnd_923491 : Nat := 4983230072969 + 3 ^ 40 * 923491 * 2
def baseEnd_923491 : Nat := 474194763101351570915449

theorem tailTrace_923491 : CollatzResearch.WordTrace tailWord_923491 prefixEnd_923491 474194763101351570915449 := by
  unfold tailWord_923491
  simp only [CollatzResearch.WordTrace]
  refine ⟨33682483897357301551202327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22454989264904867700801551 33682483897357301551202327)
  ·
    refine ⟨50523725846035952326803491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33682483897357301551202327 50523725846035952326803491)
    ·
      refine ⟨75785588769053928490205237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50523725846035952326803491 75785588769053928490205237)
      ·
        refine ⟨7104898947098805795956741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75785588769053928490205237 7104898947098805795956741)
        ·
          refine ⟨1332168552581026086741889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7104898947098805795956741 1332168552581026086741889)
          ·
            refine ⟨999126414435769565056417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1332168552581026086741889 999126414435769565056417)
            ·
              refine ⟨749344810826827173792313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999126414435769565056417 749344810826827173792313)
              ·
                refine ⟨562008608120120380344235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749344810826827173792313 562008608120120380344235)
                ·
                  refine ⟨843012912180180570516353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562008608120120380344235 843012912180180570516353)
                  ·
                    refine ⟨632259684135135427887265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 843012912180180570516353 632259684135135427887265)
                    ·
                      refine ⟨474194763101351570915449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632259684135135427887265 474194763101351570915449)
                      ·
                        rfl

theorem cell23_923491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_923491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923491 prefixEnd_923491 := by exact prefixLift 923491
  have htrace : WordTrace (prefixWord ++ tailWord_923491) baseStart_923491 baseEnd_923491 := by
    simpa [prefixWord, tailWord_923491, baseEnd_923491] using wordTrace_append hprefix tailTrace_923491
  have hstable : (prefixWord ++ tailWord_923491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923491).length < 2 ^ (prefixWord ++ tailWord_923491).sum := by decide
  have hdescent : baseEnd_923491 < baseStart_923491 := by decide
  rcases family_descends (prefixWord ++ tailWord_923491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923496 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_923496 : Nat := 118140960795 + 923496 * 2 ^ 59
def prefixEnd_923496 : Nat := 4983230072969 + 3 ^ 40 * 923496 * 2
def baseEnd_923496 : Nat := 474197330504624051352925

theorem tailTrace_923496 : CollatzResearch.WordTrace tailWord_923496 prefixEnd_923496 474197330504624051352925 := by
  unfold tailWord_923496
  simp only [CollatzResearch.WordTrace]
  refine ⟨16841333131169593702567171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22455110841559458270089561 16841333131169593702567171)
  ·
    refine ⟨25261999696754390553850757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16841333131169593702567171 25261999696754390553850757)
    ·
      refine ⟨4736624943141448228847017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25261999696754390553850757 4736624943141448228847017)
      ·
        refine ⟨3552468707356086171635263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4736624943141448228847017 3552468707356086171635263)
        ·
          refine ⟨5328703061034129257452895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3552468707356086171635263 5328703061034129257452895)
          ·
            refine ⟨7993054591551193886179343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5328703061034129257452895 7993054591551193886179343)
            ·
              refine ⟨11989581887326790829269015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7993054591551193886179343 11989581887326790829269015)
              ·
                refine ⟨17984372830990186243903523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11989581887326790829269015 17984372830990186243903523)
                ·
                  refine ⟨26976559246485279365855285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17984372830990186243903523 26976559246485279365855285)
                  ·
                    refine ⟨2529052429357994940548933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26976559246485279365855285 2529052429357994940548933)
                    ·
                      refine ⟨474197330504624051352925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2529052429357994940548933 474197330504624051352925)
                      ·
                        rfl

theorem cell23_923496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_923496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923496 prefixEnd_923496 := by exact prefixLift 923496
  have htrace : WordTrace (prefixWord ++ tailWord_923496) baseStart_923496 baseEnd_923496 := by
    simpa [prefixWord, tailWord_923496, baseEnd_923496] using wordTrace_append hprefix tailTrace_923496
  have hstable : (prefixWord ++ tailWord_923496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923496).length < 2 ^ (prefixWord ++ tailWord_923496).sum := by decide
  have hdescent : baseEnd_923496 < baseStart_923496 := by decide
  rcases family_descends (prefixWord ++ tailWord_923496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923534 : List Nat := [4, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2]
def baseStart_923534 : Nat := 118140960795 + 923534 * 2 ^ 59
def prefixEnd_923534 : Nat := 4983230072969 + 3 ^ 40 * 923534 * 2
def baseEnd_923534 : Nat := 474216842769494902677751

theorem tailTrace_923534 : CollatzResearch.WordTrace tailWord_923534 prefixEnd_923534 474216842769494902677751 := by
  unfold tailWord_923534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4210506529525189986877207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22456034824134346596678437 4210506529525189986877207)
  ·
    refine ⟨6315759794287784980315811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4210506529525189986877207 6315759794287784980315811)
    ·
      refine ⟨9473639691431677470473717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6315759794287784980315811 9473639691431677470473717)
      ·
        refine ⟨888153721071719762856911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9473639691431677470473717 888153721071719762856911)
        ·
          refine ⟨1332230581607579644285367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888153721071719762856911 1332230581607579644285367)
          ·
            refine ⟨1998345872411369466428051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332230581607579644285367 1998345872411369466428051)
            ·
              refine ⟨2997518808617054199642077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998345872411369466428051 2997518808617054199642077)
              ·
                refine ⟨1124069553231395324865779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2997518808617054199642077 1124069553231395324865779)
                ·
                  refine ⟨1686104329847092987298669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124069553231395324865779 1686104329847092987298669)
                  ·
                    refine ⟨632289123692659870237001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686104329847092987298669 632289123692659870237001)
                    ·
                      refine ⟨474216842769494902677751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632289123692659870237001 474216842769494902677751)
                      ·
                        rfl

theorem cell23_923534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_923534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923534 prefixEnd_923534 := by exact prefixLift 923534
  have htrace : WordTrace (prefixWord ++ tailWord_923534) baseStart_923534 baseEnd_923534 := by
    simpa [prefixWord, tailWord_923534, baseEnd_923534] using wordTrace_append hprefix tailTrace_923534
  have hstable : (prefixWord ++ tailWord_923534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923534).length < 2 ^ (prefixWord ++ tailWord_923534).sum := by decide
  have hdescent : baseEnd_923534 < baseStart_923534 := by decide
  rcases family_descends (prefixWord ++ tailWord_923534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923616 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 6]
def baseStart_923616 : Nat := 118140960795 + 923616 * 2 ^ 59
def prefixEnd_923616 : Nat := 4983230072969 + 3 ^ 40 * 923616 * 2
def baseEnd_923616 : Nat := 474258948183163581852373

theorem tailTrace_923616 : CollatzResearch.WordTrace tailWord_923616 prefixEnd_923616 474258948183163581852373 := by
  unfold tailWord_923616
  simp only [CollatzResearch.WordTrace]
  refine ⟨16843521510952223949751351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22458028681269631933001801 16843521510952223949751351)
  ·
    refine ⟨25265282266428335924627027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16843521510952223949751351 25265282266428335924627027)
    ·
      refine ⟨37897923399642503886940541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25265282266428335924627027 37897923399642503886940541)
      ·
        refine ⟨14211721274865938957602703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37897923399642503886940541 14211721274865938957602703)
        ·
          refine ⟨21317581912298908436404055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14211721274865938957602703 21317581912298908436404055)
          ·
            refine ⟨31976372868448362654606083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21317581912298908436404055 31976372868448362654606083)
            ·
              refine ⟨47964559302672543981909125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31976372868448362654606083 47964559302672543981909125)
              ·
                refine ⟨8993354869251101996607961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47964559302672543981909125 8993354869251101996607961)
                ·
                  refine ⟨6745016151938326497455971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8993354869251101996607961 6745016151938326497455971)
                  ·
                    refine ⟨10117524227907489746183957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6745016151938326497455971 10117524227907489746183957)
                    ·
                      refine ⟨474258948183163581852373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10117524227907489746183957 474258948183163581852373)
                      ·
                        rfl

theorem cell23_923616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_923616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923616 prefixEnd_923616 := by exact prefixLift 923616
  have htrace : WordTrace (prefixWord ++ tailWord_923616) baseStart_923616 baseEnd_923616 := by
    simpa [prefixWord, tailWord_923616, baseEnd_923616] using wordTrace_append hprefix tailTrace_923616
  have hstable : (prefixWord ++ tailWord_923616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923616).length < 2 ^ (prefixWord ++ tailWord_923616).sum := by decide
  have hdescent : baseEnd_923616 < baseStart_923616 := by decide
  rcases family_descends (prefixWord ++ tailWord_923616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923690 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 3, 5]
def baseStart_923690 : Nat := 118140960795 + 923690 * 2 ^ 59
def prefixEnd_923690 : Nat := 4983230072969 + 3 ^ 40 * 923690 * 2
def baseEnd_923690 : Nat := 158098981917198764109011

theorem tailTrace_923690 : CollatzResearch.WordTrace tailWord_923690 prefixEnd_923690 158098981917198764109011 := by
  unfold tailWord_923690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8422435505909089634424131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22459828015757572358464349 8422435505909089634424131)
  ·
    refine ⟨12633653258863634451636197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8422435505909089634424131 12633653258863634451636197)
    ·
      refine ⟨2368809986036931459681787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12633653258863634451636197 2368809986036931459681787)
      ·
        refine ⟨3553214979055397189522681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368809986036931459681787 3553214979055397189522681)
        ·
          refine ⟨2664911234291547892142011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3553214979055397189522681 2664911234291547892142011)
          ·
            refine ⟨3997366851437321838213017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664911234291547892142011 3997366851437321838213017)
            ·
              refine ⟨2998025138577991378659763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3997366851437321838213017 2998025138577991378659763)
              ·
                refine ⟨4497037707866987067989645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998025138577991378659763 4497037707866987067989645)
                ·
                  refine ⟨1686389140450120150496117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4497037707866987067989645 1686389140450120150496117)
                  ·
                    refine ⟨158098981917198764109011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1686389140450120150496117 158098981917198764109011)
                    ·
                      rfl

theorem cell23_923690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_923690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923690 prefixEnd_923690 := by exact prefixLift 923690
  have htrace : WordTrace (prefixWord ++ tailWord_923690) baseStart_923690 baseEnd_923690 := by
    simpa [prefixWord, tailWord_923690, baseEnd_923690] using wordTrace_append hprefix tailTrace_923690
  have hstable : (prefixWord ++ tailWord_923690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923690).length < 2 ^ (prefixWord ++ tailWord_923690).sum := by decide
  have hdescent : baseEnd_923690 < baseStart_923690 := by decide
  rcases family_descends (prefixWord ++ tailWord_923690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923697 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 2, 3, 2]
def baseStart_923697 : Nat := 118140960795 + 923697 * 2 ^ 59
def prefixEnd_923697 : Nat := 4983230072969 + 3 ^ 40 * 923697 * 2
def baseEnd_923697 : Nat := 474300540116177764939501

theorem tailTrace_923697 : CollatzResearch.WordTrace tailWord_923697 prefixEnd_923697 474300540116177764939501 := by
  unfold tailWord_923697
  simp only [CollatzResearch.WordTrace]
  refine ⟨33689997334610998733201345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22459998223073999155467563 33689997334610998733201345)
  ·
    refine ⟨25267498000958249049901009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33689997334610998733201345 25267498000958249049901009)
    ·
      refine ⟨18950623500718686787425757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25267498000958249049901009 18950623500718686787425757)
      ·
        refine ⟨7106483812769507545284659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18950623500718686787425757 7106483812769507545284659)
        ·
          refine ⟨10659725719154261317926989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7106483812769507545284659 10659725719154261317926989)
          ·
            refine ⟨3997397144682847994222621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10659725719154261317926989 3997397144682847994222621)
            ·
              refine ⟨1499023929256067997833483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3997397144682847994222621 1499023929256067997833483)
              ·
                refine ⟨2248535893884101996750225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1499023929256067997833483 2248535893884101996750225)
                ·
                  refine ⟨1686401920413076497562669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2248535893884101996750225 1686401920413076497562669)
                  ·
                    refine ⟨632400720154903686586001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686401920413076497562669 632400720154903686586001)
                    ·
                      refine ⟨474300540116177764939501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632400720154903686586001 474300540116177764939501)
                      ·
                        rfl

theorem cell23_923697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_923697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923697 prefixEnd_923697 := by exact prefixLift 923697
  have htrace : WordTrace (prefixWord ++ tailWord_923697) baseStart_923697 baseEnd_923697 := by
    simpa [prefixWord, tailWord_923697, baseEnd_923697] using wordTrace_append hprefix tailTrace_923697
  have hstable : (prefixWord ++ tailWord_923697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923697).length < 2 ^ (prefixWord ++ tailWord_923697).sum := by decide
  have hdescent : baseEnd_923697 < baseStart_923697 := by decide
  rcases family_descends (prefixWord ++ tailWord_923697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923703 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 1, 6]
def baseStart_923703 : Nat := 118140960795 + 923703 * 2 ^ 59
def prefixEnd_923703 : Nat := 4983230072969 + 3 ^ 40 * 923703 * 2
def baseEnd_923703 : Nat := 158101207000034913821491

theorem tailTrace_923703 : CollatzResearch.WordTrace tailWord_923703 prefixEnd_923703 158101207000034913821491 := by
  unfold tailWord_923703
  simp only [CollatzResearch.WordTrace]
  refine ⟨33690216172589261757919763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22460144115059507838613175 33690216172589261757919763)
  ·
    refine ⟨50535324258883892636879645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33690216172589261757919763 50535324258883892636879645)
    ·
      refine ⟨18950746597081459738829867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50535324258883892636879645 18950746597081459738829867)
      ·
        refine ⟨28426119895622189608244801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18950746597081459738829867 28426119895622189608244801)
        ·
          refine ⟨21319589921716642206183601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28426119895622189608244801 21319589921716642206183601)
          ·
            refine ⟨15989692441287481654637701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21319589921716642206183601 15989692441287481654637701)
            ·
              refine ⟨2998067332741402810244569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15989692441287481654637701 2998067332741402810244569)
              ·
                refine ⟨2248550499556052107683427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2998067332741402810244569 2248550499556052107683427)
                ·
                  refine ⟨3372825749334078161525141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248550499556052107683427 3372825749334078161525141)
                  ·
                    refine ⟨158101207000034913821491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3372825749334078161525141 158101207000034913821491)
                    ·
                      rfl

theorem cell23_923703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_923703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923703 prefixEnd_923703 := by exact prefixLift 923703
  have htrace : WordTrace (prefixWord ++ tailWord_923703) baseStart_923703 baseEnd_923703 := by
    simpa [prefixWord, tailWord_923703, baseEnd_923703] using wordTrace_append hprefix tailTrace_923703
  have hstable : (prefixWord ++ tailWord_923703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923703).length < 2 ^ (prefixWord ++ tailWord_923703).sum := by decide
  have hdescent : baseEnd_923703 < baseStart_923703 := by decide
  rcases family_descends (prefixWord ++ tailWord_923703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923720 : List Nat := [2, 1, 3, 1, 1, 1, 2, 6, 2, 4]
def baseStart_923720 : Nat := 118140960795 + 923720 * 2 ^ 59
def prefixEnd_923720 : Nat := 4983230072969 + 3 ^ 40 * 923720 * 2
def baseEnd_923720 : Nat := 158104116723743724983965

theorem tailTrace_923720 : CollatzResearch.WordTrace tailWord_923720 prefixEnd_923720 158104116723743724983965 := by
  unfold tailWord_923720
  simp only [CollatzResearch.WordTrace]
  refine ⟨16845418106763836830644307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22460557475685115774192409 16845418106763836830644307)
  ·
    refine ⟨25268127160145755245966461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16845418106763836830644307 25268127160145755245966461)
    ·
      refine ⟨9475547685054658217237423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25268127160145755245966461 9475547685054658217237423)
      ·
        refine ⟨14213321527581987325856135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9475547685054658217237423 14213321527581987325856135)
        ·
          refine ⟨21319982291372980988784203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14213321527581987325856135 21319982291372980988784203)
          ·
            refine ⟨31979973437059471483176305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21319982291372980988784203 31979973437059471483176305)
            ·
              refine ⟨23984980077794603612382229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31979973437059471483176305 23984980077794603612382229)
              ·
                refine ⟨1124295941146622044330417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23984980077794603612382229 1124295941146622044330417)
                ·
                  refine ⟨843221955859966533247813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1124295941146622044330417 843221955859966533247813)
                  ·
                    refine ⟨158104116723743724983965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 843221955859966533247813 158104116723743724983965)
                    ·
                      rfl

theorem cell23_923720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_923720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923720 prefixEnd_923720 := by exact prefixLift 923720
  have htrace : WordTrace (prefixWord ++ tailWord_923720) baseStart_923720 baseEnd_923720 := by
    simpa [prefixWord, tailWord_923720, baseEnd_923720] using wordTrace_append hprefix tailTrace_923720
  have hstable : (prefixWord ++ tailWord_923720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923720).length < 2 ^ (prefixWord ++ tailWord_923720).sum := by decide
  have hdescent : baseEnd_923720 < baseStart_923720 := by decide
  rcases family_descends (prefixWord ++ tailWord_923720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923737 : List Nat := [1, 2, 1, 2, 2, 1, 7, 1, 2, 4]
def baseStart_923737 : Nat := 118140960795 + 923737 * 2 ^ 59
def prefixEnd_923737 : Nat := 4983230072969 + 3 ^ 40 * 923737 * 2
def baseEnd_923737 : Nat := 158107026447452536146439

theorem tailTrace_923737 : CollatzResearch.WordTrace tailWord_923737 prefixEnd_923737 158107026447452536146439 := by
  unfold tailWord_923737
  simp only [CollatzResearch.WordTrace]
  refine ⟨33691456254466085564657465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22460970836310723709771643 33691456254466085564657465)
  ·
    refine ⟨25268592190849564173493099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33691456254466085564657465 25268592190849564173493099)
    ·
      refine ⟨37902888286274346260239649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25268592190849564173493099 37902888286274346260239649)
      ·
        refine ⟨28427166214705759695179737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37902888286274346260239649 28427166214705759695179737)
        ·
          refine ⟨21320374661029319771384803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28427166214705759695179737 21320374661029319771384803)
          ·
            refine ⟨31980561991543979657077205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21320374661029319771384803 31980561991543979657077205)
            ·
              refine ⟨749544421676812023212747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31980561991543979657077205 749544421676812023212747)
              ·
                refine ⟨1124316632515218034819121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 749544421676812023212747 1124316632515218034819121)
                ·
                  refine ⟨843237474386413526114341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1124316632515218034819121 843237474386413526114341)
                  ·
                    refine ⟨158107026447452536146439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 843237474386413526114341 158107026447452536146439)
                    ·
                      rfl

theorem cell23_923737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 2, 4].length) (baseStart_923737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923737 prefixEnd_923737 := by exact prefixLift 923737
  have htrace : WordTrace (prefixWord ++ tailWord_923737) baseStart_923737 baseEnd_923737 := by
    simpa [prefixWord, tailWord_923737, baseEnd_923737] using wordTrace_append hprefix tailTrace_923737
  have hstable : (prefixWord ++ tailWord_923737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923737).length < 2 ^ (prefixWord ++ tailWord_923737).sum := by decide
  have hdescent : baseEnd_923737 < baseStart_923737 := by decide
  rcases family_descends (prefixWord ++ tailWord_923737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923740 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_923740 : Nat := 118140960795 + 923740 * 2 ^ 59
def prefixEnd_923740 : Nat := 4983230072969 + 3 ^ 40 * 923740 * 2
def baseEnd_923740 : Nat := 474322619784321096701803

theorem tailTrace_923740 : CollatzResearch.WordTrace tailWord_923740 prefixEnd_923740 474322619784321096701803 := by
  unfold tailWord_923740
  simp only [CollatzResearch.WordTrace]
  refine ⟨16845782836727608538508337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22461043782303478051344449 16845782836727608538508337)
  ·
    refine ⟨12634337127545706403881253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16845782836727608538508337 12634337127545706403881253)
    ·
      refine ⟨2368938211414819950727735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12634337127545706403881253 2368938211414819950727735)
      ·
        refine ⟨3553407317122229926091603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368938211414819950727735 3553407317122229926091603)
        ·
          refine ⟨5330110975683344889137405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3553407317122229926091603 5330110975683344889137405)
          ·
            refine ⟨1998791615881254333426527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5330110975683344889137405 1998791615881254333426527)
            ·
              refine ⟨2998187423821881500139791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998791615881254333426527 2998187423821881500139791)
              ·
                refine ⟨4497281135732822250209687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998187423821881500139791 4497281135732822250209687)
                ·
                  refine ⟨6745921703599233375314531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497281135732822250209687 6745921703599233375314531)
                  ·
                    refine ⟨10118882555398850062971797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6745921703599233375314531 10118882555398850062971797)
                    ·
                      refine ⟨474322619784321096701803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10118882555398850062971797 474322619784321096701803)
                      ·
                        rfl

theorem cell23_923740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_923740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923740 prefixEnd_923740 := by exact prefixLift 923740
  have htrace : WordTrace (prefixWord ++ tailWord_923740) baseStart_923740 baseEnd_923740 := by
    simpa [prefixWord, tailWord_923740, baseEnd_923740] using wordTrace_append hprefix tailTrace_923740
  have hstable : (prefixWord ++ tailWord_923740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923740).length < 2 ^ (prefixWord ++ tailWord_923740).sum := by decide
  have hdescent : baseEnd_923740 < baseStart_923740 := by decide
  rcases family_descends (prefixWord ++ tailWord_923740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923794 : List Nat := [3, 2, 3, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_923794 : Nat := 118140960795 + 923794 * 2 ^ 59
def prefixEnd_923794 : Nat := 4983230072969 + 3 ^ 40 * 923794 * 2
def baseEnd_923794 : Nat := 474350347739663885426555

theorem tailTrace_923794 : CollatzResearch.WordTrace tailWord_923794 prefixEnd_923794 474350347739663885426555 := by
  unfold tailWord_923794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8423383803814896074870609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22462356810173056199654957 8423383803814896074870609)
  ·
    refine ⟨6317537852861172056152957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8423383803814896074870609 6317537852861172056152957)
    ·
      refine ⟨2369076694822939521057359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6317537852861172056152957 2369076694822939521057359)
      ·
        refine ⟨3553615042234409281586039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2369076694822939521057359 3553615042234409281586039)
        ·
          refine ⟨5330422563351613922379059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3553615042234409281586039 5330422563351613922379059)
          ·
            refine ⟨7995633845027420883568589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5330422563351613922379059 7995633845027420883568589)
            ·
              refine ⟨2998362691885282831338221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7995633845027420883568589 2998362691885282831338221)
              ·
                refine ⟨1124386009456981061751833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2998362691885282831338221 1124386009456981061751833)
                ·
                  refine ⟨843289507092735796313875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1124386009456981061751833 843289507092735796313875)
                  ·
                    refine ⟨1264934260639103694470813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 843289507092735796313875 1264934260639103694470813)
                    ·
                      refine ⟨474350347739663885426555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1264934260639103694470813 474350347739663885426555)
                      ·
                        rfl

theorem cell23_923794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_923794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923794 prefixEnd_923794 := by exact prefixLift 923794
  have htrace : WordTrace (prefixWord ++ tailWord_923794) baseStart_923794 baseEnd_923794 := by
    simpa [prefixWord, tailWord_923794, baseEnd_923794] using wordTrace_append hprefix tailTrace_923794
  have hstable : (prefixWord ++ tailWord_923794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923794).length < 2 ^ (prefixWord ++ tailWord_923794).sum := by decide
  have hdescent : baseEnd_923794 < baseStart_923794 := by decide
  rcases family_descends (prefixWord ++ tailWord_923794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923803 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 5]
def baseStart_923803 : Nat := 118140960795 + 923803 * 2 ^ 59
def prefixEnd_923803 : Nat := 4983230072969 + 3 ^ 40 * 923803 * 2
def baseEnd_923803 : Nat := 474354969065554350214013

theorem tailTrace_923803 : CollatzResearch.WordTrace tailWord_923803 prefixEnd_923803 474354969065554350214013 := by
  unfold tailWord_923803
  simp only [CollatzResearch.WordTrace]
  refine ⟨33693863472226978836560063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22462575648151319224373375 33693863472226978836560063)
  ·
    refine ⟨50540795208340468254840095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33693863472226978836560063 50540795208340468254840095)
    ·
      refine ⟨75811192812510702382260143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50540795208340468254840095 75811192812510702382260143)
      ·
        refine ⟨113716789218766053573390215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75811192812510702382260143 113716789218766053573390215)
        ·
          refine ⟨170575183828149080360085323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113716789218766053573390215 170575183828149080360085323)
          ·
            refine ⟨255862775742223620540127985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170575183828149080360085323 255862775742223620540127985)
            ·
              refine ⟨191897081806667715405095989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255862775742223620540127985 191897081806667715405095989)
              ·
                refine ⟨17990351419375098319227749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191897081806667715405095989 17990351419375098319227749)
                ·
                  refine ⟨3373190891132830934855203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17990351419375098319227749 3373190891132830934855203)
                  ·
                    refine ⟨5059786336699246402282805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3373190891132830934855203 5059786336699246402282805)
                    ·
                      refine ⟨474354969065554350214013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5059786336699246402282805 474354969065554350214013)
                      ·
                        rfl

theorem cell23_923803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 5].length) (baseStart_923803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923803 prefixEnd_923803 := by exact prefixLift 923803
  have htrace : WordTrace (prefixWord ++ tailWord_923803) baseStart_923803 baseEnd_923803 := by
    simpa [prefixWord, tailWord_923803, baseEnd_923803] using wordTrace_append hprefix tailTrace_923803
  have hstable : (prefixWord ++ tailWord_923803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923803).length < 2 ^ (prefixWord ++ tailWord_923803).sum := by decide
  have hdescent : baseEnd_923803 < baseStart_923803 := by decide
  rcases family_descends (prefixWord ++ tailWord_923803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923834 : List Nat := [3, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2]
def baseStart_923834 : Nat := 118140960795 + 923834 * 2 ^ 59
def prefixEnd_923834 : Nat := 4983230072969 + 3 ^ 40 * 923834 * 2
def baseEnd_923834 : Nat := 474370886965843728926371

theorem tailTrace_923834 : CollatzResearch.WordTrace tailWord_923834 prefixEnd_923834 474370886965843728926371 := by
  unfold tailWord_923834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8423748533778667782734639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22463329423409780753959037 8423748533778667782734639)
  ·
    refine ⟨12635622800668001674101959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8423748533778667782734639 12635622800668001674101959)
    ·
      refine ⟨18953434201002002511152939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12635622800668001674101959 18953434201002002511152939)
      ·
        refine ⟨28430151301503003766729409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18953434201002002511152939 28430151301503003766729409)
        ·
          refine ⟨21322613476127252825047057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28430151301503003766729409 21322613476127252825047057)
          ·
            refine ⟨15991960107095439618785293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21322613476127252825047057 15991960107095439618785293)
            ·
              refine ⟨5996985040160789857044485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15991960107095439618785293 5996985040160789857044485)
              ·
                refine ⟨1124434695030148098195841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5996985040160789857044485 1124434695030148098195841)
                ·
                  refine ⟨843326021272611073646881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1124434695030148098195841 843326021272611073646881)
                  ·
                    refine ⟨632494515954458305235161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 843326021272611073646881 632494515954458305235161)
                    ·
                      refine ⟨474370886965843728926371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632494515954458305235161 474370886965843728926371)
                      ·
                        rfl

theorem cell23_923834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2].length) (baseStart_923834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923834 prefixEnd_923834 := by exact prefixLift 923834
  have htrace : WordTrace (prefixWord ++ tailWord_923834) baseStart_923834 baseEnd_923834 := by
    simpa [prefixWord, tailWord_923834, baseEnd_923834] using wordTrace_append hprefix tailTrace_923834
  have hstable : (prefixWord ++ tailWord_923834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923834).length < 2 ^ (prefixWord ++ tailWord_923834).sum := by decide
  have hdescent : baseEnd_923834 < baseStart_923834 := by decide
  rcases family_descends (prefixWord ++ tailWord_923834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923885 : List Nat := [1, 5, 1, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_923885 : Nat := 118140960795 + 923885 * 2 ^ 59
def prefixEnd_923885 : Nat := 4983230072969 + 3 ^ 40 * 923885 * 2
def baseEnd_923885 : Nat := 474397074479223029388637

theorem tailTrace_923885 : CollatzResearch.WordTrace tailWord_923885 prefixEnd_923885 474397074479223029388637 := by
  unfold tailWord_923885
  simp only [CollatzResearch.WordTrace]
  refine ⟨33696854257929906841045109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22464569505286604560696739 33696854257929906841045109)
  ·
    refine ⟨3159080086680928766347979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33696854257929906841045109 3159080086680928766347979)
    ·
      refine ⟨4738620130021393149521969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3159080086680928766347979 4738620130021393149521969)
      ·
        refine ⟨3553965097516044862141477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4738620130021393149521969 3553965097516044862141477)
        ·
          refine ⟨666368455784258411651527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3553965097516044862141477 666368455784258411651527)
          ·
            refine ⟨999552683676387617477291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666368455784258411651527 999552683676387617477291)
            ·
              refine ⟨1499329025514581426215937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999552683676387617477291 1499329025514581426215937)
              ·
                refine ⟨1124496769135936069661953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1499329025514581426215937 1124496769135936069661953)
                ·
                  refine ⟨843372576851952052246465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1124496769135936069661953 843372576851952052246465)
                  ·
                    refine ⟨632529432638964039184849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 843372576851952052246465 632529432638964039184849)
                    ·
                      refine ⟨474397074479223029388637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632529432638964039184849 474397074479223029388637)
                      ·
                        rfl

theorem cell23_923885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_923885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923885 prefixEnd_923885 := by exact prefixLift 923885
  have htrace : WordTrace (prefixWord ++ tailWord_923885) baseStart_923885 baseEnd_923885 := by
    simpa [prefixWord, tailWord_923885, baseEnd_923885] using wordTrace_append hprefix tailTrace_923885
  have hstable : (prefixWord ++ tailWord_923885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923885).length < 2 ^ (prefixWord ++ tailWord_923885).sum := by decide
  have hdescent : baseEnd_923885 < baseStart_923885 := by decide
  rcases family_descends (prefixWord ++ tailWord_923885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923907 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 2, 4, 2]
def baseStart_923907 : Nat := 118140960795 + 923907 * 2 ^ 59
def prefixEnd_923907 : Nat := 4983230072969 + 3 ^ 40 * 923907 * 2
def baseEnd_923907 : Nat := 474408371053621943313535

theorem tailTrace_923907 : CollatzResearch.WordTrace tailWord_923907 prefixEnd_923907 474408371053621943313535 := by
  unfold tailWord_923907
  simp only [CollatzResearch.WordTrace]
  refine ⟨33697656663850204598345975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22465104442566803065563983 33697656663850204598345975)
  ·
    refine ⟨50546484995775306897518963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33697656663850204598345975 50546484995775306897518963)
    ·
      refine ⟨75819727493662960346278445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50546484995775306897518963 75819727493662960346278445)
      ·
        refine ⟨28432397810123610129854417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75819727493662960346278445 28432397810123610129854417)
        ·
          refine ⟨21324298357592707597390813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28432397810123610129854417 21324298357592707597390813)
          ·
            refine ⟨7996611884097265349021555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21324298357592707597390813 7996611884097265349021555)
            ·
              refine ⟨11994917826145898023532333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7996611884097265349021555 11994917826145898023532333)
              ·
                refine ⟨4498094184804711758824625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11994917826145898023532333 4498094184804711758824625)
                ·
                  refine ⟨3373570638603533819118469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4498094184804711758824625 3373570638603533819118469)
                  ·
                    refine ⟨632544494738162591084713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3373570638603533819118469 632544494738162591084713)
                    ·
                      refine ⟨474408371053621943313535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632544494738162591084713 474408371053621943313535)
                      ·
                        rfl

theorem cell23_923907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 4, 2].length) (baseStart_923907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923907 prefixEnd_923907 := by exact prefixLift 923907
  have htrace : WordTrace (prefixWord ++ tailWord_923907) baseStart_923907 baseEnd_923907 := by
    simpa [prefixWord, tailWord_923907, baseEnd_923907] using wordTrace_append hprefix tailTrace_923907
  have hstable : (prefixWord ++ tailWord_923907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923907).length < 2 ^ (prefixWord ++ tailWord_923907).sum := by decide
  have hdescent : baseEnd_923907 < baseStart_923907 := by decide
  rcases family_descends (prefixWord ++ tailWord_923907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923927 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 3]
def baseStart_923927 : Nat := 118140960795 + 923927 * 2 ^ 59
def prefixEnd_923927 : Nat := 4983230072969 + 3 ^ 40 * 923927 * 2
def baseEnd_923927 : Nat := 474418640666711865063443

theorem tailTrace_923927 : CollatzResearch.WordTrace tailWord_923927 prefixEnd_923927 474418640666711865063443 := by
  unfold tailWord_923927
  simp only [CollatzResearch.WordTrace]
  refine ⟨33698386123777748014074035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22465590749185165342716023 33698386123777748014074035)
  ·
    refine ⟨50547579185666622021111053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33698386123777748014074035 50547579185666622021111053)
    ·
      refine ⟨18955342194624983257916645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50547579185666622021111053 18955342194624983257916645)
      ·
        refine ⟨3554126661492184360859371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18955342194624983257916645 3554126661492184360859371)
        ·
          refine ⟨5331189992238276541289057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3554126661492184360859371 5331189992238276541289057)
          ·
            refine ⟨3998392494178707405966793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5331189992238276541289057 3998392494178707405966793)
            ·
              refine ⟨2998794370634030554475095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3998392494178707405966793 2998794370634030554475095)
              ·
                refine ⟨4498191555951045831712643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998794370634030554475095 4498191555951045831712643)
                ·
                  refine ⟨6747287333926568747568965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498191555951045831712643 6747287333926568747568965)
                  ·
                    refine ⟨1265116375111231640169181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6747287333926568747568965 1265116375111231640169181)
                    ·
                      refine ⟨474418640666711865063443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1265116375111231640169181 474418640666711865063443)
                      ·
                        rfl

theorem cell23_923927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_923927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923927 prefixEnd_923927 := by exact prefixLift 923927
  have htrace : WordTrace (prefixWord ++ tailWord_923927) baseStart_923927 baseEnd_923927 := by
    simpa [prefixWord, tailWord_923927, baseEnd_923927] using wordTrace_append hprefix tailTrace_923927
  have hstable : (prefixWord ++ tailWord_923927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923927).length < 2 ^ (prefixWord ++ tailWord_923927).sum := by decide
  have hdescent : baseEnd_923927 < baseStart_923927 := by decide
  rcases family_descends (prefixWord ++ tailWord_923927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923984 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 2, 3, 2]
def baseStart_923984 : Nat := 118140960795 + 923984 * 2 ^ 59
def prefixEnd_923984 : Nat := 4983230072969 + 3 ^ 40 * 923984 * 2
def baseEnd_923984 : Nat := 474447909064018142050681

theorem tailTrace_923984 : CollatzResearch.WordTrace tailWord_923984 prefixEnd_923984 474447909064018142050681 := by
  unfold tailWord_923984
  simp only [CollatzResearch.WordTrace]
  refine ⟨16850232542285623374449503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22466976723047497832599337 16850232542285623374449503)
  ·
    refine ⟨25275348813428435061674255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16850232542285623374449503 25275348813428435061674255)
    ·
      refine ⟨37913023220142652592511383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25275348813428435061674255 37913023220142652592511383)
      ·
        refine ⟨56869534830213978888767075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37913023220142652592511383 56869534830213978888767075)
        ·
          refine ⟨85304302245320968333150613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56869534830213978888767075 85304302245320968333150613)
          ·
            refine ⟨3998639167749420390616435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85304302245320968333150613 3998639167749420390616435)
            ·
              refine ⟨5997958751624130585924653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3998639167749420390616435 5997958751624130585924653)
              ·
                refine ⟨2249234531859048969721745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5997958751624130585924653 2249234531859048969721745)
                ·
                  refine ⟨1686925898894286727291309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2249234531859048969721745 1686925898894286727291309)
                  ·
                    refine ⟨632597212085357522734241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1686925898894286727291309 632597212085357522734241)
                    ·
                      refine ⟨474447909064018142050681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632597212085357522734241 474447909064018142050681)
                      ·
                        rfl

theorem cell23_923984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 2, 3, 2].length) (baseStart_923984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923984 prefixEnd_923984 := by exact prefixLift 923984
  have htrace : WordTrace (prefixWord ++ tailWord_923984) baseStart_923984 baseEnd_923984 := by
    simpa [prefixWord, tailWord_923984, baseEnd_923984] using wordTrace_append hprefix tailTrace_923984
  have hstable : (prefixWord ++ tailWord_923984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923984).length < 2 ^ (prefixWord ++ tailWord_923984).sum := by decide
  have hdescent : baseEnd_923984 < baseStart_923984 := by decide
  rcases family_descends (prefixWord ++ tailWord_923984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923991 : List Nat := [1, 1, 3, 2, 3, 1, 2, 5, 1, 1, 3]
def baseStart_923991 : Nat := 118140960795 + 923991 * 2 ^ 59
def prefixEnd_923991 : Nat := 4983230072969 + 3 ^ 40 * 923991 * 2
def baseEnd_923991 : Nat := 474451503428599614663149

theorem tailTrace_923991 : CollatzResearch.WordTrace tailWord_923991 prefixEnd_923991 474451503428599614663149 := by
  unfold tailWord_923991
  simp only [CollatzResearch.WordTrace]
  refine ⟨33700720395545886944403827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22467146930363924629602551 33700720395545886944403827)
  ·
    refine ⟨50551080593318830416605741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33700720395545886944403827 50551080593318830416605741)
    ·
      refine ⟨18956655222494561406227153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50551080593318830416605741 18956655222494561406227153)
      ·
        refine ⟨14217491416870921054670365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18956655222494561406227153 14217491416870921054670365)
        ·
          refine ⟨5331559281326595395501387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14217491416870921054670365 5331559281326595395501387)
          ·
            refine ⟨7997338921989893093252081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5331559281326595395501387 7997338921989893093252081)
            ·
              refine ⟨5998004191492419819939061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7997338921989893093252081 5998004191492419819939061)
              ·
                refine ⟨562312892952414358119287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5998004191492419819939061 562312892952414358119287)
                ·
                  refine ⟨843469339428621537178931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562312892952414358119287 843469339428621537178931)
                  ·
                    refine ⟨1265204009142932305768397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 843469339428621537178931 1265204009142932305768397)
                    ·
                      refine ⟨474451503428599614663149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1265204009142932305768397 474451503428599614663149)
                      ·
                        rfl

theorem cell23_923991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_923991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_923991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_923991 prefixEnd_923991 := by exact prefixLift 923991
  have htrace : WordTrace (prefixWord ++ tailWord_923991) baseStart_923991 baseEnd_923991 := by
    simpa [prefixWord, tailWord_923991, baseEnd_923991] using wordTrace_append hprefix tailTrace_923991
  have hstable : (prefixWord ++ tailWord_923991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923991).length < 2 ^ (prefixWord ++ tailWord_923991).sum := by decide
  have hdescent : baseEnd_923991 < baseStart_923991 := by decide
  rcases family_descends (prefixWord ++ tailWord_923991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924008 : List Nat := [2, 1, 4, 2, 2, 2, 1, 4, 1, 1, 3]
def baseStart_924008 : Nat := 118140960795 + 924008 * 2 ^ 59
def prefixEnd_924008 : Nat := 4983230072969 + 3 ^ 40 * 924008 * 2
def baseEnd_924008 : Nat := 474460232599726048150571

theorem tailTrace_924008 : CollatzResearch.WordTrace tailWord_924008 prefixEnd_924008 474460232599726048150571 := by
  unfold tailWord_924008
  simp only [CollatzResearch.WordTrace]
  refine ⟨16850670218242149423886339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22467560290989532565181785 16850670218242149423886339)
  ·
    refine ⟨25276005327363224135829509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16850670218242149423886339 25276005327363224135829509)
    ·
      refine ⟨4739250998880604525468033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25276005327363224135829509 4739250998880604525468033)
      ·
        refine ⟨3554438249160453394101025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4739250998880604525468033 3554438249160453394101025)
        ·
          refine ⟨2665828686870340045575769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3554438249160453394101025 2665828686870340045575769)
          ·
            refine ⟨1999371515152755034181827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2665828686870340045575769 1999371515152755034181827)
            ·
              refine ⟨2999057272729132551272741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999371515152755034181827 2999057272729132551272741)
              ·
                refine ⟨562323238636712353363639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2999057272729132551272741 562323238636712353363639)
                ·
                  refine ⟨843484857955068530045459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562323238636712353363639 843484857955068530045459)
                  ·
                    refine ⟨1265227286932602795068189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 843484857955068530045459 1265227286932602795068189)
                    ·
                      refine ⟨474460232599726048150571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1265227286932602795068189 474460232599726048150571)
                      ·
                        rfl

theorem cell23_924008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_924008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924008 prefixEnd_924008 := by exact prefixLift 924008
  have htrace : WordTrace (prefixWord ++ tailWord_924008) baseStart_924008 baseEnd_924008 := by
    simpa [prefixWord, tailWord_924008, baseEnd_924008] using wordTrace_append hprefix tailTrace_924008
  have hstable : (prefixWord ++ tailWord_924008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924008).length < 2 ^ (prefixWord ++ tailWord_924008).sum := by decide
  have hdescent : baseEnd_924008 < baseStart_924008 := by decide
  rcases family_descends (prefixWord ++ tailWord_924008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924027 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 4]
def baseStart_924027 : Nat := 118140960795 + 924027 * 2 ^ 59
def prefixEnd_924027 : Nat := 4983230072969 + 3 ^ 40 * 924027 * 2
def baseEnd_924027 : Nat := 474469988732161473812983

theorem tailTrace_924027 : CollatzResearch.WordTrace tailWord_924027 prefixEnd_924027 474469988732161473812983 := by
  unfold tailWord_924027
  simp only [CollatzResearch.WordTrace]
  refine ⟨33702033423415465092714335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22468022282276976728476223 33702033423415465092714335)
  ·
    refine ⟨50553050135123197639071503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33702033423415465092714335 50553050135123197639071503)
    ·
      refine ⟨75829575202684796458607255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50553050135123197639071503 75829575202684796458607255)
      ·
        refine ⟨113744362804027194687910883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75829575202684796458607255 113744362804027194687910883)
        ·
          refine ⟨170616544206040792031866325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113744362804027194687910883 170616544206040792031866325)
          ·
            refine ⟨3998825254829081063246867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 170616544206040792031866325 3998825254829081063246867)
            ·
              refine ⟨5998237882243621594870301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3998825254829081063246867 5998237882243621594870301)
              ·
                refine ⟨2249339205841358098076363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5998237882243621594870301 2249339205841358098076363)
                ·
                  refine ⟨3374008808762037147114545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249339205841358098076363 3374008808762037147114545)
                  ·
                    refine ⟨2530506606571527860335909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3374008808762037147114545 2530506606571527860335909)
                    ·
                      refine ⟨474469988732161473812983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2530506606571527860335909 474469988732161473812983)
                      ·
                        rfl

theorem cell23_924027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 4].length) (baseStart_924027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924027 prefixEnd_924027 := by exact prefixLift 924027
  have htrace : WordTrace (prefixWord ++ tailWord_924027) baseStart_924027 baseEnd_924027 := by
    simpa [prefixWord, tailWord_924027, baseEnd_924027] using wordTrace_append hprefix tailTrace_924027
  have hstable : (prefixWord ++ tailWord_924027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924027).length < 2 ^ (prefixWord ++ tailWord_924027).sum := by decide
  have hdescent : baseEnd_924027 < baseStart_924027 := by decide
  rcases family_descends (prefixWord ++ tailWord_924027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924065 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 3, 2, 2]
def baseStart_924065 : Nat := 118140960795 + 924065 * 2 ^ 59
def prefixEnd_924065 : Nat := 4983230072969 + 3 ^ 40 * 924065 * 2
def baseEnd_924065 : Nat := 474489500997032325137809

theorem tailTrace_924065 : CollatzResearch.WordTrace tailWord_924065 prefixEnd_924065 474489500997032325137809 := by
  unfold tailWord_924065
  simp only [CollatzResearch.WordTrace]
  refine ⟨33703419397277797582597649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22468946264851865055065099 33703419397277797582597649)
  ·
    refine ⟨25277564547958348186948237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33703419397277797582597649 25277564547958348186948237)
    ·
      refine ⟨9479086705484380570105589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25277564547958348186948237 9479086705484380570105589)
      ·
        refine ⟨888664378639160678447399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9479086705484380570105589 888664378639160678447399)
        ·
          refine ⟨1332996567958741017671099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888664378639160678447399 1332996567958741017671099)
          ·
            refine ⟨1999494851938111526506649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332996567958741017671099 1999494851938111526506649)
            ·
              refine ⟨1499621138953583644879987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1999494851938111526506649 1499621138953583644879987)
              ·
                refine ⟨2249431708430375467319981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1499621138953583644879987 2249431708430375467319981)
                ·
                  refine ⟨843536890661390800244993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2249431708430375467319981 843536890661390800244993)
                  ·
                    refine ⟨632652667996043100183745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 843536890661390800244993 632652667996043100183745)
                    ·
                      refine ⟨474489500997032325137809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632652667996043100183745 474489500997032325137809)
                      ·
                        rfl

theorem cell23_924065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_924065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924065 prefixEnd_924065 := by exact prefixLift 924065
  have htrace : WordTrace (prefixWord ++ tailWord_924065) baseStart_924065 baseEnd_924065 := by
    simpa [prefixWord, tailWord_924065, baseEnd_924065] using wordTrace_append hprefix tailTrace_924065
  have hstable : (prefixWord ++ tailWord_924065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924065).length < 2 ^ (prefixWord ++ tailWord_924065).sum := by decide
  have hdescent : baseEnd_924065 < baseStart_924065 := by decide
  rcases family_descends (prefixWord ++ tailWord_924065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924081 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 1, 3, 3]
def baseStart_924081 : Nat := 118140960795 + 924081 * 2 ^ 59
def prefixEnd_924081 : Nat := 4983230072969 + 3 ^ 40 * 924081 * 2
def baseEnd_924081 : Nat := 474497716687504262537735

theorem tailTrace_924081 : CollatzResearch.WordTrace tailWord_924081 prefixEnd_924081 474497716687504262537735 := by
  unfold tailWord_924081
  simp only [CollatzResearch.WordTrace]
  refine ⟨33704002965219832315180097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22469335310146554876786731 33704002965219832315180097)
  ·
    refine ⟨25278002223914874236385073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33704002965219832315180097 25278002223914874236385073)
    ·
      refine ⟨18958501667936155677288805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25278002223914874236385073 18958501667936155677288805)
      ·
        refine ⟨3554719062738029189491651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18958501667936155677288805 3554719062738029189491651)
        ·
          refine ⟨5332078594107043784237477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3554719062738029189491651 5332078594107043784237477)
          ·
            refine ⟨999764736395070709544527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5332078594107043784237477 999764736395070709544527)
            ·
              refine ⟨1499647104592606064316791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999764736395070709544527 1499647104592606064316791)
              ·
                refine ⟨2249470656888909096475187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1499647104592606064316791 2249470656888909096475187)
                ·
                  refine ⟨3374205985333363644712781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249470656888909096475187 3374205985333363644712781)
                  ·
                    refine ⟨1265327244500011366767293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3374205985333363644712781 1265327244500011366767293)
                    ·
                      refine ⟨474497716687504262537735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1265327244500011366767293 474497716687504262537735)
                      ·
                        rfl

theorem cell23_924081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_924081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924081 prefixEnd_924081 := by exact prefixLift 924081
  have htrace : WordTrace (prefixWord ++ tailWord_924081) baseStart_924081 baseEnd_924081 := by
    simpa [prefixWord, tailWord_924081, baseEnd_924081] using wordTrace_append hprefix tailTrace_924081
  have hstable : (prefixWord ++ tailWord_924081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924081).length < 2 ^ (prefixWord ++ tailWord_924081).sum := by decide
  have hdescent : baseEnd_924081 < baseStart_924081 := by decide
  rcases family_descends (prefixWord ++ tailWord_924081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924107 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 3]
def baseStart_924107 : Nat := 118140960795 + 924107 * 2 ^ 59
def prefixEnd_924107 : Nat := 4983230072969 + 3 ^ 40 * 924107 * 2
def baseEnd_924107 : Nat := 474511067184521160812615

theorem tailTrace_924107 : CollatzResearch.WordTrace tailWord_924107 prefixEnd_924107 474511067184521160812615 := by
  unfold tailWord_924107
  simp only [CollatzResearch.WordTrace]
  refine ⟨33704951263125638755626575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22469967508750425837084383 33704951263125638755626575)
  ·
    refine ⟨50557426894688458133439863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33704951263125638755626575 50557426894688458133439863)
    ·
      refine ⟨75836140342032687200159795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50557426894688458133439863 75836140342032687200159795)
      ·
        refine ⟨113754210513049030800239693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75836140342032687200159795 113754210513049030800239693)
        ·
          refine ⟨42657828942393386550089885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113754210513049030800239693 42657828942393386550089885)
          ·
            refine ⟨15996685853397519956283707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42657828942393386550089885 15996685853397519956283707)
            ·
              refine ⟨23995028780096279934425561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15996685853397519956283707 23995028780096279934425561)
              ·
                refine ⟨17996271585072209950819171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23995028780096279934425561 17996271585072209950819171)
                ·
                  refine ⟨26994407377608314926228757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17996271585072209950819171 26994407377608314926228757)
                  ·
                    refine ⟨1265362845825389762166973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26994407377608314926228757 1265362845825389762166973)
                    ·
                      refine ⟨474511067184521160812615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1265362845825389762166973 474511067184521160812615)
                      ·
                        rfl

theorem cell23_924107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 3].length) (baseStart_924107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924107 prefixEnd_924107 := by exact prefixLift 924107
  have htrace : WordTrace (prefixWord ++ tailWord_924107) baseStart_924107 baseEnd_924107 := by
    simpa [prefixWord, tailWord_924107, baseEnd_924107] using wordTrace_append hprefix tailTrace_924107
  have hstable : (prefixWord ++ tailWord_924107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924107).length < 2 ^ (prefixWord ++ tailWord_924107).sum := by decide
  have hdescent : baseEnd_924107 < baseStart_924107 := by decide
  rcases family_descends (prefixWord ++ tailWord_924107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924121 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 4, 2, 2]
def baseStart_924121 : Nat := 118140960795 + 924121 * 2 ^ 59
def prefixEnd_924121 : Nat := 4983230072969 + 3 ^ 40 * 924121 * 2
def baseEnd_924121 : Nat := 474518255913684106037551

theorem tailTrace_924121 : CollatzResearch.WordTrace tailWord_924121 prefixEnd_924121 474518255913684106037551 := by
  unfold tailWord_924121
  simp only [CollatzResearch.WordTrace]
  refine ⟨33705461885074919146636217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22470307923383279431090811 33705461885074919146636217)
  ·
    refine ⟨25279096413806189359977163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33705461885074919146636217 25279096413806189359977163)
    ·
      refine ⟨37918644620709284039965745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25279096413806189359977163 37918644620709284039965745)
      ·
        refine ⟨28438983465531963029974309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37918644620709284039965745 28438983465531963029974309)
        ·
          refine ⟨5332309399787243068120183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28438983465531963029974309 5332309399787243068120183)
          ·
            refine ⟨7998464099680864602180275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332309399787243068120183 7998464099680864602180275)
            ·
              refine ⟨11997696149521296903270413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998464099680864602180275 11997696149521296903270413)
              ·
                refine ⟨4499136056070486338726405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11997696149521296903270413 4499136056070486338726405)
                ·
                  refine ⟨843588010513216188511201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4499136056070486338726405 843588010513216188511201)
                  ·
                    refine ⟨632691007884912141383401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 843588010513216188511201 632691007884912141383401)
                    ·
                      refine ⟨474518255913684106037551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632691007884912141383401 474518255913684106037551)
                      ·
                        rfl

theorem cell23_924121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 2, 2].length) (baseStart_924121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924121 prefixEnd_924121 := by exact prefixLift 924121
  have htrace : WordTrace (prefixWord ++ tailWord_924121) baseStart_924121 baseEnd_924121 := by
    simpa [prefixWord, tailWord_924121, baseEnd_924121] using wordTrace_append hprefix tailTrace_924121
  have hstable : (prefixWord ++ tailWord_924121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924121).length < 2 ^ (prefixWord ++ tailWord_924121).sum := by decide
  have hdescent : baseEnd_924121 < baseStart_924121 := by decide
  rcases family_descends (prefixWord ++ tailWord_924121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924184 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_924184 : Nat := 118140960795 + 924184 * 2 ^ 59
def prefixEnd_924184 : Nat := 4983230072969 + 3 ^ 40 * 924184 * 2
def baseEnd_924184 : Nat := 474550605194917359549761

theorem tailTrace_924184 : CollatzResearch.WordTrace tailWord_924184 prefixEnd_924184 474550605194917359549761 := by
  unfold tailWord_924184
  simp only [CollatzResearch.WordTrace]
  refine ⟨16853879841923340453089803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22471839789231120604119737 16853879841923340453089803)
  ·
    refine ⟨25280819762885010679634705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16853879841923340453089803 25280819762885010679634705)
    ·
      refine ⟨18960614822163758009726029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25280819762885010679634705 18960614822163758009726029)
      ·
        refine ⟨7110230558311409253647261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18960614822163758009726029 7110230558311409253647261)
        ·
          refine ⟨2666336459366778470117723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7110230558311409253647261 2666336459366778470117723)
          ·
            refine ⟨3999504689050167705176585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2666336459366778470117723 3999504689050167705176585)
            ·
              refine ⟨2999628516787625778882439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3999504689050167705176585 2999628516787625778882439)
              ·
                refine ⟨4499442775181438668323659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999628516787625778882439 4499442775181438668323659)
                ·
                  refine ⟨6749164162772158002485489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4499442775181438668323659 6749164162772158002485489)
                  ·
                    refine ⟨5061873122079118501864117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6749164162772158002485489 5061873122079118501864117)
                    ·
                      refine ⟨474550605194917359549761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5061873122079118501864117 474550605194917359549761)
                      ·
                        rfl

theorem cell23_924184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_924184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924184 prefixEnd_924184 := by exact prefixLift 924184
  have htrace : WordTrace (prefixWord ++ tailWord_924184) baseStart_924184 baseEnd_924184 := by
    simpa [prefixWord, tailWord_924184, baseEnd_924184] using wordTrace_append hprefix tailTrace_924184
  have hstable : (prefixWord ++ tailWord_924184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924184).length < 2 ^ (prefixWord ++ tailWord_924184).sum := by decide
  have hdescent : baseEnd_924184 < baseStart_924184 := by decide
  rcases family_descends (prefixWord ++ tailWord_924184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924194 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_924194 : Nat := 118140960795 + 924194 * 2 ^ 59
def prefixEnd_924194 : Nat := 4983230072969 + 3 ^ 40 * 924194 * 2
def baseEnd_924194 : Nat := 474555740001462320424715

theorem tailTrace_924194 : CollatzResearch.WordTrace tailWord_924194 prefixEnd_924194 474555740001462320424715 := by
  unfold tailWord_924194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8427031103452613153510909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22472082942540301742695757 8427031103452613153510909)
  ·
    refine ⟨3160136663794729932566591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8427031103452613153510909 3160136663794729932566591)
    ·
      refine ⟨4740204995692094898849887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3160136663794729932566591 4740204995692094898849887)
      ·
        refine ⟨7110307493538142348274831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4740204995692094898849887 7110307493538142348274831)
        ·
          refine ⟨10665461240307213522412247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7110307493538142348274831 10665461240307213522412247)
          ·
            refine ⟨15998191860460820283618371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10665461240307213522412247 15998191860460820283618371)
            ·
              refine ⟨23997287790691230425427557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15998191860460820283618371 23997287790691230425427557)
              ·
                refine ⟨4499491460754605704767667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23997287790691230425427557 4499491460754605704767667)
                ·
                  refine ⟨6749237191131908557151501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4499491460754605704767667 6749237191131908557151501)
                  ·
                    refine ⟨2530963946674465708931813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6749237191131908557151501 2530963946674465708931813)
                    ·
                      refine ⟨474555740001462320424715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2530963946674465708931813 474555740001462320424715)
                      ·
                        rfl

theorem cell23_924194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_924194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924194 prefixEnd_924194 := by exact prefixLift 924194
  have htrace : WordTrace (prefixWord ++ tailWord_924194) baseStart_924194 baseEnd_924194 := by
    simpa [prefixWord, tailWord_924194, baseEnd_924194] using wordTrace_append hprefix tailTrace_924194
  have hstable : (prefixWord ++ tailWord_924194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924194).length < 2 ^ (prefixWord ++ tailWord_924194).sum := by decide
  have hdescent : baseEnd_924194 < baseStart_924194 := by decide
  rcases family_descends (prefixWord ++ tailWord_924194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924207 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 6]
def baseStart_924207 : Nat := 118140960795 + 924207 * 2 ^ 59
def prefixEnd_924207 : Nat := 4983230072969 + 3 ^ 40 * 924207 * 2
def baseEnd_924207 : Nat := 474562415249970769562155

theorem tailTrace_924207 : CollatzResearch.WordTrace tailWord_924207 prefixEnd_924207 474562415249970769562155 := by
  unfold tailWord_924207
  simp only [CollatzResearch.WordTrace]
  refine ⟨33708598562763355834266875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22472399041842237222844583 33708598562763355834266875)
  ·
    refine ⟨50562897844145033751400313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33708598562763355834266875 50562897844145033751400313)
    ·
      refine ⟨37922173383108775313550235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50562897844145033751400313 37922173383108775313550235)
      ·
        refine ⟨56883260074663162970325353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37922173383108775313550235 56883260074663162970325353)
        ·
          refine ⟨42662445055997372227744015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56883260074663162970325353 42662445055997372227744015)
          ·
            refine ⟨63993667583996058341616023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42662445055997372227744015 63993667583996058341616023)
            ·
              refine ⟨95990501375994087512424035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63993667583996058341616023 95990501375994087512424035)
              ·
                refine ⟨143985752063991131268636053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95990501375994087512424035 143985752063991131268636053)
                ·
                  refine ⟨6749332127999584278217315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143985752063991131268636053 6749332127999584278217315)
                  ·
                    refine ⟨10123998191999376417325973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6749332127999584278217315 10123998191999376417325973)
                    ·
                      refine ⟨474562415249970769562155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10123998191999376417325973 474562415249970769562155)
                      ·
                        rfl

theorem cell23_924207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_924207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924207 prefixEnd_924207 := by exact prefixLift 924207
  have htrace : WordTrace (prefixWord ++ tailWord_924207) baseStart_924207 baseEnd_924207 := by
    simpa [prefixWord, tailWord_924207, baseEnd_924207] using wordTrace_append hprefix tailTrace_924207
  have hstable : (prefixWord ++ tailWord_924207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924207).length < 2 ^ (prefixWord ++ tailWord_924207).sum := by decide
  have hdescent : baseEnd_924207 < baseStart_924207 := by decide
  rcases family_descends (prefixWord ++ tailWord_924207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924234 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 8]
def baseStart_924234 : Nat := 118140960795 + 924234 * 2 ^ 59
def prefixEnd_924234 : Nat := 4983230072969 + 3 ^ 40 * 924234 * 2
def baseEnd_924234 : Nat := 52730697691960240436059

theorem tailTrace_924234 : CollatzResearch.WordTrace tailWord_924234 prefixEnd_924234 52730697691960240436059 := by
  unfold tailWord_924234
  simp only [CollatzResearch.WordTrace]
  refine ⟨8427395833416384861374939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22473055555777026296999837 8427395833416384861374939)
  ·
    refine ⟨12641093750124577292062409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8427395833416384861374939 12641093750124577292062409)
    ·
      refine ⟨9480820312593432969046807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12641093750124577292062409 9480820312593432969046807)
      ·
        refine ⟨14221230468890149453570211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9480820312593432969046807 14221230468890149453570211)
        ·
          refine ⟨21331845703335224180355317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14221230468890149453570211 21331845703335224180355317)
          ·
            refine ⟨1999860534687677266908311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21331845703335224180355317 1999860534687677266908311)
            ·
              refine ⟨2999790802031515900362467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999860534687677266908311 2999790802031515900362467)
              ·
                refine ⟨4499686203047273850543701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999790802031515900362467 4499686203047273850543701)
                ·
                  refine ⟨52730697691960240436059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4499686203047273850543701 52730697691960240436059)
                  ·
                    rfl

theorem cell23_924234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_924234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924234 prefixEnd_924234 := by exact prefixLift 924234
  have htrace : WordTrace (prefixWord ++ tailWord_924234) baseStart_924234 baseEnd_924234 := by
    simpa [prefixWord, tailWord_924234, baseEnd_924234] using wordTrace_append hprefix tailTrace_924234
  have hstable : (prefixWord ++ tailWord_924234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924234).length < 2 ^ (prefixWord ++ tailWord_924234).sum := by decide
  have hdescent : baseEnd_924234 < baseStart_924234 := by decide
  rcases family_descends (prefixWord ++ tailWord_924234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924238 : List Nat := [4, 1, 1, 1, 1, 2, 4, 4, 1, 4]
def baseStart_924238 : Nat := 118140960795 + 924238 * 2 ^ 59
def prefixEnd_924238 : Nat := 4983230072969 + 3 ^ 40 * 924238 * 2
def baseEnd_924238 : Nat := 158192777716753382758171

theorem tailTrace_924238 : CollatzResearch.WordTrace tailWord_924238 prefixEnd_924238 158192777716753382758171 := by
  unfold tailWord_924238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4213716153206381016080671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22473152817100698752430245 4213716153206381016080671)
  ·
    refine ⟨6320574229809571524121007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4213716153206381016080671 6320574229809571524121007)
    ·
      refine ⟨9480861344714357286181511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6320574229809571524121007 9480861344714357286181511)
      ·
        refine ⟨14221292017071535929272267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9480861344714357286181511 14221292017071535929272267)
        ·
          refine ⟨21331938025607303893908401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14221292017071535929272267 21331938025607303893908401)
          ·
            refine ⟨15998953519205477920431301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21331938025607303893908401 15998953519205477920431301)
            ·
              refine ⟨2999803784851027110080869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15998953519205477920431301 2999803784851027110080869)
              ·
                refine ⟨562463209659567583140163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2999803784851027110080869 562463209659567583140163)
                ·
                  refine ⟨843694814489351374710245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562463209659567583140163 843694814489351374710245)
                  ·
                    refine ⟨158192777716753382758171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 843694814489351374710245 158192777716753382758171)
                    ·
                      rfl

theorem cell23_924238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_924238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924238 prefixEnd_924238 := by exact prefixLift 924238
  have htrace : WordTrace (prefixWord ++ tailWord_924238) baseStart_924238 baseEnd_924238 := by
    simpa [prefixWord, tailWord_924238, baseEnd_924238] using wordTrace_append hprefix tailTrace_924238
  have hstable : (prefixWord ++ tailWord_924238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924238).length < 2 ^ (prefixWord ++ tailWord_924238).sum := by decide
  have hdescent : baseEnd_924238 < baseStart_924238 := by decide
  rcases family_descends (prefixWord ++ tailWord_924238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924271 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 1, 5, 2]
def baseStart_924271 : Nat := 118140960795 + 924271 * 2 ^ 59
def prefixEnd_924271 : Nat := 4983230072969 + 3 ^ 40 * 924271 * 2
def baseEnd_924271 : Nat := 474595278011858519161861

theorem tailTrace_924271 : CollatzResearch.WordTrace tailWord_924271 prefixEnd_924271 474595278011858519161861 := by
  unfold tailWord_924271
  simp only [CollatzResearch.WordTrace]
  refine ⟨33710932834531494764596667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22473955223020996509731111 33710932834531494764596667)
  ·
    refine ⟨50566399251797242146895001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33710932834531494764596667 50566399251797242146895001)
    ·
      refine ⟨37924799438847931610171251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50566399251797242146895001 37924799438847931610171251)
      ·
        refine ⟨56887199158271897415256877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37924799438847931610171251 56887199158271897415256877)
        ·
          refine ⟨21332699684351961530721329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56887199158271897415256877 21332699684351961530721329)
          ·
            refine ⟨15999524763263971148040997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21332699684351961530721329 15999524763263971148040997)
            ·
              refine ⟨2999910893111994590257687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15999524763263971148040997 2999910893111994590257687)
              ·
                refine ⟨4499866339667991885386531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999910893111994590257687 4499866339667991885386531)
                ·
                  refine ⟨6749799509501987828079797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4499866339667991885386531 6749799509501987828079797)
                  ·
                    refine ⟨632793704015811358882481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6749799509501987828079797 632793704015811358882481)
                    ·
                      refine ⟨474595278011858519161861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632793704015811358882481 474595278011858519161861)
                      ·
                        rfl

theorem cell23_924271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 5, 2].length) (baseStart_924271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924271 prefixEnd_924271 := by exact prefixLift 924271
  have htrace : WordTrace (prefixWord ++ tailWord_924271) baseStart_924271 baseEnd_924271 := by
    simpa [prefixWord, tailWord_924271, baseEnd_924271] using wordTrace_append hprefix tailTrace_924271
  have hstable : (prefixWord ++ tailWord_924271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924271).length < 2 ^ (prefixWord ++ tailWord_924271).sum := by decide
  have hdescent : baseEnd_924271 < baseStart_924271 := by decide
  rcases family_descends (prefixWord ++ tailWord_924271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924272 : List Nat := [2, 1, 1, 1, 8, 1, 1, 3, 1, 4]
def baseStart_924272 : Nat := 118140960795 + 924272 * 2 ^ 59
def prefixEnd_924272 : Nat := 4983230072969 + 3 ^ 40 * 924272 * 2
def baseEnd_924272 : Nat := 158198597164171005083119

theorem tailTrace_924272 : CollatzResearch.WordTrace tailWord_924272 prefixEnd_924272 158198597164171005083119 := by
  unfold tailWord_924272
  simp only [CollatzResearch.WordTrace]
  refine ⟨16855484653763935967691535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22473979538351914623588713 16855484653763935967691535)
  ·
    refine ⟨25283226980645903951537303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16855484653763935967691535 25283226980645903951537303)
    ·
      refine ⟨37924840470968855927305955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25283226980645903951537303 37924840470968855927305955)
      ·
        refine ⟨56887260706453283890958933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37924840470968855927305955 56887260706453283890958933)
        ·
          refine ⟨666647586403749420597175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 56887260706453283890958933 666647586403749420597175)
          ·
            refine ⟨999971379605624130895763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666647586403749420597175 999971379605624130895763)
            ·
              refine ⟨1499957069408436196343645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999971379605624130895763 1499957069408436196343645)
              ·
                refine ⟨562483901028163573628867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1499957069408436196343645 562483901028163573628867)
                ·
                  refine ⟨843725851542245360443301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562483901028163573628867 843725851542245360443301)
                  ·
                    refine ⟨158198597164171005083119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 843725851542245360443301 158198597164171005083119)
                    ·
                      rfl

theorem cell23_924272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 1, 4].length) (baseStart_924272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924272 prefixEnd_924272 := by exact prefixLift 924272
  have htrace : WordTrace (prefixWord ++ tailWord_924272) baseStart_924272 baseEnd_924272 := by
    simpa [prefixWord, tailWord_924272, baseEnd_924272] using wordTrace_append hprefix tailTrace_924272
  have hstable : (prefixWord ++ tailWord_924272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924272).length < 2 ^ (prefixWord ++ tailWord_924272).sum := by decide
  have hdescent : baseEnd_924272 < baseStart_924272 := by decide
  rcases family_descends (prefixWord ++ tailWord_924272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924281 : List Nat := [1, 2, 1, 3, 3, 2, 2, 3, 1, 5]
def baseStart_924281 : Nat := 118140960795 + 924281 * 2 ^ 59
def prefixEnd_924281 : Nat := 4983230072969 + 3 ^ 40 * 924281 * 2
def baseEnd_924281 : Nat := 158200137606134493345605

theorem tailTrace_924281 : CollatzResearch.WordTrace tailWord_924281 prefixEnd_924281 158200137606134493345605 := by
  unfold tailWord_924281
  simp only [CollatzResearch.WordTrace]
  refine ⟨33711297564495266472460697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22474198376330177648307131 33711297564495266472460697)
  ·
    refine ⟨25283473173371449854345523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33711297564495266472460697 25283473173371449854345523)
    ·
      refine ⟨37925209760057174781518285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25283473173371449854345523 37925209760057174781518285)
      ·
        refine ⟨14221953660021440543069357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37925209760057174781518285 14221953660021440543069357)
        ·
          refine ⟨5333232622508040203651009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14221953660021440543069357 5333232622508040203651009)
          ·
            refine ⟨3999924466881030152738257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5333232622508040203651009 3999924466881030152738257)
            ·
              refine ⟨2999943350160772614553693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3999924466881030152738257 2999943350160772614553693)
              ·
                refine ⟨1124978756310289730457635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2999943350160772614553693 1124978756310289730457635)
                ·
                  refine ⟨1687468134465434595686453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124978756310289730457635 1687468134465434595686453)
                  ·
                    refine ⟨158200137606134493345605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1687468134465434595686453 158200137606134493345605)
                    ·
                      rfl

theorem cell23_924281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 5].length) (baseStart_924281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924281 prefixEnd_924281 := by exact prefixLift 924281
  have htrace : WordTrace (prefixWord ++ tailWord_924281) baseStart_924281 baseEnd_924281 := by
    simpa [prefixWord, tailWord_924281, baseEnd_924281] using wordTrace_append hprefix tailTrace_924281
  have hstable : (prefixWord ++ tailWord_924281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924281).length < 2 ^ (prefixWord ++ tailWord_924281).sum := by decide
  have hdescent : baseEnd_924281 < baseStart_924281 := by decide
  rcases family_descends (prefixWord ++ tailWord_924281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924288 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 2, 3, 2]
def baseStart_924288 : Nat := 118140960795 + 924288 * 2 ^ 59
def prefixEnd_924288 : Nat := 4983230072969 + 3 ^ 40 * 924288 * 2
def baseEnd_924288 : Nat := 474604007182984952649283

theorem tailTrace_924288 : CollatzResearch.WordTrace tailWord_924288 prefixEnd_924288 474604007182984952649283 := by
  unfold tailWord_924288
  simp only [CollatzResearch.WordTrace]
  refine ⟨16855776437734953333982759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22474368583646604445310345 16855776437734953333982759)
  ·
    refine ⟨25283664656602430000974139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16855776437734953333982759 25283664656602430000974139)
    ·
      refine ⟨37925496984903645001461209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25283664656602430000974139 37925496984903645001461209)
      ·
        refine ⟨28444122738677733751095907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37925496984903645001461209 28444122738677733751095907)
        ·
          refine ⟨42666184108016600626643861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28444122738677733751095907 42666184108016600626643861)
          ·
            refine ⟨1999977380063278154373931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42666184108016600626643861 1999977380063278154373931)
            ·
              refine ⟨2999966070094917231560897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999977380063278154373931 2999966070094917231560897)
              ·
                refine ⟨2249974552571187923670673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2999966070094917231560897 2249974552571187923670673)
                ·
                  refine ⟨1687480914428390942753005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2249974552571187923670673 1687480914428390942753005)
                  ·
                    refine ⟨632805342910646603532377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1687480914428390942753005 632805342910646603532377)
                    ·
                      refine ⟨474604007182984952649283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632805342910646603532377 474604007182984952649283)
                      ·
                        rfl

theorem cell23_924288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 2, 3, 2].length) (baseStart_924288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924288 prefixEnd_924288 := by exact prefixLift 924288
  have htrace : WordTrace (prefixWord ++ tailWord_924288) baseStart_924288 baseEnd_924288 := by
    simpa [prefixWord, tailWord_924288, baseEnd_924288] using wordTrace_append hprefix tailTrace_924288
  have hstable : (prefixWord ++ tailWord_924288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924288).length < 2 ^ (prefixWord ++ tailWord_924288).sum := by decide
  have hdescent : baseEnd_924288 < baseStart_924288 := by decide
  rcases family_descends (prefixWord ++ tailWord_924288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924304 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 3]
def baseStart_924304 : Nat := 118140960795 + 924304 * 2 ^ 59
def prefixEnd_924304 : Nat := 4983230072969 + 3 ^ 40 * 924304 * 2
def baseEnd_924304 : Nat := 474612222873456890049209

theorem tailTrace_924304 : CollatzResearch.WordTrace tailWord_924304 prefixEnd_924304 474612222873456890049209 := by
  unfold tailWord_924304
  simp only [CollatzResearch.WordTrace]
  refine ⟨16856068221705970700273983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22474757628941294267031977 16856068221705970700273983)
  ·
    refine ⟨25284102332558956050410975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16856068221705970700273983 25284102332558956050410975)
    ·
      refine ⟨37926153498838434075616463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25284102332558956050410975 37926153498838434075616463)
      ·
        refine ⟨56889230248257651113424695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37926153498838434075616463 56889230248257651113424695)
        ·
          refine ⟨85333845372386476670137043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56889230248257651113424695 85333845372386476670137043)
          ·
            refine ⟨128000768058579715005205565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85333845372386476670137043 128000768058579715005205565)
            ·
              refine ⟨48000288021967393126952087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128000768058579715005205565 48000288021967393126952087)
              ·
                refine ⟨72000432032951089690428131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48000288021967393126952087 72000432032951089690428131)
                ·
                  refine ⟨108000648049426634535642197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72000432032951089690428131 108000648049426634535642197)
                  ·
                    refine ⟨1265632594329218373464557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108000648049426634535642197 1265632594329218373464557)
                    ·
                      refine ⟨474612222873456890049209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1265632594329218373464557 474612222873456890049209)
                      ·
                        rfl

theorem cell23_924304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 3].length) (baseStart_924304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924304 prefixEnd_924304 := by exact prefixLift 924304
  have htrace : WordTrace (prefixWord ++ tailWord_924304) baseStart_924304 baseEnd_924304 := by
    simpa [prefixWord, tailWord_924304, baseEnd_924304] using wordTrace_append hprefix tailTrace_924304
  have hstable : (prefixWord ++ tailWord_924304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924304).length < 2 ^ (prefixWord ++ tailWord_924304).sum := by decide
  have hdescent : baseEnd_924304 < baseStart_924304 := by decide
  rcases family_descends (prefixWord ++ tailWord_924304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924318 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_924318 : Nat := 118140960795 + 924318 * 2 ^ 59
def prefixEnd_924318 : Nat := 4983230072969 + 3 ^ 40 * 924318 * 2
def baseEnd_924318 : Nat := 474619411602619835274145

theorem tailTrace_924318 : CollatzResearch.WordTrace tailWord_924318 prefixEnd_924318 474619411602619835274145 := by
  unfold tailWord_924318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4214080883170152723944701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22475098043574147861038405 4214080883170152723944701)
  ·
    refine ⟨1580280331188807271479263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4214080883170152723944701 1580280331188807271479263)
    ·
      refine ⟨2370420496783210907218895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1580280331188807271479263 2370420496783210907218895)
      ·
        refine ⟨3555630745174816360828343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2370420496783210907218895 3555630745174816360828343)
        ·
          refine ⟨5333446117762224541242515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3555630745174816360828343 5333446117762224541242515)
          ·
            refine ⟨8000169176643336811863773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5333446117762224541242515 8000169176643336811863773)
            ·
              refine ⟨3000063441241251304448915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8000169176643336811863773 3000063441241251304448915)
              ·
                refine ⟨4500095161861876956673373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3000063441241251304448915 4500095161861876956673373)
                ·
                  refine ⟨1687535685698203858752515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4500095161861876956673373 1687535685698203858752515)
                  ·
                    refine ⟨2531303528547305788128773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1687535685698203858752515 2531303528547305788128773)
                    ·
                      refine ⟨474619411602619835274145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2531303528547305788128773 474619411602619835274145)
                      ·
                        rfl

theorem cell23_924318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_924318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924318 prefixEnd_924318 := by exact prefixLift 924318
  have htrace : WordTrace (prefixWord ++ tailWord_924318) baseStart_924318 baseEnd_924318 := by
    simpa [prefixWord, tailWord_924318, baseEnd_924318] using wordTrace_append hprefix tailTrace_924318
  have hstable : (prefixWord ++ tailWord_924318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924318).length < 2 ^ (prefixWord ++ tailWord_924318).sum := by decide
  have hdescent : baseEnd_924318 < baseStart_924318 := by decide
  rcases family_descends (prefixWord ++ tailWord_924318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924324 : List Nat := [2, 3, 1, 2, 2, 1, 1, 11]
def baseStart_924324 : Nat := 118140960795 + 924324 * 2 ^ 59
def prefixEnd_924324 : Nat := 4983230072969 + 3 ^ 40 * 924324 * 2
def baseEnd_924324 : Nat := 17578610832835067103671

theorem tailTrace_924324 : CollatzResearch.WordTrace tailWord_924324 prefixEnd_924324 17578610832835067103671 := by
  unfold tailWord_924324
  simp only [CollatzResearch.WordTrace]
  refine ⟨16856432951669742408138013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22475243935559656544184017 16856432951669742408138013)
  ·
    refine ⟨6321162356876153403051755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16856432951669742408138013 6321162356876153403051755)
    ·
      refine ⟨9481743535314230104577633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6321162356876153403051755 9481743535314230104577633)
      ·
        refine ⟨7111307651485672578433225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9481743535314230104577633 7111307651485672578433225)
        ·
          refine ⟨5333480738614254433824919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7111307651485672578433225 5333480738614254433824919)
          ·
            refine ⟨8000221107921381650737379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5333480738614254433824919 8000221107921381650737379)
            ·
              refine ⟨12000331661882072476106069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8000221107921381650737379 12000331661882072476106069)
              ·
                refine ⟨17578610832835067103671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 12000331661882072476106069 17578610832835067103671)
                ·
                  rfl

theorem cell23_924324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 11].length) (baseStart_924324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924324 prefixEnd_924324 := by exact prefixLift 924324
  have htrace : WordTrace (prefixWord ++ tailWord_924324) baseStart_924324 baseEnd_924324 := by
    simpa [prefixWord, tailWord_924324, baseEnd_924324] using wordTrace_append hprefix tailTrace_924324
  have hstable : (prefixWord ++ tailWord_924324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924324).length < 2 ^ (prefixWord ++ tailWord_924324).sum := by decide
  have hdescent : baseEnd_924324 < baseStart_924324 := by decide
  rcases family_descends (prefixWord ++ tailWord_924324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924352 : List Nat := [2, 1, 1, 2, 4, 3, 1, 4, 1, 2, 2]
def baseStart_924352 : Nat := 118140960795 + 924352 * 2 ^ 59
def prefixEnd_924352 : Nat := 4983230072969 + 3 ^ 40 * 924352 * 2
def baseEnd_924352 : Nat := 474636869944872702248989

theorem tailTrace_924352 : CollatzResearch.WordTrace tailWord_924352 prefixEnd_924352 474636869944872702248989 := by
  unfold tailWord_924352
  simp only [CollatzResearch.WordTrace]
  refine ⟨16856943573619022799147655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22475924764825363732196873 16856943573619022799147655)
  ·
    refine ⟨25285415360428534198721483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16856943573619022799147655 25285415360428534198721483)
    ·
      refine ⟨37928123040642801298082225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25285415360428534198721483 37928123040642801298082225)
      ·
        refine ⟨28446092280482100973561669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37928123040642801298082225 28446092280482100973561669)
        ·
          refine ⟨5333642302590393932542813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28446092280482100973561669 5333642302590393932542813)
          ·
            refine ⟨2000115863471397724703555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5333642302590393932542813 2000115863471397724703555)
            ·
              refine ⟨3000173795207096587055333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000115863471397724703555 3000173795207096587055333)
              ·
                refine ⟨562532586601330610072875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3000173795207096587055333 562532586601330610072875)
                ·
                  refine ⟨843798879901995915109313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562532586601330610072875 843798879901995915109313)
                  ·
                    refine ⟨632849159926496936331985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 843798879901995915109313 632849159926496936331985)
                    ·
                      refine ⟨474636869944872702248989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632849159926496936331985 474636869944872702248989)
                      ·
                        rfl

theorem cell23_924352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 1, 2, 2].length) (baseStart_924352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924352 prefixEnd_924352 := by exact prefixLift 924352
  have htrace : WordTrace (prefixWord ++ tailWord_924352) baseStart_924352 baseEnd_924352 := by
    simpa [prefixWord, tailWord_924352, baseEnd_924352] using wordTrace_append hprefix tailTrace_924352
  have hstable : (prefixWord ++ tailWord_924352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924352).length < 2 ^ (prefixWord ++ tailWord_924352).sum := by decide
  have hdescent : baseEnd_924352 < baseStart_924352 := by decide
  rcases family_descends (prefixWord ++ tailWord_924352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924378 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2]
def baseStart_924378 : Nat := 118140960795 + 924378 * 2 ^ 59
def prefixEnd_924378 : Nat := 4983230072969 + 3 ^ 40 * 924378 * 2
def baseEnd_924378 : Nat := 474650220441889600523869

theorem tailTrace_924378 : CollatzResearch.WordTrace tailWord_924378 prefixEnd_924378 474650220441889600523869 := by
  unfold tailWord_924378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8428708861285963009685447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22476556963429234692494525 8428708861285963009685447)
  ·
    refine ⟨12643063291928944514528171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8428708861285963009685447 12643063291928944514528171)
    ·
      refine ⟨18964594937893416771792257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12643063291928944514528171 18964594937893416771792257)
      ·
        refine ⟨14223446203420062578844193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18964594937893416771792257 14223446203420062578844193)
        ·
          refine ⟨10667584652565046934133145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14223446203420062578844193 10667584652565046934133145)
          ·
            refine ⟨8000688489423785200599859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10667584652565046934133145 8000688489423785200599859)
            ·
              refine ⟨12001032734135677800899789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8000688489423785200599859 12001032734135677800899789)
              ·
                refine ⟨4500387275300879175337421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12001032734135677800899789 4500387275300879175337421)
                ·
                  refine ⟨1687645228237829690751533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4500387275300879175337421 1687645228237829690751533)
                  ·
                    refine ⟨632866960589186134031825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1687645228237829690751533 632866960589186134031825)
                    ·
                      refine ⟨474650220441889600523869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632866960589186134031825 474650220441889600523869)
                      ·
                        rfl

theorem cell23_924378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_924378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924378 prefixEnd_924378 := by exact prefixLift 924378
  have htrace : WordTrace (prefixWord ++ tailWord_924378) baseStart_924378 baseEnd_924378 := by
    simpa [prefixWord, tailWord_924378, baseEnd_924378] using wordTrace_append hprefix tailTrace_924378
  have hstable : (prefixWord ++ tailWord_924378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924378).length < 2 ^ (prefixWord ++ tailWord_924378).sum := by decide
  have hdescent : baseEnd_924378 < baseStart_924378 := by decide
  rcases family_descends (prefixWord ++ tailWord_924378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924384 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 3, 8]
def baseStart_924384 : Nat := 118140960795 + 924384 * 2 ^ 59
def prefixEnd_924384 : Nat := 4983230072969 + 3 ^ 40 * 924384 * 2
def baseEnd_924384 : Nat := 158217767108605525682947

theorem tailTrace_924384 : CollatzResearch.WordTrace tailWord_924384 prefixEnd_924384 158217767108605525682947 := by
  unfold tailWord_924384
  simp only [CollatzResearch.WordTrace]
  refine ⟨16857527141561057531730103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22476702855414743375640137 16857527141561057531730103)
  ·
    refine ⟨25286290712341586297595155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16857527141561057531730103 25286290712341586297595155)
    ·
      refine ⟨37929436068512379446392733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25286290712341586297595155 37929436068512379446392733)
      ·
        refine ⟨14223538525692142292397275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37929436068512379446392733 14223538525692142292397275)
        ·
          refine ⟨21335307788538213438595913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14223538525692142292397275 21335307788538213438595913)
          ·
            refine ⟨16001480841403660078946935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21335307788538213438595913 16001480841403660078946935)
            ·
              refine ⟨24002221262105490118420403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16001480841403660078946935 24002221262105490118420403)
              ·
                refine ⟨36003331893158235177630605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24002221262105490118420403 36003331893158235177630605)
                ·
                  refine ⟨13501249459934338191611477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36003331893158235177630605 13501249459934338191611477)
                  ·
                    refine ⟨158217767108605525682947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13501249459934338191611477 158217767108605525682947)
                    ·
                      rfl

theorem cell23_924384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_924384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924384 prefixEnd_924384 := by exact prefixLift 924384
  have htrace : WordTrace (prefixWord ++ tailWord_924384) baseStart_924384 baseEnd_924384 := by
    simpa [prefixWord, tailWord_924384, baseEnd_924384] using wordTrace_append hprefix tailTrace_924384
  have hstable : (prefixWord ++ tailWord_924384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924384).length < 2 ^ (prefixWord ++ tailWord_924384).sum := by decide
  have hdescent : baseEnd_924384 < baseStart_924384 := by decide
  rcases family_descends (prefixWord ++ tailWord_924384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924402 : List Nat := [3, 2, 1, 3, 1, 4, 1, 2, 2, 1, 3]
def baseStart_924402 : Nat := 118140960795 + 924402 * 2 ^ 59
def prefixEnd_924402 : Nat := 4983230072969 + 3 ^ 40 * 924402 * 2
def baseEnd_924402 : Nat := 474662543977597506623759

theorem tailTrace_924402 : CollatzResearch.WordTrace tailWord_924402 prefixEnd_924402 474662543977597506623759 := by
  unfold tailWord_924402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8428927699264226034403865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22477140531371269425076973 8428927699264226034403865)
  ·
    refine ⟨6321695774448169525802899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8428927699264226034403865 6321695774448169525802899)
    ·
      refine ⟨9482543661672254288704349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6321695774448169525802899 9482543661672254288704349)
      ·
        refine ⟨3555953873127095358264131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9482543661672254288704349 3555953873127095358264131)
        ·
          refine ⟨5333930809690643037396197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3555953873127095358264131 5333930809690643037396197)
          ·
            refine ⟨1000112026816995569511787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5333930809690643037396197 1000112026816995569511787)
            ·
              refine ⟨1500168040225493354267681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000112026816995569511787 1500168040225493354267681)
              ·
                refine ⟨1125126030169120015700761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1500168040225493354267681 1125126030169120015700761)
                ·
                  refine ⟨843844522626840011775571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1125126030169120015700761 843844522626840011775571)
                  ·
                    refine ⟨1265766783940260017663357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 843844522626840011775571 1265766783940260017663357)
                    ·
                      refine ⟨474662543977597506623759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1265766783940260017663357 474662543977597506623759)
                      ·
                        rfl

theorem cell23_924402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_924402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924402 prefixEnd_924402 := by exact prefixLift 924402
  have htrace : WordTrace (prefixWord ++ tailWord_924402) baseStart_924402 baseEnd_924402 := by
    simpa [prefixWord, tailWord_924402, baseEnd_924402] using wordTrace_append hprefix tailTrace_924402
  have hstable : (prefixWord ++ tailWord_924402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924402).length < 2 ^ (prefixWord ++ tailWord_924402).sum := by decide
  have hdescent : baseEnd_924402 < baseStart_924402 := by decide
  rcases family_descends (prefixWord ++ tailWord_924402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924418 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_924418 : Nat := 118140960795 + 924418 * 2 ^ 59
def prefixEnd_924418 : Nat := 4983230072969 + 3 ^ 40 * 924418 * 2
def baseEnd_924418 : Nat := 158223586556023148007895

theorem tailTrace_924418 : CollatzResearch.WordTrace tailWord_924418 prefixEnd_924418 158223586556023148007895 := by
  unfold tailWord_924418
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429073591249734717549477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22477529576665959246798605 8429073591249734717549477)
  ·
    refine ⟨1580451298359325259540527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8429073591249734717549477 1580451298359325259540527)
    ·
      refine ⟨2370676947538987889310791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1580451298359325259540527 2370676947538987889310791)
      ·
        refine ⟨3556015421308481833966187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2370676947538987889310791 3556015421308481833966187)
        ·
          refine ⟨5334023131962722750949281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3556015421308481833966187 5334023131962722750949281)
          ·
            refine ⟨4000517348972042063211961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5334023131962722750949281 4000517348972042063211961)
            ·
              refine ⟨3000388011729031547408971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4000517348972042063211961 3000388011729031547408971)
              ·
                refine ⟨4500582017593547321113457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3000388011729031547408971 4500582017593547321113457)
                ·
                  refine ⟨3375436513195160490835093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4500582017593547321113457 3375436513195160490835093)
                  ·
                    refine ⟨158223586556023148007895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3375436513195160490835093 158223586556023148007895)
                    ·
                      rfl

theorem cell23_924418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_924418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924418 prefixEnd_924418 := by exact prefixLift 924418
  have htrace : WordTrace (prefixWord ++ tailWord_924418) baseStart_924418 baseEnd_924418 := by
    simpa [prefixWord, tailWord_924418, baseEnd_924418] using wordTrace_append hprefix tailTrace_924418
  have hstable : (prefixWord ++ tailWord_924418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924418).length < 2 ^ (prefixWord ++ tailWord_924418).sum := by decide
  have hdescent : baseEnd_924418 < baseStart_924418 := by decide
  rcases family_descends (prefixWord ++ tailWord_924418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924425 : List Nat := [1, 2, 1, 1, 3, 2, 2, 5, 2, 2, 2]
def baseStart_924425 : Nat := 118140960795 + 924425 * 2 ^ 59
def prefixEnd_924425 : Nat := 4983230072969 + 3 ^ 40 * 924425 * 2
def baseEnd_924425 : Nat := 474674354032650916636153

theorem tailTrace_924425 : CollatzResearch.WordTrace tailWord_924425 prefixEnd_924425 474674354032650916636153 := by
  unfold tailWord_924425
  simp only [CollatzResearch.WordTrace]
  refine ⟨33716549675973579065702729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22477699783982386043801819 33716549675973579065702729)
  ·
    refine ⟨25287412256980184299277047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33716549675973579065702729 25287412256980184299277047)
    ·
      refine ⟨37931118385470276448915571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25287412256980184299277047 37931118385470276448915571)
      ·
        refine ⟨56896677578205414673373357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37931118385470276448915571 56896677578205414673373357)
        ·
          refine ⟨21336254091827030502515009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56896677578205414673373357 21336254091827030502515009)
          ·
            refine ⟨16002190568870272876886257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21336254091827030502515009 16002190568870272876886257)
            ·
              refine ⟨12001642926652704657664693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16002190568870272876886257 12001642926652704657664693)
              ·
                refine ⟨1125154024373691061656065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12001642926652704657664693 1125154024373691061656065)
                ·
                  refine ⟨843865518280268296242049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1125154024373691061656065 843865518280268296242049)
                  ·
                    refine ⟨632899138710201222181537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 843865518280268296242049 632899138710201222181537)
                    ·
                      refine ⟨474674354032650916636153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 632899138710201222181537 474674354032650916636153)
                      ·
                        rfl

theorem cell23_924425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 2, 2].length) (baseStart_924425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924425 prefixEnd_924425 := by exact prefixLift 924425
  have htrace : WordTrace (prefixWord ++ tailWord_924425) baseStart_924425 baseEnd_924425 := by
    simpa [prefixWord, tailWord_924425, baseEnd_924425] using wordTrace_append hprefix tailTrace_924425
  have hstable : (prefixWord ++ tailWord_924425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924425).length < 2 ^ (prefixWord ++ tailWord_924425).sum := by decide
  have hdescent : baseEnd_924425 < baseStart_924425 := by decide
  rcases family_descends (prefixWord ++ tailWord_924425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924441 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 4, 3, 3]
def baseStart_924441 : Nat := 118140960795 + 924441 * 2 ^ 59
def prefixEnd_924441 : Nat := 4983230072969 + 3 ^ 40 * 924441 * 2
def baseEnd_924441 : Nat := 474682569723122854036079

theorem tailTrace_924441 : CollatzResearch.WordTrace tailWord_924441 prefixEnd_924441 474682569723122854036079 := by
  unfold tailWord_924441
  simp only [CollatzResearch.WordTrace]
  refine ⟨33717133243915613798285177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22478088829277075865523451 33717133243915613798285177)
  ·
    refine ⟨25287849932936710348713883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33717133243915613798285177 25287849932936710348713883)
    ·
      refine ⟨37931774899405065523070825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25287849932936710348713883 37931774899405065523070825)
      ·
        refine ⟨28448831174553799142303119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37931774899405065523070825 28448831174553799142303119)
        ·
          refine ⟨42673246761830698713454679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28448831174553799142303119 42673246761830698713454679)
          ·
            refine ⟨64009870142746048070182019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42673246761830698713454679 64009870142746048070182019)
            ·
              refine ⟨96014805214119072105273029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64009870142746048070182019 96014805214119072105273029)
              ·
                refine ⟨18002775977647326019738693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96014805214119072105273029 18002775977647326019738693)
                ·
                  refine ⟨3375520495808873628701005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18002775977647326019738693 3375520495808873628701005)
                  ·
                    refine ⟨1265820185928327610762877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3375520495808873628701005 1265820185928327610762877)
                    ·
                      refine ⟨474682569723122854036079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1265820185928327610762877 474682569723122854036079)
                      ·
                        rfl

theorem cell23_924441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_924441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924441 prefixEnd_924441 := by exact prefixLift 924441
  have htrace : WordTrace (prefixWord ++ tailWord_924441) baseStart_924441 baseEnd_924441 := by
    simpa [prefixWord, tailWord_924441, baseEnd_924441] using wordTrace_append hprefix tailTrace_924441
  have hstable : (prefixWord ++ tailWord_924441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924441).length < 2 ^ (prefixWord ++ tailWord_924441).sum := by decide
  have hdescent : baseEnd_924441 < baseStart_924441 := by decide
  rcases family_descends (prefixWord ++ tailWord_924441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924445 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_924445 : Nat := 118140960795 + 924445 * 2 ^ 59
def prefixEnd_924445 : Nat := 4983230072969 + 3 ^ 40 * 924445 * 2
def baseEnd_924445 : Nat := 474684623645740838386061

theorem tailTrace_924445 : CollatzResearch.WordTrace tailWord_924445 prefixEnd_924445 474684623645740838386061 := by
  unfold tailWord_924445
  simp only [CollatzResearch.WordTrace]
  refine ⟨33717279135901122481430789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22478186090600748320953859 33717279135901122481430789)
  ·
    refine ⟨6321989837981460465268273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33717279135901122481430789 6321989837981460465268273)
    ·
      refine ⟨4741492378486095348951205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6321989837981460465268273 4741492378486095348951205)
      ·
        refine ⟨889029820966142877928351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4741492378486095348951205 889029820966142877928351)
        ·
          refine ⟨1333544731449214316892527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889029820966142877928351 1333544731449214316892527)
          ·
            refine ⟨2000317097173821475338791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333544731449214316892527 2000317097173821475338791)
            ·
              refine ⟨3000475645760732213008187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000317097173821475338791 3000475645760732213008187)
              ·
                refine ⟨4500713468641098319512281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3000475645760732213008187 4500713468641098319512281)
                ·
                  refine ⟨3375535101480823739634211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4500713468641098319512281 3375535101480823739634211)
                  ·
                    refine ⟨5063302652221235609451317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3375535101480823739634211 5063302652221235609451317)
                    ·
                      refine ⟨474684623645740838386061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5063302652221235609451317 474684623645740838386061)
                      ·
                        rfl

theorem cell23_924445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_924445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924445 prefixEnd_924445 := by exact prefixLift 924445
  have htrace : WordTrace (prefixWord ++ tailWord_924445) baseStart_924445 baseEnd_924445 := by
    simpa [prefixWord, tailWord_924445, baseEnd_924445] using wordTrace_append hprefix tailTrace_924445
  have hstable : (prefixWord ++ tailWord_924445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924445).length < 2 ^ (prefixWord ++ tailWord_924445).sum := by decide
  have hdescent : baseEnd_924445 < baseStart_924445 := by decide
  rcases family_descends (prefixWord ++ tailWord_924445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924465 : List Nat := [1, 2, 2, 3, 2, 1, 5, 2, 5]
def baseStart_924465 : Nat := 118140960795 + 924465 * 2 ^ 59
def prefixEnd_924465 : Nat := 4983230072969 + 3 ^ 40 * 924465 * 2
def baseEnd_924465 : Nat := 52743877028758973348441

theorem tailTrace_924465 : CollatzResearch.WordTrace tailWord_924465 prefixEnd_924465 52743877028758973348441 := by
  unfold tailWord_924465
  simp only [CollatzResearch.WordTrace]
  refine ⟨33718008595828665897158849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22478672397219110598105899 33718008595828665897158849)
  ·
    refine ⟨25288506446871499422869137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33718008595828665897158849 25288506446871499422869137)
    ·
      refine ⟨18966379835153624567151853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25288506446871499422869137 18966379835153624567151853)
      ·
        refine ⟨7112392438182609212681945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18966379835153624567151853 7112392438182609212681945)
        ·
          refine ⟨5334294328636956909511459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7112392438182609212681945 5334294328636956909511459)
          ·
            refine ⟨8001441492955435364267189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5334294328636956909511459 8001441492955435364267189)
            ·
              refine ⟨750135139964572065400049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8001441492955435364267189 750135139964572065400049)
              ·
                refine ⟨562601354973429049050037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750135139964572065400049 562601354973429049050037)
                ·
                  refine ⟨52743877028758973348441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 562601354973429049050037 52743877028758973348441)
                  ·
                    rfl

theorem cell23_924465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 5].length) (baseStart_924465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924465 prefixEnd_924465 := by exact prefixLift 924465
  have htrace : WordTrace (prefixWord ++ tailWord_924465) baseStart_924465 baseEnd_924465 := by
    simpa [prefixWord, tailWord_924465, baseEnd_924465] using wordTrace_append hprefix tailTrace_924465
  have hstable : (prefixWord ++ tailWord_924465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924465).length < 2 ^ (prefixWord ++ tailWord_924465).sum := by decide
  have hdescent : baseEnd_924465 < baseStart_924465 := by decide
  rcases family_descends (prefixWord ++ tailWord_924465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924471 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_924471 : Nat := 118140960795 + 924471 * 2 ^ 59
def prefixEnd_924471 : Nat := 4983230072969 + 3 ^ 40 * 924471 * 2
def baseEnd_924471 : Nat := 474697974142757736660941

theorem tailTrace_924471 : CollatzResearch.WordTrace tailWord_924471 prefixEnd_924471 474697974142757736660941 := by
  unfold tailWord_924471
  simp only [CollatzResearch.WordTrace]
  refine ⟨33718227433806928921877267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22478818289204619281251511 33718227433806928921877267)
  ·
    refine ⟨50577341150710393382815901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33718227433806928921877267 50577341150710393382815901)
    ·
      refine ⟨18966502931516397518555963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50577341150710393382815901 18966502931516397518555963)
      ·
        refine ⟨28449754397274596277833945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18966502931516397518555963 28449754397274596277833945)
        ·
          refine ⟨21337315797955947208375459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28449754397274596277833945 21337315797955947208375459)
          ·
            refine ⟨32005973696933920812563189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21337315797955947208375459 32005973696933920812563189)
            ·
              refine ⟨3000560034087555076177799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32005973696933920812563189 3000560034087555076177799)
              ·
                refine ⟨4500840051131332614266699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3000560034087555076177799 4500840051131332614266699)
                ·
                  refine ⟨6751260076696998921400049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500840051131332614266699 6751260076696998921400049)
                  ·
                    refine ⟨5063445057522749191050037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6751260076696998921400049 5063445057522749191050037)
                    ·
                      refine ⟨474697974142757736660941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5063445057522749191050037 474697974142757736660941)
                      ·
                        rfl

theorem cell23_924471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_924471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924471 prefixEnd_924471 := by exact prefixLift 924471
  have htrace : WordTrace (prefixWord ++ tailWord_924471) baseStart_924471 baseEnd_924471 := by
    simpa [prefixWord, tailWord_924471, baseEnd_924471] using wordTrace_append hprefix tailTrace_924471
  have hstable : (prefixWord ++ tailWord_924471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924471).length < 2 ^ (prefixWord ++ tailWord_924471).sum := by decide
  have hdescent : baseEnd_924471 < baseStart_924471 := by decide
  rcases family_descends (prefixWord ++ tailWord_924471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924511 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 6]
def baseStart_924511 : Nat := 118140960795 + 924511 * 2 ^ 59
def prefixEnd_924511 : Nat := 4983230072969 + 3 ^ 40 * 924511 * 2
def baseEnd_924511 : Nat := 474718513368937580160757

theorem tailTrace_924511 : CollatzResearch.WordTrace tailWord_924511 prefixEnd_924511 474718513368937580160757 := by
  unfold tailWord_924511
  simp only [CollatzResearch.WordTrace]
  refine ⟨33719686353662015753333387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22479790902441343835555591 33719686353662015753333387)
  ·
    refine ⟨50579529530493023630000081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33719686353662015753333387 50579529530493023630000081)
    ·
      refine ⟨37934647147869767722500061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50579529530493023630000081 37934647147869767722500061)
      ·
        refine ⟨14225492680451162895937523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37934647147869767722500061 14225492680451162895937523)
        ·
          refine ⟨21338239020676744343906285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14225492680451162895937523 21338239020676744343906285)
          ·
            refine ⟨8001839632753779128964857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21338239020676744343906285 8001839632753779128964857)
            ·
              refine ⟨6001379724565334346723643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8001839632753779128964857 6001379724565334346723643)
              ·
                refine ⟨9002069586848001520085465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6001379724565334346723643 9002069586848001520085465)
                ·
                  refine ⟨6751552190136001140064099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9002069586848001520085465 6751552190136001140064099)
                  ·
                    refine ⟨10127328285204001710096149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6751552190136001140064099 10127328285204001710096149)
                    ·
                      refine ⟨474718513368937580160757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10127328285204001710096149 474718513368937580160757)
                      ·
                        rfl

theorem cell23_924511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_924511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924511 prefixEnd_924511 := by exact prefixLift 924511
  have htrace : WordTrace (prefixWord ++ tailWord_924511) baseStart_924511 baseEnd_924511 := by
    simpa [prefixWord, tailWord_924511, baseEnd_924511] using wordTrace_append hprefix tailTrace_924511
  have hstable : (prefixWord ++ tailWord_924511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924511).length < 2 ^ (prefixWord ++ tailWord_924511).sum := by decide
  have hdescent : baseEnd_924511 < baseStart_924511 := by decide
  rcases family_descends (prefixWord ++ tailWord_924511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924546 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_924546 : Nat := 118140960795 + 924546 * 2 ^ 59
def prefixEnd_924546 : Nat := 4983230072969 + 3 ^ 40 * 924546 * 2
def baseEnd_924546 : Nat := 158245495063948314407699

theorem tailTrace_924546 : CollatzResearch.WordTrace tailWord_924546 prefixEnd_924546 158245495063948314407699 := by
  unfold tailWord_924546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8430240727133804182714373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22480641939023477820571661 8430240727133804182714373)
  ·
    refine ⟨1580670136337588284258945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8430240727133804182714373 1580670136337588284258945)
    ·
      refine ⟨1185502602253191213194209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1580670136337588284258945 1185502602253191213194209)
      ·
        refine ⟨889126951689893409895657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1185502602253191213194209 889126951689893409895657)
        ·
          refine ⟨666845213767420057421743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 889126951689893409895657 666845213767420057421743)
          ·
            refine ⟨1000267820651130086132615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666845213767420057421743 1000267820651130086132615)
            ·
              refine ⟨1500401730976695129198923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000267820651130086132615 1500401730976695129198923)
              ·
                refine ⟨2250602596465042693798385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500401730976695129198923 2250602596465042693798385)
                ·
                  refine ⟨1687951947348782020348789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2250602596465042693798385 1687951947348782020348789)
                  ·
                    refine ⟨158245495063948314407699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1687951947348782020348789 158245495063948314407699)
                    ·
                      rfl

theorem cell23_924546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_924546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924546 prefixEnd_924546 := by exact prefixLift 924546
  have htrace : WordTrace (prefixWord ++ tailWord_924546) baseStart_924546 baseEnd_924546 := by
    simpa [prefixWord, tailWord_924546, baseEnd_924546] using wordTrace_append hprefix tailTrace_924546
  have hstable : (prefixWord ++ tailWord_924546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924546).length < 2 ^ (prefixWord ++ tailWord_924546).sum := by decide
  have hdescent : baseEnd_924546 < baseStart_924546 := by decide
  rcases family_descends (prefixWord ++ tailWord_924546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924552 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 2, 2, 3]
def baseStart_924552 : Nat := 118140960795 + 924552 * 2 ^ 59
def prefixEnd_924552 : Nat := 4983230072969 + 3 ^ 40 * 924552 * 2
def baseEnd_924552 : Nat := 474739566075771919748069

theorem tailTrace_924552 : CollatzResearch.WordTrace tailWord_924552 prefixEnd_924552 474739566075771919748069 := by
  unfold tailWord_924552
  simp only [CollatzResearch.WordTrace]
  refine ⟨16860590873256739877787955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22480787831008986503717273 16860590873256739877787955)
  ·
    refine ⟨25290886309885109816681933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16860590873256739877787955 25290886309885109816681933)
    ·
      refine ⟨9484082366206916181255725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25290886309885109816681933 9484082366206916181255725)
      ·
        refine ⟨3556530887327593567970897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9484082366206916181255725 3556530887327593567970897)
        ·
          refine ⟨2667398165495695175978173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3556530887327593567970897 2667398165495695175978173)
          ·
            refine ⟨1000274312060885690991815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2667398165495695175978173 1000274312060885690991815)
            ·
              refine ⟨1500411468091328536487723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000274312060885690991815 1500411468091328536487723)
              ·
                refine ⟨2250617202136992804731585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500411468091328536487723 2250617202136992804731585)
                ·
                  refine ⟨1687962901602744603548689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2250617202136992804731585 1687962901602744603548689)
                  ·
                    refine ⟨1265972176202058452661517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1687962901602744603548689 1265972176202058452661517)
                    ·
                      refine ⟨474739566075771919748069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1265972176202058452661517 474739566075771919748069)
                      ·
                        rfl

theorem cell23_924552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_924552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924552 prefixEnd_924552 := by exact prefixLift 924552
  have htrace : WordTrace (prefixWord ++ tailWord_924552) baseStart_924552 baseEnd_924552 := by
    simpa [prefixWord, tailWord_924552, baseEnd_924552] using wordTrace_append hprefix tailTrace_924552
  have hstable : (prefixWord ++ tailWord_924552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924552).length < 2 ^ (prefixWord ++ tailWord_924552).sum := by decide
  have hdescent : baseEnd_924552 < baseStart_924552 := by decide
  rcases family_descends (prefixWord ++ tailWord_924552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924561 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_924561 : Nat := 118140960795 + 924561 * 2 ^ 59
def prefixEnd_924561 : Nat := 4983230072969 + 3 ^ 40 * 924561 * 2
def baseEnd_924561 : Nat := 474744187401662384535527

theorem tailTrace_924561 : CollatzResearch.WordTrace tailWord_924561 prefixEnd_924561 474744187401662384535527 := by
  unfold tailWord_924561
  simp only [CollatzResearch.WordTrace]
  refine ⟨33721510003480874292653537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22481006668987249528435691 33721510003480874292653537)
  ·
    refine ⟨25291132502610655719490153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33721510003480874292653537 25291132502610655719490153)
    ·
      refine ⟨18968349376957991789617615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25291132502610655719490153 18968349376957991789617615)
      ·
        refine ⟨28452524065436987684426423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18968349376957991789617615 28452524065436987684426423)
        ·
          refine ⟨42678786098155481526639635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28452524065436987684426423 42678786098155481526639635)
          ·
            refine ⟨64018179147233222289959453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42678786098155481526639635 64018179147233222289959453)
            ·
              refine ⟨24006817180212458358734795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64018179147233222289959453 24006817180212458358734795)
              ·
                refine ⟨36010225770318687538102193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24006817180212458358734795 36010225770318687538102193)
                ·
                  refine ⟨27007669327739015653576645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36010225770318687538102193 27007669327739015653576645)
                  ·
                    refine ⟨5063937998951065435045621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27007669327739015653576645 5063937998951065435045621)
                    ·
                      refine ⟨474744187401662384535527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5063937998951065435045621 474744187401662384535527)
                      ·
                        rfl

theorem cell23_924561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_924561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924561 prefixEnd_924561 := by exact prefixLift 924561
  have htrace : WordTrace (prefixWord ++ tailWord_924561) baseStart_924561 baseEnd_924561 := by
    simpa [prefixWord, tailWord_924561, baseEnd_924561] using wordTrace_append hprefix tailTrace_924561
  have hstable : (prefixWord ++ tailWord_924561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924561).length < 2 ^ (prefixWord ++ tailWord_924561).sum := by decide
  have hdescent : baseEnd_924561 < baseStart_924561 := by decide
  rcases family_descends (prefixWord ++ tailWord_924561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924572 : List Nat := [2, 2, 3, 3, 2, 2, 1, 2, 6]
def baseStart_924572 : Nat := 118140960795 + 924572 * 2 ^ 59
def prefixEnd_924572 : Nat := 4983230072969 + 3 ^ 40 * 924572 * 2
def baseEnd_924572 : Nat := 52749981743206871277553

theorem tailTrace_924572 : CollatzResearch.WordTrace tailWord_924572 prefixEnd_924572 52749981743206871277553 := by
  unfold tailWord_924572
  simp only [CollatzResearch.WordTrace]
  refine ⟨16860955603220511585651985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22481274137627348780869313 16860955603220511585651985)
  ·
    refine ⟨12645716702415383689238989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16860955603220511585651985 12645716702415383689238989)
    ·
      refine ⟨4742143763405768883464621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12645716702415383689238989 4742143763405768883464621)
      ·
        refine ⟨1778303911277163331299233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4742143763405768883464621 1778303911277163331299233)
        ·
          refine ⟨1333727933457872498474425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1778303911277163331299233 1333727933457872498474425)
          ·
            refine ⟨1000295950093404373855819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1333727933457872498474425 1000295950093404373855819)
            ·
              refine ⟨1500443925140106560783729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000295950093404373855819 1500443925140106560783729)
              ·
                refine ⟨1125332943855079920587797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1500443925140106560783729 1125332943855079920587797)
                ·
                  refine ⟨52749981743206871277553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1125332943855079920587797 52749981743206871277553)
                  ·
                    rfl

theorem cell23_924572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 6].length) (baseStart_924572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924572 prefixEnd_924572 := by exact prefixLift 924572
  have htrace : WordTrace (prefixWord ++ tailWord_924572) baseStart_924572 baseEnd_924572 := by
    simpa [prefixWord, tailWord_924572, baseEnd_924572] using wordTrace_append hprefix tailTrace_924572
  have hstable : (prefixWord ++ tailWord_924572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924572).length < 2 ^ (prefixWord ++ tailWord_924572).sum := by decide
  have hdescent : baseEnd_924572 < baseStart_924572 := by decide
  rcases family_descends (prefixWord ++ tailWord_924572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924581 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 2, 10]
def baseStart_924581 : Nat := 118140960795 + 924581 * 2 ^ 59
def prefixEnd_924581 : Nat := 4983230072969 + 3 ^ 40 * 924581 * 2
def baseEnd_924581 : Nat := 158251485671584102095145

theorem tailTrace_924581 : CollatzResearch.WordTrace tailWord_924581 prefixEnd_924581 158251485671584102095145 := by
  unfold tailWord_924581
  simp only [CollatzResearch.WordTrace]
  refine ⟨33722239463408417708381597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22481492975605611805587731 33722239463408417708381597)
  ·
    refine ⟨12645839798778156640643099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33722239463408417708381597 12645839798778156640643099)
    ·
      refine ⟨18968759698167234960964649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12645839798778156640643099 18968759698167234960964649)
      ·
        refine ⟨14226569773625426220723487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18968759698167234960964649 14226569773625426220723487)
        ·
          refine ⟨21339854660438139331085231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14226569773625426220723487 21339854660438139331085231)
          ·
            refine ⟨32009781990657208996627847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21339854660438139331085231 32009781990657208996627847)
            ·
              refine ⟨48014672985985813494941771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32009781990657208996627847 48014672985985813494941771)
              ·
                refine ⟨72022009478978720242412657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48014672985985813494941771 72022009478978720242412657)
                ·
                  refine ⟨54016507109234040181809493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72022009478978720242412657 54016507109234040181809493)
                  ·
                    refine ⟨158251485671584102095145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 54016507109234040181809493 158251485671584102095145)
                    ·
                      rfl

theorem cell23_924581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_924581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924581 prefixEnd_924581 := by exact prefixLift 924581
  have htrace : WordTrace (prefixWord ++ tailWord_924581) baseStart_924581 baseEnd_924581 := by
    simpa [prefixWord, tailWord_924581, baseEnd_924581] using wordTrace_append hprefix tailTrace_924581
  have hstable : (prefixWord ++ tailWord_924581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924581).length < 2 ^ (prefixWord ++ tailWord_924581).sum := by decide
  have hdescent : baseEnd_924581 < baseStart_924581 := by decide
  rcases family_descends (prefixWord ++ tailWord_924581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924589 : List Nat := [1, 5, 2, 3, 1, 1, 3, 1, 6]
def baseStart_924589 : Nat := 118140960795 + 924589 * 2 ^ 59
def prefixEnd_924589 : Nat := 4983230072969 + 3 ^ 40 * 924589 * 2
def baseEnd_924589 : Nat := 52750951651109808331711

theorem tailTrace_924589 : CollatzResearch.WordTrace tailWord_924589 prefixEnd_924589 52750951651109808331711 := by
  unfold tailWord_924589
  simp only [CollatzResearch.WordTrace]
  refine ⟨33722531247379435074672821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22481687498252956716448547 33722531247379435074672821)
  ·
    refine ⟨3161487304441822038250577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33722531247379435074672821 3161487304441822038250577)
    ·
      refine ⟨2371115478331366528687933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3161487304441822038250577 2371115478331366528687933)
      ·
        refine ⟨889168304374262448257975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2371115478331366528687933 889168304374262448257975)
        ·
          refine ⟨1333752456561393672386963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889168304374262448257975 1333752456561393672386963)
          ·
            refine ⟨2000628684842090508580445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333752456561393672386963 2000628684842090508580445)
            ·
              refine ⟨750235756815783940717667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2000628684842090508580445 750235756815783940717667)
              ·
                refine ⟨1125353635223675911076501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750235756815783940717667 1125353635223675911076501)
                ·
                  refine ⟨52750951651109808331711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1125353635223675911076501 52750951651109808331711)
                  ·
                    rfl

theorem cell23_924589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_924589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924589 prefixEnd_924589 := by exact prefixLift 924589
  have htrace : WordTrace (prefixWord ++ tailWord_924589) baseStart_924589 baseEnd_924589 := by
    simpa [prefixWord, tailWord_924589, baseEnd_924589] using wordTrace_append hprefix tailTrace_924589
  have hstable : (prefixWord ++ tailWord_924589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924589).length < 2 ^ (prefixWord ++ tailWord_924589).sum := by decide
  have hdescent : baseEnd_924589 < baseStart_924589 := by decide
  rcases family_descends (prefixWord ++ tailWord_924589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924611 : List Nat := [1, 1, 1, 3, 1, 1, 2, 13]
def baseStart_924611 : Nat := 118140960795 + 924611 * 2 ^ 59
def prefixEnd_924611 : Nat := 4983230072969 + 3 ^ 40 * 924611 * 2
def baseEnd_924611 : Nat := 17584068942014340330011

theorem tailTrace_924611 : CollatzResearch.WordTrace tailWord_924611 prefixEnd_924611 17584068942014340330011 := by
  unfold tailWord_924611
  simp only [CollatzResearch.WordTrace]
  refine ⟨33723333653299732831973687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22482222435533155221315791 33723333653299732831973687)
  ·
    refine ⟨50585000479949599247960531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33723333653299732831973687 50585000479949599247960531)
    ·
      refine ⟨75877500719924398871940797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50585000479949599247960531 75877500719924398871940797)
      ·
        refine ⟨28454062769971649576977799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75877500719924398871940797 28454062769971649576977799)
        ·
          refine ⟨42681094154957474365466699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28454062769971649576977799 42681094154957474365466699)
          ·
            refine ⟨64021641232436211548200049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42681094154957474365466699 64021641232436211548200049)
            ·
              refine ⟨48016230924327158661150037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64021641232436211548200049 48016230924327158661150037)
              ·
                refine ⟨17584068942014340330011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 48016230924327158661150037 17584068942014340330011)
                ·
                  rfl

theorem cell23_924611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 13].length) (baseStart_924611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924611 prefixEnd_924611 := by exact prefixLift 924611
  have htrace : WordTrace (prefixWord ++ tailWord_924611) baseStart_924611 baseEnd_924611 := by
    simpa [prefixWord, tailWord_924611, baseEnd_924611] using wordTrace_append hprefix tailTrace_924611
  have hstable : (prefixWord ++ tailWord_924611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924611).length < 2 ^ (prefixWord ++ tailWord_924611).sum := by decide
  have hdescent : baseEnd_924611 < baseStart_924611 := by decide
  rcases family_descends (prefixWord ++ tailWord_924611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924616 : List Nat := [2, 1, 3, 1, 5, 2, 1, 3, 1, 1, 3]
def baseStart_924616 : Nat := 118140960795 + 924616 * 2 ^ 59
def prefixEnd_924616 : Nat := 4983230072969 + 3 ^ 40 * 924616 * 2
def baseEnd_924616 : Nat := 474772428837659669347775

theorem tailTrace_924616 : CollatzResearch.WordTrace tailWord_924616 prefixEnd_924616 474772428837659669347775 := by
  unfold tailWord_924616
  simp only [CollatzResearch.WordTrace]
  refine ⟨16861758009140809342952851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22482344012187745790603801 16861758009140809342952851)
  ·
    refine ⟨25292637013711214014429277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16861758009140809342952851 25292637013711214014429277)
    ·
      refine ⟨9484738880141705255410979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25292637013711214014429277 9484738880141705255410979)
      ·
        refine ⟨14227108320212557883116469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9484738880141705255410979 14227108320212557883116469)
        ·
          refine ⟨1333791405019927301542169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14227108320212557883116469 1333791405019927301542169)
          ·
            refine ⟨1000343553764945476156627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1333791405019927301542169 1000343553764945476156627)
            ·
              refine ⟨1500515330647418214234941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000343553764945476156627 1500515330647418214234941)
              ·
                refine ⟨562693248992781830338103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1500515330647418214234941 562693248992781830338103)
                ·
                  refine ⟨844039873489172745507155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562693248992781830338103 844039873489172745507155)
                  ·
                    refine ⟨1266059810233759118260733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 844039873489172745507155 1266059810233759118260733)
                    ·
                      refine ⟨474772428837659669347775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1266059810233759118260733 474772428837659669347775)
                      ·
                        rfl

theorem cell23_924616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 1, 1, 3].length) (baseStart_924616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924616 prefixEnd_924616 := by exact prefixLift 924616
  have htrace : WordTrace (prefixWord ++ tailWord_924616) baseStart_924616 baseEnd_924616 := by
    simpa [prefixWord, tailWord_924616, baseEnd_924616] using wordTrace_append hprefix tailTrace_924616
  have hstable : (prefixWord ++ tailWord_924616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924616).length < 2 ^ (prefixWord ++ tailWord_924616).sum := by decide
  have hdescent : baseEnd_924616 < baseStart_924616 := by decide
  rcases family_descends (prefixWord ++ tailWord_924616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924618 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_924618 : Nat := 118140960795 + 924618 * 2 ^ 59
def prefixEnd_924618 : Nat := 4983230072969 + 3 ^ 40 * 924618 * 2
def baseEnd_924618 : Nat := 474773455798968661522765

theorem tailTrace_924618 : CollatzResearch.WordTrace tailWord_924618 prefixEnd_924618 474773455798968661522765 := by
  unfold tailWord_924618
  simp only [CollatzResearch.WordTrace]
  refine ⟨8430897241068593256869627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22482392642849582018319005 8430897241068593256869627)
  ·
    refine ⟨12646345861602889885304441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8430897241068593256869627 12646345861602889885304441)
    ·
      refine ⟨9484759396202167413978331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12646345861602889885304441 9484759396202167413978331)
      ·
        refine ⟨14227139094303251120967497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9484759396202167413978331 14227139094303251120967497)
        ·
          refine ⟨10670354320727438340725623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14227139094303251120967497 10670354320727438340725623)
          ·
            refine ⟨16005531481091157511088435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10670354320727438340725623 16005531481091157511088435)
            ·
              refine ⟨24008297221636736266632653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16005531481091157511088435 24008297221636736266632653)
              ·
                refine ⟨9003111458113776099987245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24008297221636736266632653 9003111458113776099987245)
                ·
                  refine ⟨3376166796792666037495217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9003111458113776099987245 3376166796792666037495217)
                  ·
                    refine ⟨2532125097594499528121413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3376166796792666037495217 2532125097594499528121413)
                    ·
                      refine ⟨474773455798968661522765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2532125097594499528121413 474773455798968661522765)
                      ·
                        rfl

theorem cell23_924618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_924618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924618 prefixEnd_924618 := by exact prefixLift 924618
  have htrace : WordTrace (prefixWord ++ tailWord_924618) baseStart_924618 baseEnd_924618 := by
    simpa [prefixWord, tailWord_924618, baseEnd_924618] using wordTrace_append hprefix tailTrace_924618
  have hstable : (prefixWord ++ tailWord_924618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924618).length < 2 ^ (prefixWord ++ tailWord_924618).sum := by decide
  have hdescent : baseEnd_924618 < baseStart_924618 := by decide
  rcases family_descends (prefixWord ++ tailWord_924618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924625 : List Nat := [1, 2, 2, 1, 2, 1, 3, 5, 1, 2, 3]
def baseStart_924625 : Nat := 118140960795 + 924625 * 2 ^ 59
def prefixEnd_924625 : Nat := 4983230072969 + 3 ^ 40 * 924625 * 2
def baseEnd_924625 : Nat := 474777050163550134135233

theorem tailTrace_924625 : CollatzResearch.WordTrace tailWord_924625 prefixEnd_924625 474777050163550134135233 := by
  unfold tailWord_924625
  simp only [CollatzResearch.WordTrace]
  refine ⟨33723844275249013222983329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22482562850166008815322219 33723844275249013222983329)
  ·
    refine ⟨25292883206436759917237497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33723844275249013222983329 25292883206436759917237497)
    ·
      refine ⟨18969662404827569937928123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25292883206436759917237497 18969662404827569937928123)
      ·
        refine ⟨28454493607241354906892185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18969662404827569937928123 28454493607241354906892185)
        ·
          refine ⟨21340870205431016180169139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28454493607241354906892185 21340870205431016180169139)
          ·
            refine ⟨32011305308146524270253709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21340870205431016180169139 32011305308146524270253709)
            ·
              refine ⟨12004239490554946601345141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32011305308146524270253709 12004239490554946601345141)
              ·
                refine ⟨1125397452239526243876107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12004239490554946601345141 1125397452239526243876107)
                ·
                  refine ⟨1688096178359289365814161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125397452239526243876107 1688096178359289365814161)
                  ·
                    refine ⟨1266072133769467024360621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1688096178359289365814161 1266072133769467024360621)
                    ·
                      refine ⟨474777050163550134135233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1266072133769467024360621 474777050163550134135233)
                      ·
                        rfl

theorem cell23_924625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_924625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924625 prefixEnd_924625 := by exact prefixLift 924625
  have htrace : WordTrace (prefixWord ++ tailWord_924625) baseStart_924625 baseEnd_924625 := by
    simpa [prefixWord, tailWord_924625, baseEnd_924625] using wordTrace_append hprefix tailTrace_924625
  have hstable : (prefixWord ++ tailWord_924625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924625).length < 2 ^ (prefixWord ++ tailWord_924625).sum := by decide
  have hdescent : baseEnd_924625 < baseStart_924625 := by decide
  rcases family_descends (prefixWord ++ tailWord_924625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924628 : List Nat := [2, 4, 1, 2, 1, 2, 11]
def baseStart_924628 : Nat := 118140960795 + 924628 * 2 ^ 59
def prefixEnd_924628 : Nat := 4983230072969 + 3 ^ 40 * 924628 * 2
def baseEnd_924628 : Nat := 5861464081549550893799

theorem tailTrace_924628 : CollatzResearch.WordTrace tailWord_924628 prefixEnd_924628 5861464081549550893799 := by
  unfold tailWord_924628
  simp only [CollatzResearch.WordTrace]
  refine ⟨16861976847119072367671269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22482635796158763156895025 16861976847119072367671269)
  ·
    refine ⟨3161620658834826068938363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16861976847119072367671269 3161620658834826068938363)
    ·
      refine ⟨4742430988252239103407545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3161620658834826068938363 4742430988252239103407545)
      ·
        refine ⟨3556823241189179327555659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4742430988252239103407545 3556823241189179327555659)
        ·
          refine ⟨5335234861783768991333489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3556823241189179327555659 5335234861783768991333489)
          ·
            refine ⟨4001426146337826743500117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5335234861783768991333489 4001426146337826743500117)
            ·
              refine ⟨5861464081549550893799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4001426146337826743500117 5861464081549550893799)
              ·
                rfl

theorem cell23_924628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 11].length) (baseStart_924628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924628 prefixEnd_924628 := by exact prefixLift 924628
  have htrace : WordTrace (prefixWord ++ tailWord_924628) baseStart_924628 baseEnd_924628 := by
    simpa [prefixWord, tailWord_924628, baseEnd_924628] using wordTrace_append hprefix tailTrace_924628
  have hstable : (prefixWord ++ tailWord_924628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924628).length < 2 ^ (prefixWord ++ tailWord_924628).sum := by decide
  have hdescent : baseEnd_924628 < baseStart_924628 := by decide
  rcases family_descends (prefixWord ++ tailWord_924628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924642 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_924642 : Nat := 118140960795 + 924642 * 2 ^ 59
def prefixEnd_924642 : Nat := 4983230072969 + 3 ^ 40 * 924642 * 2
def baseEnd_924642 : Nat := 474785779334676567622655

theorem tailTrace_924642 : CollatzResearch.WordTrace tailWord_924642 prefixEnd_924642 474785779334676567622655 := by
  unfold tailWord_924642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8431116079046856281588045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22482976210791616750901453 8431116079046856281588045)
  ·
    refine ⟨3161668529642571105595517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8431116079046856281588045 3161668529642571105595517)
    ·
      refine ⟨1185625698615964164598319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3161668529642571105595517 1185625698615964164598319)
      ·
        refine ⟨1778438547923946246897479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185625698615964164598319 1778438547923946246897479)
        ·
          refine ⟨2667657821885919370346219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778438547923946246897479 2667657821885919370346219)
          ·
            refine ⟨4001486732828879055519329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667657821885919370346219 4001486732828879055519329)
            ·
              refine ⟨3001115049621659291639497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4001486732828879055519329 3001115049621659291639497)
              ·
                refine ⟨2250836287216244468729623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001115049621659291639497 2250836287216244468729623)
                ·
                  refine ⟨3376254430824366703094435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250836287216244468729623 3376254430824366703094435)
                  ·
                    refine ⟨5064381646236550054641653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3376254430824366703094435 5064381646236550054641653)
                    ·
                      refine ⟨474785779334676567622655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5064381646236550054641653 474785779334676567622655)
                      ·
                        rfl

theorem cell23_924642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_924642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924642 prefixEnd_924642 := by exact prefixLift 924642
  have htrace : WordTrace (prefixWord ++ tailWord_924642) baseStart_924642 baseEnd_924642 := by
    simpa [prefixWord, tailWord_924642, baseEnd_924642] using wordTrace_append hprefix tailTrace_924642
  have hstable : (prefixWord ++ tailWord_924642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924642).length < 2 ^ (prefixWord ++ tailWord_924642).sum := by decide
  have hdescent : baseEnd_924642 < baseStart_924642 := by decide
  rcases family_descends (prefixWord ++ tailWord_924642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924660 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_924660 : Nat := 118140960795 + 924660 * 2 ^ 59
def prefixEnd_924660 : Nat := 4983230072969 + 3 ^ 40 * 924660 * 2
def baseEnd_924660 : Nat := 474795021986457497197573

theorem tailTrace_924660 : CollatzResearch.WordTrace tailWord_924660 prefixEnd_924660 474795021986457497197573 := by
  unfold tailWord_924660
  simp only [CollatzResearch.WordTrace]
  refine ⟨16862560415061107100253717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22483413886748142800338289 16862560415061107100253717)
  ·
    refine ⟨790432519455989395324393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16862560415061107100253717 790432519455989395324393)
    ·
      refine ⟨592824389591992046493295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 790432519455989395324393 592824389591992046493295)
      ·
        refine ⟨889236584387988069739943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592824389591992046493295 889236584387988069739943)
        ·
          refine ⟨1333854876581982104609915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889236584387988069739943 1333854876581982104609915)
          ·
            refine ⟨2000782314872973156914873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333854876581982104609915 2000782314872973156914873)
            ·
              refine ⟨1500586736154729867686155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2000782314872973156914873 1500586736154729867686155)
              ·
                refine ⟨2250880104232094801529233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500586736154729867686155 2250880104232094801529233)
                ·
                  refine ⟨1688160078174071101146925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2250880104232094801529233 1688160078174071101146925)
                  ·
                    refine ⟨633060029315276662930097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1688160078174071101146925 633060029315276662930097)
                    ·
                      refine ⟨474795021986457497197573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 633060029315276662930097 474795021986457497197573)
                      ·
                        rfl

theorem cell23_924660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_924660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924660 prefixEnd_924660 := by exact prefixLift 924660
  have htrace : WordTrace (prefixWord ++ tailWord_924660) baseStart_924660 baseEnd_924660 := by
    simpa [prefixWord, tailWord_924660, baseEnd_924660] using wordTrace_append hprefix tailTrace_924660
  have hstable : (prefixWord ++ tailWord_924660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924660).length < 2 ^ (prefixWord ++ tailWord_924660).sum := by decide
  have hdescent : baseEnd_924660 < baseStart_924660 := by decide
  rcases family_descends (prefixWord ++ tailWord_924660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924695 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 4]
def baseStart_924695 : Nat := 118140960795 + 924695 * 2 ^ 59
def prefixEnd_924695 : Nat := 4983230072969 + 3 ^ 40 * 924695 * 2
def baseEnd_924695 : Nat := 474812993809364860259911

theorem tailTrace_924695 : CollatzResearch.WordTrace tailWord_924695 prefixEnd_924695 474812993809364860259911 := by
  unfold tailWord_924695
  simp only [CollatzResearch.WordTrace]
  refine ⟨33726397384995415178031539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22484264923330276785354359 33726397384995415178031539)
  ·
    refine ⟨50589596077493122767047309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33726397384995415178031539 50589596077493122767047309)
    ·
      refine ⟨18971098529059921037642741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50589596077493122767047309 18971098529059921037642741)
      ·
        refine ⟨1778540487099367597279007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18971098529059921037642741 1778540487099367597279007)
        ·
          refine ⟨2667810730649051395918511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778540487099367597279007 2667810730649051395918511)
          ·
            refine ⟨4001716095973577093877767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667810730649051395918511 4001716095973577093877767)
            ·
              refine ⟨6002574143960365640816651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4001716095973577093877767 6002574143960365640816651)
              ·
                refine ⟨9003861215940548461224977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6002574143960365640816651 9003861215940548461224977)
                ·
                  refine ⟨6752895911955411345918733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9003861215940548461224977 6752895911955411345918733)
                  ·
                    refine ⟨2532335966983279254719525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6752895911955411345918733 2532335966983279254719525)
                    ·
                      refine ⟨474812993809364860259911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2532335966983279254719525 474812993809364860259911)
                      ·
                        rfl

theorem cell23_924695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_924695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924695 prefixEnd_924695 := by exact prefixLift 924695
  have htrace : WordTrace (prefixWord ++ tailWord_924695) baseStart_924695 baseEnd_924695 := by
    simpa [prefixWord, tailWord_924695, baseEnd_924695] using wordTrace_append hprefix tailTrace_924695
  have hstable : (prefixWord ++ tailWord_924695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924695).length < 2 ^ (prefixWord ++ tailWord_924695).sum := by decide
  have hdescent : baseEnd_924695 < baseStart_924695 := by decide
  rcases family_descends (prefixWord ++ tailWord_924695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924705 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 2, 6]
def baseStart_924705 : Nat := 118140960795 + 924705 * 2 ^ 59
def prefixEnd_924705 : Nat := 4983230072969 + 3 ^ 40 * 924705 * 2
def baseEnd_924705 : Nat := 158272709538636607044955

theorem tailTrace_924705 : CollatzResearch.WordTrace tailWord_924705 prefixEnd_924705 158272709538636607044955 := by
  unfold tailWord_924705
  simp only [CollatzResearch.WordTrace]
  refine ⟨33726762114959186885895569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22484508076639457923930379 33726762114959186885895569)
  ·
    refine ⟨25295071586219390164421677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33726762114959186885895569 25295071586219390164421677)
    ·
      refine ⟨9485651844832271311658129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25295071586219390164421677 9485651844832271311658129)
      ·
        refine ⟨7114238883624203483743597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9485651844832271311658129 7114238883624203483743597)
        ·
          refine ⟨2667839581359076306403849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7114238883624203483743597 2667839581359076306403849)
          ·
            refine ⟨2000879686019307229802887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2667839581359076306403849 2000879686019307229802887)
            ·
              refine ⟨3001319529028960844704331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000879686019307229802887 3001319529028960844704331)
              ·
                refine ⟨4501979293543441267056497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3001319529028960844704331 4501979293543441267056497)
                ·
                  refine ⟨3376484470157580950292373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4501979293543441267056497 3376484470157580950292373)
                  ·
                    refine ⟨158272709538636607044955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3376484470157580950292373 158272709538636607044955)
                    ·
                      rfl

theorem cell23_924705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_924705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924705 prefixEnd_924705 := by exact prefixLift 924705
  have htrace : WordTrace (prefixWord ++ tailWord_924705) baseStart_924705 baseEnd_924705 := by
    simpa [prefixWord, tailWord_924705, baseEnd_924705] using wordTrace_append hprefix tailTrace_924705
  have hstable : (prefixWord ++ tailWord_924705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924705).length < 2 ^ (prefixWord ++ tailWord_924705).sum := by decide
  have hdescent : baseEnd_924705 < baseStart_924705 := by decide
  rcases family_descends (prefixWord ++ tailWord_924705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924795 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 5, 4]
def baseStart_924795 : Nat := 118140960795 + 924795 * 2 ^ 59
def prefixEnd_924795 : Nat := 4983230072969 + 3 ^ 40 * 924795 * 2
def baseEnd_924795 : Nat := 158288113958271489669817

theorem tailTrace_924795 : CollatzResearch.WordTrace tailWord_924795 prefixEnd_924795 158288113958271489669817 := by
  unfold tailWord_924795
  simp only [CollatzResearch.WordTrace]
  refine ⟨33730044684633132256671839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22486696456422088171114559 33730044684633132256671839)
  ·
    refine ⟨50595067026949698385007759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33730044684633132256671839 50595067026949698385007759)
    ·
      refine ⟨75892600540424547577511639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50595067026949698385007759 75892600540424547577511639)
      ·
        refine ⟨113838900810636821366267459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75892600540424547577511639 113838900810636821366267459)
        ·
          refine ⟨170758351215955232049401189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113838900810636821366267459 170758351215955232049401189)
          ·
            refine ⟨32017190852991606009262723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170758351215955232049401189 32017190852991606009262723)
            ·
              refine ⟨48025786279487409013894085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32017190852991606009262723 48025786279487409013894085)
              ·
                refine ⟨9004834927403889190105141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48025786279487409013894085 9004834927403889190105141)
                ·
                  refine ⟨844203274444114611572357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9004834927403889190105141 844203274444114611572357)
                  ·
                    refine ⟨158288113958271489669817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 844203274444114611572357 158288113958271489669817)
                    ·
                      rfl

theorem cell23_924795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 4].length) (baseStart_924795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924795 prefixEnd_924795 := by exact prefixLift 924795
  have htrace : WordTrace (prefixWord ++ tailWord_924795) baseStart_924795 baseEnd_924795 := by
    simpa [prefixWord, tailWord_924795, baseEnd_924795] using wordTrace_append hprefix tailTrace_924795
  have hstable : (prefixWord ++ tailWord_924795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924795).length < 2 ^ (prefixWord ++ tailWord_924795).sum := by decide
  have hdescent : baseEnd_924795 < baseStart_924795 := by decide
  rcases family_descends (prefixWord ++ tailWord_924795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924835 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 3]
def baseStart_924835 : Nat := 118140960795 + 924835 * 2 ^ 59
def prefixEnd_924835 : Nat := 4983230072969 + 3 ^ 40 * 924835 * 2
def baseEnd_924835 : Nat := 474884881100994312509267

theorem tailTrace_924835 : CollatzResearch.WordTrace tailWord_924835 prefixEnd_924835 474884881100994312509267 := by
  unfold tailWord_924835
  simp only [CollatzResearch.WordTrace]
  refine ⟨33731503604488219088127959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22487669069658812725418639 33731503604488219088127959)
  ·
    refine ⟨50597255406732328632191939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33731503604488219088127959 50597255406732328632191939)
    ·
      refine ⟨75895883110098492948287909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50597255406732328632191939 75895883110098492948287909)
      ·
        refine ⟨14230478083143467427803983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75895883110098492948287909 14230478083143467427803983)
        ·
          refine ⟨21345717124715201141705975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14230478083143467427803983 21345717124715201141705975)
          ·
            refine ⟨32018575687072801712558963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21345717124715201141705975 32018575687072801712558963)
            ·
              refine ⟨48027863530609202568838445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32018575687072801712558963 48027863530609202568838445)
              ·
                refine ⟨18010448823978450963314417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48027863530609202568838445 18010448823978450963314417)
                ·
                  refine ⟨13507836617983838222485813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18010448823978450963314417 13507836617983838222485813)
                  ·
                    refine ⟨1266359682935984833358045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13507836617983838222485813 1266359682935984833358045)
                    ·
                      refine ⟨474884881100994312509267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1266359682935984833358045 474884881100994312509267)
                      ·
                        rfl

theorem cell23_924835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_924835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924835 prefixEnd_924835 := by exact prefixLift 924835
  have htrace : WordTrace (prefixWord ++ tailWord_924835) baseStart_924835 baseEnd_924835 := by
    simpa [prefixWord, tailWord_924835, baseEnd_924835] using wordTrace_append hprefix tailTrace_924835
  have hstable : (prefixWord ++ tailWord_924835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924835).length < 2 ^ (prefixWord ++ tailWord_924835).sum := by decide
  have hdescent : baseEnd_924835 < baseStart_924835 := by decide
  rcases family_descends (prefixWord ++ tailWord_924835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924839 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_924839 : Nat := 118140960795 + 924839 * 2 ^ 59
def prefixEnd_924839 : Nat := 4983230072969 + 3 ^ 40 * 924839 * 2
def baseEnd_924839 : Nat := 474886935023612296859249

theorem tailTrace_924839 : CollatzResearch.WordTrace tailWord_924839 prefixEnd_924839 474886935023612296859249 := by
  unfold tailWord_924839
  simp only [CollatzResearch.WordTrace]
  refine ⟨33731649496473727771273571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22487766330982485180849047 33731649496473727771273571)
  ·
    refine ⟨50597474244710591656910357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33731649496473727771273571 50597474244710591656910357)
    ·
      refine ⟨2371756605220808983917673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50597474244710591656910357 2371756605220808983917673)
      ·
        refine ⟨1778817453915606737938255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2371756605220808983917673 1778817453915606737938255)
        ·
          refine ⟨2668226180873410106907383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778817453915606737938255 2668226180873410106907383)
          ·
            refine ⟨4002339271310115160361075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2668226180873410106907383 4002339271310115160361075)
            ·
              refine ⟨6003508906965172740541613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4002339271310115160361075 6003508906965172740541613)
              ·
                refine ⟨2251315840111939777703105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6003508906965172740541613 2251315840111939777703105)
                ·
                  refine ⟨1688486880083954833277329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2251315840111939777703105 1688486880083954833277329)
                  ·
                    refine ⟨1266365160062966124957997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1688486880083954833277329 1266365160062966124957997)
                    ·
                      refine ⟨474886935023612296859249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1266365160062966124957997 474886935023612296859249)
                      ·
                        rfl

theorem cell23_924839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_924839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924839 prefixEnd_924839 := by exact prefixLift 924839
  have htrace : WordTrace (prefixWord ++ tailWord_924839) baseStart_924839 baseEnd_924839 := by
    simpa [prefixWord, tailWord_924839, baseEnd_924839] using wordTrace_append hprefix tailTrace_924839
  have hstable : (prefixWord ++ tailWord_924839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924839).length < 2 ^ (prefixWord ++ tailWord_924839).sum := by decide
  have hdescent : baseEnd_924839 < baseStart_924839 := by decide
  rcases family_descends (prefixWord ++ tailWord_924839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924870 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_924870 : Nat := 118140960795 + 924870 * 2 ^ 59
def prefixEnd_924870 : Nat := 4983230072969 + 3 ^ 40 * 924870 * 2
def baseEnd_924870 : Nat := 474902852923901675571607

theorem tailTrace_924870 : CollatzResearch.WordTrace tailWord_924870 prefixEnd_924870 474902852923901675571607 := by
  unfold tailWord_924870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054149379980044377051627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22488520106240946710434709 1054149379980044377051627)
  ·
    refine ⟨1581224069970066565577441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1054149379980044377051627 1581224069970066565577441)
    ·
      refine ⟨1185918052477549924183081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1581224069970066565577441 1185918052477549924183081)
      ·
        refine ⟨889438539358162443137311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1185918052477549924183081 889438539358162443137311)
        ·
          refine ⟨1334157809037243664705967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889438539358162443137311 1334157809037243664705967)
          ·
            refine ⟨2001236713555865497058951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334157809037243664705967 2001236713555865497058951)
            ·
              refine ⟨3001855070333798245588427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001236713555865497058951 3001855070333798245588427)
              ·
                refine ⟨4502782605500697368382641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3001855070333798245588427 4502782605500697368382641)
                ·
                  refine ⟨3377086954125523026286981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4502782605500697368382641 3377086954125523026286981)
                  ·
                    refine ⟨633203803898535567428809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3377086954125523026286981 633203803898535567428809)
                    ·
                      refine ⟨474902852923901675571607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 633203803898535567428809 474902852923901675571607)
                      ·
                        rfl

theorem cell23_924870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_924870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924870 prefixEnd_924870 := by exact prefixLift 924870
  have htrace : WordTrace (prefixWord ++ tailWord_924870) baseStart_924870 baseEnd_924870 := by
    simpa [prefixWord, tailWord_924870, baseEnd_924870] using wordTrace_append hprefix tailTrace_924870
  have hstable : (prefixWord ++ tailWord_924870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924870).length < 2 ^ (prefixWord ++ tailWord_924870).sum := by decide
  have hdescent : baseEnd_924870 < baseStart_924870 := by decide
  rcases family_descends (prefixWord ++ tailWord_924870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924896 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 2, 3, 2]
def baseStart_924896 : Nat := 118140960795 + 924896 * 2 ^ 59
def prefixEnd_924896 : Nat := 4983230072969 + 3 ^ 40 * 924896 * 2
def baseEnd_924896 : Nat := 474916203420918573846487

theorem tailTrace_924896 : CollatzResearch.WordTrace tailWord_924896 prefixEnd_924896 474916203420918573846487 := by
  unfold tailWord_924896
  simp only [CollatzResearch.WordTrace]
  refine ⟨16866864228633613253049271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22489152304844817670732361 16866864228633613253049271)
  ·
    refine ⟨25300296342950419879573907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16866864228633613253049271 25300296342950419879573907)
    ·
      refine ⟨37950444514425629819360861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25300296342950419879573907 37950444514425629819360861)
      ·
        refine ⟨14231416692909611182260323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37950444514425629819360861 14231416692909611182260323)
        ·
          refine ⟨21347125039364416773390485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14231416692909611182260323 21347125039364416773390485)
          ·
            refine ⟨1000646486220207036252679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21347125039364416773390485 1000646486220207036252679)
            ·
              refine ⟨1500969729330310554379019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000646486220207036252679 1500969729330310554379019)
              ·
                refine ⟨2251454593995465831568529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500969729330310554379019 2251454593995465831568529)
                ·
                  refine ⟨1688590945496599373676397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2251454593995465831568529 1688590945496599373676397)
                  ·
                    refine ⟨633221604561224765128649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1688590945496599373676397 633221604561224765128649)
                    ·
                      refine ⟨474916203420918573846487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 633221604561224765128649 474916203420918573846487)
                      ·
                        rfl

theorem cell23_924896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_924896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924896 prefixEnd_924896 := by exact prefixLift 924896
  have htrace : WordTrace (prefixWord ++ tailWord_924896) baseStart_924896 baseEnd_924896 := by
    simpa [prefixWord, tailWord_924896, baseEnd_924896] using wordTrace_append hprefix tailTrace_924896
  have hstable : (prefixWord ++ tailWord_924896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924896).length < 2 ^ (prefixWord ++ tailWord_924896).sum := by decide
  have hdescent : baseEnd_924896 < baseStart_924896 := by decide
  rcases family_descends (prefixWord ++ tailWord_924896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924906 : List Nat := [3, 1, 3, 1, 1, 5, 2, 1, 1, 5]
def baseStart_924906 : Nat := 118140960795 + 924906 * 2 ^ 59
def prefixEnd_924906 : Nat := 4983230072969 + 3 ^ 40 * 924906 * 2
def baseEnd_924906 : Nat := 158307112742487844907147

theorem tailTrace_924906 : CollatzResearch.WordTrace tailWord_924906 prefixEnd_924906 158307112742487844907147 := by
  unfold tailWord_924906
  simp only [CollatzResearch.WordTrace]
  refine ⟨8433523296807749553490643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22489395458153998809308381 8433523296807749553490643)
  ·
    refine ⟨12650284945211624330235965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8433523296807749553490643 12650284945211624330235965)
    ·
      refine ⟨4743856854454359123838487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12650284945211624330235965 4743856854454359123838487)
      ·
        refine ⟨7115785281681538685757731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4743856854454359123838487 7115785281681538685757731)
        ·
          refine ⟨10673677922522308028636597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7115785281681538685757731 10673677922522308028636597)
          ·
            refine ⟨1000657305236466377684681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10673677922522308028636597 1000657305236466377684681)
            ·
              refine ⟨750492978927349783263511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1000657305236466377684681 750492978927349783263511)
              ·
                refine ⟨1125739468391024674895267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750492978927349783263511 1125739468391024674895267)
                ·
                  refine ⟨1688609202586537012342901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125739468391024674895267 1688609202586537012342901)
                  ·
                    refine ⟨158307112742487844907147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1688609202586537012342901 158307112742487844907147)
                    ·
                      rfl

theorem cell23_924906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_924906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924906 prefixEnd_924906 := by exact prefixLift 924906
  have htrace : WordTrace (prefixWord ++ tailWord_924906) baseStart_924906 baseEnd_924906 := by
    simpa [prefixWord, tailWord_924906, baseEnd_924906] using wordTrace_append hprefix tailTrace_924906
  have hstable : (prefixWord ++ tailWord_924906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924906).length < 2 ^ (prefixWord ++ tailWord_924906).sum := by decide
  have hdescent : baseEnd_924906 < baseStart_924906 := by decide
  rcases family_descends (prefixWord ++ tailWord_924906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924915 : List Nat := [1, 1, 1, 2, 2, 6, 10]
def baseStart_924915 : Nat := 118140960795 + 924915 * 2 ^ 59
def prefixEnd_924915 : Nat := 4983230072969 + 3 ^ 40 * 924915 * 2
def baseEnd_924915 : Nat := 5863283451275975302579

theorem tailTrace_924915 : CollatzResearch.WordTrace tailWord_924915 prefixEnd_924915 5863283451275975302579 := by
  unfold tailWord_924915
  simp only [CollatzResearch.WordTrace]
  refine ⟨33734421444198392751040199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22489614296132261834026799 33734421444198392751040199)
  ·
    refine ⟨50601632166297589126560299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33734421444198392751040199 50601632166297589126560299)
    ·
      refine ⟨75902448249446383689840449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50601632166297589126560299 75902448249446383689840449)
      ·
        refine ⟨56926836187084787767380337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75902448249446383689840449 56926836187084787767380337)
        ·
          refine ⟨42695127140313590825535253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56926836187084787767380337 42695127140313590825535253)
          ·
            refine ⟨2001334084702199569946965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42695127140313590825535253 2001334084702199569946965)
            ·
              refine ⟨5863283451275975302579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2001334084702199569946965 5863283451275975302579)
              ·
                rfl

theorem cell23_924915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 10].length) (baseStart_924915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924915 prefixEnd_924915 := by exact prefixLift 924915
  have htrace : WordTrace (prefixWord ++ tailWord_924915) baseStart_924915 baseEnd_924915 := by
    simpa [prefixWord, tailWord_924915, baseEnd_924915] using wordTrace_append hprefix tailTrace_924915
  have hstable : (prefixWord ++ tailWord_924915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924915).length < 2 ^ (prefixWord ++ tailWord_924915).sum := by decide
  have hdescent : baseEnd_924915 < baseStart_924915 := by decide
  rcases family_descends (prefixWord ++ tailWord_924915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924925 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_924925 : Nat := 118140960795 + 924925 * 2 ^ 59
def prefixEnd_924925 : Nat := 4983230072969 + 3 ^ 40 * 924925 * 2
def baseEnd_924925 : Nat := 474931094359898960383853

theorem tailTrace_924925 : CollatzResearch.WordTrace tailWord_924925 prefixEnd_924925 474931094359898960383853 := by
  unfold tailWord_924925
  simp only [CollatzResearch.WordTrace]
  refine ⟨33734786174162164458904229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22489857449441442972602819 33734786174162164458904229)
  ·
    refine ⟨6325272407655405836044543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33734786174162164458904229 6325272407655405836044543)
    ·
      refine ⟨9487908611483108754066815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6325272407655405836044543 9487908611483108754066815)
      ·
        refine ⟨14231862917224663131100223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9487908611483108754066815 14231862917224663131100223)
        ·
          refine ⟨21347794375836994696650335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14231862917224663131100223 21347794375836994696650335)
          ·
            refine ⟨32021691563755492044975503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21347794375836994696650335 32021691563755492044975503)
            ·
              refine ⟨48032537345633238067463255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32021691563755492044975503 48032537345633238067463255)
              ·
                refine ⟨72048806018449857101194883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48032537345633238067463255 72048806018449857101194883)
                ·
                  refine ⟨108073209027674785651792325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72048806018449857101194883 108073209027674785651792325)
                  ·
                    refine ⟨20263726692689022309711061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108073209027674785651792325 20263726692689022309711061)
                    ·
                      refine ⟨474931094359898960383853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20263726692689022309711061 474931094359898960383853)
                      ·
                        rfl

theorem cell23_924925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_924925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924925 prefixEnd_924925 := by exact prefixLift 924925
  have htrace : WordTrace (prefixWord ++ tailWord_924925) baseStart_924925 baseEnd_924925 := by
    simpa [prefixWord, tailWord_924925, baseEnd_924925] using wordTrace_append hprefix tailTrace_924925
  have hstable : (prefixWord ++ tailWord_924925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924925).length < 2 ^ (prefixWord ++ tailWord_924925).sum := by decide
  have hdescent : baseEnd_924925 < baseStart_924925 := by decide
  rcases family_descends (prefixWord ++ tailWord_924925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924936 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 1, 6]
def baseStart_924936 : Nat := 118140960795 + 924936 * 2 ^ 59
def prefixEnd_924936 : Nat := 4983230072969 + 3 ^ 40 * 924936 * 2
def baseEnd_924936 : Nat := 158312247549032805782101

theorem tailTrace_924936 : CollatzResearch.WordTrace tailWord_924936 prefixEnd_924936 158312247549032805782101 := by
  unfold tailWord_924936
  simp only [CollatzResearch.WordTrace]
  refine ⟨16867593688561156668777331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22490124918081542225036441 16867593688561156668777331)
  ·
    refine ⟨25301390532841735003165997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16867593688561156668777331 25301390532841735003165997)
    ·
      refine ⟨9488021449815650626187249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25301390532841735003165997 9488021449815650626187249)
      ·
        refine ⟨7116016087361737969640437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9488021449815650626187249 7116016087361737969640437)
        ·
          refine ⟨667126508190162934653791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7116016087361737969640437 667126508190162934653791)
          ·
            refine ⟨1000689762285244401980687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667126508190162934653791 1000689762285244401980687)
            ·
              refine ⟨1501034643427866602971031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000689762285244401980687 1501034643427866602971031)
              ·
                refine ⟨2251551965141799904456547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501034643427866602971031 2251551965141799904456547)
                ·
                  refine ⟨3377327947712699856684821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251551965141799904456547 3377327947712699856684821)
                  ·
                    refine ⟨158312247549032805782101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3377327947712699856684821 158312247549032805782101)
                    ·
                      rfl

theorem cell23_924936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_924936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924936 prefixEnd_924936 := by exact prefixLift 924936
  have htrace : WordTrace (prefixWord ++ tailWord_924936) baseStart_924936 baseEnd_924936 := by
    simpa [prefixWord, tailWord_924936, baseEnd_924936] using wordTrace_append hprefix tailTrace_924936
  have hstable : (prefixWord ++ tailWord_924936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924936).length < 2 ^ (prefixWord ++ tailWord_924936).sum := by decide
  have hdescent : baseEnd_924936 < baseStart_924936 := by decide
  rcases family_descends (prefixWord ++ tailWord_924936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924939 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 1, 2, 4]
def baseStart_924939 : Nat := 118140960795 + 924939 * 2 ^ 59
def prefixEnd_924939 : Nat := 4983230072969 + 3 ^ 40 * 924939 * 2
def baseEnd_924939 : Nat := 474938283089061905608789

theorem tailTrace_924939 : CollatzResearch.WordTrace tailWord_924939 prefixEnd_924939 474938283089061905608789 := by
  unfold tailWord_924939
  simp only [CollatzResearch.WordTrace]
  refine ⟨33735296796111444849913871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22490197864074296566609247 33735296796111444849913871)
  ·
    refine ⟨50602945194167167274870807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33735296796111444849913871 50602945194167167274870807)
    ·
      refine ⟨75904417791250750912306211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50602945194167167274870807 75904417791250750912306211)
      ·
        refine ⟨113856626686876126368459317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75904417791250750912306211 113856626686876126368459317)
        ·
          refine ⟨10674058751894636847043061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113856626686876126368459317 10674058751894636847043061)
          ·
            refine ⟨1000693007990122204410287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10674058751894636847043061 1000693007990122204410287)
            ·
              refine ⟨1501039511985183306615431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000693007990122204410287 1501039511985183306615431)
              ·
                refine ⟨2251559267977774959923147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501039511985183306615431 2251559267977774959923147)
                ·
                  refine ⟨3377338901966662439884721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251559267977774959923147 3377338901966662439884721)
                  ·
                    refine ⟨2533004176474996829913541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3377338901966662439884721 2533004176474996829913541)
                    ·
                      refine ⟨474938283089061905608789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2533004176474996829913541 474938283089061905608789)
                      ·
                        rfl

theorem cell23_924939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 2, 4].length) (baseStart_924939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924939 prefixEnd_924939 := by exact prefixLift 924939
  have htrace : WordTrace (prefixWord ++ tailWord_924939) baseStart_924939 baseEnd_924939 := by
    simpa [prefixWord, tailWord_924939, baseEnd_924939] using wordTrace_append hprefix tailTrace_924939
  have hstable : (prefixWord ++ tailWord_924939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924939).length < 2 ^ (prefixWord ++ tailWord_924939).sum := by decide
  have hdescent : baseEnd_924939 < baseStart_924939 := by decide
  rcases family_descends (prefixWord ++ tailWord_924939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924993 : List Nat := [1, 2, 5, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_924993 : Nat := 118140960795 + 924993 * 2 ^ 59
def prefixEnd_924993 : Nat := 4983230072969 + 3 ^ 40 * 924993 * 2
def baseEnd_924993 : Nat := 474966011044404694333541

theorem tailTrace_924993 : CollatzResearch.WordTrace tailWord_924993 prefixEnd_924993 474966011044404694333541 := by
  unfold tailWord_924993
  simp only [CollatzResearch.WordTrace]
  refine ⟨33737266337915812072379633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22491510891943874714919755 33737266337915812072379633)
  ·
    refine ⟨25302949753436859054284725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33737266337915812072379633 25302949753436859054284725)
    ·
      refine ⟨2372151539384705536339193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25302949753436859054284725 2372151539384705536339193)
      ·
        refine ⟨1779113654538529152254395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2372151539384705536339193 1779113654538529152254395)
        ·
          refine ⟨2668670481807793728381593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1779113654538529152254395 2668670481807793728381593)
          ·
            refine ⟨2001502861355845296286195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2668670481807793728381593 2001502861355845296286195)
            ·
              refine ⟨3002254292033767944429293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001502861355845296286195 3002254292033767944429293)
              ·
                refine ⟨1125845359512662979160985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3002254292033767944429293 1125845359512662979160985)
                ·
                  refine ⟨844384019634497234370739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1125845359512662979160985 844384019634497234370739)
                  ·
                    refine ⟨1266576029451745851556109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 844384019634497234370739 1266576029451745851556109)
                    ·
                      refine ⟨474966011044404694333541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1266576029451745851556109 474966011044404694333541)
                      ·
                        rfl

theorem cell23_924993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_924993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_924993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_924993 prefixEnd_924993 := by exact prefixLift 924993
  have htrace : WordTrace (prefixWord ++ tailWord_924993) baseStart_924993 baseEnd_924993 := by
    simpa [prefixWord, tailWord_924993, baseEnd_924993] using wordTrace_append hprefix tailTrace_924993
  have hstable : (prefixWord ++ tailWord_924993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924993).length < 2 ^ (prefixWord ++ tailWord_924993).sum := by decide
  have hdescent : baseEnd_924993 < baseStart_924993 := by decide
  rcases family_descends (prefixWord ++ tailWord_924993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925014 : List Nat := [5, 2, 3, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_925014 : Nat := 118140960795 + 925014 * 2 ^ 59
def prefixEnd_925014 : Nat := 4983230072969 + 3 ^ 40 * 925014 * 2
def baseEnd_925014 : Nat := 474976794138149112170945

theorem tailTrace_925014 : CollatzResearch.WordTrace tailWord_925014 prefixEnd_925014 474976794138149112170945 := by
  unfold tailWord_925014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2108627016927483291180881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22492021513893155105929397 2108627016927483291180881)
  ·
    refine ⟨1581470262695612468385661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2108627016927483291180881 1581470262695612468385661)
    ·
      refine ⟨593051348510854675644623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1581470262695612468385661 593051348510854675644623)
      ·
        refine ⟨889577022766282013466935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593051348510854675644623 889577022766282013466935)
        ·
          refine ⟨1334365534149423020200403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889577022766282013466935 1334365534149423020200403)
          ·
            refine ⟨2001548301224134530300605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334365534149423020200403 2001548301224134530300605)
            ·
              refine ⟨750580612959050448862727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2001548301224134530300605 750580612959050448862727)
              ·
                refine ⟨1125870919438575673294091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750580612959050448862727 1125870919438575673294091)
                ·
                  refine ⟨1688806379157863509941137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125870919438575673294091 1688806379157863509941137)
                  ·
                    refine ⟨1266604784368397632455853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1688806379157863509941137 1266604784368397632455853)
                    ·
                      refine ⟨474976794138149112170945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1266604784368397632455853 474976794138149112170945)
                      ·
                        rfl

theorem cell23_925014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_925014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925014 prefixEnd_925014 := by exact prefixLift 925014
  have htrace : WordTrace (prefixWord ++ tailWord_925014) baseStart_925014 baseEnd_925014 := by
    simpa [prefixWord, tailWord_925014, baseEnd_925014] using wordTrace_append hprefix tailTrace_925014
  have hstable : (prefixWord ++ tailWord_925014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925014).length < 2 ^ (prefixWord ++ tailWord_925014).sum := by decide
  have hdescent : baseEnd_925014 < baseStart_925014 := by decide
  rcases family_descends (prefixWord ++ tailWord_925014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925039 : List Nat := [1, 1, 2, 1, 3, 1, 5, 4, 5]
def baseStart_925039 : Nat := 118140960795 + 925039 * 2 ^ 59
def prefixEnd_925039 : Nat := 4983230072969 + 3 ^ 40 * 925039 * 2
def baseEnd_925039 : Nat := 52776625683834612706481

theorem tailTrace_925039 : CollatzResearch.WordTrace tailWord_925039 prefixEnd_925039 52776625683834612706481 := by
  unfold tailWord_925039
  simp only [CollatzResearch.WordTrace]
  refine ⟨33738944095749161928554171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22492629397166107952369447 33738944095749161928554171)
  ·
    refine ⟨50608416143623742892831257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33738944095749161928554171 50608416143623742892831257)
    ·
      refine ⟨37956312107717807169623443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50608416143623742892831257 37956312107717807169623443)
      ·
        refine ⟨56934468161576710754435165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37956312107717807169623443 56934468161576710754435165)
        ·
          refine ⟨21350425560591266532913187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56934468161576710754435165 21350425560591266532913187)
          ·
            refine ⟨32025638340886899799369781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21350425560591266532913187 32025638340886899799369781)
            ·
              refine ⟨3002403594458146856190917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32025638340886899799369781 3002403594458146856190917)
              ·
                refine ⟨562950673960902535535797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3002403594458146856190917 562950673960902535535797)
                ·
                  refine ⟨52776625683834612706481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 562950673960902535535797 52776625683834612706481)
                  ·
                    rfl

theorem cell23_925039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 5].length) (baseStart_925039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925039 prefixEnd_925039 := by exact prefixLift 925039
  have htrace : WordTrace (prefixWord ++ tailWord_925039) baseStart_925039 baseEnd_925039 := by
    simpa [prefixWord, tailWord_925039, baseEnd_925039] using wordTrace_append hprefix tailTrace_925039
  have hstable : (prefixWord ++ tailWord_925039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925039).length < 2 ^ (prefixWord ++ tailWord_925039).sum := by decide
  have hdescent : baseEnd_925039 < baseStart_925039 := by decide
  rcases family_descends (prefixWord ++ tailWord_925039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925052 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 1, 7]
def baseStart_925052 : Nat := 118140960795 + 925052 * 2 ^ 59
def prefixEnd_925052 : Nat := 4983230072969 + 3 ^ 40 * 925052 * 2
def baseEnd_925052 : Nat := 158332102134339987831923

theorem tailTrace_925052 : CollatzResearch.WordTrace tailWord_925052 prefixEnd_925052 158332102134339987831923 := by
  unfold tailWord_925052
  simp only [CollatzResearch.WordTrace]
  refine ⟨16869709122351032574388705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22492945496468043432518273 16869709122351032574388705)
  ·
    refine ⟨12652281841763274430791529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16869709122351032574388705 12652281841763274430791529)
    ·
      refine ⟨9489211381322455823093647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12652281841763274430791529 9489211381322455823093647)
      ·
        refine ⟨14233817071983683734640471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9489211381322455823093647 14233817071983683734640471)
        ·
          refine ⟨21350725607975525601960707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14233817071983683734640471 21350725607975525601960707)
          ·
            refine ⟨32026088411963288402941061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21350725607975525601960707 32026088411963288402941061)
            ·
              refine ⟨6004891577243116575551449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32026088411963288402941061 6004891577243116575551449)
              ·
                refine ⟨4503668682932337431663587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6004891577243116575551449 4503668682932337431663587)
                ·
                  refine ⟨6755503024398506147495381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503668682932337431663587 6755503024398506147495381)
                  ·
                    refine ⟨158332102134339987831923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6755503024398506147495381 158332102134339987831923)
                    ·
                      rfl

theorem cell23_925052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_925052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925052 prefixEnd_925052 := by exact prefixLift 925052
  have htrace : WordTrace (prefixWord ++ tailWord_925052) baseStart_925052 baseEnd_925052 := by
    simpa [prefixWord, tailWord_925052, baseEnd_925052] using wordTrace_append hprefix tailTrace_925052
  have hstable : (prefixWord ++ tailWord_925052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925052).length < 2 ^ (prefixWord ++ tailWord_925052).sum := by decide
  have hdescent : baseEnd_925052 < baseStart_925052 := by decide
  rcases family_descends (prefixWord ++ tailWord_925052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925084 : List Nat := [2, 2, 3, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_925084 : Nat := 118140960795 + 925084 * 2 ^ 59
def prefixEnd_925084 : Nat := 4983230072969 + 3 ^ 40 * 925084 * 2
def baseEnd_925084 : Nat := 475012737783963838295623

theorem tailTrace_925084 : CollatzResearch.WordTrace tailWord_925084 prefixEnd_925084 475012737783963838295623 := by
  unfold tailWord_925084
  simp only [CollatzResearch.WordTrace]
  refine ⟨16870292690293067306971153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22493723587057423075961537 16870292690293067306971153)
  ·
    refine ⟨12652719517719800480228365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16870292690293067306971153 12652719517719800480228365)
    ·
      refine ⟨4744769819144925180085637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12652719517719800480228365 4744769819144925180085637)
      ·
        refine ⟨889644341089673471266057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4744769819144925180085637 889644341089673471266057)
        ·
          refine ⟨667233255817255103449543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 889644341089673471266057 667233255817255103449543)
          ·
            refine ⟨1000849883725882655174315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667233255817255103449543 1000849883725882655174315)
            ·
              refine ⟨1501274825588823982761473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000849883725882655174315 1501274825588823982761473)
              ·
                refine ⟨1125956119191617987071105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501274825588823982761473 1125956119191617987071105)
                ·
                  refine ⟨844467089393713490303329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1125956119191617987071105 844467089393713490303329)
                  ·
                    refine ⟨633350317045285117727497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 844467089393713490303329 633350317045285117727497)
                    ·
                      refine ⟨475012737783963838295623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 633350317045285117727497 475012737783963838295623)
                      ·
                        rfl

theorem cell23_925084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_925084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925084 prefixEnd_925084 := by exact prefixLift 925084
  have htrace : WordTrace (prefixWord ++ tailWord_925084) baseStart_925084 baseEnd_925084 := by
    simpa [prefixWord, tailWord_925084, baseEnd_925084] using wordTrace_append hprefix tailTrace_925084
  have hstable : (prefixWord ++ tailWord_925084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925084).length < 2 ^ (prefixWord ++ tailWord_925084).sum := by decide
  have hdescent : baseEnd_925084 < baseStart_925084 := by decide
  rcases family_descends (prefixWord ++ tailWord_925084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925176 : List Nat := [2, 1, 2, 1, 1, 5, 3, 2, 1, 5]
def baseStart_925176 : Nat := 118140960795 + 925176 * 2 ^ 59
def prefixEnd_925176 : Nat := 4983230072969 + 3 ^ 40 * 925176 * 2
def baseEnd_925176 : Nat := 158353326001392492781733

theorem tailTrace_925176 : CollatzResearch.WordTrace tailWord_925176 prefixEnd_925176 158353326001392492781733 := by
  unfold tailWord_925176
  simp only [CollatzResearch.WordTrace]
  refine ⟨16871970448126417163145691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22495960597501889550860921 16871970448126417163145691)
  ·
    refine ⟨25307955672189625744718537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16871970448126417163145691 25307955672189625744718537)
    ·
      refine ⟨18980966754142219308538903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25307955672189625744718537 18980966754142219308538903)
      ·
        refine ⟨28471450131213328962808355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18980966754142219308538903 28471450131213328962808355)
        ·
          refine ⟨42707175196819993444212533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28471450131213328962808355 42707175196819993444212533)
          ·
            refine ⟨4003797674701874385394925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42707175196819993444212533 4003797674701874385394925)
            ·
              refine ⟨1501424128013202894523097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4003797674701874385394925 1501424128013202894523097)
              ·
                refine ⟨1126068096009902170892323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501424128013202894523097 1126068096009902170892323)
                ·
                  refine ⟨1689102144014853256338485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126068096009902170892323 1689102144014853256338485)
                  ·
                    refine ⟨158353326001392492781733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1689102144014853256338485 158353326001392492781733)
                    ·
                      rfl

theorem cell23_925176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_925176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925176 prefixEnd_925176 := by exact prefixLift 925176
  have htrace : WordTrace (prefixWord ++ tailWord_925176) baseStart_925176 baseEnd_925176 := by
    simpa [prefixWord, tailWord_925176, baseEnd_925176] using wordTrace_append hprefix tailTrace_925176
  have hstable : (prefixWord ++ tailWord_925176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925176).length < 2 ^ (prefixWord ++ tailWord_925176).sum := by decide
  have hdescent : baseEnd_925176 < baseStart_925176 := by decide
  rcases family_descends (prefixWord ++ tailWord_925176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925179 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 4]
def baseStart_925179 : Nat := 118140960795 + 925179 * 2 ^ 59
def prefixEnd_925179 : Nat := 4983230072969 + 3 ^ 40 * 925179 * 2
def baseEnd_925179 : Nat := 475061518446140966607685

theorem tailTrace_925179 : CollatzResearch.WordTrace tailWord_925179 prefixEnd_925179 475061518446140966607685 := by
  unfold tailWord_925179
  simp only [CollatzResearch.WordTrace]
  refine ⟨33744050315241965838650591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22496033543494643892433727 33744050315241965838650591)
  ·
    refine ⟨50616075472862948757975887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33744050315241965838650591 50616075472862948757975887)
    ·
      refine ⟨75924113209294423136963831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50616075472862948757975887 75924113209294423136963831)
      ·
        refine ⟨113886169813941634705445747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75924113209294423136963831 113886169813941634705445747)
        ·
          refine ⟨170829254720912452058168621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113886169813941634705445747 170829254720912452058168621)
          ·
            refine ⟨64060970520342169521813233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170829254720912452058168621 64060970520342169521813233)
            ·
              refine ⟨48045727890256627141359925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64060970520342169521813233 48045727890256627141359925)
              ·
                refine ⟨4504286989711558794502493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48045727890256627141359925 4504286989711558794502493)
                ·
                  refine ⟨1689107621141834547938435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4504286989711558794502493 1689107621141834547938435)
                  ·
                    refine ⟨2533661431712751821907653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1689107621141834547938435 2533661431712751821907653)
                    ·
                      refine ⟨475061518446140966607685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2533661431712751821907653 475061518446140966607685)
                      ·
                        rfl

theorem cell23_925179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 4].length) (baseStart_925179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925179 prefixEnd_925179 := by exact prefixLift 925179
  have htrace : WordTrace (prefixWord ++ tailWord_925179) baseStart_925179 baseEnd_925179 := by
    simpa [prefixWord, tailWord_925179, baseEnd_925179] using wordTrace_append hprefix tailTrace_925179
  have hstable : (prefixWord ++ tailWord_925179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925179).length < 2 ^ (prefixWord ++ tailWord_925179).sum := by decide
  have hdescent : baseEnd_925179 < baseStart_925179 := by decide
  rcases family_descends (prefixWord ++ tailWord_925179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925230 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_925230 : Nat := 118140960795 + 925230 * 2 ^ 59
def prefixEnd_925230 : Nat := 4983230072969 + 3 ^ 40 * 925230 * 2
def baseEnd_925230 : Nat := 475087705959520267069951

theorem tailTrace_925230 : CollatzResearch.WordTrace tailWord_925230 prefixEnd_925230 475087705959520267069951 := by
  unfold tailWord_925230
  simp only [CollatzResearch.WordTrace]
  refine ⟨4218238804757150193594643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22497273625371467699171429 4218238804757150193594643)
  ·
    refine ⟨6327358207135725290391965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4218238804757150193594643 6327358207135725290391965)
    ·
      refine ⟨2372759327675896983896987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6327358207135725290391965 2372759327675896983896987)
      ·
        refine ⟨3559138991513845475845481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2372759327675896983896987 3559138991513845475845481)
        ·
          refine ⟨2669354243635384106884111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3559138991513845475845481 2669354243635384106884111)
          ·
            refine ⟨4004031365453076160326167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2669354243635384106884111 4004031365453076160326167)
            ·
              refine ⟨6006047048179614240489251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4004031365453076160326167 6006047048179614240489251)
              ·
                refine ⟨9009070572269421360733877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6006047048179614240489251 9009070572269421360733877)
                ·
                  refine ⟨844600366150258252568801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9009070572269421360733877 844600366150258252568801)
                  ·
                    refine ⟨633450274612693689426601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 844600366150258252568801 633450274612693689426601)
                    ·
                      refine ⟨475087705959520267069951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 633450274612693689426601 475087705959520267069951)
                      ·
                        rfl

theorem cell23_925230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_925230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925230 prefixEnd_925230 := by exact prefixLift 925230
  have htrace : WordTrace (prefixWord ++ tailWord_925230) baseStart_925230 baseEnd_925230 := by
    simpa [prefixWord, tailWord_925230, baseEnd_925230] using wordTrace_append hprefix tailTrace_925230
  have hstable : (prefixWord ++ tailWord_925230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925230).length < 2 ^ (prefixWord ++ tailWord_925230).sum := by decide
  have hdescent : baseEnd_925230 < baseStart_925230 := by decide
  rcases family_descends (prefixWord ++ tailWord_925230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925247 : List Nat := [1, 1, 2, 2, 3, 4, 2, 3, 1, 2, 2]
def baseStart_925247 : Nat := 118140960795 + 925247 * 2 ^ 59
def prefixEnd_925247 : Nat := 4983230072969 + 3 ^ 40 * 925247 * 2
def baseEnd_925247 : Nat := 475096435130646700557373

theorem tailTrace_925247 : CollatzResearch.WordTrace tailWord_925247 prefixEnd_925247 475096435130646700557373 := by
  unfold tailWord_925247
  simp only [CollatzResearch.WordTrace]
  refine ⟨33746530478995613452125995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22497686985997075634750663 33746530478995613452125995)
  ·
    refine ⟨50619795718493420178188993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33746530478995613452125995 50619795718493420178188993)
    ·
      refine ⟨37964846788870065133641745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50619795718493420178188993 37964846788870065133641745)
      ·
        refine ⟨28473635091652548850231309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37964846788870065133641745 28473635091652548850231309)
        ·
          refine ⟨10677613159369705818836741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28473635091652548850231309 10677613159369705818836741)
          ·
            refine ⟨2002052467381819841031889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10677613159369705818836741 2002052467381819841031889)
            ·
              refine ⟨1501539350536364880773917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2002052467381819841031889 1501539350536364880773917)
              ·
                refine ⟨563077256451136830290219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1501539350536364880773917 563077256451136830290219)
                ·
                  refine ⟨844615884676705245435329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563077256451136830290219 844615884676705245435329)
                  ·
                    refine ⟨633461913507528934076497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 844615884676705245435329 633461913507528934076497)
                    ·
                      refine ⟨475096435130646700557373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 633461913507528934076497 475096435130646700557373)
                      ·
                        rfl

theorem cell23_925247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 1, 2, 2].length) (baseStart_925247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925247 prefixEnd_925247 := by exact prefixLift 925247
  have htrace : WordTrace (prefixWord ++ tailWord_925247) baseStart_925247 baseEnd_925247 := by
    simpa [prefixWord, tailWord_925247, baseEnd_925247] using wordTrace_append hprefix tailTrace_925247
  have hstable : (prefixWord ++ tailWord_925247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925247).length < 2 ^ (prefixWord ++ tailWord_925247).sum := by decide
  have hdescent : baseEnd_925247 < baseStart_925247 := by decide
  rcases family_descends (prefixWord ++ tailWord_925247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925277 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_925277 : Nat := 118140960795 + 925277 * 2 ^ 59
def prefixEnd_925277 : Nat := 4983230072969 + 3 ^ 40 * 925277 * 2
def baseEnd_925277 : Nat := 475111839550281583182235

theorem tailTrace_925277 : CollatzResearch.WordTrace tailWord_925277 prefixEnd_925277 475111839550281583182235 := by
  unfold tailWord_925277
  simp only [CollatzResearch.WordTrace]
  refine ⟨33747624668886928575718085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22498416445924619050478723 33747624668886928575718085)
  ·
    refine ⟨6327679625416299107947141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33747624668886928575718085 6327679625416299107947141)
    ·
      refine ⟨1186439929765556082740089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6327679625416299107947141 1186439929765556082740089)
      ·
        refine ⟨889829947324167062055067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1186439929765556082740089 889829947324167062055067)
        ·
          refine ⟨1334744920986250593082601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889829947324167062055067 1334744920986250593082601)
          ·
            refine ⟨1001058690739687944811951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1334744920986250593082601 1001058690739687944811951)
            ·
              refine ⟨1501588036109531917217927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001058690739687944811951 1501588036109531917217927)
              ·
                refine ⟨2252382054164297875826891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501588036109531917217927 2252382054164297875826891)
                ·
                  refine ⟨3378573081246446813740337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2252382054164297875826891 3378573081246446813740337)
                  ·
                    refine ⟨2533929810934835110305253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3378573081246446813740337 2533929810934835110305253)
                    ·
                      refine ⟨475111839550281583182235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2533929810934835110305253 475111839550281583182235)
                      ·
                        rfl

theorem cell23_925277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_925277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925277 prefixEnd_925277 := by exact prefixLift 925277
  have htrace : WordTrace (prefixWord ++ tailWord_925277) baseStart_925277 baseEnd_925277 := by
    simpa [prefixWord, tailWord_925277, baseEnd_925277] using wordTrace_append hprefix tailTrace_925277
  have hstable : (prefixWord ++ tailWord_925277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925277).length < 2 ^ (prefixWord ++ tailWord_925277).sum := by decide
  have hdescent : baseEnd_925277 < baseStart_925277 := by decide
  rcases family_descends (prefixWord ++ tailWord_925277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925290 : List Nat := [3, 1, 3, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_925290 : Nat := 118140960795 + 925290 * 2 ^ 59
def prefixEnd_925290 : Nat := 4983230072969 + 3 ^ 40 * 925290 * 2
def baseEnd_925290 : Nat := 475118514798790032319675

theorem tailTrace_925290 : CollatzResearch.WordTrace tailWord_925290 prefixEnd_925290 475118514798790032319675 := by
  unfold tailWord_925290
  simp only [CollatzResearch.WordTrace]
  refine ⟨8437024704459957948985331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22498732545226554530627549 8437024704459957948985331)
  ·
    refine ⟨12655537056689936923477997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8437024704459957948985331 12655537056689936923477997)
    ·
      refine ⟨4745826396258726346304249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12655537056689936923477997 4745826396258726346304249)
      ·
        refine ⟨3559369797194044759728187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4745826396258726346304249 3559369797194044759728187)
        ·
          refine ⟨5339054695791067139592281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3559369797194044759728187 5339054695791067139592281)
          ·
            refine ⟨4004291021843300354694211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5339054695791067139592281 4004291021843300354694211)
            ·
              refine ⟨6006436532764950532041317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4004291021843300354694211 6006436532764950532041317)
              ·
                refine ⟨1126206849893428224757747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6006436532764950532041317 1126206849893428224757747)
                ·
                  refine ⟨1689310274840142337136621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126206849893428224757747 1689310274840142337136621)
                  ·
                    refine ⟨633491353065053376426233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1689310274840142337136621 633491353065053376426233)
                    ·
                      refine ⟨475118514798790032319675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 633491353065053376426233 475118514798790032319675)
                      ·
                        rfl

theorem cell23_925290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_925290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925290 prefixEnd_925290 := by exact prefixLift 925290
  have htrace : WordTrace (prefixWord ++ tailWord_925290) baseStart_925290 baseEnd_925290 := by
    simpa [prefixWord, tailWord_925290, baseEnd_925290] using wordTrace_append hprefix tailTrace_925290
  have hstable : (prefixWord ++ tailWord_925290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925290).length < 2 ^ (prefixWord ++ tailWord_925290).sum := by decide
  have hdescent : baseEnd_925290 < baseStart_925290 := by decide
  rcases family_descends (prefixWord ++ tailWord_925290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925329 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_925329 : Nat := 118140960795 + 925329 * 2 ^ 59
def prefixEnd_925329 : Nat := 4983230072969 + 3 ^ 40 * 925329 * 2
def baseEnd_925329 : Nat := 475138540544315379731995

theorem tailTrace_925329 : CollatzResearch.WordTrace tailWord_925329 prefixEnd_925329 475138540544315379731995 := by
  unfold tailWord_925329
  simp only [CollatzResearch.WordTrace]
  refine ⟨33749521264698541456611041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22499680843132360971074027 33749521264698541456611041)
  ·
    refine ⟨25312140948523906092458281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33749521264698541456611041 25312140948523906092458281)
    ·
      refine ⟨18984105711392929569343711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25312140948523906092458281 18984105711392929569343711)
      ·
        refine ⟨28476158567089394354015567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18984105711392929569343711 28476158567089394354015567)
        ·
          refine ⟨42714237850634091531023351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28476158567089394354015567 42714237850634091531023351)
          ·
            refine ⟨64071356775951137296535027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42714237850634091531023351 64071356775951137296535027)
            ·
              refine ⟨96107035163926705944802541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64071356775951137296535027 96107035163926705944802541)
              ·
                refine ⟨36040138186472514729300953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96107035163926705944802541 36040138186472514729300953)
                ·
                  refine ⟨27030103639854386046975715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36040138186472514729300953 27030103639854386046975715)
                  ·
                    refine ⟨40545155459781579070463573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27030103639854386046975715 40545155459781579070463573)
                    ·
                      refine ⟨475138540544315379731995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 40545155459781579070463573 475138540544315379731995)
                      ·
                        rfl

theorem cell23_925329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_925329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925329 prefixEnd_925329 := by exact prefixLift 925329
  have htrace : WordTrace (prefixWord ++ tailWord_925329) baseStart_925329 baseEnd_925329 := by
    simpa [prefixWord, tailWord_925329, baseEnd_925329] using wordTrace_append hprefix tailTrace_925329
  have hstable : (prefixWord ++ tailWord_925329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925329).length < 2 ^ (prefixWord ++ tailWord_925329).sum := by decide
  have hdescent : baseEnd_925329 < baseStart_925329 := by decide
  rcases family_descends (prefixWord ++ tailWord_925329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925393 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 1, 6, 2]
def baseStart_925393 : Nat := 118140960795 + 925393 * 2 ^ 59
def prefixEnd_925393 : Nat := 4983230072969 + 3 ^ 40 * 925393 * 2
def baseEnd_925393 : Nat := 475171403306203129331701

theorem tailTrace_925393 : CollatzResearch.WordTrace tailWord_925393 prefixEnd_925393 475171403306203129331701 := by
  unfold tailWord_925393
  simp only [CollatzResearch.WordTrace]
  refine ⟨33751855536466680386940833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22501237024311120257960555 33751855536466680386940833)
  ·
    refine ⟨25313891652350010290205625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33751855536466680386940833 25313891652350010290205625)
    ·
      refine ⟨18985418739262507717654219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25313891652350010290205625 18985418739262507717654219)
      ·
        refine ⟨28478128108893761576481329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18985418739262507717654219 28478128108893761576481329)
        ·
          refine ⟨21358596081670321182360997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28478128108893761576481329 21358596081670321182360997)
          ·
            refine ⟨4004736765313185221692687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21358596081670321182360997 4004736765313185221692687)
            ·
              refine ⟨6007105147969777832539031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4004736765313185221692687 6007105147969777832539031)
              ·
                refine ⟨9010657721954666748808547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6007105147969777832539031 9010657721954666748808547)
                ·
                  refine ⟨13515986582932000123212821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9010657721954666748808547 13515986582932000123212821)
                  ·
                    refine ⟨633561871074937505775601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13515986582932000123212821 633561871074937505775601)
                    ·
                      refine ⟨475171403306203129331701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 633561871074937505775601 475171403306203129331701)
                      ·
                        rfl

theorem cell23_925393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 6, 2].length) (baseStart_925393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925393 prefixEnd_925393 := by exact prefixLift 925393
  have htrace : WordTrace (prefixWord ++ tailWord_925393) baseStart_925393 baseEnd_925393 := by
    simpa [prefixWord, tailWord_925393, baseEnd_925393] using wordTrace_append hprefix tailTrace_925393
  have hstable : (prefixWord ++ tailWord_925393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925393).length < 2 ^ (prefixWord ++ tailWord_925393).sum := by decide
  have hdescent : baseEnd_925393 < baseStart_925393 := by decide
  rcases family_descends (prefixWord ++ tailWord_925393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925413 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 1, 4, 3]
def baseStart_925413 : Nat := 118140960795 + 925413 * 2 ^ 59
def prefixEnd_925413 : Nat := 4983230072969 + 3 ^ 40 * 925413 * 2
def baseEnd_925413 : Nat := 475181672919293051081609

theorem tailTrace_925413 : CollatzResearch.WordTrace tailWord_925413 prefixEnd_925413 475181672919293051081609 := by
  unfold tailWord_925413
  simp only [CollatzResearch.WordTrace]
  refine ⟨33752584996394223802668893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22501723330929482535112595 33752584996394223802668893)
  ·
    refine ⟨12657219373647833926000835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33752584996394223802668893 12657219373647833926000835)
    ·
      refine ⟨18985829060471750889001253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12657219373647833926000835 18985829060471750889001253)
      ·
        refine ⟨3559842948838453291687735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18985829060471750889001253 3559842948838453291687735)
        ·
          refine ⟨5339764423257679937531603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3559842948838453291687735 5339764423257679937531603)
          ·
            refine ⟨8009646634886519906297405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5339764423257679937531603 8009646634886519906297405)
            ·
              refine ⟨3003617488082444964861527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8009646634886519906297405 3003617488082444964861527)
              ·
                refine ⟨4505426232123667447292291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3003617488082444964861527 4505426232123667447292291)
                ·
                  refine ⟨6758139348185501170938437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4505426232123667447292291 6758139348185501170938437)
                  ·
                    refine ⟨1267151127784781469550957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6758139348185501170938437 1267151127784781469550957)
                    ·
                      refine ⟨475181672919293051081609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1267151127784781469550957 475181672919293051081609)
                      ·
                        rfl

theorem cell23_925413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_925413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925413 prefixEnd_925413 := by exact prefixLift 925413
  have htrace : WordTrace (prefixWord ++ tailWord_925413) baseStart_925413 baseEnd_925413 := by
    simpa [prefixWord, tailWord_925413, baseEnd_925413] using wordTrace_append hprefix tailTrace_925413
  have hstable : (prefixWord ++ tailWord_925413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925413).length < 2 ^ (prefixWord ++ tailWord_925413).sum := by decide
  have hdescent : baseEnd_925413 < baseStart_925413 := by decide
  rcases family_descends (prefixWord ++ tailWord_925413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925420 : List Nat := [2, 2, 1, 1, 2, 2, 3, 5, 1, 4]
def baseStart_925420 : Nat := 118140960795 + 925420 * 2 ^ 59
def prefixEnd_925420 : Nat := 4983230072969 + 3 ^ 40 * 925420 * 2
def baseEnd_925420 : Nat := 158395089094624841231359

theorem tailTrace_925420 : CollatzResearch.WordTrace tailWord_925420 prefixEnd_925420 158395089094624841231359 := by
  unfold tailWord_925420
  simp only [CollatzResearch.WordTrace]
  refine ⟨16876420153684431999086857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22501893538245909332115809 16876420153684431999086857)
  ·
    refine ⟨12657315115263323999315143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16876420153684431999086857 12657315115263323999315143)
    ·
      refine ⟨18985972672894985998972715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12657315115263323999315143 18985972672894985998972715)
      ·
        refine ⟨28478959009342478998459073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18985972672894985998972715 28478959009342478998459073)
        ·
          refine ⟨21359219257006859248844305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28478959009342478998459073 21359219257006859248844305)
          ·
            refine ⟨16019414442755144436633229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21359219257006859248844305 16019414442755144436633229)
            ·
              refine ⟨6007280416033179163737461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16019414442755144436633229 6007280416033179163737461)
              ·
                refine ⟨563182539003110546600387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6007280416033179163737461 563182539003110546600387)
                ·
                  refine ⟨844773808504665819900581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563182539003110546600387 844773808504665819900581)
                  ·
                    refine ⟨158395089094624841231359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 844773808504665819900581 158395089094624841231359)
                    ·
                      rfl

theorem cell23_925420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_925420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925420 prefixEnd_925420 := by exact prefixLift 925420
  have htrace : WordTrace (prefixWord ++ tailWord_925420) baseStart_925420 baseEnd_925420 := by
    simpa [prefixWord, tailWord_925420, baseEnd_925420] using wordTrace_append hprefix tailTrace_925420
  have hstable : (prefixWord ++ tailWord_925420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925420).length < 2 ^ (prefixWord ++ tailWord_925420).sum := by decide
  have hdescent : baseEnd_925420 < baseStart_925420 := by decide
  rcases family_descends (prefixWord ++ tailWord_925420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925436 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_925436 : Nat := 118140960795 + 925436 * 2 ^ 59
def prefixEnd_925436 : Nat := 4983230072969 + 3 ^ 40 * 925436 * 2
def baseEnd_925436 : Nat := 475193482974346461094003

theorem tailTrace_925436 : CollatzResearch.WordTrace tailWord_925436 prefixEnd_925436 475193482974346461094003 := by
  unfold tailWord_925436
  simp only [CollatzResearch.WordTrace]
  refine ⟨16876711937655449365378081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22502282583540599153837441 16876711937655449365378081)
  ·
    refine ⟨12657533953241587024033561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16876711937655449365378081 12657533953241587024033561)
    ·
      refine ⟨9493150464931190268025171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12657533953241587024033561 9493150464931190268025171)
      ·
        refine ⟨14239725697396785402037757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9493150464931190268025171 14239725697396785402037757)
        ·
          refine ⟨5339897136523794525764159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14239725697396785402037757 5339897136523794525764159)
          ·
            refine ⟨8009845704785691788646239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5339897136523794525764159 8009845704785691788646239)
            ·
              refine ⟨12014768557178537682969359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009845704785691788646239 12014768557178537682969359)
              ·
                refine ⟨18022152835767806524454039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12014768557178537682969359 18022152835767806524454039)
                ·
                  refine ⟨27033229253651709786681059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18022152835767806524454039 27033229253651709786681059)
                  ·
                    refine ⟨40549843880477564680021589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27033229253651709786681059 40549843880477564680021589)
                    ·
                      refine ⟨475193482974346461094003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 40549843880477564680021589 475193482974346461094003)
                      ·
                        rfl

theorem cell23_925436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_925436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925436 prefixEnd_925436 := by exact prefixLift 925436
  have htrace : WordTrace (prefixWord ++ tailWord_925436) baseStart_925436 baseEnd_925436 := by
    simpa [prefixWord, tailWord_925436, baseEnd_925436] using wordTrace_append hprefix tailTrace_925436
  have hstable : (prefixWord ++ tailWord_925436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925436).length < 2 ^ (prefixWord ++ tailWord_925436).sum := by decide
  have hdescent : baseEnd_925436 < baseStart_925436 := by decide
  rcases family_descends (prefixWord ++ tailWord_925436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925450 : List Nat := [3, 1, 2, 2, 1, 4, 3, 1, 6]
def baseStart_925450 : Nat := 118140960795 + 925450 * 2 ^ 59
def prefixEnd_925450 : Nat := 4983230072969 + 3 ^ 40 * 925450 * 2
def baseEnd_925450 : Nat := 52800074633723267368771

theorem tailTrace_925450 : CollatzResearch.WordTrace tailWord_925450 prefixEnd_925450 52800074633723267368771 := by
  unfold tailWord_925450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8438483624315044780441451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22502622998173452747843869 8438483624315044780441451)
  ·
    refine ⟨12657725436472567170662177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8438483624315044780441451 12657725436472567170662177)
    ·
      refine ⟨9493294077354425377996633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12657725436472567170662177 9493294077354425377996633)
      ·
        refine ⟨7119970558015819033497475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9493294077354425377996633 7119970558015819033497475)
        ·
          refine ⟨10679955837023728550246213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7119970558015819033497475 10679955837023728550246213)
          ·
            refine ⟨2002491719441949103171165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10679955837023728550246213 2002491719441949103171165)
            ·
              refine ⟨750934394790730913689187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2002491719441949103171165 750934394790730913689187)
              ·
                refine ⟨1126401592186096370533781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750934394790730913689187 1126401592186096370533781)
                ·
                  refine ⟨52800074633723267368771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1126401592186096370533781 52800074633723267368771)
                  ·
                    rfl

theorem cell23_925450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 6].length) (baseStart_925450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925450 prefixEnd_925450 := by exact prefixLift 925450
  have htrace : WordTrace (prefixWord ++ tailWord_925450) baseStart_925450 baseEnd_925450 := by
    simpa [prefixWord, tailWord_925450, baseEnd_925450] using wordTrace_append hprefix tailTrace_925450
  have hstable : (prefixWord ++ tailWord_925450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925450).length < 2 ^ (prefixWord ++ tailWord_925450).sum := by decide
  have hdescent : baseEnd_925450 < baseStart_925450 := by decide
  rcases family_descends (prefixWord ++ tailWord_925450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925480 : List Nat := [2, 1, 5, 1, 1, 2, 2, 3, 1, 5]
def baseStart_925480 : Nat := 118140960795 + 925480 * 2 ^ 59
def prefixEnd_925480 : Nat := 4983230072969 + 3 ^ 40 * 925480 * 2
def baseEnd_925480 : Nat := 158405358707714762981267

theorem tailTrace_925480 : CollatzResearch.WordTrace tailWord_925480 prefixEnd_925480 158405358707714762981267 := by
  unfold tailWord_925480
  simp only [CollatzResearch.WordTrace]
  refine ⟨16877514343575747122678947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22503352458100996163571929 16877514343575747122678947)
  ·
    refine ⟨25316271515363620684018421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16877514343575747122678947 25316271515363620684018421)
    ·
      refine ⟨2373400454565339439126727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25316271515363620684018421 2373400454565339439126727)
      ·
        refine ⟨3560100681848009158690091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2373400454565339439126727 3560100681848009158690091)
        ·
          refine ⟨5340151022772013738035137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3560100681848009158690091 5340151022772013738035137)
          ·
            refine ⟨4005113267079010303526353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5340151022772013738035137 4005113267079010303526353)
            ·
              refine ⟨3003834950309257727644765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4005113267079010303526353 3003834950309257727644765)
              ·
                refine ⟨1126438106365971647866787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3003834950309257727644765 1126438106365971647866787)
                ·
                  refine ⟨1689657159548957471800181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126438106365971647866787 1689657159548957471800181)
                  ·
                    refine ⟨158405358707714762981267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1689657159548957471800181 158405358707714762981267)
                    ·
                      rfl

theorem cell23_925480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_925480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925480 prefixEnd_925480 := by exact prefixLift 925480
  have htrace : WordTrace (prefixWord ++ tailWord_925480) baseStart_925480 baseEnd_925480 := by
    simpa [prefixWord, tailWord_925480, baseEnd_925480] using wordTrace_append hprefix tailTrace_925480
  have hstable : (prefixWord ++ tailWord_925480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925480).length < 2 ^ (prefixWord ++ tailWord_925480).sum := by decide
  have hdescent : baseEnd_925480 < baseStart_925480 := by decide
  rcases family_descends (prefixWord ++ tailWord_925480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925483 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 4, 6, 2]
def baseStart_925483 : Nat := 118140960795 + 925483 * 2 ^ 59
def prefixEnd_925483 : Nat := 4983230072969 + 3 ^ 40 * 925483 * 2
def baseEnd_925483 : Nat := 475217616565107777206287

theorem tailTrace_925483 : CollatzResearch.WordTrace tailWord_925483 prefixEnd_925483 475217616565107777206287 := by
  unfold tailWord_925483
  simp only [CollatzResearch.WordTrace]
  refine ⟨33755138106140625757717103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22503425404093750505144735 33755138106140625757717103)
  ·
    refine ⟨50632707159210938636575655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33755138106140625757717103 50632707159210938636575655)
    ·
      refine ⟨75949060738816407954863483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50632707159210938636575655 75949060738816407954863483)
      ·
        refine ⟨113923591108224611932295225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75949060738816407954863483 113923591108224611932295225)
        ·
          refine ⟨85442693331168458949221419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113923591108224611932295225 85442693331168458949221419)
          ·
            refine ⟨128164039996752688423832129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85442693331168458949221419 128164039996752688423832129)
            ·
              refine ⟨96123029997564516317874097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128164039996752688423832129 96123029997564516317874097)
              ·
                refine ⟨72092272498173387238405573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96123029997564516317874097 72092272498173387238405573)
                ·
                  refine ⟨13517301093407510107201045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72092272498173387238405573 13517301093407510107201045)
                  ·
                    refine ⟨633623488753477036275049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13517301093407510107201045 633623488753477036275049)
                    ·
                      refine ⟨475217616565107777206287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 633623488753477036275049 475217616565107777206287)
                      ·
                        rfl

theorem cell23_925483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 6, 2].length) (baseStart_925483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925483 prefixEnd_925483 := by exact prefixLift 925483
  have htrace : WordTrace (prefixWord ++ tailWord_925483) baseStart_925483 baseEnd_925483 := by
    simpa [prefixWord, tailWord_925483, baseEnd_925483] using wordTrace_append hprefix tailTrace_925483
  have hstable : (prefixWord ++ tailWord_925483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925483).length < 2 ^ (prefixWord ++ tailWord_925483).sum := by decide
  have hdescent : baseEnd_925483 < baseStart_925483 := by decide
  rcases family_descends (prefixWord ++ tailWord_925483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925494 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_925494 : Nat := 118140960795 + 925494 * 2 ^ 59
def prefixEnd_925494 : Nat := 4983230072969 + 3 ^ 40 * 925494 * 2
def baseEnd_925494 : Nat := 475223264852307234168737

theorem tailTrace_925494 : CollatzResearch.WordTrace tailWord_925494 prefixEnd_925494 475223264852307234168737 := by
  unfold tailWord_925494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2109721206818798414772971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22503692872733849757578357 2109721206818798414772971)
  ·
    refine ⟨3164581810228197622159457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2109721206818798414772971 3164581810228197622159457)
    ·
      refine ⟨2373436357671148216619593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3164581810228197622159457 2373436357671148216619593)
      ·
        refine ⟨1780077268253361162464695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2373436357671148216619593 1780077268253361162464695)
        ·
          refine ⟨2670115902380041743697043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1780077268253361162464695 2670115902380041743697043)
          ·
            refine ⟨4005173853570062615545565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670115902380041743697043 4005173853570062615545565)
            ·
              refine ⟨1501940195088773480829587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4005173853570062615545565 1501940195088773480829587)
              ·
                refine ⟨2252910292633160221244381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501940195088773480829587 2252910292633160221244381)
                ·
                  refine ⟨844841359737435082966643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2252910292633160221244381 844841359737435082966643)
                  ·
                    refine ⟨1267262039606152624449965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 844841359737435082966643 1267262039606152624449965)
                    ·
                      refine ⟨475223264852307234168737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1267262039606152624449965 475223264852307234168737)
                      ·
                        rfl

theorem cell23_925494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_925494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925494 prefixEnd_925494 := by exact prefixLift 925494
  have htrace : WordTrace (prefixWord ++ tailWord_925494) baseStart_925494 baseEnd_925494 := by
    simpa [prefixWord, tailWord_925494, baseEnd_925494] using wordTrace_append hprefix tailTrace_925494
  have hstable : (prefixWord ++ tailWord_925494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925494).length < 2 ^ (prefixWord ++ tailWord_925494).sum := by decide
  have hdescent : baseEnd_925494 < baseStart_925494 := by decide
  rcases family_descends (prefixWord ++ tailWord_925494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925513 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 1, 2, 4]
def baseStart_925513 : Nat := 118140960795 + 925513 * 2 ^ 59
def prefixEnd_925513 : Nat := 4983230072969 + 3 ^ 40 * 925513 * 2
def baseEnd_925513 : Nat := 475233020984742659831149

theorem tailTrace_925513 : CollatzResearch.WordTrace tailWord_925513 prefixEnd_925513 475233020984742659831149 := by
  unfold tailWord_925513
  simp only [CollatzResearch.WordTrace]
  refine ⟨33756232296031940881309193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22504154864021293920872795 33756232296031940881309193)
  ·
    refine ⟨25317174222023955660981895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33756232296031940881309193 25317174222023955660981895)
    ·
      refine ⟨37975761333035933491472843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25317174222023955660981895 37975761333035933491472843)
      ·
        refine ⟨56963641999553900237209265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37975761333035933491472843 56963641999553900237209265)
        ·
          refine ⟨42722731499665425177906949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56963641999553900237209265 42722731499665425177906949)
          ·
            refine ⟨8010512156187267220857553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42722731499665425177906949 8010512156187267220857553)
            ·
              refine ⟨6007884117140450415643165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8010512156187267220857553 6007884117140450415643165)
              ·
                refine ⟨2252956543927668905866187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6007884117140450415643165 2252956543927668905866187)
                ·
                  refine ⟨3379434815891503358799281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2252956543927668905866187 3379434815891503358799281)
                  ·
                    refine ⟨2534576111918627519099461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3379434815891503358799281 2534576111918627519099461)
                    ·
                      refine ⟨475233020984742659831149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2534576111918627519099461 475233020984742659831149)
                      ·
                        rfl

theorem cell23_925513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_925513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925513 prefixEnd_925513 := by exact prefixLift 925513
  have htrace : WordTrace (prefixWord ++ tailWord_925513) baseStart_925513 baseEnd_925513 := by
    simpa [prefixWord, tailWord_925513, baseEnd_925513] using wordTrace_append hprefix tailTrace_925513
  have hstable : (prefixWord ++ tailWord_925513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925513).length < 2 ^ (prefixWord ++ tailWord_925513).sum := by decide
  have hdescent : baseEnd_925513 < baseStart_925513 := by decide
  rcases family_descends (prefixWord ++ tailWord_925513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925517 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_925517 : Nat := 118140960795 + 925517 * 2 ^ 59
def prefixEnd_925517 : Nat := 4983230072969 + 3 ^ 40 * 925517 * 2
def baseEnd_925517 : Nat := 475235074907360644181131

theorem tailTrace_925517 : CollatzResearch.WordTrace tailWord_925517 prefixEnd_925517 475235074907360644181131 := by
  unfold tailWord_925517
  simp only [CollatzResearch.WordTrace]
  refine ⟨33756378188017449564454805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22504252125344966376303203 33756378188017449564454805)
  ·
    refine ⟨1582330227563317948333819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33756378188017449564454805 1582330227563317948333819)
    ·
      refine ⟨2373495341344976922500729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582330227563317948333819 2373495341344976922500729)
      ·
        refine ⟨1780121506008732691875547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2373495341344976922500729 1780121506008732691875547)
        ·
          refine ⟨2670182259013099037813321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1780121506008732691875547 2670182259013099037813321)
          ·
            refine ⟨2002636694259824278359991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2670182259013099037813321 2002636694259824278359991)
            ·
              refine ⟨3003955041389736417539987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002636694259824278359991 3003955041389736417539987)
              ·
                refine ⟨4505932562084604626309981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3003955041389736417539987 4505932562084604626309981)
                ·
                  refine ⟨1689724710781726734866243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4505932562084604626309981 1689724710781726734866243)
                  ·
                    refine ⟨2534587066172590102299365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1689724710781726734866243 2534587066172590102299365)
                    ·
                      refine ⟨475235074907360644181131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2534587066172590102299365 475235074907360644181131)
                      ·
                        rfl

theorem cell23_925517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_925517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925517 prefixEnd_925517 := by exact prefixLift 925517
  have htrace : WordTrace (prefixWord ++ tailWord_925517) baseStart_925517 baseEnd_925517 := by
    simpa [prefixWord, tailWord_925517, baseEnd_925517] using wordTrace_append hprefix tailTrace_925517
  have hstable : (prefixWord ++ tailWord_925517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925517).length < 2 ^ (prefixWord ++ tailWord_925517).sum := by decide
  have hdescent : baseEnd_925517 < baseStart_925517 := by decide
  rcases family_descends (prefixWord ++ tailWord_925517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925537 : List Nat := [1, 2, 3, 1, 1, 1, 7, 1, 1, 2, 3]
def baseStart_925537 : Nat := 118140960795 + 925537 * 2 ^ 59
def prefixEnd_925537 : Nat := 4983230072969 + 3 ^ 40 * 925537 * 2
def baseEnd_925537 : Nat := 475245344520450565931039

theorem tailTrace_925537 : CollatzResearch.WordTrace tailWord_925537 prefixEnd_925537 475245344520450565931039 := by
  unfold tailWord_925537
  simp only [CollatzResearch.WordTrace]
  refine ⟨33757107647944992980182865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22504738431963328653455243 33757107647944992980182865)
  ·
    refine ⟨25317830735958744735137149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33757107647944992980182865 25317830735958744735137149)
    ·
      refine ⟨9494186525984529275676431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25317830735958744735137149 9494186525984529275676431)
      ·
        refine ⟨14241279788976793913514647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9494186525984529275676431 14241279788976793913514647)
        ·
          refine ⟨21361919683465190870271971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14241279788976793913514647 21361919683465190870271971)
          ·
            refine ⟨32042879525197786305407957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21361919683465190870271971 32042879525197786305407957)
            ·
              refine ⟨751004988871823116532999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32042879525197786305407957 751004988871823116532999)
              ·
                refine ⟨1126507483307734674799499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751004988871823116532999 1126507483307734674799499)
                ·
                  refine ⟨1689761224961602012199249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126507483307734674799499 1689761224961602012199249)
                  ·
                    refine ⟨1267320918721201509149437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1689761224961602012199249 1267320918721201509149437)
                    ·
                      refine ⟨475245344520450565931039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1267320918721201509149437 475245344520450565931039)
                      ·
                        rfl

theorem cell23_925537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_925537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925537 prefixEnd_925537 := by exact prefixLift 925537
  have htrace : WordTrace (prefixWord ++ tailWord_925537) baseStart_925537 baseEnd_925537 := by
    simpa [prefixWord, tailWord_925537, baseEnd_925537] using wordTrace_append hprefix tailTrace_925537
  have hstable : (prefixWord ++ tailWord_925537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925537).length < 2 ^ (prefixWord ++ tailWord_925537).sum := by decide
  have hdescent : baseEnd_925537 < baseStart_925537 := by decide
  rcases family_descends (prefixWord ++ tailWord_925537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925573 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_925573 : Nat := 118140960795 + 925573 * 2 ^ 59
def prefixEnd_925573 : Nat := 4983230072969 + 3 ^ 40 * 925573 * 2
def baseEnd_925573 : Nat := 475263829824012425080873

theorem tailTrace_925573 : CollatzResearch.WordTrace tailWord_925573 prefixEnd_925573 475263829824012425080873 := by
  unfold tailWord_925573
  simp only [CollatzResearch.WordTrace]
  refine ⟨33758420675814571128493373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22505613783876380752328915 33758420675814571128493373)
  ·
    refine ⟨12659407753430464173185015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33758420675814571128493373 12659407753430464173185015)
    ·
      refine ⟨18989111630145696259777523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12659407753430464173185015 18989111630145696259777523)
      ·
        refine ⟨28483667445218544389666285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18989111630145696259777523 28483667445218544389666285)
        ·
          refine ⟨10681375291956954146124857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28483667445218544389666285 10681375291956954146124857)
          ·
            refine ⟨8011031468967715609593643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10681375291956954146124857 8011031468967715609593643)
            ·
              refine ⟨12016547203451573414390465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8011031468967715609593643 12016547203451573414390465)
              ·
                refine ⟨9012410402588680060792849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12016547203451573414390465 9012410402588680060792849)
                ·
                  refine ⟨6759307801941510045594637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9012410402588680060792849 6759307801941510045594637)
                  ·
                    refine ⟨2534740425728066267097989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6759307801941510045594637 2534740425728066267097989)
                    ·
                      refine ⟨475263829824012425080873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2534740425728066267097989 475263829824012425080873)
                      ·
                        rfl

theorem cell23_925573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_925573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925573 prefixEnd_925573 := by exact prefixLift 925573
  have htrace : WordTrace (prefixWord ++ tailWord_925573) baseStart_925573 baseEnd_925573 := by
    simpa [prefixWord, tailWord_925573, baseEnd_925573] using wordTrace_append hprefix tailTrace_925573
  have hstable : (prefixWord ++ tailWord_925573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925573).length < 2 ^ (prefixWord ++ tailWord_925573).sum := by decide
  have hdescent : baseEnd_925573 < baseStart_925573 := by decide
  rcases family_descends (prefixWord ++ tailWord_925573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925577 : List Nat := [1, 2, 1, 1, 5, 1, 2, 4, 1, 3, 2]
def baseStart_925577 : Nat := 118140960795 + 925577 * 2 ^ 59
def prefixEnd_925577 : Nat := 4983230072969 + 3 ^ 40 * 925577 * 2
def baseEnd_925577 : Nat := 475265883746630409430855

theorem tailTrace_925577 : CollatzResearch.WordTrace tailWord_925577 prefixEnd_925577 475265883746630409430855 := by
  unfold tailWord_925577
  simp only [CollatzResearch.WordTrace]
  refine ⟨33758566567800079811638985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22505711045200053207759323 33758566567800079811638985)
  ·
    refine ⟨25318924925850059858729239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33758566567800079811638985 25318924925850059858729239)
    ·
      refine ⟨37978387388775089788093859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25318924925850059858729239 37978387388775089788093859)
      ·
        refine ⟨56967581083162634682140789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37978387388775089788093859 56967581083162634682140789)
        ·
          refine ⟨5340710726546497001450699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56967581083162634682140789 5340710726546497001450699)
          ·
            refine ⟨8011066089819745502176049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5340710726546497001450699 8011066089819745502176049)
            ·
              refine ⟨6008299567364809126632037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8011066089819745502176049 6008299567364809126632037)
              ·
                refine ⟨1126556168880901711243507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6008299567364809126632037 1126556168880901711243507)
                ·
                  refine ⟨1689834253321352566865261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126556168880901711243507 1689834253321352566865261)
                  ·
                    refine ⟨633687844995507212574473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1689834253321352566865261 633687844995507212574473)
                    ·
                      refine ⟨475265883746630409430855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 633687844995507212574473 475265883746630409430855)
                      ·
                        rfl

theorem cell23_925577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 3, 2].length) (baseStart_925577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925577 prefixEnd_925577 := by exact prefixLift 925577
  have htrace : WordTrace (prefixWord ++ tailWord_925577) baseStart_925577 baseEnd_925577 := by
    simpa [prefixWord, tailWord_925577, baseEnd_925577] using wordTrace_append hprefix tailTrace_925577
  have hstable : (prefixWord ++ tailWord_925577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925577).length < 2 ^ (prefixWord ++ tailWord_925577).sum := by decide
  have hdescent : baseEnd_925577 < baseStart_925577 := by decide
  rcases family_descends (prefixWord ++ tailWord_925577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925593 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 2, 1, 5]
def baseStart_925593 : Nat := 118140960795 + 925593 * 2 ^ 59
def prefixEnd_925593 : Nat := 4983230072969 + 3 ^ 40 * 925593 * 2
def baseEnd_925593 : Nat := 475274099437102346830781

theorem tailTrace_925593 : CollatzResearch.WordTrace tailWord_925593 prefixEnd_925593 475274099437102346830781 := by
  unfold tailWord_925593
  simp only [CollatzResearch.WordTrace]
  refine ⟨33759150135742114544221433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22506100090494743029480955 33759150135742114544221433)
  ·
    refine ⟨25319362601806585908166075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33759150135742114544221433 25319362601806585908166075)
    ·
      refine ⟨37979043902709878862249113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25319362601806585908166075 37979043902709878862249113)
      ·
        refine ⟨28484282927032409146686835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37979043902709878862249113 28484282927032409146686835)
        ·
          refine ⟨42726424390548613720030253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28484282927032409146686835 42726424390548613720030253)
          ·
            refine ⟨16022409146455730145011345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42726424390548613720030253 16022409146455730145011345)
            ·
              refine ⟨12016806859841797608758509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16022409146455730145011345 12016806859841797608758509)
              ·
                refine ⟨4506302572440674103284441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12016806859841797608758509 4506302572440674103284441)
                ·
                  refine ⟨3379726929330505577463331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4506302572440674103284441 3379726929330505577463331)
                  ·
                    refine ⟨5069590393995758366194997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3379726929330505577463331 5069590393995758366194997)
                    ·
                      refine ⟨475274099437102346830781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5069590393995758366194997 475274099437102346830781)
                      ·
                        rfl

theorem cell23_925593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_925593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925593 prefixEnd_925593 := by exact prefixLift 925593
  have htrace : WordTrace (prefixWord ++ tailWord_925593) baseStart_925593 baseEnd_925593 := by
    simpa [prefixWord, tailWord_925593, baseEnd_925593] using wordTrace_append hprefix tailTrace_925593
  have hstable : (prefixWord ++ tailWord_925593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925593).length < 2 ^ (prefixWord ++ tailWord_925593).sum := by decide
  have hdescent : baseEnd_925593 < baseStart_925593 := by decide
  rcases family_descends (prefixWord ++ tailWord_925593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925594 : List Nat := [3, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2]
def baseStart_925594 : Nat := 118140960795 + 925594 * 2 ^ 59
def prefixEnd_925594 : Nat := 4983230072969 + 3 ^ 40 * 925594 * 2
def baseEnd_925594 : Nat := 475274612917756842918277

theorem tailTrace_925594 : CollatzResearch.WordTrace tailWord_925594 prefixEnd_925594 475274612917756842918277 := by
  unfold tailWord_925594
  simp only [CollatzResearch.WordTrace]
  refine ⟨8439796652184622928751959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22506124405825661143338557 8439796652184622928751959)
  ·
    refine ⟨12659694978276934393127939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8439796652184622928751959 12659694978276934393127939)
    ·
      refine ⟨18989542467415401589691909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12659694978276934393127939 18989542467415401589691909)
      ·
        refine ⟨3560539212640387798067233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18989542467415401589691909 3560539212640387798067233)
        ·
          refine ⟨2670404409480290848550425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3560539212640387798067233 2670404409480290848550425)
          ·
            refine ⟨2002803307110218136412819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2670404409480290848550425 2002803307110218136412819)
            ·
              refine ⟨3004204960665327204619229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002803307110218136412819 3004204960665327204619229)
              ·
                refine ⟨1126576860249497701732211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3004204960665327204619229 1126576860249497701732211)
                ·
                  refine ⟨1689865290374246552598317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126576860249497701732211 1689865290374246552598317)
                  ·
                    refine ⟨633699483890342457224369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1689865290374246552598317 633699483890342457224369)
                    ·
                      refine ⟨475274612917756842918277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 633699483890342457224369 475274612917756842918277)
                      ·
                        rfl

theorem cell23_925594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_925594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925594 prefixEnd_925594 := by exact prefixLift 925594
  have htrace : WordTrace (prefixWord ++ tailWord_925594) baseStart_925594 baseEnd_925594 := by
    simpa [prefixWord, tailWord_925594, baseEnd_925594] using wordTrace_append hprefix tailTrace_925594
  have hstable : (prefixWord ++ tailWord_925594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925594).length < 2 ^ (prefixWord ++ tailWord_925594).sum := by decide
  have hdescent : baseEnd_925594 < baseStart_925594 := by decide
  rcases family_descends (prefixWord ++ tailWord_925594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925601 : List Nat := [1, 2, 3, 4, 2, 2, 1, 2, 2, 1, 3]
def baseStart_925601 : Nat := 118140960795 + 925601 * 2 ^ 59
def prefixEnd_925601 : Nat := 4983230072969 + 3 ^ 40 * 925601 * 2
def baseEnd_925601 : Nat := 475278207282338315530745

theorem tailTrace_925601 : CollatzResearch.WordTrace tailWord_925601 prefixEnd_925601 475278207282338315530745 := by
  unfold tailWord_925601
  simp only [CollatzResearch.WordTrace]
  refine ⟨33759441919713131910512657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22506294613142087940341771 33759441919713131910512657)
  ·
    refine ⟨25319581439784848932884493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33759441919713131910512657 25319581439784848932884493)
    ·
      refine ⟨9494843039919318349831685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25319581439784848932884493 9494843039919318349831685)
      ·
        refine ⟨1780283069984872190593441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9494843039919318349831685 1780283069984872190593441)
        ·
          refine ⟨1335212302488654142945081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1780283069984872190593441 1335212302488654142945081)
          ·
            refine ⟨1001409226866490607208811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335212302488654142945081 1001409226866490607208811)
            ·
              refine ⟨1502113840299735910813217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001409226866490607208811 1502113840299735910813217)
              ·
                refine ⟨1126585380224801933109913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502113840299735910813217 1126585380224801933109913)
                ·
                  refine ⟨844939035168601449832435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1126585380224801933109913 844939035168601449832435)
                  ·
                    refine ⟨1267408552752902174748653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 844939035168601449832435 1267408552752902174748653)
                    ·
                      refine ⟨475278207282338315530745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1267408552752902174748653 475278207282338315530745)
                      ·
                        rfl

theorem cell23_925601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_925601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925601 prefixEnd_925601 := by exact prefixLift 925601
  have htrace : WordTrace (prefixWord ++ tailWord_925601) baseStart_925601 baseEnd_925601 := by
    simpa [prefixWord, tailWord_925601, baseEnd_925601] using wordTrace_append hprefix tailTrace_925601
  have hstable : (prefixWord ++ tailWord_925601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925601).length < 2 ^ (prefixWord ++ tailWord_925601).sum := by decide
  have hdescent : baseEnd_925601 < baseStart_925601 := by decide
  rcases family_descends (prefixWord ++ tailWord_925601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925630 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 7]
def baseStart_925630 : Nat := 118140960795 + 925630 * 2 ^ 59
def prefixEnd_925630 : Nat := 4983230072969 + 3 ^ 40 * 925630 * 2
def baseEnd_925630 : Nat := 52810344246813189118679

theorem tailTrace_925630 : CollatzResearch.WordTrace tailWord_925630 prefixEnd_925630 52810344246813189118679 := by
  unfold tailWord_925630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4220062454576008732914793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22506999757738713242212229 4220062454576008732914793)
  ·
    refine ⟨3165046840932006549686095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4220062454576008732914793 3165046840932006549686095)
    ·
      refine ⟨4747570261398009824529143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3165046840932006549686095 4747570261398009824529143)
      ·
        refine ⟨7121355392097014736793715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4747570261398009824529143 7121355392097014736793715)
        ·
          refine ⟨10682033088145522105190573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7121355392097014736793715 10682033088145522105190573)
          ·
            refine ⟨4005762408054570789446465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10682033088145522105190573 4005762408054570789446465)
            ·
              refine ⟨3004321806040928092084849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4005762408054570789446465 3004321806040928092084849)
              ·
                refine ⟨2253241354530696069063637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3004321806040928092084849 2253241354530696069063637)
                ·
                  refine ⟨52810344246813189118679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2253241354530696069063637 52810344246813189118679)
                  ·
                    rfl

theorem cell23_925630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_925630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925630 prefixEnd_925630 := by exact prefixLift 925630
  have htrace : WordTrace (prefixWord ++ tailWord_925630) baseStart_925630 baseEnd_925630 := by
    simpa [prefixWord, tailWord_925630, baseEnd_925630] using wordTrace_append hprefix tailTrace_925630
  have hstable : (prefixWord ++ tailWord_925630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925630).length < 2 ^ (prefixWord ++ tailWord_925630).sum := by decide
  have hdescent : baseEnd_925630 < baseStart_925630 := by decide
  rcases family_descends (prefixWord ++ tailWord_925630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925643 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 1, 7]
def baseStart_925643 : Nat := 118140960795 + 925643 * 2 ^ 59
def prefixEnd_925643 : Nat := 4983230072969 + 3 ^ 40 * 925643 * 2
def baseEnd_925643 : Nat := 158433257823275717068517

theorem tailTrace_925643 : CollatzResearch.WordTrace tailWord_925643 prefixEnd_925643 158433257823275717068517 := by
  unfold tailWord_925643
  simp only [CollatzResearch.WordTrace]
  refine ⟨33760973785560973083541583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22507315857040648722361055 33760973785560973083541583)
  ·
    refine ⟨50641460678341459625312375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33760973785560973083541583 50641460678341459625312375)
    ·
      refine ⟨75962191017512189437968563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50641460678341459625312375 75962191017512189437968563)
      ·
        refine ⟨113943286526268284156952845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75962191017512189437968563 113943286526268284156952845)
        ·
          refine ⟨42728732447350606558857317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113943286526268284156952845 42728732447350606558857317)
          ·
            refine ⟨8011637333878238729785747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42728732447350606558857317 8011637333878238729785747)
            ·
              refine ⟨12017456000817358094678621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8011637333878238729785747 12017456000817358094678621)
              ·
                refine ⟨4506546000306509285504483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12017456000817358094678621 4506546000306509285504483)
                ·
                  refine ⟨6759819000459763928256725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4506546000306509285504483 6759819000459763928256725)
                  ·
                    refine ⟨158433257823275717068517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6759819000459763928256725 158433257823275717068517)
                    ·
                      rfl

theorem cell23_925643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 7].length) (baseStart_925643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925643 prefixEnd_925643 := by exact prefixLift 925643
  have htrace : WordTrace (prefixWord ++ tailWord_925643) baseStart_925643 baseEnd_925643 := by
    simpa [prefixWord, tailWord_925643, baseEnd_925643] using wordTrace_append hprefix tailTrace_925643
  have hstable : (prefixWord ++ tailWord_925643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925643).length < 2 ^ (prefixWord ++ tailWord_925643).sum := by decide
  have hdescent : baseEnd_925643 < baseStart_925643 := by decide
  rcases family_descends (prefixWord ++ tailWord_925643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925683 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 5]
def baseStart_925683 : Nat := 118140960795 + 925683 * 2 ^ 59
def prefixEnd_925683 : Nat := 4983230072969 + 3 ^ 40 * 925683 * 2
def baseEnd_925683 : Nat := 475320312696006994705367

theorem tailTrace_925683 : CollatzResearch.WordTrace tailWord_925683 prefixEnd_925683 475320312696006994705367 := by
  unfold tailWord_925683
  simp only [CollatzResearch.WordTrace]
  refine ⟨33762432705416059914997703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22508288470277373276665135 33762432705416059914997703)
  ·
    refine ⟨50643649058124089872496555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33762432705416059914997703 50643649058124089872496555)
    ·
      refine ⟨75965473587186134808744833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50643649058124089872496555 75965473587186134808744833)
      ·
        refine ⟨56974105190389601106558625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75965473587186134808744833 56974105190389601106558625)
        ·
          refine ⟨42730578892792200829918969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56974105190389601106558625 42730578892792200829918969)
          ·
            refine ⟨32047934169594150622439227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42730578892792200829918969 32047934169594150622439227)
            ·
              refine ⟨48071901254391225933658841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32047934169594150622439227 48071901254391225933658841)
              ·
                refine ⟨36053925940793419450244131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48071901254391225933658841 36053925940793419450244131)
                ·
                  refine ⟨54080888911190129175366197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36053925940793419450244131 54080888911190129175366197)
                  ·
                    refine ⟨5070083335424074610190581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54080888911190129175366197 5070083335424074610190581)
                    ·
                      refine ⟨475320312696006994705367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5070083335424074610190581 475320312696006994705367)
                      ·
                        rfl

theorem cell23_925683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_925683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925683 prefixEnd_925683 := by exact prefixLift 925683
  have htrace : WordTrace (prefixWord ++ tailWord_925683) baseStart_925683 baseEnd_925683 := by
    simpa [prefixWord, tailWord_925683, baseEnd_925683] using wordTrace_append hprefix tailTrace_925683
  have hstable : (prefixWord ++ tailWord_925683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925683).length < 2 ^ (prefixWord ++ tailWord_925683).sum := by decide
  have hdescent : baseEnd_925683 < baseStart_925683 := by decide
  rcases family_descends (prefixWord ++ tailWord_925683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925694 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_925694 : Nat := 118140960795 + 925694 * 2 ^ 59
def prefixEnd_925694 : Nat := 4983230072969 + 3 ^ 40 * 925694 * 2
def baseEnd_925694 : Nat := 158441986994402150555939

theorem tailTrace_925694 : CollatzResearch.WordTrace tailWord_925694 prefixEnd_925694 158441986994402150555939 := by
  unfold tailWord_925694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4220354238547026099206017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22508555938917472529098757 4220354238547026099206017)
  ·
    refine ⟨3165265678910269574404513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4220354238547026099206017 3165265678910269574404513)
    ·
      refine ⟨2373949259182702180803385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3165265678910269574404513 2373949259182702180803385)
      ·
        refine ⟨1780461944387026635602539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2373949259182702180803385 1780461944387026635602539)
        ·
          refine ⟨2670692916580539953403809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1780461944387026635602539 2670692916580539953403809)
          ·
            refine ⟨2003019687435404965052857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2670692916580539953403809 2003019687435404965052857)
            ·
              refine ⟨1502264765576553723789643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2003019687435404965052857 1502264765576553723789643)
              ·
                refine ⟨2253397148364830585684465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502264765576553723789643 2253397148364830585684465)
                ·
                  refine ⟨1690047861273622939263349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2253397148364830585684465 1690047861273622939263349)
                  ·
                    refine ⟨158441986994402150555939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1690047861273622939263349 158441986994402150555939)
                    ·
                      rfl

theorem cell23_925694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_925694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925694 prefixEnd_925694 := by exact prefixLift 925694
  have htrace : WordTrace (prefixWord ++ tailWord_925694) baseStart_925694 baseEnd_925694 := by
    simpa [prefixWord, tailWord_925694, baseEnd_925694] using wordTrace_append hprefix tailTrace_925694
  have hstable : (prefixWord ++ tailWord_925694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925694).length < 2 ^ (prefixWord ++ tailWord_925694).sum := by decide
  have hdescent : baseEnd_925694 < baseStart_925694 := by decide
  rcases family_descends (prefixWord ++ tailWord_925694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925697 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_925697 : Nat := 118140960795 + 925697 * 2 ^ 59
def prefixEnd_925697 : Nat := 4983230072969 + 3 ^ 40 * 925697 * 2
def baseEnd_925697 : Nat := 475327501425169939930303

theorem tailTrace_925697 : CollatzResearch.WordTrace tailWord_925697 prefixEnd_925697 475327501425169939930303 := by
  unfold tailWord_925697
  simp only [CollatzResearch.WordTrace]
  refine ⟨33762943327365340306007345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22508628884910226870671563 33762943327365340306007345)
  ·
    refine ⟨25322207495524005229505509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33762943327365340306007345 25322207495524005229505509)
    ·
      refine ⟨4747913905410750980532283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25322207495524005229505509 4747913905410750980532283)
      ·
        refine ⟨7121870858116126470798425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4747913905410750980532283 7121870858116126470798425)
        ·
          refine ⟨5341403143587094853098819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7121870858116126470798425 5341403143587094853098819)
          ·
            refine ⟨8012104715380642279648229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5341403143587094853098819 8012104715380642279648229)
            ·
              refine ⟨1502269634133870427434043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8012104715380642279648229 1502269634133870427434043)
              ·
                refine ⟨2253404451200805641151065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502269634133870427434043 2253404451200805641151065)
                ·
                  refine ⟨1690053338400604230863299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2253404451200805641151065 1690053338400604230863299)
                  ·
                    refine ⟨2535080007600906346294949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1690053338400604230863299 2535080007600906346294949)
                    ·
                      refine ⟨475327501425169939930303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2535080007600906346294949 475327501425169939930303)
                      ·
                        rfl

theorem cell23_925697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_925697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925697 prefixEnd_925697 := by exact prefixLift 925697
  have htrace : WordTrace (prefixWord ++ tailWord_925697) baseStart_925697 baseEnd_925697 := by
    simpa [prefixWord, tailWord_925697, baseEnd_925697] using wordTrace_append hprefix tailTrace_925697
  have hstable : (prefixWord ++ tailWord_925697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925697).length < 2 ^ (prefixWord ++ tailWord_925697).sum := by decide
  have hdescent : baseEnd_925697 < baseStart_925697 := by decide
  rcases family_descends (prefixWord ++ tailWord_925697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925710 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_925710 : Nat := 118140960795 + 925710 * 2 ^ 59
def prefixEnd_925710 : Nat := 4983230072969 + 3 ^ 40 * 925710 * 2
def baseEnd_925710 : Nat := 475334176673678389067743

theorem tailTrace_925710 : CollatzResearch.WordTrace tailWord_925710 prefixEnd_925710 475334176673678389067743 := by
  unfold tailWord_925710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4220427184539780440778823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22508944984212162350820389 4220427184539780440778823)
  ·
    refine ⟨6330640776809670661168235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4220427184539780440778823 6330640776809670661168235)
    ·
      refine ⟨9495961165214505991752353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6330640776809670661168235 9495961165214505991752353)
      ·
        refine ⟨7121970873910879493814265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9495961165214505991752353 7121970873910879493814265)
        ·
          refine ⟨5341478155433159620360699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7121970873910879493814265 5341478155433159620360699)
          ·
            refine ⟨8012217233149739430541049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5341478155433159620360699 8012217233149739430541049)
            ·
              refine ⟨6009162924862304572905787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8012217233149739430541049 6009162924862304572905787)
              ·
                refine ⟨9013744387293456859358681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6009162924862304572905787 9013744387293456859358681)
                ·
                  refine ⟨6760308290470092644519011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9013744387293456859358681 6760308290470092644519011)
                  ·
                    refine ⟨10140462435705138966778517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6760308290470092644519011 10140462435705138966778517)
                    ·
                      refine ⟨475334176673678389067743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10140462435705138966778517 475334176673678389067743)
                      ·
                        rfl

theorem cell23_925710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_925710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925710 prefixEnd_925710 := by exact prefixLift 925710
  have htrace : WordTrace (prefixWord ++ tailWord_925710) baseStart_925710 baseEnd_925710 := by
    simpa [prefixWord, tailWord_925710, baseEnd_925710] using wordTrace_append hprefix tailTrace_925710
  have hstable : (prefixWord ++ tailWord_925710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925710).length < 2 ^ (prefixWord ++ tailWord_925710).sum := by decide
  have hdescent : baseEnd_925710 < baseStart_925710 := by decide
  rcases family_descends (prefixWord ++ tailWord_925710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925747 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 5, 1, 3]
def baseStart_925747 : Nat := 118140960795 + 925747 * 2 ^ 59
def prefixEnd_925747 : Nat := 4983230072969 + 3 ^ 40 * 925747 * 2
def baseEnd_925747 : Nat := 475353175457894744305073

theorem tailTrace_925747 : CollatzResearch.WordTrace tailWord_925747 prefixEnd_925747 475353175457894744305073 := by
  unfold tailWord_925747
  simp only [CollatzResearch.WordTrace]
  refine ⟨33764766977184198845327495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22509844651456132563551663 33764766977184198845327495)
  ·
    refine ⟨50647150465776298267991243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33764766977184198845327495 50647150465776298267991243)
    ·
      refine ⟨75970725698664447401986865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50647150465776298267991243 75970725698664447401986865)
      ·
        refine ⟨56978044273998335551490149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75970725698664447401986865 56978044273998335551490149)
        ·
          refine ⟨10683383301374687915904403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56978044273998335551490149 10683383301374687915904403)
          ·
            refine ⟨16025074952062031873856605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10683383301374687915904403 16025074952062031873856605)
            ·
              refine ⟨6009403107023261952696227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16025074952062031873856605 6009403107023261952696227)
              ·
                refine ⟨9014104660534892929044341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6009403107023261952696227 9014104660534892929044341)
                ·
                  refine ⟨845072311925146212097907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9014104660534892929044341 845072311925146212097907)
                  ·
                    refine ⟨1267608467887719318146861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 845072311925146212097907 1267608467887719318146861)
                    ·
                      refine ⟨475353175457894744305073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1267608467887719318146861 475353175457894744305073)
                      ·
                        rfl

theorem cell23_925747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 1, 3].length) (baseStart_925747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925747 prefixEnd_925747 := by exact prefixLift 925747
  have htrace : WordTrace (prefixWord ++ tailWord_925747) baseStart_925747 baseEnd_925747 := by
    simpa [prefixWord, tailWord_925747, baseEnd_925747] using wordTrace_append hprefix tailTrace_925747
  have hstable : (prefixWord ++ tailWord_925747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925747).length < 2 ^ (prefixWord ++ tailWord_925747).sum := by decide
  have hdescent : baseEnd_925747 < baseStart_925747 := by decide
  rcases family_descends (prefixWord ++ tailWord_925747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925748 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_925748 : Nat := 118140960795 + 925748 * 2 ^ 59
def prefixEnd_925748 : Nat := 4983230072969 + 3 ^ 40 * 925748 * 2
def baseEnd_925748 : Nat := 475353688938549240392569

theorem tailTrace_925748 : CollatzResearch.WordTrace tailWord_925748 prefixEnd_925748 475353688938549240392569 := by
  unfold tailWord_925748
  simp only [CollatzResearch.WordTrace]
  refine ⟨16882401725090288008056949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22509868966787050677409265 16882401725090288008056949)
  ·
    refine ⟨1582725161727214500755339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16882401725090288008056949 1582725161727214500755339)
    ·
      refine ⟨2374087742590821751133009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582725161727214500755339 2374087742590821751133009)
      ·
        refine ⟨1780565806943116313349757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2374087742590821751133009 1780565806943116313349757)
        ·
          refine ⟨667712177603668617506159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1780565806943116313349757 667712177603668617506159)
          ·
            refine ⟨1001568266405502926259239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667712177603668617506159 1001568266405502926259239)
            ·
              refine ⟨1502352399608254389388859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001568266405502926259239 1502352399608254389388859)
              ·
                refine ⟨2253528599412381584083289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502352399608254389388859 2253528599412381584083289)
                ·
                  refine ⟨1690146449559286188062467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2253528599412381584083289 1690146449559286188062467)
                  ·
                    refine ⟨2535219674338929282093701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1690146449559286188062467 2535219674338929282093701)
                    ·
                      refine ⟨475353688938549240392569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2535219674338929282093701 475353688938549240392569)
                      ·
                        rfl

theorem cell23_925748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_925748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925748 prefixEnd_925748 := by exact prefixLift 925748
  have htrace : WordTrace (prefixWord ++ tailWord_925748) baseStart_925748 baseEnd_925748 := by
    simpa [prefixWord, tailWord_925748, baseEnd_925748] using wordTrace_append hprefix tailTrace_925748
  have hstable : (prefixWord ++ tailWord_925748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925748).length < 2 ^ (prefixWord ++ tailWord_925748).sum := by decide
  have hdescent : baseEnd_925748 < baseStart_925748 := by decide
  rcases family_descends (prefixWord ++ tailWord_925748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925758 : List Nat := [4, 2, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_925758 : Nat := 118140960795 + 925758 * 2 ^ 59
def prefixEnd_925758 : Nat := 4983230072969 + 3 ^ 40 * 925758 * 2
def baseEnd_925758 : Nat := 158452941248364733755841

theorem tailTrace_925758 : CollatzResearch.WordTrace tailWord_925758 prefixEnd_925758 158452941248364733755841 := by
  unfold tailWord_925758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4220646022518043465497241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22510112120096231815985285 4220646022518043465497241)
  ·
    refine ⟨3165484516888532599122931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4220646022518043465497241 3165484516888532599122931)
    ·
      refine ⟨4748226775332798898684397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3165484516888532599122931 4748226775332798898684397)
      ·
        refine ⟨1780585040749799587006649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4748226775332798898684397 1780585040749799587006649)
        ·
          refine ⟨1335438780562349690254987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1780585040749799587006649 1335438780562349690254987)
          ·
            refine ⟨2003158170843524535382481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335438780562349690254987 2003158170843524535382481)
            ·
              refine ⟨1502368628132643401536861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2003158170843524535382481 1502368628132643401536861)
              ·
                refine ⟨563388235549741275576323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1502368628132643401536861 563388235549741275576323)
                ·
                  refine ⟨845082353324611913364485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563388235549741275576323 845082353324611913364485)
                  ·
                    refine ⟨158452941248364733755841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 845082353324611913364485 158452941248364733755841)
                    ·
                      rfl

theorem cell23_925758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_925758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925758 prefixEnd_925758 := by exact prefixLift 925758
  have htrace : WordTrace (prefixWord ++ tailWord_925758) baseStart_925758 baseEnd_925758 := by
    simpa [prefixWord, tailWord_925758, baseEnd_925758] using wordTrace_append hprefix tailTrace_925758
  have hstable : (prefixWord ++ tailWord_925758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925758).length < 2 ^ (prefixWord ++ tailWord_925758).sum := by decide
  have hdescent : baseEnd_925758 < baseStart_925758 := by decide
  rcases family_descends (prefixWord ++ tailWord_925758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925767 : List Nat := [1, 1, 4, 1, 3, 1, 3, 3, 1, 5]
def baseStart_925767 : Nat := 118140960795 + 925767 * 2 ^ 59
def prefixEnd_925767 : Nat := 4983230072969 + 3 ^ 40 * 925767 * 2
def baseEnd_925767 : Nat := 158454481690328222018327

theorem tailTrace_925767 : CollatzResearch.WordTrace tailWord_925767 prefixEnd_925767 158454481690328222018327 := by
  unfold tailWord_925767
  simp only [CollatzResearch.WordTrace]
  refine ⟨33765496437111742261055555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22510330958074494840703703 33765496437111742261055555)
  ·
    refine ⟨50648244655667613391583333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33765496437111742261055555 50648244655667613391583333)
    ·
      refine ⟨9496545872937677510921875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50648244655667613391583333 9496545872937677510921875)
      ·
        refine ⟨14244818809406516266382813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9496545872937677510921875 14244818809406516266382813)
        ·
          refine ⟨5341807053527443599893555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14244818809406516266382813 5341807053527443599893555)
          ·
            refine ⟨8012710580291165399840333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5341807053527443599893555 8012710580291165399840333)
            ·
              refine ⟨3004766467609187024940125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8012710580291165399840333 3004766467609187024940125)
              ·
                refine ⟨1126787425353445134352547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3004766467609187024940125 1126787425353445134352547)
                ·
                  refine ⟨1690181138030167701528821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126787425353445134352547 1690181138030167701528821)
                  ·
                    refine ⟨158454481690328222018327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1690181138030167701528821 158454481690328222018327)
                    ·
                      rfl

theorem cell23_925767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_925767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925767 prefixEnd_925767 := by exact prefixLift 925767
  have htrace : WordTrace (prefixWord ++ tailWord_925767) baseStart_925767 baseEnd_925767 := by
    simpa [prefixWord, tailWord_925767, baseEnd_925767] using wordTrace_append hprefix tailTrace_925767
  have hstable : (prefixWord ++ tailWord_925767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925767).length < 2 ^ (prefixWord ++ tailWord_925767).sum := by decide
  have hdescent : baseEnd_925767 < baseStart_925767 := by decide
  rcases family_descends (prefixWord ++ tailWord_925767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925781 : List Nat := [1, 3, 2, 2, 1, 3, 2, 4, 1, 1, 3]
def baseStart_925781 : Nat := 118140960795 + 925781 * 2 ^ 59
def prefixEnd_925781 : Nat := 4983230072969 + 3 ^ 40 * 925781 * 2
def baseEnd_925781 : Nat := 475370633800147611279917

theorem tailTrace_925781 : CollatzResearch.WordTrace tailWord_925781 prefixEnd_925781 475370633800147611279917 := by
  unfold tailWord_925781
  simp only [CollatzResearch.WordTrace]
  refine ⟨33766007059061022652065197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22510671372707348434710131 33766007059061022652065197)
  ·
    refine ⟨12662252647147883494524449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33766007059061022652065197 12662252647147883494524449)
    ·
      refine ⟨9496689485360912620893337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12662252647147883494524449 9496689485360912620893337)
      ·
        refine ⟨7122517114020684465670003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9496689485360912620893337 7122517114020684465670003)
        ·
          refine ⟨10683775671031026698505005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7122517114020684465670003 10683775671031026698505005)
          ·
            refine ⟨4006415876636635011939377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10683775671031026698505005 4006415876636635011939377)
            ·
              refine ⟨3004811907477476258954533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4006415876636635011939377 3004811907477476258954533)
              ·
                refine ⟨563402232652026798553975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3004811907477476258954533 563402232652026798553975)
                ·
                  refine ⟨845103348978040197830963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563402232652026798553975 845103348978040197830963)
                  ·
                    refine ⟨1267655023467060296746445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 845103348978040197830963 1267655023467060296746445)
                    ·
                      refine ⟨475370633800147611279917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1267655023467060296746445 475370633800147611279917)
                      ·
                        rfl

theorem cell23_925781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_925781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925781 prefixEnd_925781 := by exact prefixLift 925781
  have htrace : WordTrace (prefixWord ++ tailWord_925781) baseStart_925781 baseEnd_925781 := by
    simpa [prefixWord, tailWord_925781, baseEnd_925781] using wordTrace_append hprefix tailTrace_925781
  have hstable : (prefixWord ++ tailWord_925781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925781).length < 2 ^ (prefixWord ++ tailWord_925781).sum := by decide
  have hdescent : baseEnd_925781 < baseStart_925781 := by decide
  rcases family_descends (prefixWord ++ tailWord_925781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925797 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 1, 6]
def baseStart_925797 : Nat := 118140960795 + 925797 * 2 ^ 59
def prefixEnd_925797 : Nat := 4983230072969 + 3 ^ 40 * 925797 * 2
def baseEnd_925797 : Nat := 158459616496873182893281

theorem tailTrace_925797 : CollatzResearch.WordTrace tailWord_925797 prefixEnd_925797 158459616496873182893281 := by
  unfold tailWord_925797
  simp only [CollatzResearch.WordTrace]
  refine ⟨33766590627003057384647645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22511060418002038256431763 33766590627003057384647645)
  ·
    refine ⟨12662471485126146519242867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33766590627003057384647645 12662471485126146519242867)
    ·
      refine ⟨18993707227689219778864301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12662471485126146519242867 18993707227689219778864301)
      ·
        refine ⟨7122640210383457417074113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18993707227689219778864301 7122640210383457417074113)
        ·
          refine ⟨5341980157787593062805585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7122640210383457417074113 5341980157787593062805585)
          ·
            refine ⟨4006485118340694797104189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5341980157787593062805585 4006485118340694797104189)
            ·
              refine ⟨1502431919377760548914071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4006485118340694797104189 1502431919377760548914071)
              ·
                refine ⟨2253647879066640823371107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502431919377760548914071 2253647879066640823371107)
                ·
                  refine ⟨3380471818599961235056661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2253647879066640823371107 3380471818599961235056661)
                  ·
                    refine ⟨158459616496873182893281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3380471818599961235056661 158459616496873182893281)
                    ·
                      rfl

theorem cell23_925797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_925797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925797 prefixEnd_925797 := by exact prefixLift 925797
  have htrace : WordTrace (prefixWord ++ tailWord_925797) baseStart_925797 baseEnd_925797 := by
    simpa [prefixWord, tailWord_925797, baseEnd_925797] using wordTrace_append hprefix tailTrace_925797
  have hstable : (prefixWord ++ tailWord_925797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925797).length < 2 ^ (prefixWord ++ tailWord_925797).sum := by decide
  have hdescent : baseEnd_925797 < baseStart_925797 := by decide
  rcases family_descends (prefixWord ++ tailWord_925797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925804 : List Nat := [2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 4]
def baseStart_925804 : Nat := 118140960795 + 925804 * 2 ^ 59
def prefixEnd_925804 : Nat := 4983230072969 + 3 ^ 40 * 925804 * 2
def baseEnd_925804 : Nat := 475382443855201021292311

theorem tailTrace_925804 : CollatzResearch.WordTrace tailWord_925804 prefixEnd_925804 475382443855201021292311 := by
  unfold tailWord_925804
  simp only [CollatzResearch.WordTrace]
  refine ⟨16883422968988848790076233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22511230625318465053434977 16883422968988848790076233)
  ·
    refine ⟨12662567226741636592557175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16883422968988848790076233 12662567226741636592557175)
    ·
      refine ⟨18993850840112454888835763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12662567226741636592557175 18993850840112454888835763)
      ·
        refine ⟨28490776260168682333253645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18993850840112454888835763 28490776260168682333253645)
        ·
          refine ⟨10684041097563255874970117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28490776260168682333253645 10684041097563255874970117)
          ·
            refine ⟨2003257705793110476556897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10684041097563255874970117 2003257705793110476556897)
            ·
              refine ⟨1502443279344832857417673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2003257705793110476556897 1502443279344832857417673)
              ·
                refine ⟨1126832459508624643063255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502443279344832857417673 1126832459508624643063255)
                ·
                  refine ⟨1690248689262936964594883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126832459508624643063255 1690248689262936964594883)
                  ·
                    refine ⟨2535373033894405446892325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1690248689262936964594883 2535373033894405446892325)
                    ·
                      refine ⟨475382443855201021292311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2535373033894405446892325 475382443855201021292311)
                      ·
                        rfl

theorem cell23_925804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_925804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925804 prefixEnd_925804 := by exact prefixLift 925804
  have htrace : WordTrace (prefixWord ++ tailWord_925804) baseStart_925804 baseEnd_925804 := by
    simpa [prefixWord, tailWord_925804, baseEnd_925804] using wordTrace_append hprefix tailTrace_925804
  have hstable : (prefixWord ++ tailWord_925804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925804).length < 2 ^ (prefixWord ++ tailWord_925804).sum := by decide
  have hdescent : baseEnd_925804 < baseStart_925804 := by decide
  rcases family_descends (prefixWord ++ tailWord_925804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925814 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_925814 : Nat := 118140960795 + 925814 * 2 ^ 59
def prefixEnd_925814 : Nat := 4983230072969 + 3 ^ 40 * 925814 * 2
def baseEnd_925814 : Nat := 158462526220581994055755

theorem tailTrace_925814 : CollatzResearch.WordTrace tailWord_925814 prefixEnd_925814 158462526220581994055755 := by
  unfold tailWord_925814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110450666746341830501031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22511473778627646192010997 2110450666746341830501031)
  ·
    refine ⟨3165676000119512745751547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2110450666746341830501031 3165676000119512745751547)
    ·
      refine ⟨4748514000179269118627321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3165676000119512745751547 4748514000179269118627321)
      ·
        refine ⟨3561385500134451838970491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4748514000179269118627321 3561385500134451838970491)
        ·
          refine ⟨5342078250201677758455737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561385500134451838970491 5342078250201677758455737)
          ·
            refine ⟨4006558687651258318841803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5342078250201677758455737 4006558687651258318841803)
            ·
              refine ⟨6009838031476887478262705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4006558687651258318841803 6009838031476887478262705)
              ·
                refine ⟨4507378523607665608697029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6009838031476887478262705 4507378523607665608697029)
                ·
                  refine ⟨845133473176437301630693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4507378523607665608697029 845133473176437301630693)
                  ·
                    refine ⟨158462526220581994055755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 845133473176437301630693 158462526220581994055755)
                    ·
                      rfl

theorem cell23_925814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_925814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925814 prefixEnd_925814 := by exact prefixLift 925814
  have htrace : WordTrace (prefixWord ++ tailWord_925814) baseStart_925814 baseEnd_925814 := by
    simpa [prefixWord, tailWord_925814, baseEnd_925814] using wordTrace_append hprefix tailTrace_925814
  have hstable : (prefixWord ++ tailWord_925814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925814).length < 2 ^ (prefixWord ++ tailWord_925814).sum := by decide
  have hdescent : baseEnd_925814 < baseStart_925814 := by decide
  rcases family_descends (prefixWord ++ tailWord_925814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925840 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 2, 7]
def baseStart_925840 : Nat := 118140960795 + 925840 * 2 ^ 59
def prefixEnd_925840 : Nat := 4983230072969 + 3 ^ 40 * 925840 * 2
def baseEnd_925840 : Nat := 158466976386254293480715

theorem tailTrace_925840 : CollatzResearch.WordTrace tailWord_925840 prefixEnd_925840 158466976386254293480715 := by
  unfold tailWord_925840
  simp only [CollatzResearch.WordTrace]
  refine ⟨16884079482923637864231487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22512105977231517152308649 16884079482923637864231487)
  ·
    refine ⟨25326119224385456796347231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16884079482923637864231487 25326119224385456796347231)
    ·
      refine ⟨37989178836578185194520847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25326119224385456796347231 37989178836578185194520847)
      ·
        refine ⟨56983768254867277791781271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37989178836578185194520847 56983768254867277791781271)
        ·
          refine ⟨85475652382300916687671907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56983768254867277791781271 85475652382300916687671907)
          ·
            refine ⟨128213478573451375031507861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85475652382300916687671907 128213478573451375031507861)
            ·
              refine ⟨6010006808130533204601931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128213478573451375031507861 6010006808130533204601931)
              ·
                refine ⟨9015010212195799806902897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6010006808130533204601931 9015010212195799806902897)
                ·
                  refine ⟨6761257659146849855177173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9015010212195799806902897 6761257659146849855177173)
                  ·
                    refine ⟨158466976386254293480715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6761257659146849855177173 158466976386254293480715)
                    ·
                      rfl

theorem cell23_925840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_925840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925840 prefixEnd_925840 := by exact prefixLift 925840
  have htrace : WordTrace (prefixWord ++ tailWord_925840) baseStart_925840 baseEnd_925840 := by
    simpa [prefixWord, tailWord_925840, baseEnd_925840] using wordTrace_append hprefix tailTrace_925840
  have hstable : (prefixWord ++ tailWord_925840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925840).length < 2 ^ (prefixWord ++ tailWord_925840).sum := by decide
  have hdescent : baseEnd_925840 < baseStart_925840 := by decide
  rcases family_descends (prefixWord ++ tailWord_925840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925848 : List Nat := [2, 1, 2, 4, 3, 2, 2, 1, 2, 4]
def baseStart_925848 : Nat := 118140960795 + 925848 * 2 ^ 59
def prefixEnd_925848 : Nat := 4983230072969 + 3 ^ 40 * 925848 * 2
def baseEnd_925848 : Nat := 158468345667999616380703

theorem tailTrace_925848 : CollatzResearch.WordTrace tailWord_925848 prefixEnd_925848 158468345667999616380703 := by
  unfold tailWord_925848
  simp only [CollatzResearch.WordTrace]
  refine ⟨16884225374909146547377099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22512300499878862063169465 16884225374909146547377099)
  ·
    refine ⟨25326338062363719821065649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16884225374909146547377099 25326338062363719821065649)
    ·
      refine ⟨18994753546772789865799237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25326338062363719821065649 18994753546772789865799237)
      ·
        refine ⟨3561516290019898099837357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18994753546772789865799237 3561516290019898099837357)
        ·
          refine ⟨1335568608757461787439009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3561516290019898099837357 1335568608757461787439009)
          ·
            refine ⟨1001676456568096340579257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335568608757461787439009 1001676456568096340579257)
            ·
              refine ⟨751257342426072255434443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1001676456568096340579257 751257342426072255434443)
              ·
                refine ⟨1126886013639108383151665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751257342426072255434443 1126886013639108383151665)
                ·
                  refine ⟨845164510229331287363749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1126886013639108383151665 845164510229331287363749)
                  ·
                    refine ⟨158468345667999616380703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 845164510229331287363749 158468345667999616380703)
                    ·
                      rfl

theorem cell23_925848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_925848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925848 prefixEnd_925848 := by exact prefixLift 925848
  have htrace : WordTrace (prefixWord ++ tailWord_925848) baseStart_925848 baseEnd_925848 := by
    simpa [prefixWord, tailWord_925848, baseEnd_925848] using wordTrace_append hprefix tailTrace_925848
  have hstable : (prefixWord ++ tailWord_925848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925848).length < 2 ^ (prefixWord ++ tailWord_925848).sum := by decide
  have hdescent : baseEnd_925848 < baseStart_925848 := by decide
  rcases family_descends (prefixWord ++ tailWord_925848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925858 : List Nat := [3, 3, 1, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_925858 : Nat := 118140960795 + 925858 * 2 ^ 59
def prefixEnd_925858 : Nat := 4983230072969 + 3 ^ 40 * 925858 * 2
def baseEnd_925858 : Nat := 475410171810543810017063

theorem tailTrace_925858 : CollatzResearch.WordTrace tailWord_925858 prefixEnd_925858 475410171810543810017063 := by
  unfold tailWord_925858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8442203869945516200654557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22512543653188043201745485 8442203869945516200654557)
  ·
    refine ⟨3165826451229568575245459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8442203869945516200654557 3165826451229568575245459)
    ·
      refine ⟨4748739676844352862868189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3165826451229568575245459 4748739676844352862868189)
      ·
        refine ⟨1780777378816632323575571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4748739676844352862868189 1780777378816632323575571)
        ·
          refine ⟨2671166068224948485363357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1780777378816632323575571 2671166068224948485363357)
          ·
            refine ⟨1001687275584355682011259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2671166068224948485363357 1001687275584355682011259)
            ·
              refine ⟨1502530913376533523016889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001687275584355682011259 1502530913376533523016889)
              ·
                refine ⟨1126898185032400142262667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502530913376533523016889 1126898185032400142262667)
                ·
                  refine ⟨1690347277548600213394001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1126898185032400142262667 1690347277548600213394001)
                  ·
                    refine ⟨1267760458161450160045501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1690347277548600213394001 1267760458161450160045501)
                    ·
                      refine ⟨475410171810543810017063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1267760458161450160045501 475410171810543810017063)
                      ·
                        rfl

theorem cell23_925858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_925858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925858 prefixEnd_925858 := by exact prefixLift 925858
  have htrace : WordTrace (prefixWord ++ tailWord_925858) baseStart_925858 baseEnd_925858 := by
    simpa [prefixWord, tailWord_925858, baseEnd_925858] using wordTrace_append hprefix tailTrace_925858
  have hstable : (prefixWord ++ tailWord_925858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925858).length < 2 ^ (prefixWord ++ tailWord_925858).sum := by decide
  have hdescent : baseEnd_925858 < baseStart_925858 := by decide
  rcases family_descends (prefixWord ++ tailWord_925858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925889 : List Nat := [1, 2, 6, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_925889 : Nat := 118140960795 + 925889 * 2 ^ 59
def prefixEnd_925889 : Nat := 4983230072969 + 3 ^ 40 * 925889 * 2
def baseEnd_925889 : Nat := 475426089710833188729421

theorem tailTrace_925889 : CollatzResearch.WordTrace tailWord_925889 prefixEnd_925889 475426089710833188729421 := by
  unfold tailWord_925889
  simp only [CollatzResearch.WordTrace]
  refine ⟨33769946142669757096996721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22513297428446504731331147 33769946142669757096996721)
  ·
    refine ⟨25327459607002317822747541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33769946142669757096996721 25327459607002317822747541)
    ·
      refine ⟨1187224669078233647941291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25327459607002317822747541 1187224669078233647941291)
      ·
        refine ⟨1780837003617350471911937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1187224669078233647941291 1780837003617350471911937)
        ·
          refine ⟨1335627752713012853933953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1780837003617350471911937 1335627752713012853933953)
          ·
            refine ⟨1001720814534759640450465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335627752713012853933953 1001720814534759640450465)
            ·
              refine ⟨751290610901069730337849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1001720814534759640450465 751290610901069730337849)
              ·
                refine ⟨563467958175802297753387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751290610901069730337849 563467958175802297753387)
                ·
                  refine ⟨845201937263703446630081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563467958175802297753387 845201937263703446630081)
                  ·
                    refine ⟨633901452947777584972561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 845201937263703446630081 633901452947777584972561)
                    ·
                      refine ⟨475426089710833188729421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 633901452947777584972561 475426089710833188729421)
                      ·
                        rfl

theorem cell23_925889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_925889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925889 prefixEnd_925889 := by exact prefixLift 925889
  have htrace : WordTrace (prefixWord ++ tailWord_925889) baseStart_925889 baseEnd_925889 := by
    simpa [prefixWord, tailWord_925889, baseEnd_925889] using wordTrace_append hprefix tailTrace_925889
  have hstable : (prefixWord ++ tailWord_925889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925889).length < 2 ^ (prefixWord ++ tailWord_925889).sum := by decide
  have hdescent : baseEnd_925889 < baseStart_925889 := by decide
  rcases family_descends (prefixWord ++ tailWord_925889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925984 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 4]
def baseStart_925984 : Nat := 118140960795 + 925984 * 2 ^ 59
def prefixEnd_925984 : Nat := 4983230072969 + 3 ^ 40 * 925984 * 2
def baseEnd_925984 : Nat := 475474870373010317041483

theorem tailTrace_925984 : CollatzResearch.WordTrace tailWord_925984 prefixEnd_925984 475474870373010317041483 := by
  unfold tailWord_925984
  simp only [CollatzResearch.WordTrace]
  refine ⟨16886705538662794160852503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22515607384883725547803337 16886705538662794160852503)
  ·
    refine ⟨25330058307994191241278755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16886705538662794160852503 25330058307994191241278755)
    ·
      refine ⟨37995087461991286861918133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25330058307994191241278755 37995087461991286861918133)
      ·
        refine ⟨3562039449561683143304825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37995087461991286861918133 3562039449561683143304825)
        ·
          refine ⟨2671529587171262357478619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3562039449561683143304825 2671529587171262357478619)
          ·
            refine ⟨4007294380756893536217929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671529587171262357478619 4007294380756893536217929)
            ·
              refine ⟨3005470785567670152163447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4007294380756893536217929 3005470785567670152163447)
              ·
                refine ⟨4508206178351505228245171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3005470785567670152163447 4508206178351505228245171)
                ·
                  refine ⟨6762309267527257842367757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4508206178351505228245171 6762309267527257842367757)
                  ·
                    refine ⟨2535865975322721690887909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6762309267527257842367757 2535865975322721690887909)
                    ·
                      refine ⟨475474870373010317041483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2535865975322721690887909 475474870373010317041483)
                      ·
                        rfl

theorem cell23_925984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_925984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925984 prefixEnd_925984 := by exact prefixLift 925984
  have htrace : WordTrace (prefixWord ++ tailWord_925984) baseStart_925984 baseEnd_925984 := by
    simpa [prefixWord, tailWord_925984, baseEnd_925984] using wordTrace_append hprefix tailTrace_925984
  have hstable : (prefixWord ++ tailWord_925984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925984).length < 2 ^ (prefixWord ++ tailWord_925984).sum := by decide
  have hdescent : baseEnd_925984 < baseStart_925984 := by decide
  rcases family_descends (prefixWord ++ tailWord_925984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925998 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_925998 : Nat := 118140960795 + 925998 * 2 ^ 59
def prefixEnd_925998 : Nat := 4983230072969 + 3 ^ 40 * 925998 * 2
def baseEnd_925998 : Nat := 158494019700724420755473

theorem tailTrace_925998 : CollatzResearch.WordTrace tailWord_925998 prefixEnd_925998 158494019700724420755473 := by
  unfold tailWord_925998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4221740212409358589089331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22515947799516579141809765 4221740212409358589089331)
  ·
    refine ⟨6332610318614037883633997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4221740212409358589089331 6332610318614037883633997)
    ·
      refine ⟨2374728869480264206362749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6332610318614037883633997 2374728869480264206362749)
      ·
        refine ⟨890523326055099077386031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2374728869480264206362749 890523326055099077386031)
        ·
          refine ⟨1335784989082648616079047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890523326055099077386031 1335784989082648616079047)
          ·
            refine ⟨2003677483623972924118571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335784989082648616079047 2003677483623972924118571)
            ·
              refine ⟨3005516225435959386177857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003677483623972924118571 3005516225435959386177857)
              ·
                refine ⟨2254137169076969539633393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3005516225435959386177857 2254137169076969539633393)
                ·
                  refine ⟨1690602876807727154725045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2254137169076969539633393 1690602876807727154725045)
                  ·
                    refine ⟨158494019700724420755473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1690602876807727154725045 158494019700724420755473)
                    ·
                      rfl

theorem cell23_925998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_925998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_925998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_925998 prefixEnd_925998 := by exact prefixLift 925998
  have htrace : WordTrace (prefixWord ++ tailWord_925998) baseStart_925998 baseEnd_925998 := by
    simpa [prefixWord, tailWord_925998, baseEnd_925998] using wordTrace_append hprefix tailTrace_925998
  have hstable : (prefixWord ++ tailWord_925998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925998).length < 2 ^ (prefixWord ++ tailWord_925998).sum := by decide
  have hdescent : baseEnd_925998 < baseStart_925998 := by decide
  rcases family_descends (prefixWord ++ tailWord_925998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926001 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 2, 1, 4]
def baseStart_926001 : Nat := 118140960795 + 926001 * 2 ^ 59
def prefixEnd_926001 : Nat := 4983230072969 + 3 ^ 40 * 926001 * 2
def baseEnd_926001 : Nat := 475483599544136750528905

theorem tailTrace_926001 : CollatzResearch.WordTrace tailWord_926001 prefixEnd_926001 475483599544136750528905 := by
  unfold tailWord_926001
  simp only [CollatzResearch.WordTrace]
  refine ⟨33774031118264000225073857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22516020745509333483382571 33774031118264000225073857)
  ·
    refine ⟨25330523338698000168805393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33774031118264000225073857 25330523338698000168805393)
    ·
      refine ⟨18997892504023500126604045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25330523338698000168805393 18997892504023500126604045)
      ·
        refine ⟨7124209689008812547476517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18997892504023500126604045 7124209689008812547476517)
        ·
          refine ⟨1335789316689152352651847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7124209689008812547476517 1335789316689152352651847)
          ·
            refine ⟨2003683975033728528977771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335789316689152352651847 2003683975033728528977771)
            ·
              refine ⟨3005525962550592793466657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003683975033728528977771 3005525962550592793466657)
              ·
                refine ⟨2254144471912944595099993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3005525962550592793466657 2254144471912944595099993)
                ·
                  refine ⟨1690608353934708446324995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2254144471912944595099993 1690608353934708446324995)
                  ·
                    refine ⟨2535912530902062669487493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1690608353934708446324995 2535912530902062669487493)
                    ·
                      refine ⟨475483599544136750528905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2535912530902062669487493 475483599544136750528905)
                      ·
                        rfl

theorem cell23_926001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_926001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926001 prefixEnd_926001 := by exact prefixLift 926001
  have htrace : WordTrace (prefixWord ++ tailWord_926001) baseStart_926001 baseEnd_926001 := by
    simpa [prefixWord, tailWord_926001, baseEnd_926001] using wordTrace_append hprefix tailTrace_926001
  have hstable : (prefixWord ++ tailWord_926001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926001).length < 2 ^ (prefixWord ++ tailWord_926001).sum := by decide
  have hdescent : baseEnd_926001 < baseStart_926001 := by decide
  rcases family_descends (prefixWord ++ tailWord_926001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926034 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_926034 : Nat := 118140960795 + 926034 * 2 ^ 59
def prefixEnd_926034 : Nat := 4983230072969 + 3 ^ 40 * 926034 * 2
def baseEnd_926034 : Nat := 475500544405735121416253

theorem tailTrace_926034 : CollatzResearch.WordTrace tailWord_926034 prefixEnd_926034 475500544405735121416253 := by
  unfold tailWord_926034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8443808681786111715256289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22516823151429631240683437 8443808681786111715256289)
  ·
    refine ⟨6332856511339583786442217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8443808681786111715256289 6332856511339583786442217)
    ·
      refine ⟨4749642383504687839831663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6332856511339583786442217 4749642383504687839831663)
      ·
        refine ⟨7124463575257031759747495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4749642383504687839831663 7124463575257031759747495)
        ·
          refine ⟨10686695362885547639621243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7124463575257031759747495 10686695362885547639621243)
          ·
            refine ⟨16030043044328321459431865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10686695362885547639621243 16030043044328321459431865)
            ·
              refine ⟨12022532283246241094573899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16030043044328321459431865 12022532283246241094573899)
              ·
                refine ⟨18033798424869361641860849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12022532283246241094573899 18033798424869361641860849)
                ·
                  refine ⟨13525348818652021231395637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18033798424869361641860849 13525348818652021231395637)
                  ·
                    refine ⟨1268001451748626990443341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13525348818652021231395637 1268001451748626990443341)
                    ·
                      refine ⟨475500544405735121416253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1268001451748626990443341 475500544405735121416253)
                      ·
                        rfl

theorem cell23_926034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_926034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926034 prefixEnd_926034 := by exact prefixLift 926034
  have htrace : WordTrace (prefixWord ++ tailWord_926034) baseStart_926034 baseEnd_926034 := by
    simpa [prefixWord, tailWord_926034, baseEnd_926034] using wordTrace_append hprefix tailTrace_926034
  have hstable : (prefixWord ++ tailWord_926034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926034).length < 2 ^ (prefixWord ++ tailWord_926034).sum := by decide
  have hdescent : baseEnd_926034 < baseStart_926034 := by decide
  rcases family_descends (prefixWord ++ tailWord_926034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926114 : List Nat := [3, 3, 1, 2, 1, 1, 12]
def baseStart_926114 : Nat := 118140960795 + 926114 * 2 ^ 59
def prefixEnd_926114 : Nat := 4983230072969 + 3 ^ 40 * 926114 * 2
def baseEnd_926114 : Nat := 5870884232815985289085

theorem tailTrace_926114 : CollatzResearch.WordTrace tailWord_926114 prefixEnd_926114 5870884232815985289085 := by
  unfold tailWord_926114
  simp only [CollatzResearch.WordTrace]
  refine ⟨8444538141713655130984349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22518768377903080349291597 8444538141713655130984349)
  ·
    refine ⟨3166701803142620674119131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8444538141713655130984349 3166701803142620674119131)
    ·
      refine ⟨4750052704713931011178697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3166701803142620674119131 4750052704713931011178697)
      ·
        refine ⟨3562539528535448258384023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4750052704713931011178697 3562539528535448258384023)
        ·
          refine ⟨5343809292803172387576035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3562539528535448258384023 5343809292803172387576035)
          ·
            refine ⟨8015713939204758581364053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5343809292803172387576035 8015713939204758581364053)
            ·
              refine ⟨5870884232815985289085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 8015713939204758581364053 5870884232815985289085)
              ·
                rfl

theorem cell23_926114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 12].length) (baseStart_926114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926114 prefixEnd_926114 := by exact prefixLift 926114
  have htrace : WordTrace (prefixWord ++ tailWord_926114) baseStart_926114 baseEnd_926114 := by
    simpa [prefixWord, tailWord_926114, baseEnd_926114] using wordTrace_append hprefix tailTrace_926114
  have hstable : (prefixWord ++ tailWord_926114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926114).length < 2 ^ (prefixWord ++ tailWord_926114).sum := by decide
  have hdescent : baseEnd_926114 < baseStart_926114 := by decide
  rcases family_descends (prefixWord ++ tailWord_926114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926154 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_926154 : Nat := 118140960795 + 926154 * 2 ^ 59
def prefixEnd_926154 : Nat := 4983230072969 + 3 ^ 40 * 926154 * 2
def baseEnd_926154 : Nat := 475562162084274651915701

theorem tailTrace_926154 : CollatzResearch.WordTrace tailWord_926154 prefixEnd_926154 475562162084274651915701 := by
  unfold tailWord_926154
  simp only [CollatzResearch.WordTrace]
  refine ⟨8444902871677426838848379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22519740991139804903595677 8444902871677426838848379)
  ·
    refine ⟨12667354307516140258272569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8444902871677426838848379 12667354307516140258272569)
    ·
      refine ⟨9500515730637105193704427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12667354307516140258272569 9500515730637105193704427)
      ·
        refine ⟨14250773595955657790556641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9500515730637105193704427 14250773595955657790556641)
        ·
          refine ⟨10688080196966743342917481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14250773595955657790556641 10688080196966743342917481)
          ·
            refine ⟨8016060147725057507188111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10688080196966743342917481 8016060147725057507188111)
            ·
              refine ⟨12024090221587586260782167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8016060147725057507188111 12024090221587586260782167)
              ·
                refine ⟨18036135332381379391173251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12024090221587586260782167 18036135332381379391173251)
                ·
                  refine ⟨27054202998572069086759877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18036135332381379391173251 27054202998572069086759877)
                  ·
                    refine ⟨5072663062232262953767477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27054202998572069086759877 5072663062232262953767477)
                    ·
                      refine ⟨475562162084274651915701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5072663062232262953767477 475562162084274651915701)
                      ·
                        rfl

theorem cell23_926154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_926154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926154 prefixEnd_926154 := by exact prefixLift 926154
  have htrace : WordTrace (prefixWord ++ tailWord_926154) baseStart_926154 baseEnd_926154 := by
    simpa [prefixWord, tailWord_926154, baseEnd_926154] using wordTrace_append hprefix tailTrace_926154
  have hstable : (prefixWord ++ tailWord_926154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926154).length < 2 ^ (prefixWord ++ tailWord_926154).sum := by decide
  have hdescent : baseEnd_926154 < baseStart_926154 := by decide
  rcases family_descends (prefixWord ++ tailWord_926154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926204 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 9]
def baseStart_926204 : Nat := 118140960795 + 926204 * 2 ^ 59
def prefixEnd_926204 : Nat := 4983230072969 + 3 ^ 40 * 926204 * 2
def baseEnd_926204 : Nat := 52843092901888828476719

theorem tailTrace_926204 : CollatzResearch.WordTrace tailWord_926204 prefixEnd_926204 52843092901888828476719 := by
  unfold tailWord_926204
  simp only [CollatzResearch.WordTrace]
  refine ⟨16890717568264282947356833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22520956757685710596475777 16890717568264282947356833)
  ·
    refine ⟨12668038176198212210517625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16890717568264282947356833 12668038176198212210517625)
    ·
      refine ⟨9501028632148659157888219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12668038176198212210517625 9501028632148659157888219)
      ·
        refine ⟨14251542948222988736832329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9501028632148659157888219 14251542948222988736832329)
        ·
          refine ⟨10688657211167241552624247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14251542948222988736832329 10688657211167241552624247)
          ·
            refine ⟨16032985816750862328936371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10688657211167241552624247 16032985816750862328936371)
            ·
              refine ⟨24049478725126293493404557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16032985816750862328936371 24049478725126293493404557)
              ·
                refine ⟨9018554521922360060026709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24049478725126293493404557 9018554521922360060026709)
                ·
                  refine ⟨52843092901888828476719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9018554521922360060026709 52843092901888828476719)
                  ·
                    rfl

theorem cell23_926204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_926204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926204 prefixEnd_926204 := by exact prefixLift 926204
  have htrace : WordTrace (prefixWord ++ tailWord_926204) baseStart_926204 baseEnd_926204 := by
    simpa [prefixWord, tailWord_926204, baseEnd_926204] using wordTrace_append hprefix tailTrace_926204
  have hstable : (prefixWord ++ tailWord_926204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926204).length < 2 ^ (prefixWord ++ tailWord_926204).sum := by decide
  have hdescent : baseEnd_926204 < baseStart_926204 := by decide
  rcases family_descends (prefixWord ++ tailWord_926204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926215 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 1, 4, 2]
def baseStart_926215 : Nat := 118140960795 + 926215 * 2 ^ 59
def prefixEnd_926215 : Nat := 4983230072969 + 3 ^ 40 * 926215 * 2
def baseEnd_926215 : Nat := 475593484404198913252921

theorem tailTrace_926215 : CollatzResearch.WordTrace tailWord_926215 prefixEnd_926215 475593484404198913252921 := by
  unfold tailWord_926215
  simp only [CollatzResearch.WordTrace]
  refine ⟨33781836339488714773364099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22521224226325809848909399 33781836339488714773364099)
  ·
    refine ⟨50672754509233072160046149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33781836339488714773364099 50672754509233072160046149)
    ·
      refine ⟨9501141470481201030008653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50672754509233072160046149 9501141470481201030008653)
      ·
        refine ⟨3562928051430450386253245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9501141470481201030008653 3562928051430450386253245)
        ·
          refine ⟨1336098019286418894844967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3562928051430450386253245 1336098019286418894844967)
          ·
            refine ⟨2004147028929628342267451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336098019286418894844967 2004147028929628342267451)
            ·
              refine ⟨3006220543394442513401177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004147028929628342267451 3006220543394442513401177)
              ·
                refine ⟨2254665407545831885050883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3006220543394442513401177 2254665407545831885050883)
                ·
                  refine ⟨3381998111318747827576325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2254665407545831885050883 3381998111318747827576325)
                  ·
                    refine ⟨634124645872265217670561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3381998111318747827576325 634124645872265217670561)
                    ·
                      refine ⟨475593484404198913252921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 634124645872265217670561 475593484404198913252921)
                      ·
                        rfl

theorem cell23_926215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_926215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926215 prefixEnd_926215 := by exact prefixLift 926215
  have htrace : WordTrace (prefixWord ++ tailWord_926215) baseStart_926215 baseEnd_926215 := by
    simpa [prefixWord, tailWord_926215, baseEnd_926215] using wordTrace_append hprefix tailTrace_926215
  have hstable : (prefixWord ++ tailWord_926215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926215).length < 2 ^ (prefixWord ++ tailWord_926215).sum := by decide
  have hdescent : baseEnd_926215 < baseStart_926215 := by decide
  rcases family_descends (prefixWord ++ tailWord_926215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926232 : List Nat := [2, 1, 2, 3, 3, 2, 2, 2, 2, 2, 2]
def baseStart_926232 : Nat := 118140960795 + 926232 * 2 ^ 59
def prefixEnd_926232 : Nat := 4983230072969 + 3 ^ 40 * 926232 * 2
def baseEnd_926232 : Nat := 475602213575325346740343

theorem tailTrace_926232 : CollatzResearch.WordTrace tailWord_926232 prefixEnd_926232 475602213575325346740343 := by
  unfold tailWord_926232
  simp only [CollatzResearch.WordTrace]
  refine ⟨16891228190213563338366475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22521637586951417784488633 16891228190213563338366475)
  ·
    refine ⟨25336842285320345007549713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16891228190213563338366475 25336842285320345007549713)
    ·
      refine ⟨19002631713990258755662285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25336842285320345007549713 19002631713990258755662285)
      ·
        refine ⟨7125986892746347033373357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19002631713990258755662285 7125986892746347033373357)
        ·
          refine ⟨2672245084779880137515009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7125986892746347033373357 2672245084779880137515009)
          ·
            refine ⟨2004183813584910103136257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2672245084779880137515009 2004183813584910103136257)
            ·
              refine ⟨1503137860188682577352193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2004183813584910103136257 1503137860188682577352193)
              ·
                refine ⟨1127353395141511933014145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1503137860188682577352193 1127353395141511933014145)
                ·
                  refine ⟨845515046356133949760609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1127353395141511933014145 845515046356133949760609)
                  ·
                    refine ⟨634136284767100462320457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 845515046356133949760609 634136284767100462320457)
                    ·
                      refine ⟨475602213575325346740343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 634136284767100462320457 475602213575325346740343)
                      ·
                        rfl

theorem cell23_926232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_926232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926232 prefixEnd_926232 := by exact prefixLift 926232
  have htrace : WordTrace (prefixWord ++ tailWord_926232) baseStart_926232 baseEnd_926232 := by
    simpa [prefixWord, tailWord_926232, baseEnd_926232] using wordTrace_append hprefix tailTrace_926232
  have hstable : (prefixWord ++ tailWord_926232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926232).length < 2 ^ (prefixWord ++ tailWord_926232).sum := by decide
  have hdescent : baseEnd_926232 < baseStart_926232 := by decide
  rcases family_descends (prefixWord ++ tailWord_926232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926248 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_926248 : Nat := 118140960795 + 926248 * 2 ^ 59
def prefixEnd_926248 : Nat := 4983230072969 + 3 ^ 40 * 926248 * 2
def baseEnd_926248 : Nat := 475610429265797284140269

theorem tailTrace_926248 : CollatzResearch.WordTrace tailWord_926248 prefixEnd_926248 475610429265797284140269 := by
  unfold tailWord_926248
  simp only [CollatzResearch.WordTrace]
  refine ⟨16891519974184580704657699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22522026632246107606210265 16891519974184580704657699)
  ·
    refine ⟨25337279961276871056986549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16891519974184580704657699 25337279961276871056986549)
    ·
      refine ⟨2375369996369706661592489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25337279961276871056986549 2375369996369706661592489)
      ·
        refine ⟨1781527497277279996194367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2375369996369706661592489 1781527497277279996194367)
        ·
          refine ⟨2672291245915919994291551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1781527497277279996194367 2672291245915919994291551)
          ·
            refine ⟨4008436868873879991437327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2672291245915919994291551 4008436868873879991437327)
            ·
              refine ⟨6012655303310819987155991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4008436868873879991437327 6012655303310819987155991)
              ·
                refine ⟨9018982954966229980733987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6012655303310819987155991 9018982954966229980733987)
                ·
                  refine ⟨13528474432449344971100981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9018982954966229980733987 13528474432449344971100981)
                  ·
                    refine ⟨1268294478042126091040717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13528474432449344971100981 1268294478042126091040717)
                    ·
                      refine ⟨475610429265797284140269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1268294478042126091040717 475610429265797284140269)
                      ·
                        rfl

theorem cell23_926248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_926248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926248 prefixEnd_926248 := by exact prefixLift 926248
  have htrace : WordTrace (prefixWord ++ tailWord_926248) baseStart_926248 baseEnd_926248 := by
    simpa [prefixWord, tailWord_926248, baseEnd_926248] using wordTrace_append hprefix tailTrace_926248
  have hstable : (prefixWord ++ tailWord_926248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926248).length < 2 ^ (prefixWord ++ tailWord_926248).sum := by decide
  have hdescent : baseEnd_926248 < baseStart_926248 := by decide
  rcases family_descends (prefixWord ++ tailWord_926248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926268 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 2, 5]
def baseStart_926268 : Nat := 118140960795 + 926268 * 2 ^ 59
def prefixEnd_926268 : Nat := 4983230072969 + 3 ^ 40 * 926268 * 2
def baseEnd_926268 : Nat := 158540232959629068630059

theorem tailTrace_926268 : CollatzResearch.WordTrace tailWord_926268 prefixEnd_926268 158540232959629068630059 := by
  unfold tailWord_926268
  simp only [CollatzResearch.WordTrace]
  refine ⟨16891884704148352412521729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22522512938864469883362305 16891884704148352412521729)
  ·
    refine ⟨12668913528111264309391297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16891884704148352412521729 12668913528111264309391297)
    ·
      refine ⟨9501685146083448232043473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12668913528111264309391297 9501685146083448232043473)
      ·
        refine ⟨7126263859562586174032605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9501685146083448232043473 7126263859562586174032605)
        ·
          refine ⟨2672348947335969815262227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7126263859562586174032605 2672348947335969815262227)
          ·
            refine ⟨4008523421003954722893341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2672348947335969815262227 4008523421003954722893341)
            ·
              refine ⟨1503196282876483021085003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4008523421003954722893341 1503196282876483021085003)
              ·
                refine ⟨2254794424314724531627505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503196282876483021085003 2254794424314724531627505)
                ·
                  refine ⟨1691095818236043398720629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2254794424314724531627505 1691095818236043398720629)
                  ·
                    refine ⟨158540232959629068630059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1691095818236043398720629 158540232959629068630059)
                    ·
                      rfl

theorem cell23_926268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_926268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926268 prefixEnd_926268 := by exact prefixLift 926268
  have htrace : WordTrace (prefixWord ++ tailWord_926268) baseStart_926268 baseEnd_926268 := by
    simpa [prefixWord, tailWord_926268, baseEnd_926268] using wordTrace_append hprefix tailTrace_926268
  have hstable : (prefixWord ++ tailWord_926268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926268).length < 2 ^ (prefixWord ++ tailWord_926268).sum := by decide
  have hdescent : baseEnd_926268 < baseStart_926268 := by decide
  rcases family_descends (prefixWord ++ tailWord_926268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926271 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 4]
def baseStart_926271 : Nat := 118140960795 + 926271 * 2 ^ 59
def prefixEnd_926271 : Nat := 4983230072969 + 3 ^ 40 * 926271 * 2
def baseEnd_926271 : Nat := 475622239320850694152663

theorem tailTrace_926271 : CollatzResearch.WordTrace tailWord_926271 prefixEnd_926271 475622239320850694152663 := by
  unfold tailWord_926271
  simp only [CollatzResearch.WordTrace]
  refine ⟨33783878827285836337402667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22522585884857224224935111 33783878827285836337402667)
  ·
    refine ⟨50675818240928754506104001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33783878827285836337402667 50675818240928754506104001)
    ·
      refine ⟨38006863680696565879578001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50675818240928754506104001 38006863680696565879578001)
      ·
        refine ⟨28505147760522424409683501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38006863680696565879578001 28505147760522424409683501)
        ·
          refine ⟨10689430410195909153631313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28505147760522424409683501 10689430410195909153631313)
          ·
            refine ⟨8017072807646931865223485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10689430410195909153631313 8017072807646931865223485)
            ·
              refine ⟨3006402302867599449458807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8017072807646931865223485 3006402302867599449458807)
              ·
                refine ⟨4509603454301399174188211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3006402302867599449458807 4509603454301399174188211)
                ·
                  refine ⟨6764405181452098761282317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4509603454301399174188211 6764405181452098761282317)
                  ·
                    refine ⟨2536651943044537035480869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6764405181452098761282317 2536651943044537035480869)
                    ·
                      refine ⟨475622239320850694152663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2536651943044537035480869 475622239320850694152663)
                      ·
                        rfl

theorem cell23_926271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_926271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926271 prefixEnd_926271 := by exact prefixLift 926271
  have htrace : WordTrace (prefixWord ++ tailWord_926271) baseStart_926271 baseEnd_926271 := by
    simpa [prefixWord, tailWord_926271, baseEnd_926271] using wordTrace_append hprefix tailTrace_926271
  have hstable : (prefixWord ++ tailWord_926271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926271).length < 2 ^ (prefixWord ++ tailWord_926271).sum := by decide
  have hdescent : baseEnd_926271 < baseStart_926271 := by decide
  rcases family_descends (prefixWord ++ tailWord_926271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926348 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 3, 5, 2]
def baseStart_926348 : Nat := 118140960795 + 926348 * 2 ^ 59
def prefixEnd_926348 : Nat := 4983230072969 + 3 ^ 40 * 926348 * 2
def baseEnd_926348 : Nat := 475661777331246892889809

theorem tailTrace_926348 : CollatzResearch.WordTrace tailWord_926348 prefixEnd_926348 475661777331246892889809 := by
  unfold tailWord_926348
  simp only [CollatzResearch.WordTrace]
  refine ⟨16893343624003439243977849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22524458165337918991970465 16893343624003439243977849)
  ·
    refine ⟨12670007718002579432983387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16893343624003439243977849 12670007718002579432983387)
    ·
      refine ⟨19005011577003869149475081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12670007718002579432983387 19005011577003869149475081)
      ·
        refine ⟨14253758682752901862106311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19005011577003869149475081 14253758682752901862106311)
        ·
          refine ⟨21380638024129352793159467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14253758682752901862106311 21380638024129352793159467)
          ·
            refine ⟨32070957036194029189739201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21380638024129352793159467 32070957036194029189739201)
            ·
              refine ⟨24053217777145521892304401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32070957036194029189739201 24053217777145521892304401)
              ·
                refine ⟨18039913332859141419228301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24053217777145521892304401 18039913332859141419228301)
                ·
                  refine ⟨6764967499822178032210613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18039913332859141419228301 6764967499822178032210613)
                  ·
                    refine ⟨634215703108329190519745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6764967499822178032210613 634215703108329190519745)
                    ·
                      refine ⟨475661777331246892889809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 634215703108329190519745 475661777331246892889809)
                      ·
                        rfl

theorem cell23_926348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_926348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926348 prefixEnd_926348 := by exact prefixLift 926348
  have htrace : WordTrace (prefixWord ++ tailWord_926348) baseStart_926348 baseEnd_926348 := by
    simpa [prefixWord, tailWord_926348, baseEnd_926348] using wordTrace_append hprefix tailTrace_926348
  have hstable : (prefixWord ++ tailWord_926348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926348).length < 2 ^ (prefixWord ++ tailWord_926348).sum := by decide
  have hdescent : baseEnd_926348 < baseStart_926348 := by decide
  rcases family_descends (prefixWord ++ tailWord_926348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926435 : List Nat := [1, 1, 1, 7, 1, 2, 3, 7]
def baseStart_926435 : Nat := 118140960795 + 926435 * 2 ^ 59
def prefixEnd_926435 : Nat := 4983230072969 + 3 ^ 40 * 926435 * 2
def baseEnd_926435 : Nat := 17618757412895853796367

theorem tailTrace_926435 : CollatzResearch.WordTrace tailWord_926435 prefixEnd_926435 17618757412895853796367 := by
  unfold tailWord_926435
  simp only [CollatzResearch.WordTrace]
  refine ⟨33789860398691692346372759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22526573599127794897581839 33789860398691692346372759)
  ·
    refine ⟨50684790598037538519559139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33789860398691692346372759 50684790598037538519559139)
    ·
      refine ⟨76027185897056307779338709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50684790598037538519559139 76027185897056307779338709)
      ·
        refine ⟨1781887169462257213578251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 76027185897056307779338709 1781887169462257213578251)
        ·
          refine ⟨2672830754193385820367377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1781887169462257213578251 2672830754193385820367377)
          ·
            refine ⟨2004623065645039365275533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2672830754193385820367377 2004623065645039365275533)
            ·
              refine ⟨751733649616889761978325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2004623065645039365275533 751733649616889761978325)
              ·
                refine ⟨17618757412895853796367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 751733649616889761978325 17618757412895853796367)
                ·
                  rfl

theorem cell23_926435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 7].length) (baseStart_926435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926435 prefixEnd_926435 := by exact prefixLift 926435
  have htrace : WordTrace (prefixWord ++ tailWord_926435) baseStart_926435 baseEnd_926435 := by
    simpa [prefixWord, tailWord_926435, baseEnd_926435] using wordTrace_append hprefix tailTrace_926435
  have hstable : (prefixWord ++ tailWord_926435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926435).length < 2 ^ (prefixWord ++ tailWord_926435).sum := by decide
  have hdescent : baseEnd_926435 < baseStart_926435 := by decide
  rcases family_descends (prefixWord ++ tailWord_926435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926445 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_926445 : Nat := 118140960795 + 926445 * 2 ^ 59
def prefixEnd_926445 : Nat := 4983230072969 + 3 ^ 40 * 926445 * 2
def baseEnd_926445 : Nat := 475711584954733013376863

theorem tailTrace_926445 : CollatzResearch.WordTrace tailWord_926445 prefixEnd_926445 475711584954733013376863 := by
  unfold tailWord_926445
  simp only [CollatzResearch.WordTrace]
  refine ⟨33790225128655464054236789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22526816752436976036157859 33790225128655464054236789)
  ·
    refine ⟨3167833605811449755084699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33790225128655464054236789 3167833605811449755084699)
    ·
      refine ⟨4751750408717174632627049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3167833605811449755084699 4751750408717174632627049)
      ·
        refine ⟨3563812806537880974470287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4751750408717174632627049 3563812806537880974470287)
        ·
          refine ⟨5345719209806821461705431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563812806537880974470287 5345719209806821461705431)
          ·
            refine ⟨8018578814710232192558147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5345719209806821461705431 8018578814710232192558147)
            ·
              refine ⟨12027868222065348288837221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8018578814710232192558147 12027868222065348288837221)
              ·
                refine ⟨2255225291637252804156979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12027868222065348288837221 2255225291637252804156979)
                ·
                  refine ⟨3382837937455879206235469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2255225291637252804156979 3382837937455879206235469)
                  ·
                    refine ⟨1268564226545954702338301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3382837937455879206235469 1268564226545954702338301)
                    ·
                      refine ⟨475711584954733013376863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1268564226545954702338301 475711584954733013376863)
                      ·
                        rfl

theorem cell23_926445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_926445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926445 prefixEnd_926445 := by exact prefixLift 926445
  have htrace : WordTrace (prefixWord ++ tailWord_926445) baseStart_926445 baseEnd_926445 := by
    simpa [prefixWord, tailWord_926445, baseEnd_926445] using wordTrace_append hprefix tailTrace_926445
  have hstable : (prefixWord ++ tailWord_926445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926445).length < 2 ^ (prefixWord ++ tailWord_926445).sum := by decide
  have hdescent : baseEnd_926445 < baseStart_926445 := by decide
  rcases family_descends (prefixWord ++ tailWord_926445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926446 : List Nat := [4, 1, 2, 1, 1, 4, 2, 3, 1, 2, 2]
def baseStart_926446 : Nat := 118140960795 + 926446 * 2 ^ 59
def prefixEnd_926446 : Nat := 4983230072969 + 3 ^ 40 * 926446 * 2
def baseEnd_926446 : Nat := 475712098435387509464359

theorem tailTrace_926446 : CollatzResearch.WordTrace tailWord_926446 prefixEnd_926446 475712098435387509464359 := by
  unfold tailWord_926446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4223782700206480153127899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22526841067767894150015461 4223782700206480153127899)
  ·
    refine ⟨6335674050309720229691849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4223782700206480153127899 6335674050309720229691849)
    ·
      refine ⟨4751755537732290172268887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6335674050309720229691849 4751755537732290172268887)
      ·
        refine ⟨7127633306598435258403331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4751755537732290172268887 7127633306598435258403331)
        ·
          refine ⟨10691449959897652887604997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7127633306598435258403331 10691449959897652887604997)
          ·
            refine ⟨2004646867480809916425937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10691449959897652887604997 2004646867480809916425937)
            ·
              refine ⟨1503485150610607437319453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2004646867480809916425937 1503485150610607437319453)
              ·
                refine ⟨563806931478977788994795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1503485150610607437319453 563806931478977788994795)
                ·
                  refine ⟨845710397218466683492193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 563806931478977788994795 845710397218466683492193)
                  ·
                    refine ⟨634282797913850012619145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 845710397218466683492193 634282797913850012619145)
                    ·
                      refine ⟨475712098435387509464359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 634282797913850012619145 475712098435387509464359)
                      ·
                        rfl

theorem cell23_926446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_926446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926446 prefixEnd_926446 := by exact prefixLift 926446
  have htrace : WordTrace (prefixWord ++ tailWord_926446) baseStart_926446 baseEnd_926446 := by
    simpa [prefixWord, tailWord_926446, baseEnd_926446] using wordTrace_append hprefix tailTrace_926446
  have hstable : (prefixWord ++ tailWord_926446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926446).length < 2 ^ (prefixWord ++ tailWord_926446).sum := by decide
  have hdescent : baseEnd_926446 < baseStart_926446 := by decide
  rcases family_descends (prefixWord ++ tailWord_926446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926452 : List Nat := [2, 6, 1, 1, 2, 1, 10]
def baseStart_926452 : Nat := 118140960795 + 926452 * 2 ^ 59
def prefixEnd_926452 : Nat := 4983230072969 + 3 ^ 40 * 926452 * 2
def baseEnd_926452 : Nat := 5873026905176722049251

theorem tailTrace_926452 : CollatzResearch.WordTrace tailWord_926452 prefixEnd_926452 5873026905176722049251 := by
  unfold tailWord_926452
  simp only [CollatzResearch.WordTrace]
  refine ⟨16895240219815052124870805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22526986959753402833161073 16895240219815052124870805)
  ·
    refine ⟨791964385303830568353319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16895240219815052124870805 791964385303830568353319)
    ·
      refine ⟨1187946577955745852529979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 791964385303830568353319 1187946577955745852529979)
      ·
        refine ⟨1781919866933618778794969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1187946577955745852529979 1781919866933618778794969)
        ·
          refine ⟨1336439900200214084096227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1781919866933618778794969 1336439900200214084096227)
          ·
            refine ⟨2004659850300321126144341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336439900200214084096227 2004659850300321126144341)
            ·
              refine ⟨5873026905176722049251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2004659850300321126144341 5873026905176722049251)
              ·
                rfl

theorem cell23_926452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 10].length) (baseStart_926452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926452 prefixEnd_926452 := by exact prefixLift 926452
  have htrace : WordTrace (prefixWord ++ tailWord_926452) baseStart_926452 baseEnd_926452 := by
    simpa [prefixWord, tailWord_926452, baseEnd_926452] using wordTrace_append hprefix tailTrace_926452
  have hstable : (prefixWord ++ tailWord_926452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926452).length < 2 ^ (prefixWord ++ tailWord_926452).sum := by decide
  have hdescent : baseEnd_926452 < baseStart_926452 := by decide
  rcases family_descends (prefixWord ++ tailWord_926452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926488 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_926488 : Nat := 118140960795 + 926488 * 2 ^ 59
def prefixEnd_926488 : Nat := 4983230072969 + 3 ^ 40 * 926488 * 2
def baseEnd_926488 : Nat := 475733664622876345139165

theorem tailTrace_926488 : CollatzResearch.WordTrace tailWord_926488 prefixEnd_926488 475733664622876345139165 := by
  unfold tailWord_926488
  simp only [CollatzResearch.WordTrace]
  refine ⟨16895896733749841199026059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22527862311666454932034745 16895896733749841199026059)
  ·
    refine ⟨25343845100624761798539089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16895896733749841199026059 25343845100624761798539089)
    ·
      refine ⟨19007883825468571348904317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25343845100624761798539089 19007883825468571348904317)
      ·
        refine ⟨7127956434550714255839119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19007883825468571348904317 7127956434550714255839119)
        ·
          refine ⟨10691934651826071383758679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7127956434550714255839119 10691934651826071383758679)
          ·
            refine ⟨16037901977739107075638019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10691934651826071383758679 16037901977739107075638019)
            ·
              refine ⟨24056852966608660613457029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16037901977739107075638019 24056852966608660613457029)
              ·
                refine ⟨4510659931239123865023193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24056852966608660613457029 4510659931239123865023193)
                ·
                  refine ⟨3382994948429342898767395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4510659931239123865023193 3382994948429342898767395)
                  ·
                    refine ⟨5074492422644014348151093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3382994948429342898767395 5074492422644014348151093)
                    ·
                      refine ⟨475733664622876345139165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5074492422644014348151093 475733664622876345139165)
                      ·
                        rfl

theorem cell23_926488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_926488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926488 prefixEnd_926488 := by exact prefixLift 926488
  have htrace : WordTrace (prefixWord ++ tailWord_926488) baseStart_926488 baseEnd_926488 := by
    simpa [prefixWord, tailWord_926488, baseEnd_926488] using wordTrace_append hprefix tailTrace_926488
  have hstable : (prefixWord ++ tailWord_926488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926488).length < 2 ^ (prefixWord ++ tailWord_926488).sum := by decide
  have hdescent : baseEnd_926488 < baseStart_926488 := by decide
  rcases family_descends (prefixWord ++ tailWord_926488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926538 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 1, 7]
def baseStart_926538 : Nat := 118140960795 + 926538 * 2 ^ 59
def prefixEnd_926538 : Nat := 4983230072969 + 3 ^ 40 * 926538 * 2
def baseEnd_926538 : Nat := 158586446218533716504645

theorem tailTrace_926538 : CollatzResearch.WordTrace tailWord_926538 prefixEnd_926538 158586446218533716504645 := by
  unfold tailWord_926538
  simp only [CollatzResearch.WordTrace]
  refine ⟨8448404279329635234343067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22529078078212360624914845 8448404279329635234343067)
  ·
    refine ⟨12672606418994452851514601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8448404279329635234343067 12672606418994452851514601)
    ·
      refine ⟨9504454814245839638635951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12672606418994452851514601 9504454814245839638635951)
      ·
        refine ⟨14256682221368759457953927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9504454814245839638635951 14256682221368759457953927)
        ·
          refine ⟨21385023332053139186930891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14256682221368759457953927 21385023332053139186930891)
          ·
            refine ⟨32077534998079708780396337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21385023332053139186930891 32077534998079708780396337)
            ·
              refine ⟨24058151248559781585297253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32077534998079708780396337 24058151248559781585297253)
              ·
                refine ⟨4510903359104959047243235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24058151248559781585297253 4510903359104959047243235)
                ·
                  refine ⟨6766355038657438570864853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4510903359104959047243235 6766355038657438570864853)
                  ·
                    refine ⟨158586446218533716504645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6766355038657438570864853 158586446218533716504645)
                    ·
                      rfl

theorem cell23_926538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_926538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926538 prefixEnd_926538 := by exact prefixLift 926538
  have htrace : WordTrace (prefixWord ++ tailWord_926538) baseStart_926538 baseEnd_926538 := by
    simpa [prefixWord, tailWord_926538, baseEnd_926538] using wordTrace_append hprefix tailTrace_926538
  have hstable : (prefixWord ++ tailWord_926538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926538).length < 2 ^ (prefixWord ++ tailWord_926538).sum := by decide
  have hdescent : baseEnd_926538 < baseStart_926538 := by decide
  rcases family_descends (prefixWord ++ tailWord_926538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926575 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 3, 6, 2]
def baseStart_926575 : Nat := 118140960795 + 926575 * 2 ^ 59
def prefixEnd_926575 : Nat := 4983230072969 + 3 ^ 40 * 926575 * 2
def baseEnd_926575 : Nat := 475778337439817504751265

theorem tailTrace_926575 : CollatzResearch.WordTrace tailWord_926575 prefixEnd_926575 475778337439817504751265 := by
  unfold tailWord_926575
  simp only [CollatzResearch.WordTrace]
  refine ⟨33794966618184496256469179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22529977745456330837646119 33794966618184496256469179)
  ·
    refine ⟨50692449927276744384703769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33794966618184496256469179 50692449927276744384703769)
    ·
      refine ⟨38019337445457558288527827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50692449927276744384703769 38019337445457558288527827)
      ·
        refine ⟨57029006168186337432791741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38019337445457558288527827 57029006168186337432791741)
        ·
          refine ⟨21385877313069876537296903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57029006168186337432791741 21385877313069876537296903)
          ·
            refine ⟨32078815969604814805945355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21385877313069876537296903 32078815969604814805945355)
            ·
              refine ⟨48118223954407222208918033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32078815969604814805945355 48118223954407222208918033)
              ·
                refine ⟨36088667965805416656688525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48118223954407222208918033 36088667965805416656688525)
                ·
                  refine ⟨13533250487177031246258197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36088667965805416656688525 13533250487177031246258197)
                  ·
                    refine ⟨634371116586423339668353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13533250487177031246258197 634371116586423339668353)
                    ·
                      refine ⟨475778337439817504751265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 634371116586423339668353 475778337439817504751265)
                      ·
                        rfl

theorem cell23_926575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 6, 2].length) (baseStart_926575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926575 prefixEnd_926575 := by exact prefixLift 926575
  have htrace : WordTrace (prefixWord ++ tailWord_926575) baseStart_926575 baseEnd_926575 := by
    simpa [prefixWord, tailWord_926575, baseEnd_926575] using wordTrace_append hprefix tailTrace_926575
  have hstable : (prefixWord ++ tailWord_926575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926575).length < 2 ^ (prefixWord ++ tailWord_926575).sum := by decide
  have hdescent : baseEnd_926575 < baseStart_926575 := by decide
  rcases family_descends (prefixWord ++ tailWord_926575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926582 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_926582 : Nat := 118140960795 + 926582 * 2 ^ 59
def prefixEnd_926582 : Nat := 4983230072969 + 3 ^ 40 * 926582 * 2
def baseEnd_926582 : Nat := 475781931804398977363733

theorem tailTrace_926582 : CollatzResearch.WordTrace tailWord_926582 prefixEnd_926582 475781931804398977363733 := by
  unfold tailWord_926582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2112201370572446028248375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22530147952772757634649333 2112201370572446028248375)
  ·
    refine ⟨3168302055858669042372563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2112201370572446028248375 3168302055858669042372563)
    ·
      refine ⟨4752453083788003563558845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3168302055858669042372563 4752453083788003563558845)
      ·
        refine ⟨1782169906420501336334567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4752453083788003563558845 1782169906420501336334567)
        ·
          refine ⟨2673254859630752004501851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782169906420501336334567 2673254859630752004501851)
          ·
            refine ⟨4009882289446128006752777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673254859630752004501851 4009882289446128006752777)
            ·
              refine ⟨3007411717084596005064583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4009882289446128006752777 3007411717084596005064583)
              ·
                refine ⟨4511117575626894007596875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007411717084596005064583 4511117575626894007596875)
                ·
                  refine ⟨6766676363440341011395313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511117575626894007596875 6766676363440341011395313)
                  ·
                    refine ⟨5075007272580255758546485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6766676363440341011395313 5075007272580255758546485)
                    ·
                      refine ⟨475781931804398977363733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5075007272580255758546485 475781931804398977363733)
                      ·
                        rfl

theorem cell23_926582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_926582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926582 prefixEnd_926582 := by exact prefixLift 926582
  have htrace : WordTrace (prefixWord ++ tailWord_926582) baseStart_926582 baseEnd_926582 := by
    simpa [prefixWord, tailWord_926582, baseEnd_926582] using wordTrace_append hprefix tailTrace_926582
  have hstable : (prefixWord ++ tailWord_926582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926582).length < 2 ^ (prefixWord ++ tailWord_926582).sum := by decide
  have hdescent : baseEnd_926582 < baseStart_926582 := by decide
  rcases family_descends (prefixWord ++ tailWord_926582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926595 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 3]
def baseStart_926595 : Nat := 118140960795 + 926595 * 2 ^ 59
def prefixEnd_926595 : Nat := 4983230072969 + 3 ^ 40 * 926595 * 2
def baseEnd_926595 : Nat := 475788607052907426501173

theorem tailTrace_926595 : CollatzResearch.WordTrace tailWord_926595 prefixEnd_926595 475788607052907426501173 := by
  unfold tailWord_926595
  simp only [CollatzResearch.WordTrace]
  refine ⟨33795696078112039672197239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22530464052074693114798159 33795696078112039672197239)
  ·
    refine ⟨50693544117168059508295859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33795696078112039672197239 50693544117168059508295859)
    ·
      refine ⟨76040316175752089262443789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50693544117168059508295859 76040316175752089262443789)
      ·
        refine ⟨28515118565907033473416421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76040316175752089262443789 28515118565907033473416421)
        ·
          refine ⟨5346584731107568776265579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28515118565907033473416421 5346584731107568776265579)
          ·
            refine ⟨8019877096661353164398369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346584731107568776265579 8019877096661353164398369)
            ·
              refine ⟨6014907822496014873298777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8019877096661353164398369 6014907822496014873298777)
              ·
                refine ⟨4511180866872011154974083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6014907822496014873298777 4511180866872011154974083)
                ·
                  refine ⟨6766771300308016732461125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511180866872011154974083 6766771300308016732461125)
                  ·
                    refine ⟨1268769618807753137336461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6766771300308016732461125 1268769618807753137336461)
                    ·
                      refine ⟨475788607052907426501173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1268769618807753137336461 475788607052907426501173)
                      ·
                        rfl

theorem cell23_926595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_926595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926595 prefixEnd_926595 := by exact prefixLift 926595
  have htrace : WordTrace (prefixWord ++ tailWord_926595) baseStart_926595 baseEnd_926595 := by
    simpa [prefixWord, tailWord_926595, baseEnd_926595] using wordTrace_append hprefix tailTrace_926595
  have hstable : (prefixWord ++ tailWord_926595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926595).length < 2 ^ (prefixWord ++ tailWord_926595).sum := by decide
  have hdescent : baseEnd_926595 < baseStart_926595 := by decide
  rcases family_descends (prefixWord ++ tailWord_926595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926602 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 5, 4]
def baseStart_926602 : Nat := 118140960795 + 926602 * 2 ^ 59
def prefixEnd_926602 : Nat := 4983230072969 + 3 ^ 40 * 926602 * 2
def baseEnd_926602 : Nat := 158597400472496299704547

theorem tailTrace_926602 : CollatzResearch.WordTrace tailWord_926602 prefixEnd_926602 158597400472496299704547 := by
  unfold tailWord_926602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8448987847271669966925515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22530634259391119911801373 8448987847271669966925515)
  ·
    refine ⟨12673481770907504950388273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8448987847271669966925515 12673481770907504950388273)
    ·
      refine ⟨9505111328180628712791205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12673481770907504950388273 9505111328180628712791205)
      ·
        refine ⟨1782208374033867883648351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9505111328180628712791205 1782208374033867883648351)
        ·
          refine ⟨2673312561050801825472527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782208374033867883648351 2673312561050801825472527)
          ·
            refine ⟨4009968841576202738208791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673312561050801825472527 4009968841576202738208791)
            ·
              refine ⟨6014953262364304107313187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4009968841576202738208791 6014953262364304107313187)
              ·
                refine ⟨9022429893546456160969781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6014953262364304107313187 9022429893546456160969781)
                ·
                  refine ⟨845852802519980265090917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9022429893546456160969781 845852802519980265090917)
                  ·
                    refine ⟨158597400472496299704547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 845852802519980265090917 158597400472496299704547)
                    ·
                      rfl

theorem cell23_926602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_926602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926602 prefixEnd_926602 := by exact prefixLift 926602
  have htrace : WordTrace (prefixWord ++ tailWord_926602) baseStart_926602 baseEnd_926602 := by
    simpa [prefixWord, tailWord_926602, baseEnd_926602] using wordTrace_append hprefix tailTrace_926602
  have hstable : (prefixWord ++ tailWord_926602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926602).length < 2 ^ (prefixWord ++ tailWord_926602).sum := by decide
  have hdescent : baseEnd_926602 < baseStart_926602 := by decide
  rcases family_descends (prefixWord ++ tailWord_926602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926612 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_926612 : Nat := 118140960795 + 926612 * 2 ^ 59
def prefixEnd_926612 : Nat := 4983230072969 + 3 ^ 40 * 926612 * 2
def baseEnd_926612 : Nat := 475797336224033859988595

theorem tailTrace_926612 : CollatzResearch.WordTrace tailWord_926612 prefixEnd_926612 475797336224033859988595 := by
  unfold tailWord_926612
  simp only [CollatzResearch.WordTrace]
  refine ⟨16898158059525225787783045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22530877412700301050377393 16898158059525225787783045)
  ·
    refine ⟨3168404636160979835209321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16898158059525225787783045 3168404636160979835209321)
    ·
      refine ⟨2376303477120734876406991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3168404636160979835209321 2376303477120734876406991)
      ·
        refine ⟨3564455215681102314610487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2376303477120734876406991 3564455215681102314610487)
        ·
          refine ⟨5346682823521653471915731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3564455215681102314610487 5346682823521653471915731)
          ·
            refine ⟨8020024235282480207873597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5346682823521653471915731 8020024235282480207873597)
            ·
              refine ⟨3007509088230930077952599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8020024235282480207873597 3007509088230930077952599)
              ·
                refine ⟨4511263632346395116928899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007509088230930077952599 4511263632346395116928899)
                ·
                  refine ⟨6766895448519592675393349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4511263632346395116928899 6766895448519592675393349)
                  ·
                    refine ⟨1268792896597423626636253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6766895448519592675393349 1268792896597423626636253)
                    ·
                      refine ⟨475797336224033859988595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1268792896597423626636253 475797336224033859988595)
                      ·
                        rfl

theorem cell23_926612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_926612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926612 prefixEnd_926612 := by exact prefixLift 926612
  have htrace : WordTrace (prefixWord ++ tailWord_926612) baseStart_926612 baseEnd_926612 := by
    simpa [prefixWord, tailWord_926612, baseEnd_926612] using wordTrace_append hprefix tailTrace_926612
  have hstable : (prefixWord ++ tailWord_926612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926612).length < 2 ^ (prefixWord ++ tailWord_926612).sum := by decide
  have hdescent : baseEnd_926612 < baseStart_926612 := by decide
  rcases family_descends (prefixWord ++ tailWord_926612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926693 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 3, 1, 3]
def baseStart_926693 : Nat := 118140960795 + 926693 * 2 ^ 59
def prefixEnd_926693 : Nat := 4983230072969 + 3 ^ 40 * 926693 * 2
def baseEnd_926693 : Nat := 475838928157048043075723

theorem tailTrace_926693 : CollatzResearch.WordTrace tailWord_926693 prefixEnd_926693 475838928157048043075723 := by
  unfold tailWord_926693
  simp only [CollatzResearch.WordTrace]
  refine ⟨33799270431757002409264733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22532846954504668272843155 33799270431757002409264733)
  ·
    refine ⟨12674726411908875903474275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33799270431757002409264733 12674726411908875903474275)
    ·
      refine ⟨19012089617863313855211413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12674726411908875903474275 19012089617863313855211413)
      ·
        refine ⟨891191700837342836963035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19012089617863313855211413 891191700837342836963035)
        ·
          refine ⟨1336787551256014255444553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891191700837342836963035 1336787551256014255444553)
          ·
            refine ⟨1002590663442010691583415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1336787551256014255444553 1002590663442010691583415)
            ·
              refine ⟨1503885995163016037375123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1002590663442010691583415 1503885995163016037375123)
              ·
                refine ⟨2255828992744524056062685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503885995163016037375123 2255828992744524056062685)
                ·
                  refine ⟨845935872279196521023507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2255828992744524056062685 845935872279196521023507)
                  ·
                    refine ⟨1268903808418794781535261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 845935872279196521023507 1268903808418794781535261)
                    ·
                      refine ⟨475838928157048043075723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1268903808418794781535261 475838928157048043075723)
                      ·
                        rfl

theorem cell23_926693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_926693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926693 prefixEnd_926693 := by exact prefixLift 926693
  have htrace : WordTrace (prefixWord ++ tailWord_926693) baseStart_926693 baseEnd_926693 := by
    simpa [prefixWord, tailWord_926693, baseEnd_926693] using wordTrace_append hprefix tailTrace_926693
  have hstable : (prefixWord ++ tailWord_926693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926693).length < 2 ^ (prefixWord ++ tailWord_926693).sum := by decide
  have hdescent : baseEnd_926693 < baseStart_926693 := by decide
  rcases family_descends (prefixWord ++ tailWord_926693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926705 : List Nat := [1, 2, 2, 2, 4, 1, 1, 10]
def baseStart_926705 : Nat := 118140960795 + 926705 * 2 ^ 59
def prefixEnd_926705 : Nat := 4983230072969 + 3 ^ 40 * 926705 * 2
def baseEnd_926705 : Nat := 17623892219440814671321

theorem tailTrace_926705 : CollatzResearch.WordTrace tailWord_926705 prefixEnd_926705 17623892219440814671321 := by
  unfold tailWord_926705
  simp only [CollatzResearch.WordTrace]
  refine ⟨33799708107713528458701569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22533138738475685639134379 33799708107713528458701569)
  ·
    refine ⟨25349781080785146344026177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33799708107713528458701569 25349781080785146344026177)
    ·
      refine ⟨19012335810588859758019633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25349781080785146344026177 19012335810588859758019633)
      ·
        refine ⟨14259251857941644818514725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19012335810588859758019633 14259251857941644818514725)
        ·
          refine ⟨2673609723364058403471511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14259251857941644818514725 2673609723364058403471511)
          ·
            refine ⟨4010414585046087605207267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673609723364058403471511 4010414585046087605207267)
            ·
              refine ⟨6015621877569131407810901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010414585046087605207267 6015621877569131407810901)
              ·
                refine ⟨17623892219440814671321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6015621877569131407810901 17623892219440814671321)
                ·
                  rfl

theorem cell23_926705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 10].length) (baseStart_926705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926705 prefixEnd_926705 := by exact prefixLift 926705
  have htrace : WordTrace (prefixWord ++ tailWord_926705) baseStart_926705 baseEnd_926705 := by
    simpa [prefixWord, tailWord_926705, baseEnd_926705] using wordTrace_append hprefix tailTrace_926705
  have hstable : (prefixWord ++ tailWord_926705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926705).length < 2 ^ (prefixWord ++ tailWord_926705).sum := by decide
  have hdescent : baseEnd_926705 < baseStart_926705 := by decide
  rcases family_descends (prefixWord ++ tailWord_926705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926732 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 3, 3, 3]
def baseStart_926732 : Nat := 118140960795 + 926732 * 2 ^ 59
def prefixEnd_926732 : Nat := 4983230072969 + 3 ^ 40 * 926732 * 2
def baseEnd_926732 : Nat := 475858953902573390488043

theorem tailTrace_926732 : CollatzResearch.WordTrace tailWord_926732 prefixEnd_926732 475858953902573390488043 := by
  unfold tailWord_926732
  simp only [CollatzResearch.WordTrace]
  refine ⟨16900346439307856034967225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22533795252410474713289633 16900346439307856034967225)
  ·
    refine ⟨12675259829480892026225419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16900346439307856034967225 12675259829480892026225419)
    ·
      refine ⟨19012889744221338039338129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12675259829480892026225419 19012889744221338039338129)
      ·
        refine ⟨14259667308166003529503597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19012889744221338039338129 14259667308166003529503597)
        ·
          refine ⟨5347375240562251323563849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14259667308166003529503597 5347375240562251323563849)
          ·
            refine ⟨4010531430421688492672887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5347375240562251323563849 4010531430421688492672887)
            ·
              refine ⟨6015797145632532739009331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010531430421688492672887 6015797145632532739009331)
              ·
                refine ⟨9023695718448799108513997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6015797145632532739009331 9023695718448799108513997)
                ·
                  refine ⟨3383885894418299665692749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9023695718448799108513997 3383885894418299665692749)
                  ·
                    refine ⟨1268957210406862374634781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3383885894418299665692749 1268957210406862374634781)
                    ·
                      refine ⟨475858953902573390488043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1268957210406862374634781 475858953902573390488043)
                      ·
                        rfl

theorem cell23_926732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_926732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926732 prefixEnd_926732 := by exact prefixLift 926732
  have htrace : WordTrace (prefixWord ++ tailWord_926732) baseStart_926732 baseEnd_926732 := by
    simpa [prefixWord, tailWord_926732, baseEnd_926732] using wordTrace_append hprefix tailTrace_926732
  have hstable : (prefixWord ++ tailWord_926732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926732).length < 2 ^ (prefixWord ++ tailWord_926732).sum := by decide
  have hdescent : baseEnd_926732 < baseStart_926732 := by decide
  rcases family_descends (prefixWord ++ tailWord_926732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926745 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 2, 2, 5]
def baseStart_926745 : Nat := 118140960795 + 926745 * 2 ^ 59
def prefixEnd_926745 : Nat := 4983230072969 + 3 ^ 40 * 926745 * 2
def baseEnd_926745 : Nat := 475865629151081839625483

theorem tailTrace_926745 : CollatzResearch.WordTrace tailWord_926745 prefixEnd_926745 475865629151081839625483 := by
  unfold tailWord_926745
  simp only [CollatzResearch.WordTrace]
  refine ⟨33801167027568615290157689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22534111351712410193438459 33801167027568615290157689)
  ·
    refine ⟨25350875270676461467618267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33801167027568615290157689 25350875270676461467618267)
    ·
      refine ⟨38026312906014692201427401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25350875270676461467618267 38026312906014692201427401)
      ·
        refine ⟨28519734679511019151070551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38026312906014692201427401 28519734679511019151070551)
        ·
          refine ⟨42779602019266528726605827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28519734679511019151070551 42779602019266528726605827)
          ·
            refine ⟨64169403028899793089908741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42779602019266528726605827 64169403028899793089908741)
            ·
              refine ⟨12031763067918711204357889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64169403028899793089908741 12031763067918711204357889)
              ·
                refine ⟨9023822300939033403268417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12031763067918711204357889 9023822300939033403268417)
                ·
                  refine ⟨6767866725704275052451313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9023822300939033403268417 6767866725704275052451313)
                  ·
                    refine ⟨5075900044278206289338485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6767866725704275052451313 5075900044278206289338485)
                    ·
                      refine ⟨475865629151081839625483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5075900044278206289338485 475865629151081839625483)
                      ·
                        rfl

theorem cell23_926745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_926745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926745 prefixEnd_926745 := by exact prefixLift 926745
  have htrace : WordTrace (prefixWord ++ tailWord_926745) baseStart_926745 baseEnd_926745 := by
    simpa [prefixWord, tailWord_926745, baseEnd_926745] using wordTrace_append hprefix tailTrace_926745
  have hstable : (prefixWord ++ tailWord_926745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926745).length < 2 ^ (prefixWord ++ tailWord_926745).sum := by decide
  have hdescent : baseEnd_926745 < baseStart_926745 := by decide
  rcases family_descends (prefixWord ++ tailWord_926745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926766 : List Nat := [4, 1, 3, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_926766 : Nat := 118140960795 + 926766 * 2 ^ 59
def prefixEnd_926766 : Nat := 4983230072969 + 3 ^ 40 * 926766 * 2
def baseEnd_926766 : Nat := 475876412244826257462887

theorem tailTrace_926766 : CollatzResearch.WordTrace tailWord_926766 prefixEnd_926766 475876412244826257462887 := by
  unfold tailWord_926766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4225241620061566984584019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22534621973661690584448101 4225241620061566984584019)
  ·
    refine ⟨6337862430092350476876029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4225241620061566984584019 6337862430092350476876029)
    ·
      refine ⟨2376698411284631428828511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6337862430092350476876029 2376698411284631428828511)
      ·
        refine ⟨3565047616926947143242767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2376698411284631428828511 3565047616926947143242767)
        ·
          refine ⟨5347571425390420714864151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565047616926947143242767 5347571425390420714864151)
          ·
            refine ⟨8021357138085631072296227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5347571425390420714864151 8021357138085631072296227)
            ·
              refine ⟨12032035707128446608444341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8021357138085631072296227 12032035707128446608444341)
              ·
                refine ⟨1128003347543291869541657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12032035707128446608444341 1128003347543291869541657)
                ·
                  refine ⟨846002510657468902156243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1128003347543291869541657 846002510657468902156243)
                  ·
                    refine ⟨1269003765986203353234365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 846002510657468902156243 1269003765986203353234365)
                    ·
                      refine ⟨475876412244826257462887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1269003765986203353234365 475876412244826257462887)
                      ·
                        rfl

theorem cell23_926766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_926766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926766 prefixEnd_926766 := by exact prefixLift 926766
  have htrace : WordTrace (prefixWord ++ tailWord_926766) baseStart_926766 baseEnd_926766 := by
    simpa [prefixWord, tailWord_926766, baseEnd_926766] using wordTrace_append hprefix tailTrace_926766
  have hstable : (prefixWord ++ tailWord_926766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926766).length < 2 ^ (prefixWord ++ tailWord_926766).sum := by decide
  have hdescent : baseEnd_926766 < baseStart_926766 := by decide
  rcases family_descends (prefixWord ++ tailWord_926766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926789 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 1, 4, 2]
def baseStart_926789 : Nat := 118140960795 + 926789 * 2 ^ 59
def prefixEnd_926789 : Nat := 4983230072969 + 3 ^ 40 * 926789 * 2
def baseEnd_926789 : Nat := 475888222299879667475281

theorem tailTrace_926789 : CollatzResearch.WordTrace tailWord_926789 prefixEnd_926789 475888222299879667475281 := by
  unfold tailWord_926789
  simp only [CollatzResearch.WordTrace]
  refine ⟨33802771839409210804759421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22535181226272807203172947 33802771839409210804759421)
  ·
    refine ⟨12676039439778454051784783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33802771839409210804759421 12676039439778454051784783)
    ·
      refine ⟨19014059159667681077677175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12676039439778454051784783 19014059159667681077677175)
      ·
        refine ⟨28521088739501521616515763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19014059159667681077677175 28521088739501521616515763)
        ·
          refine ⟨42781633109252282424773645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28521088739501521616515763 42781633109252282424773645)
          ·
            refine ⟨16043112415969605909290117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42781633109252282424773645 16043112415969605909290117)
            ·
              refine ⟨3008083577994301107991897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16043112415969605909290117 3008083577994301107991897)
              ·
                refine ⟨2256062683495725830993923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3008083577994301107991897 2256062683495725830993923)
                ·
                  refine ⟨3384094025243588746490885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2256062683495725830993923 3384094025243588746490885)
                  ·
                    refine ⟨634517629733172889967041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3384094025243588746490885 634517629733172889967041)
                    ·
                      refine ⟨475888222299879667475281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 634517629733172889967041 475888222299879667475281)
                      ·
                        rfl

theorem cell23_926789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 4, 2].length) (baseStart_926789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926789 prefixEnd_926789 := by exact prefixLift 926789
  have htrace : WordTrace (prefixWord ++ tailWord_926789) baseStart_926789 baseEnd_926789 := by
    simpa [prefixWord, tailWord_926789, baseEnd_926789] using wordTrace_append hprefix tailTrace_926789
  have hstable : (prefixWord ++ tailWord_926789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926789).length < 2 ^ (prefixWord ++ tailWord_926789).sum := by decide
  have hdescent : baseEnd_926789 < baseStart_926789 := by decide
  rcases family_descends (prefixWord ++ tailWord_926789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926899 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 3]
def baseStart_926899 : Nat := 118140960795 + 926899 * 2 ^ 59
def prefixEnd_926899 : Nat := 4983230072969 + 3 ^ 40 * 926899 * 2
def baseEnd_926899 : Nat := 475944705171874237099775

theorem tailTrace_926899 : CollatzResearch.WordTrace tailWord_926899 prefixEnd_926899 475944705171874237099775 := by
  unfold tailWord_926899
  simp only [CollatzResearch.WordTrace]
  refine ⟨33806783869010699591263751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22537855912673799727509167 33806783869010699591263751)
  ·
    refine ⟨50710175803516049386895627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33806783869010699591263751 50710175803516049386895627)
    ·
      refine ⟨76065263705274074080343441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50710175803516049386895627 76065263705274074080343441)
      ·
        refine ⟨57048947778955555560257581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76065263705274074080343441 57048947778955555560257581)
        ·
          refine ⟨21393355417108333335096593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57048947778955555560257581 21393355417108333335096593)
          ·
            refine ⟨16045016562831250001322445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21393355417108333335096593 16045016562831250001322445)
            ·
              refine ⟨6016881211061718750495917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16045016562831250001322445 6016881211061718750495917)
              ·
                refine ⟨2256330454148144531435969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6016881211061718750495917 2256330454148144531435969)
                ·
                  refine ⟨1692247840611108398576977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2256330454148144531435969 1692247840611108398576977)
                  ·
                    refine ⟨1269185880458331298932733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1692247840611108398576977 1269185880458331298932733)
                    ·
                      refine ⟨475944705171874237099775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1269185880458331298932733 475944705171874237099775)
                      ·
                        rfl

theorem cell23_926899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 3].length) (baseStart_926899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926899 prefixEnd_926899 := by exact prefixLift 926899
  have htrace : WordTrace (prefixWord ++ tailWord_926899) baseStart_926899 baseEnd_926899 := by
    simpa [prefixWord, tailWord_926899, baseEnd_926899] using wordTrace_append hprefix tailTrace_926899
  have hstable : (prefixWord ++ tailWord_926899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926899).length < 2 ^ (prefixWord ++ tailWord_926899).sum := by decide
  have hdescent : baseEnd_926899 < baseStart_926899 := by decide
  rcases family_descends (prefixWord ++ tailWord_926899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926906 : List Nat := [3, 1, 1, 1, 2, 2, 1, 7, 1, 4]
def baseStart_926906 : Nat := 118140960795 + 926906 * 2 ^ 59
def prefixEnd_926906 : Nat := 4983230072969 + 3 ^ 40 * 926906 * 2
def baseEnd_926906 : Nat := 158649433178818569904081

theorem tailTrace_926906 : CollatzResearch.WordTrace tailWord_926906 prefixEnd_926906 158649433178818569904081 := by
  unfold tailWord_926906
  simp only [CollatzResearch.WordTrace]
  refine ⟨8451759794996334946692143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22538026119990226524512381 8451759794996334946692143)
  ·
    refine ⟨12677639692494502420038215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8451759794996334946692143 12677639692494502420038215)
    ·
      refine ⟨19016459538741753630057323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12677639692494502420038215 19016459538741753630057323)
      ·
        refine ⟨28524689308112630445085985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19016459538741753630057323 28524689308112630445085985)
        ·
          refine ⟨21393516981084472833814489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28524689308112630445085985 21393516981084472833814489)
          ·
            refine ⟨16045137735813354625360867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21393516981084472833814489 16045137735813354625360867)
            ·
              refine ⟨24067706603720031938041301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16045137735813354625360867 24067706603720031938041301)
              ·
                refine ⟨564086873524688248547843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24067706603720031938041301 564086873524688248547843)
                ·
                  refine ⟨846130310287032372821765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564086873524688248547843 846130310287032372821765)
                  ·
                    refine ⟨158649433178818569904081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 846130310287032372821765 158649433178818569904081)
                    ·
                      rfl

theorem cell23_926906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_926906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926906 prefixEnd_926906 := by exact prefixLift 926906
  have htrace : WordTrace (prefixWord ++ tailWord_926906) baseStart_926906 baseEnd_926906 := by
    simpa [prefixWord, tailWord_926906, baseEnd_926906] using wordTrace_append hprefix tailTrace_926906
  have hstable : (prefixWord ++ tailWord_926906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926906).length < 2 ^ (prefixWord ++ tailWord_926906).sum := by decide
  have hdescent : baseEnd_926906 < baseStart_926906 := by decide
  rcases family_descends (prefixWord ++ tailWord_926906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926914 : List Nat := [3, 5, 1, 1, 3, 1, 2, 2, 5]
def baseStart_926914 : Nat := 118140960795 + 926914 * 2 ^ 59
def prefixEnd_926914 : Nat := 4983230072969 + 3 ^ 40 * 926914 * 2
def baseEnd_926914 : Nat := 52883600820187964268023

theorem tailTrace_926914 : CollatzResearch.WordTrace tailWord_926914 prefixEnd_926914 52883600820187964268023 := by
  unfold tailWord_926914
  simp only [CollatzResearch.WordTrace]
  refine ⟨8451832740989089288264949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22538220642637571435373197 8451832740989089288264949)
  ·
    refine ⟨792359319467727120774839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8451832740989089288264949 792359319467727120774839)
    ·
      refine ⟨1188538979201590681162259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 792359319467727120774839 1188538979201590681162259)
      ·
        refine ⟨1782808468802386021743389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188538979201590681162259 1782808468802386021743389)
        ·
          refine ⟨668553175800894758153771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1782808468802386021743389 668553175800894758153771)
          ·
            refine ⟨1002829763701342137230657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668553175800894758153771 1002829763701342137230657)
            ·
              refine ⟨752122322776006602922993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002829763701342137230657 752122322776006602922993)
              ·
                refine ⟨564091742082004952192245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752122322776006602922993 564091742082004952192245)
                ·
                  refine ⟨52883600820187964268023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 564091742082004952192245 52883600820187964268023)
                  ·
                    rfl

theorem cell23_926914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_926914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926914 prefixEnd_926914 := by exact prefixLift 926914
  have htrace : WordTrace (prefixWord ++ tailWord_926914) baseStart_926914 baseEnd_926914 := by
    simpa [prefixWord, tailWord_926914, baseEnd_926914] using wordTrace_append hprefix tailTrace_926914
  have hstable : (prefixWord ++ tailWord_926914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926914).length < 2 ^ (prefixWord ++ tailWord_926914).sum := by decide
  have hdescent : baseEnd_926914 < baseStart_926914 := by decide
  rcases family_descends (prefixWord ++ tailWord_926914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926956 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 1, 5, 2]
def baseStart_926956 : Nat := 118140960795 + 926956 * 2 ^ 59
def prefixEnd_926956 : Nat := 4983230072969 + 3 ^ 40 * 926956 * 2
def baseEnd_926956 : Nat := 475973973569180514087013

theorem tailTrace_926956 : CollatzResearch.WordTrace tailWord_926956 prefixEnd_926956 475973973569180514087013 := by
  unfold tailWord_926956
  simp only [CollatzResearch.WordTrace]
  refine ⟨16904431414902099163044361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22539241886536132217392481 16904431414902099163044361)
  ·
    refine ⟨12678323561176574372283271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16904431414902099163044361 12678323561176574372283271)
    ·
      refine ⟨19017485341764861558424907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12678323561176574372283271 19017485341764861558424907)
      ·
        refine ⟨28526228012647292337637361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19017485341764861558424907 28526228012647292337637361)
        ·
          refine ⟨21394671009485469253228021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28526228012647292337637361 21394671009485469253228021)
          ·
            refine ⟨2005750407139262742490127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21394671009485469253228021 2005750407139262742490127)
            ·
              refine ⟨3008625610708894113735191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2005750407139262742490127 3008625610708894113735191)
              ·
                refine ⟨4512938416063341170602787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3008625610708894113735191 4512938416063341170602787)
                ·
                  refine ⟨6769407624095011755904181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4512938416063341170602787 6769407624095011755904181)
                  ·
                    refine ⟨634631964758907352116017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6769407624095011755904181 634631964758907352116017)
                    ·
                      refine ⟨475973973569180514087013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 634631964758907352116017 475973973569180514087013)
                      ·
                        rfl

theorem cell23_926956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 5, 2].length) (baseStart_926956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926956 prefixEnd_926956 := by exact prefixLift 926956
  have htrace : WordTrace (prefixWord ++ tailWord_926956) baseStart_926956 baseEnd_926956 := by
    simpa [prefixWord, tailWord_926956, baseEnd_926956] using wordTrace_append hprefix tailTrace_926956
  have hstable : (prefixWord ++ tailWord_926956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926956).length < 2 ^ (prefixWord ++ tailWord_926956).sum := by decide
  have hdescent : baseEnd_926956 < baseStart_926956 := by decide
  rcases family_descends (prefixWord ++ tailWord_926956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926963 : List Nat := [1, 1, 1, 2, 2, 5, 1, 5, 1, 1, 3]
def baseStart_926963 : Nat := 118140960795 + 926963 * 2 ^ 59
def prefixEnd_926963 : Nat := 4983230072969 + 3 ^ 40 * 926963 * 2
def baseEnd_926963 : Nat := 475977567933761986699481

theorem tailTrace_926963 : CollatzResearch.WordTrace tailWord_926963 prefixEnd_926963 475977567933761986699481 := by
  unfold tailWord_926963
  simp only [CollatzResearch.WordTrace]
  refine ⟨33809118140778838521593543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22539412093852559014395695 33809118140778838521593543)
  ·
    refine ⟨50713677211168257782390315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33809118140778838521593543 50713677211168257782390315)
    ·
      refine ⟨76070515816752386673585473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50713677211168257782390315 76070515816752386673585473)
      ·
        refine ⟨57052886862564290005189105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76070515816752386673585473 57052886862564290005189105)
        ·
          refine ⟨42789665146923217503891829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57052886862564290005189105 42789665146923217503891829)
          ·
            refine ⟨4011531107524051640989859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42789665146923217503891829 4011531107524051640989859)
            ·
              refine ⟨6017296661286077461484789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4011531107524051640989859 6017296661286077461484789)
              ·
                refine ⟨564121561995569762014199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6017296661286077461484789 564121561995569762014199)
                ·
                  refine ⟨846182342993354643021299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564121561995569762014199 846182342993354643021299)
                  ·
                    refine ⟨1269273514490031964531949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 846182342993354643021299 1269273514490031964531949)
                    ·
                      refine ⟨475977567933761986699481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1269273514490031964531949 475977567933761986699481)
                      ·
                        rfl

theorem cell23_926963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 1, 1, 3].length) (baseStart_926963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926963 prefixEnd_926963 := by exact prefixLift 926963
  have htrace : WordTrace (prefixWord ++ tailWord_926963) baseStart_926963 baseEnd_926963 := by
    simpa [prefixWord, tailWord_926963, baseEnd_926963] using wordTrace_append hprefix tailTrace_926963
  have hstable : (prefixWord ++ tailWord_926963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926963).length < 2 ^ (prefixWord ++ tailWord_926963).sum := by decide
  have hdescent : baseEnd_926963 < baseStart_926963 := by decide
  rcases family_descends (prefixWord ++ tailWord_926963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926980 : List Nat := [2, 3, 2, 2, 2, 1, 2, 4, 1, 1, 3]
def baseStart_926980 : Nat := 118140960795 + 926980 * 2 ^ 59
def prefixEnd_926980 : Nat := 4983230072969 + 3 ^ 40 * 926980 * 2
def baseEnd_926980 : Nat := 475986297104888420186903

theorem tailTrace_926980 : CollatzResearch.WordTrace tailWord_926980 prefixEnd_926980 475986297104888420186903 := by
  unfold tailWord_926980
  simp only [CollatzResearch.WordTrace]
  refine ⟨16904869090858625212481197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22539825454478166949974929 16904869090858625212481197)
  ·
    refine ⟨6339325909071984454680449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16904869090858625212481197 6339325909071984454680449)
    ·
      refine ⟨4754494431803988341010337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6339325909071984454680449 4754494431803988341010337)
      ·
        refine ⟨3565870823852991255757753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4754494431803988341010337 3565870823852991255757753)
        ·
          refine ⟨2674403117889743441818315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3565870823852991255757753 2674403117889743441818315)
          ·
            refine ⟨4011604676834615162727473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674403117889743441818315 4011604676834615162727473)
            ·
              refine ⟨3008703507625961372045605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4011604676834615162727473 3008703507625961372045605)
              ·
                refine ⟨564131907679867757258551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3008703507625961372045605 564131907679867757258551)
                ·
                  refine ⟨846197861519801635887827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564131907679867757258551 846197861519801635887827)
                  ·
                    refine ⟨1269296792279702453831741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 846197861519801635887827 1269296792279702453831741)
                    ·
                      refine ⟨475986297104888420186903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1269296792279702453831741 475986297104888420186903)
                      ·
                        rfl

theorem cell23_926980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_926980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926980 prefixEnd_926980 := by exact prefixLift 926980
  have htrace : WordTrace (prefixWord ++ tailWord_926980) baseStart_926980 baseEnd_926980 := by
    simpa [prefixWord, tailWord_926980, baseEnd_926980] using wordTrace_append hprefix tailTrace_926980
  have hstable : (prefixWord ++ tailWord_926980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926980).length < 2 ^ (prefixWord ++ tailWord_926980).sum := by decide
  have hdescent : baseEnd_926980 < baseStart_926980 := by decide
  rcases family_descends (prefixWord ++ tailWord_926980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926999 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_926999 : Nat := 118140960795 + 926999 * 2 ^ 59
def prefixEnd_926999 : Nat := 4983230072969 + 3 ^ 40 * 926999 * 2
def baseEnd_926999 : Nat := 475996053237323845849315

theorem tailTrace_926999 : CollatzResearch.WordTrace tailWord_926999 prefixEnd_926999 475996053237323845849315 := by
  unfold tailWord_926999
  simp only [CollatzResearch.WordTrace]
  refine ⟨33810431168648416669904051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22540287445765611113269367 33810431168648416669904051)
  ·
    refine ⟨50715646752972625004856077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33810431168648416669904051 50715646752972625004856077)
    ·
      refine ⟨19018367532364734376821029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50715646752972625004856077 19018367532364734376821029)
      ·
        refine ⟨3565943912318387695653943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19018367532364734376821029 3565943912318387695653943)
        ·
          refine ⟨5348915868477581543480915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565943912318387695653943 5348915868477581543480915)
          ·
            refine ⟨8023373802716372315221373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5348915868477581543480915 8023373802716372315221373)
            ·
              refine ⟨3008765176018639618208015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8023373802716372315221373 3008765176018639618208015)
              ·
                refine ⟨4513147764027959427312023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3008765176018639618208015 4513147764027959427312023)
                ·
                  refine ⟨6769721646041939140968035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4513147764027959427312023 6769721646041939140968035)
                  ·
                    refine ⟨10154582469062908711452053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6769721646041939140968035 10154582469062908711452053)
                    ·
                      refine ⟨475996053237323845849315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10154582469062908711452053 475996053237323845849315)
                      ·
                        rfl

theorem cell23_926999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_926999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_926999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_926999 prefixEnd_926999 := by exact prefixLift 926999
  have htrace : WordTrace (prefixWord ++ tailWord_926999) baseStart_926999 baseEnd_926999 := by
    simpa [prefixWord, tailWord_926999, baseEnd_926999] using wordTrace_append hprefix tailTrace_926999
  have hstable : (prefixWord ++ tailWord_926999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926999).length < 2 ^ (prefixWord ++ tailWord_926999).sum := by decide
  have hdescent : baseEnd_926999 < baseStart_926999 := by decide
  rcases family_descends (prefixWord ++ tailWord_926999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927063 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 3, 3, 2]
def baseStart_927063 : Nat := 118140960795 + 927063 * 2 ^ 59
def prefixEnd_927063 : Nat := 4983230072969 + 3 ^ 40 * 927063 * 2
def baseEnd_927063 : Nat := 476028915999211595449021

theorem tailTrace_927063 : CollatzResearch.WordTrace tailWord_927063 prefixEnd_927063 476028915999211595449021 := by
  unfold tailWord_927063
  simp only [CollatzResearch.WordTrace]
  refine ⟨33812765440416555600233843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22541843626944370400155895 33812765440416555600233843)
  ·
    refine ⟨50719148160624833400350765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33812765440416555600233843 50719148160624833400350765)
    ·
      refine ⟨19019680560234312525131537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50719148160624833400350765 19019680560234312525131537)
      ·
        refine ⟨14264760420175734393848653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19019680560234312525131537 14264760420175734393848653)
        ·
          refine ⟨5349285157565900397693245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14264760420175734393848653 5349285157565900397693245)
          ·
            refine ⟨2005981934087212649134967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5349285157565900397693245 2005981934087212649134967)
            ·
              refine ⟨3008972901130818973702451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2005981934087212649134967 3008972901130818973702451)
              ·
                refine ⟨4513459351696228460553677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3008972901130818973702451 4513459351696228460553677)
                ·
                  refine ⟨1692547256886085672707629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4513459351696228460553677 1692547256886085672707629)
                  ·
                    refine ⟨634705221332282127265361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1692547256886085672707629 634705221332282127265361)
                    ·
                      refine ⟨476028915999211595449021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 634705221332282127265361 476028915999211595449021)
                      ·
                        rfl

theorem cell23_927063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_927063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927063 prefixEnd_927063 := by exact prefixLift 927063
  have htrace : WordTrace (prefixWord ++ tailWord_927063) baseStart_927063 baseEnd_927063 := by
    simpa [prefixWord, tailWord_927063, baseEnd_927063] using wordTrace_append hprefix tailTrace_927063
  have hstable : (prefixWord ++ tailWord_927063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927063).length < 2 ^ (prefixWord ++ tailWord_927063).sum := by decide
  have hdescent : baseEnd_927063 < baseStart_927063 := by decide
  rcases family_descends (prefixWord ++ tailWord_927063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927099 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 7]
def baseStart_927099 : Nat := 118140960795 + 927099 * 2 ^ 59
def prefixEnd_927099 : Nat := 4983230072969 + 3 ^ 40 * 927099 * 2
def baseEnd_927099 : Nat := 52894155700308161622095

theorem tailTrace_927099 : CollatzResearch.WordTrace tailWord_927099 prefixEnd_927099 52894155700308161622095 := by
  unfold tailWord_927099
  simp only [CollatzResearch.WordTrace]
  refine ⟨33814078468286133748544351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22542718978857422499029567 33814078468286133748544351)
  ·
    refine ⟨50721117702429200622816527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33814078468286133748544351 50721117702429200622816527)
    ·
      refine ⟨76081676553643800934224791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50721117702429200622816527 76081676553643800934224791)
      ·
        refine ⟨114122514830465701401337187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76081676553643800934224791 114122514830465701401337187)
        ·
          refine ⟨171183772245698552102005781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114122514830465701401337187 171183772245698552102005781)
          ·
            refine ⟨8024239324017119629781521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171183772245698552102005781 8024239324017119629781521)
            ·
              refine ⟨6018179493012839722336141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8024239324017119629781521 6018179493012839722336141)
              ·
                refine ⟨2256817309879814895876053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6018179493012839722336141 2256817309879814895876053)
                ·
                  refine ⟨52894155700308161622095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2256817309879814895876053 52894155700308161622095)
                  ·
                    rfl

theorem cell23_927099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 7].length) (baseStart_927099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927099 prefixEnd_927099 := by exact prefixLift 927099
  have htrace : WordTrace (prefixWord ++ tailWord_927099) baseStart_927099 baseEnd_927099 := by
    simpa [prefixWord, tailWord_927099, baseEnd_927099] using wordTrace_append hprefix tailTrace_927099
  have hstable : (prefixWord ++ tailWord_927099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927099).length < 2 ^ (prefixWord ++ tailWord_927099).sum := by decide
  have hdescent : baseEnd_927099 < baseStart_927099 := by decide
  rcases family_descends (prefixWord ++ tailWord_927099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927133 : List Nat := [1, 4, 2, 1, 3, 1, 1, 5, 5]
def baseStart_927133 : Nat := 118140960795 + 927133 * 2 ^ 59
def prefixEnd_927133 : Nat := 4983230072969 + 3 ^ 40 * 927133 * 2
def baseEnd_927133 : Nat := 52896095516114035730411

theorem tailTrace_927133 : CollatzResearch.WordTrace tailWord_927133 prefixEnd_927133 52896095516114035730411 := by
  unfold tailWord_927133
  simp only [CollatzResearch.WordTrace]
  refine ⟨33815318550162957555282053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22543545700108638370188035 33815318550162957555282053)
  ·
    refine ⟨6340372228155554541615385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33815318550162957555282053 6340372228155554541615385)
    ·
      refine ⟨4755279171116665906211539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6340372228155554541615385 4755279171116665906211539)
      ·
        refine ⟨7132918756674998859317309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4755279171116665906211539 7132918756674998859317309)
        ·
          refine ⟨2674844533753124572243991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7132918756674998859317309 2674844533753124572243991)
          ·
            refine ⟨4012266800629686858365987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674844533753124572243991 4012266800629686858365987)
            ·
              refine ⟨6018400200944530287548981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012266800629686858365987 6018400200944530287548981)
              ·
                refine ⟨564225018838549714457717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6018400200944530287548981 564225018838549714457717)
                ·
                  refine ⟨52896095516114035730411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 564225018838549714457717 52896095516114035730411)
                  ·
                    rfl

theorem cell23_927133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_927133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927133 prefixEnd_927133 := by exact prefixLift 927133
  have htrace : WordTrace (prefixWord ++ tailWord_927133) baseStart_927133 baseEnd_927133 := by
    simpa [prefixWord, tailWord_927133, baseEnd_927133] using wordTrace_append hprefix tailTrace_927133
  have hstable : (prefixWord ++ tailWord_927133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927133).length < 2 ^ (prefixWord ++ tailWord_927133).sum := by decide
  have hdescent : baseEnd_927133 < baseStart_927133 := by decide
  rcases family_descends (prefixWord ++ tailWord_927133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927203 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 3]
def baseStart_927203 : Nat := 118140960795 + 927203 * 2 ^ 59
def prefixEnd_927203 : Nat := 4983230072969 + 3 ^ 40 * 927203 * 2
def baseEnd_927203 : Nat := 476100803290841047698377

theorem tailTrace_927203 : CollatzResearch.WordTrace tailWord_927203 prefixEnd_927203 476100803290841047698377 := by
  unfold tailWord_927203
  simp only [CollatzResearch.WordTrace]
  refine ⟨33817871659909359510330263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22545247773272906340220175 33817871659909359510330263)
  ·
    refine ⟨50726807489864039265495395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33817871659909359510330263 50726807489864039265495395)
    ·
      refine ⟨76090211234796058898243093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50726807489864039265495395 76090211234796058898243093)
      ·
        refine ⟨3566728651631065260855145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76090211234796058898243093 3566728651631065260855145)
        ·
          refine ⟨2675046488723298945641359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3566728651631065260855145 2675046488723298945641359)
          ·
            refine ⟨4012569733084948418462039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675046488723298945641359 4012569733084948418462039)
            ·
              refine ⟨6018854599627422627693059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012569733084948418462039 6018854599627422627693059)
              ·
                refine ⟨9028281899441133941539589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6018854599627422627693059 9028281899441133941539589)
                ·
                  refine ⟨1692802856145212614038673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9028281899441133941539589 1692802856145212614038673)
                  ·
                    refine ⟨1269602142108909460529005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1692802856145212614038673 1269602142108909460529005)
                    ·
                      refine ⟨476100803290841047698377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1269602142108909460529005 476100803290841047698377)
                      ·
                        rfl

theorem cell23_927203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_927203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927203 prefixEnd_927203 := by exact prefixLift 927203
  have htrace : WordTrace (prefixWord ++ tailWord_927203) baseStart_927203 baseEnd_927203 := by
    simpa [prefixWord, tailWord_927203, baseEnd_927203] using wordTrace_append hprefix tailTrace_927203
  have hstable : (prefixWord ++ tailWord_927203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927203).length < 2 ^ (prefixWord ++ tailWord_927203).sum := by decide
  have hdescent : baseEnd_927203 < baseStart_927203 := by decide
  rcases family_descends (prefixWord ++ tailWord_927203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927260 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_927260 : Nat := 118140960795 + 927260 * 2 ^ 59
def prefixEnd_927260 : Nat := 4983230072969 + 3 ^ 40 * 927260 * 2
def baseEnd_927260 : Nat := 476130071688147324685615

theorem tailTrace_927260 : CollatzResearch.WordTrace tailWord_927260 prefixEnd_927260 476130071688147324685615 := by
  unfold tailWord_927260
  simp only [CollatzResearch.WordTrace]
  refine ⟨16909975310351429122577617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22546633747135238830103489 16909975310351429122577617)
  ·
    refine ⟨12682481482763571841933213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16909975310351429122577617 12682481482763571841933213)
    ·
      refine ⟨4755930556036339440724955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12682481482763571841933213 4755930556036339440724955)
      ·
        refine ⟨7133895834054509161087433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4755930556036339440724955 7133895834054509161087433)
        ·
          refine ⟨5350421875540881870815575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7133895834054509161087433 5350421875540881870815575)
          ·
            refine ⟨8025632813311322806223363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5350421875540881870815575 8025632813311322806223363)
            ·
              refine ⟨12038449219966984209335045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8025632813311322806223363 12038449219966984209335045)
              ·
                refine ⟨2257209228743809539250321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12038449219966984209335045 2257209228743809539250321)
                ·
                  refine ⟨1692906921557857154437741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2257209228743809539250321 1692906921557857154437741)
                  ·
                    refine ⟨634840095584196432914153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1692906921557857154437741 634840095584196432914153)
                    ·
                      refine ⟨476130071688147324685615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 634840095584196432914153 476130071688147324685615)
                      ·
                        rfl

theorem cell23_927260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_927260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927260 prefixEnd_927260 := by exact prefixLift 927260
  have htrace : WordTrace (prefixWord ++ tailWord_927260) baseStart_927260 baseEnd_927260 := by
    simpa [prefixWord, tailWord_927260, baseEnd_927260] using wordTrace_append hprefix tailTrace_927260
  have hstable : (prefixWord ++ tailWord_927260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927260).length < 2 ^ (prefixWord ++ tailWord_927260).sum := by decide
  have hdescent : baseEnd_927260 < baseStart_927260 := by decide
  rcases family_descends (prefixWord ++ tailWord_927260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927283 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 1, 6]
def baseStart_927283 : Nat := 118140960795 + 927283 * 2 ^ 59
def prefixEnd_927283 : Nat := 4983230072969 + 3 ^ 40 * 927283 * 2
def baseEnd_927283 : Nat := 158713960581066911566003

theorem tailTrace_927283 : CollatzResearch.WordTrace tailWord_927283 prefixEnd_927283 158713960581066911566003 := by
  unfold tailWord_927283
  simp only [CollatzResearch.WordTrace]
  refine ⟨33820789499619533173242503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22547192999746355448828335 33820789499619533173242503)
  ·
    refine ⟨50731184249429299759863755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33820789499619533173242503 50731184249429299759863755)
    ·
      refine ⟨76096776374143949639795633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50731184249429299759863755 76096776374143949639795633)
      ·
        refine ⟨57072582280607962229846725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76096776374143949639795633 57072582280607962229846725)
        ·
          refine ⟨10701109177613992918096261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57072582280607962229846725 10701109177613992918096261)
          ·
            refine ⟨2006457970802623672143049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10701109177613992918096261 2006457970802623672143049)
            ·
              refine ⟨1504843478101967754107287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2006457970802623672143049 1504843478101967754107287)
              ·
                refine ⟨2257265217152951631160931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1504843478101967754107287 2257265217152951631160931)
                ·
                  refine ⟨3385897825729427446741397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2257265217152951631160931 3385897825729427446741397)
                  ·
                    refine ⟨158713960581066911566003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3385897825729427446741397 158713960581066911566003)
                    ·
                      rfl

theorem cell23_927283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 6].length) (baseStart_927283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927283 prefixEnd_927283 := by exact prefixLift 927283
  have htrace : WordTrace (prefixWord ++ tailWord_927283) baseStart_927283 baseEnd_927283 := by
    simpa [prefixWord, tailWord_927283, baseEnd_927283] using wordTrace_append hprefix tailTrace_927283
  have hstable : (prefixWord ++ tailWord_927283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927283).length < 2 ^ (prefixWord ++ tailWord_927283).sum := by decide
  have hdescent : baseEnd_927283 < baseStart_927283 := by decide
  rcases family_descends (prefixWord ++ tailWord_927283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927324 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_927324 : Nat := 118140960795 + 927324 * 2 ^ 59
def prefixEnd_927324 : Nat := 4983230072969 + 3 ^ 40 * 927324 * 2
def baseEnd_927324 : Nat := 476162934450035074285321

theorem tailTrace_927324 : CollatzResearch.WordTrace tailWord_927324 prefixEnd_927324 476162934450035074285321 := by
  unfold tailWord_927324
  simp only [CollatzResearch.WordTrace]
  refine ⟨16911142446235498587742513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22548189928313998116990017 16911142446235498587742513)
  ·
    refine ⟨12683356834676623940806885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16911142446235498587742513 12683356834676623940806885)
    ·
      refine ⟨2378129406501866988901291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12683356834676623940806885 2378129406501866988901291)
      ·
        refine ⟨3567194109752800483351937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2378129406501866988901291 3567194109752800483351937)
        ·
          refine ⟨2675395582314600362513953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3567194109752800483351937 2675395582314600362513953)
          ·
            refine ⟨2006546686735950271885465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2675395582314600362513953 2006546686735950271885465)
            ·
              refine ⟨1504910015051962703914099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2006546686735950271885465 1504910015051962703914099)
              ·
                refine ⟨2257365022577944055871149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1504910015051962703914099 2257365022577944055871149)
                ·
                  refine ⟨846511883466729020951681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2257365022577944055871149 846511883466729020951681)
                  ·
                    refine ⟨634883912600046765713761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 846511883466729020951681 634883912600046765713761)
                    ·
                      refine ⟨476162934450035074285321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 634883912600046765713761 476162934450035074285321)
                      ·
                        rfl

theorem cell23_927324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_927324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927324 prefixEnd_927324 := by exact prefixLift 927324
  have htrace : WordTrace (prefixWord ++ tailWord_927324) baseStart_927324 baseEnd_927324 := by
    simpa [prefixWord, tailWord_927324, baseEnd_927324] using wordTrace_append hprefix tailTrace_927324
  have hstable : (prefixWord ++ tailWord_927324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927324).length < 2 ^ (prefixWord ++ tailWord_927324).sum := by decide
  have hdescent : baseEnd_927324 < baseStart_927324 := by decide
  rcases family_descends (prefixWord ++ tailWord_927324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927367 : List Nat := [1, 1, 4, 2, 1, 3, 2, 3, 1, 3, 2]
def baseStart_927367 : Nat := 118140960795 + 927367 * 2 ^ 59
def prefixEnd_927367 : Nat := 4983230072969 + 3 ^ 40 * 927367 * 2
def baseEnd_927367 : Nat := 476185014118178406047623

theorem tailTrace_927367 : CollatzResearch.WordTrace tailWord_927367 prefixEnd_927367 476185014118178406047623 := by
  unfold tailWord_927367
  simp only [CollatzResearch.WordTrace]
  refine ⟨33823853231315215519300355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22549235487543477012866903 33823853231315215519300355)
  ·
    refine ⟨50735779846972823278950533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33823853231315215519300355 50735779846972823278950533)
    ·
      refine ⟨9512958721307404364803225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50735779846972823278950533 9512958721307404364803225)
      ·
        refine ⟨7134719040980553273602419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9512958721307404364803225 7134719040980553273602419)
        ·
          refine ⟨10702078561470829910403629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7134719040980553273602419 10702078561470829910403629)
          ·
            refine ⟨4013279460551561216401361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10702078561470829910403629 4013279460551561216401361)
            ·
              refine ⟨3009959595413670912301021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4013279460551561216401361 3009959595413670912301021)
              ·
                refine ⟨1128734848280126592112883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3009959595413670912301021 1128734848280126592112883)
                ·
                  refine ⟨1693102272420189888169325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1128734848280126592112883 1693102272420189888169325)
                  ·
                    refine ⟨634913352157571208063497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1693102272420189888169325 634913352157571208063497)
                    ·
                      refine ⟨476185014118178406047623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 634913352157571208063497 476185014118178406047623)
                      ·
                        rfl

theorem cell23_927367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_927367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927367 prefixEnd_927367 := by exact prefixLift 927367
  have htrace : WordTrace (prefixWord ++ tailWord_927367) baseStart_927367 baseEnd_927367 := by
    simpa [prefixWord, tailWord_927367, baseEnd_927367] using wordTrace_append hprefix tailTrace_927367
  have hstable : (prefixWord ++ tailWord_927367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927367).length < 2 ^ (prefixWord ++ tailWord_927367).sum := by decide
  have hdescent : baseEnd_927367 < baseStart_927367 := by decide
  rcases family_descends (prefixWord ++ tailWord_927367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927414 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_927414 : Nat := 118140960795 + 927414 * 2 ^ 59
def prefixEnd_927414 : Nat := 4983230072969 + 3 ^ 40 * 927414 * 2
def baseEnd_927414 : Nat := 476209147708939722159907

theorem tailTrace_927414 : CollatzResearch.WordTrace tailWord_927414 prefixEnd_927414 476209147708939722159907 := by
  unfold tailWord_927414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2114097966384058909141331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22550378308096628364174197 2114097966384058909141331)
  ·
    refine ⟨3171146949576088363711997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2114097966384058909141331 3171146949576088363711997)
    ·
      refine ⟨1189180106091033136391999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3171146949576088363711997 1189180106091033136391999)
      ·
        refine ⟨1783770159136549704587999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1189180106091033136391999 1783770159136549704587999)
        ·
          refine ⟨2675655238704824556881999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783770159136549704587999 2675655238704824556881999)
          ·
            refine ⟨4013482858057236835322999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675655238704824556881999 4013482858057236835322999)
            ·
              refine ⟨6020224287085855252984499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013482858057236835322999 6020224287085855252984499)
              ·
                refine ⟨9030336430628782879476749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6020224287085855252984499 9030336430628782879476749)
                ·
                  refine ⟨3386376161485793579803781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9030336430628782879476749 3386376161485793579803781)
                  ·
                    refine ⟨634945530278586296213209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3386376161485793579803781 634945530278586296213209)
                    ·
                      refine ⟨476209147708939722159907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 634945530278586296213209 476209147708939722159907)
                      ·
                        rfl

theorem cell23_927414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_927414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927414 prefixEnd_927414 := by exact prefixLift 927414
  have htrace : WordTrace (prefixWord ++ tailWord_927414) baseStart_927414 baseEnd_927414 := by
    simpa [prefixWord, tailWord_927414, baseEnd_927414] using wordTrace_append hprefix tailTrace_927414
  have hstable : (prefixWord ++ tailWord_927414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927414).length < 2 ^ (prefixWord ++ tailWord_927414).sum := by decide
  have hdescent : baseEnd_927414 < baseStart_927414 := by decide
  rcases family_descends (prefixWord ++ tailWord_927414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927470 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_927470 : Nat := 118140960795 + 927470 * 2 ^ 59
def prefixEnd_927470 : Nat := 4983230072969 + 3 ^ 40 * 927470 * 2
def baseEnd_927470 : Nat := 476237902625591503059649

theorem tailTrace_927470 : CollatzResearch.WordTrace tailWord_927470 prefixEnd_927470 476237902625591503059649 := by
  unfold tailWord_927470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4228451243742758013787483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22551739966628042740199909 4228451243742758013787483)
  ·
    refine ⟨6342676865614137020681225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4228451243742758013787483 6342676865614137020681225)
    ·
      refine ⟨4757007649210602765510919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6342676865614137020681225 4757007649210602765510919)
      ·
        refine ⟨7135511473815904148266379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4757007649210602765510919 7135511473815904148266379)
        ·
          refine ⟨10703267210723856222399569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7135511473815904148266379 10703267210723856222399569)
          ·
            refine ⟨8027450408042892166799677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10703267210723856222399569 8027450408042892166799677)
            ·
              refine ⟨3010293903016084562549879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8027450408042892166799677 3010293903016084562549879)
              ·
                refine ⟨4515440854524126843824819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3010293903016084562549879 4515440854524126843824819)
                ·
                  refine ⟨6773161281786190265737229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4515440854524126843824819 6773161281786190265737229)
                  ·
                    refine ⟨2539935480669821349651461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6773161281786190265737229 2539935480669821349651461)
                    ·
                      refine ⟨476237902625591503059649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2539935480669821349651461 476237902625591503059649)
                      ·
                        rfl

theorem cell23_927470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_927470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927470 prefixEnd_927470 := by exact prefixLift 927470
  have htrace : WordTrace (prefixWord ++ tailWord_927470) baseStart_927470 baseEnd_927470 := by
    simpa [prefixWord, tailWord_927470, baseEnd_927470] using wordTrace_append hprefix tailTrace_927470
  have hstable : (prefixWord ++ tailWord_927470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927470).length < 2 ^ (prefixWord ++ tailWord_927470).sum := by decide
  have hdescent : baseEnd_927470 < baseStart_927470 := by decide
  rcases family_descends (prefixWord ++ tailWord_927470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927520 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 3]
def baseStart_927520 : Nat := 118140960795 + 927520 * 2 ^ 59
def prefixEnd_927520 : Nat := 4983230072969 + 3 ^ 40 * 927520 * 2
def baseEnd_927520 : Nat := 476263576658316307434419

theorem tailTrace_927520 : CollatzResearch.WordTrace tailWord_927520 prefixEnd_927520 476263576658316307434419 := by
  unfold tailWord_927520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16914716799880461324810007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22552955733173948433080009 16914716799880461324810007)
  ·
    refine ⟨25372075199820691987215011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16914716799880461324810007 25372075199820691987215011)
    ·
      refine ⟨38058112799731037980822517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25372075199820691987215011 38058112799731037980822517)
      ·
        refine ⟨3567948074974784810702111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38058112799731037980822517 3567948074974784810702111)
        ·
          refine ⟨5351922112462177216053167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3567948074974784810702111 5351922112462177216053167)
          ·
            refine ⟨8027883168693265824079751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5351922112462177216053167 8027883168693265824079751)
            ·
              refine ⟨12041824753039898736119627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8027883168693265824079751 12041824753039898736119627)
              ·
                refine ⟨18062737129559848104179441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12041824753039898736119627 18062737129559848104179441)
                ·
                  refine ⟨13547052847169886078134581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18062737129559848104179441 13547052847169886078134581)
                  ·
                    refine ⟨1270036204422176819825117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13547052847169886078134581 1270036204422176819825117)
                    ·
                      refine ⟨476263576658316307434419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1270036204422176819825117 476263576658316307434419)
                      ·
                        rfl

theorem cell23_927520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_927520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927520 prefixEnd_927520 := by exact prefixLift 927520
  have htrace : WordTrace (prefixWord ++ tailWord_927520) baseStart_927520 baseEnd_927520 := by
    simpa [prefixWord, tailWord_927520, baseEnd_927520] using wordTrace_append hprefix tailTrace_927520
  have hstable : (prefixWord ++ tailWord_927520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927520).length < 2 ^ (prefixWord ++ tailWord_927520).sum := by decide
  have hdescent : baseEnd_927520 < baseStart_927520 := by decide
  rcases family_descends (prefixWord ++ tailWord_927520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927587 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 1, 6]
def baseStart_927587 : Nat := 118140960795 + 927587 * 2 ^ 59
def prefixEnd_927587 : Nat := 4983230072969 + 3 ^ 40 * 927587 * 2
def baseEnd_927587 : Nat := 158765993287389181765537

theorem tailTrace_927587 : CollatzResearch.WordTrace tailWord_927587 prefixEnd_927587 158765993287389181765537 := by
  unfold tailWord_927587
  simp only [CollatzResearch.WordTrace]
  refine ⟨33831877290518193092309015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22554584860345462061539343 33831877290518193092309015)
  ·
    refine ⟨50747815935777289638463523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33831877290518193092309015 50747815935777289638463523)
    ·
      refine ⟨76121723903665934457695285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50747815935777289638463523 76121723903665934457695285)
      ·
        refine ⟨7136411615968681355408933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76121723903665934457695285 7136411615968681355408933)
        ·
          refine ⟨1338077177994127754139175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7136411615968681355408933 1338077177994127754139175)
          ·
            refine ⟨2007115766991191631208763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338077177994127754139175 2007115766991191631208763)
            ·
              refine ⟨3010673650486787446813145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007115766991191631208763 3010673650486787446813145)
              ·
                refine ⟨2258005237865090585109859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3010673650486787446813145 2258005237865090585109859)
                ·
                  refine ⟨3387007856797635877664789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258005237865090585109859 3387007856797635877664789)
                  ·
                    refine ⟨158765993287389181765537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3387007856797635877664789 158765993287389181765537)
                    ·
                      rfl

theorem cell23_927587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 6].length) (baseStart_927587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927587 prefixEnd_927587 := by exact prefixLift 927587
  have htrace : WordTrace (prefixWord ++ tailWord_927587) baseStart_927587 baseEnd_927587 := by
    simpa [prefixWord, tailWord_927587, baseEnd_927587] using wordTrace_append hprefix tailTrace_927587
  have hstable : (prefixWord ++ tailWord_927587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927587).length < 2 ^ (prefixWord ++ tailWord_927587).sum := by decide
  have hdescent : baseEnd_927587 < baseStart_927587 := by decide
  rcases family_descends (prefixWord ++ tailWord_927587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927597 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_927597 : Nat := 118140960795 + 927597 * 2 ^ 59
def prefixEnd_927597 : Nat := 4983230072969 + 3 ^ 40 * 927597 * 2
def baseEnd_927597 : Nat := 476303114668712506171565

theorem tailTrace_927597 : CollatzResearch.WordTrace tailWord_927597 prefixEnd_927597 476303114668712506171565 := by
  unfold tailWord_927597
  simp only [CollatzResearch.WordTrace]
  refine ⟨33832242020481964800173045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22554828013654643200115363 33832242020481964800173045)
  ·
    refine ⟨3171772689420184200016223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33832242020481964800173045 3171772689420184200016223)
    ·
      refine ⟨4757659034130276300024335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3171772689420184200016223 4757659034130276300024335)
      ·
        refine ⟨7136488551195414450036503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4757659034130276300024335 7136488551195414450036503)
        ·
          refine ⟨10704732826793121675054755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7136488551195414450036503 10704732826793121675054755)
          ·
            refine ⟨16057099240189682512582133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10704732826793121675054755 16057099240189682512582133)
            ·
              refine ⟨1505353053767782735554575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16057099240189682512582133 1505353053767782735554575)
              ·
                refine ⟨2258029580651674103331863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1505353053767782735554575 2258029580651674103331863)
                ·
                  refine ⟨3387044370977511154997795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258029580651674103331863 3387044370977511154997795)
                  ·
                    refine ⟨5080566556466266732496693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3387044370977511154997795 5080566556466266732496693)
                    ·
                      refine ⟨476303114668712506171565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5080566556466266732496693 476303114668712506171565)
                      ·
                        rfl

theorem cell23_927597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_927597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927597 prefixEnd_927597 := by exact prefixLift 927597
  have htrace : WordTrace (prefixWord ++ tailWord_927597) baseStart_927597 baseEnd_927597 := by
    simpa [prefixWord, tailWord_927597, baseEnd_927597] using wordTrace_append hprefix tailTrace_927597
  have hstable : (prefixWord ++ tailWord_927597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927597).length < 2 ^ (prefixWord ++ tailWord_927597).sum := by decide
  have hdescent : baseEnd_927597 < baseStart_927597 := by decide
  rcases family_descends (prefixWord ++ tailWord_927597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927620 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_927620 : Nat := 118140960795 + 927620 * 2 ^ 59
def prefixEnd_927620 : Nat := 4983230072969 + 3 ^ 40 * 927620 * 2
def baseEnd_927620 : Nat := 476314924723765916183959

theorem tailTrace_927620 : CollatzResearch.WordTrace tailWord_927620 prefixEnd_927620 476314924723765916183959 := by
  unfold tailWord_927620
  simp only [CollatzResearch.WordTrace]
  refine ⟨16916540449699319864130157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22555387266265759818840209 16916540449699319864130157)
  ·
    refine ⟨6343702668637244949048809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16916540449699319864130157 6343702668637244949048809)
    ·
      refine ⟨4757777001477933711786607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6343702668637244949048809 4757777001477933711786607)
      ·
        refine ⟨7136665502216900567679911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4757777001477933711786607 7136665502216900567679911)
        ·
          refine ⟨10704998253325350851519867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7136665502216900567679911 10704998253325350851519867)
          ·
            refine ⟨16057497379988026277279801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10704998253325350851519867 16057497379988026277279801)
            ·
              refine ⟨12043123034991019707959851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16057497379988026277279801 12043123034991019707959851)
              ·
                refine ⟨18064684552486529561939777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12043123034991019707959851 18064684552486529561939777)
                ·
                  refine ⟨13548513414364897171454833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18064684552486529561939777 13548513414364897171454833)
                  ·
                    refine ⟨10161385060773672878591125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13548513414364897171454833 10161385060773672878591125)
                    ·
                      refine ⟨476314924723765916183959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10161385060773672878591125 476314924723765916183959)
                      ·
                        rfl

theorem cell23_927620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_927620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927620 prefixEnd_927620 := by exact prefixLift 927620
  have htrace : WordTrace (prefixWord ++ tailWord_927620) baseStart_927620 baseEnd_927620 := by
    simpa [prefixWord, tailWord_927620, baseEnd_927620] using wordTrace_append hprefix tailTrace_927620
  have hstable : (prefixWord ++ tailWord_927620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927620).length < 2 ^ (prefixWord ++ tailWord_927620).sum := by decide
  have hdescent : baseEnd_927620 < baseStart_927620 := by decide
  rcases family_descends (prefixWord ++ tailWord_927620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927624 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_927624 : Nat := 118140960795 + 927624 * 2 ^ 59
def prefixEnd_927624 : Nat := 4983230072969 + 3 ^ 40 * 927624 * 2
def baseEnd_927624 : Nat := 476316978646383900533941

theorem tailTrace_927624 : CollatzResearch.WordTrace tailWord_927624 prefixEnd_927624 476316978646383900533941 := by
  unfold tailWord_927624
  simp only [CollatzResearch.WordTrace]
  refine ⟨16916613395692074205702963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22555484527589432274270617 16916613395692074205702963)
  ·
    refine ⟨25374920093538111308554445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16916613395692074205702963 25374920093538111308554445)
    ·
      refine ⟨9515595035076791740707917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25374920093538111308554445 9515595035076791740707917)
      ·
        refine ⟨3568348138153796902765469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9515595035076791740707917 3568348138153796902765469)
        ·
          refine ⟨1338130551807673838537051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3568348138153796902765469 1338130551807673838537051)
          ·
            refine ⟨2007195827711510757805577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338130551807673838537051 2007195827711510757805577)
            ·
              refine ⟨1505396870783633068354183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2007195827711510757805577 1505396870783633068354183)
              ·
                refine ⟨2258095306175449602531275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1505396870783633068354183 2258095306175449602531275)
                ·
                  refine ⟨3387142959263174403796913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258095306175449602531275 3387142959263174403796913)
                  ·
                    refine ⟨2540357219447380802847685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3387142959263174403796913 2540357219447380802847685)
                    ·
                      refine ⟨476316978646383900533941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2540357219447380802847685 476316978646383900533941)
                      ·
                        rfl

theorem cell23_927624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_927624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927624 prefixEnd_927624 := by exact prefixLift 927624
  have htrace : WordTrace (prefixWord ++ tailWord_927624) baseStart_927624 baseEnd_927624 := by
    simpa [prefixWord, tailWord_927624, baseEnd_927624] using wordTrace_append hprefix tailTrace_927624
  have hstable : (prefixWord ++ tailWord_927624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927624).length < 2 ^ (prefixWord ++ tailWord_927624).sum := by decide
  have hdescent : baseEnd_927624 < baseStart_927624 := by decide
  rcases family_descends (prefixWord ++ tailWord_927624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927627 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 6, 1, 3]
def baseStart_927627 : Nat := 118140960795 + 927627 * 2 ^ 59
def prefixEnd_927627 : Nat := 4983230072969 + 3 ^ 40 * 927627 * 2
def baseEnd_927627 : Nat := 476318519088347388796427

theorem tailTrace_927627 : CollatzResearch.WordTrace tailWord_927627 prefixEnd_927627 476318519088347388796427 := by
  unfold tailWord_927627
  simp only [CollatzResearch.WordTrace]
  refine ⟨33833336210373279923765135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22555557473582186615843423 33833336210373279923765135)
  ·
    refine ⟨50750004315559919885647703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33833336210373279923765135 50750004315559919885647703)
    ·
      refine ⟨76125006473339879828471555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50750004315559919885647703 76125006473339879828471555)
      ·
        refine ⟨114187509710009819742707333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76125006473339879828471555 114187509710009819742707333)
        ·
          refine ⟨21410158070626841201757625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114187509710009819742707333 21410158070626841201757625)
          ·
            refine ⟨16057618552970130901318219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21410158070626841201757625 16057618552970130901318219)
            ·
              refine ⟨24086427829455196351977329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16057618552970130901318219 24086427829455196351977329)
              ·
                refine ⟨18064820872091397263982997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24086427829455196351977329 18064820872091397263982997)
                ·
                  refine ⟨846788478379284246749203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18064820872091397263982997 846788478379284246749203)
                  ·
                    refine ⟨1270182717568926370123805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 846788478379284246749203 1270182717568926370123805)
                    ·
                      refine ⟨476318519088347388796427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1270182717568926370123805 476318519088347388796427)
                      ·
                        rfl

theorem cell23_927627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 1, 3].length) (baseStart_927627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927627 prefixEnd_927627 := by exact prefixLift 927627
  have htrace : WordTrace (prefixWord ++ tailWord_927627) baseStart_927627 baseEnd_927627 := by
    simpa [prefixWord, tailWord_927627, baseEnd_927627] using wordTrace_append hprefix tailTrace_927627
  have hstable : (prefixWord ++ tailWord_927627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927627).length < 2 ^ (prefixWord ++ tailWord_927627).sum := by decide
  have hdescent : baseEnd_927627 < baseStart_927627 := by decide
  rcases family_descends (prefixWord ++ tailWord_927627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927634 : List Nat := [3, 2, 3, 2, 1, 2, 3, 7]
def baseStart_927634 : Nat := 118140960795 + 927634 * 2 ^ 59
def prefixEnd_927634 : Nat := 4983230072969 + 3 ^ 40 * 927634 * 2
def baseEnd_927634 : Nat := 17641559757515883755885

theorem tailTrace_927634 : CollatzResearch.WordTrace tailWord_927634 prefixEnd_927634 17641559757515883755885 := by
  unfold tailWord_927634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8458397880336980029817489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22555727680898613412846637 8458397880336980029817489)
  ·
    refine ⟨6343798410252735022363117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8458397880336980029817489 6343798410252735022363117)
    ·
      refine ⟨2378924403844775633386169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6343798410252735022363117 2378924403844775633386169)
      ·
        refine ⟨1784193302883581725039627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2378924403844775633386169 1784193302883581725039627)
        ·
          refine ⟨2676289954325372587559441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1784193302883581725039627 2676289954325372587559441)
          ·
            refine ⟨2007217465744029440669581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2676289954325372587559441 2007217465744029440669581)
            ·
              refine ⟨752706549654011040251093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2007217465744029440669581 752706549654011040251093)
              ·
                refine ⟨17641559757515883755885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 752706549654011040251093 17641559757515883755885)
                ·
                  rfl

theorem cell23_927634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 7].length) (baseStart_927634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927634 prefixEnd_927634 := by exact prefixLift 927634
  have htrace : WordTrace (prefixWord ++ tailWord_927634) baseStart_927634 baseEnd_927634 := by
    simpa [prefixWord, tailWord_927634, baseEnd_927634] using wordTrace_append hprefix tailTrace_927634
  have hstable : (prefixWord ++ tailWord_927634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927634).length < 2 ^ (prefixWord ++ tailWord_927634).sum := by decide
  have hdescent : baseEnd_927634 < baseStart_927634 := by decide
  rcases family_descends (prefixWord ++ tailWord_927634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927644 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_927644 : Nat := 118140960795 + 927644 * 2 ^ 59
def prefixEnd_927644 : Nat := 4983230072969 + 3 ^ 40 * 927644 * 2
def baseEnd_927644 : Nat := 476327248259473822283849

theorem tailTrace_927644 : CollatzResearch.WordTrace tailWord_927644 prefixEnd_927644 476327248259473822283849 := by
  unfold tailWord_927644
  simp only [CollatzResearch.WordTrace]
  refine ⟨16916978125655845913566993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22555970834207794551422657 16916978125655845913566993)
  ·
    refine ⟨12687733594241884435175245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16916978125655845913566993 12687733594241884435175245)
    ·
      refine ⟨4757900097840706663190717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12687733594241884435175245 4757900097840706663190717)
      ·
        refine ⟨1784212536690264998696519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4757900097840706663190717 1784212536690264998696519)
        ·
          refine ⟨2676318805035397498044779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1784212536690264998696519 2676318805035397498044779)
          ·
            refine ⟨4014478207553096247067169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2676318805035397498044779 4014478207553096247067169)
            ·
              refine ⟨3010858655664822185300377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4014478207553096247067169 3010858655664822185300377)
              ·
                refine ⟨2258143991748616638975283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3010858655664822185300377 2258143991748616638975283)
                ·
                  refine ⟨3387215987622924958462925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2258143991748616638975283 3387215987622924958462925)
                  ·
                    refine ⟨1270205995358596859423597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3387215987622924958462925 1270205995358596859423597)
                    ·
                      refine ⟨476327248259473822283849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1270205995358596859423597 476327248259473822283849)
                      ·
                        rfl

theorem cell23_927644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_927644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927644 prefixEnd_927644 := by exact prefixLift 927644
  have htrace : WordTrace (prefixWord ++ tailWord_927644) baseStart_927644 baseEnd_927644 := by
    simpa [prefixWord, tailWord_927644, baseEnd_927644] using wordTrace_append hprefix tailTrace_927644
  have hstable : (prefixWord ++ tailWord_927644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927644).length < 2 ^ (prefixWord ++ tailWord_927644).sum := by decide
  have hdescent : baseEnd_927644 < baseStart_927644 := by decide
  rcases family_descends (prefixWord ++ tailWord_927644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927662 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_927662 : Nat := 118140960795 + 927662 * 2 ^ 59
def prefixEnd_927662 : Nat := 4983230072969 + 3 ^ 40 * 927662 * 2
def baseEnd_927662 : Nat := 476336490911254751858767

theorem tailTrace_927662 : CollatzResearch.WordTrace tailWord_927662 prefixEnd_927662 476336490911254751858767 := by
  unfold tailWord_927662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4229326595655810112661155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22556408510164320600859493 4229326595655810112661155)
  ·
    refine ⟨6343989893483715168991733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4229326595655810112661155 6343989893483715168991733)
    ·
      refine ⟨594749052514098297092975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6343989893483715168991733 594749052514098297092975)
      ·
        refine ⟨892123578771147445639463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594749052514098297092975 892123578771147445639463)
        ·
          refine ⟨1338185368156721168459195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892123578771147445639463 1338185368156721168459195)
          ·
            refine ⟨2007278052235081752688793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338185368156721168459195 2007278052235081752688793)
            ·
              refine ⟨1505458539176311314516595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2007278052235081752688793 1505458539176311314516595)
              ·
                refine ⟨2258187808764466971774893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1505458539176311314516595 2258187808764466971774893)
                ·
                  refine ⟨846820428286675114415585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2258187808764466971774893 846820428286675114415585)
                  ·
                    refine ⟨635115321215006335811689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 846820428286675114415585 635115321215006335811689)
                    ·
                      refine ⟨476336490911254751858767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 635115321215006335811689 476336490911254751858767)
                      ·
                        rfl

theorem cell23_927662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_927662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927662 prefixEnd_927662 := by exact prefixLift 927662
  have htrace : WordTrace (prefixWord ++ tailWord_927662) baseStart_927662 baseEnd_927662 := by
    simpa [prefixWord, tailWord_927662, baseEnd_927662] using wordTrace_append hprefix tailTrace_927662
  have hstable : (prefixWord ++ tailWord_927662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927662).length < 2 ^ (prefixWord ++ tailWord_927662).sum := by decide
  have hdescent : baseEnd_927662 < baseStart_927662 := by decide
  rcases family_descends (prefixWord ++ tailWord_927662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927677 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_927677 : Nat := 118140960795 + 927677 * 2 ^ 59
def prefixEnd_927677 : Nat := 4983230072969 + 3 ^ 40 * 927677 * 2
def baseEnd_927677 : Nat := 158781397707024064390399

theorem tailTrace_927677 : CollatzResearch.WordTrace tailWord_927677 prefixEnd_927677 158781397707024064390399 := by
  unfold tailWord_927677
  simp only [CollatzResearch.WordTrace]
  refine ⟨33835159860192138463085285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22556773240128092308723523 33835159860192138463085285)
  ·
    refine ⟨6344092473786025961828491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33835159860192138463085285 6344092473786025961828491)
    ·
      refine ⟨9516138710679038942742737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6344092473786025961828491 9516138710679038942742737)
      ·
        refine ⟨7137104033009279207057053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9516138710679038942742737 7137104033009279207057053)
        ·
          refine ⟨2676414012378479702646395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7137104033009279207057053 2676414012378479702646395)
          ·
            refine ⟨4014621018567719553969593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2676414012378479702646395 4014621018567719553969593)
            ·
              refine ⟨3010965763925789665477195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4014621018567719553969593 3010965763925789665477195)
              ·
                refine ⟨4516448645888684498215793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3010965763925789665477195 4516448645888684498215793)
                ·
                  refine ⟨3387336484416513373661845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4516448645888684498215793 3387336484416513373661845)
                  ·
                    refine ⟨158781397707024064390399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3387336484416513373661845 158781397707024064390399)
                    ·
                      rfl

theorem cell23_927677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_927677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927677 prefixEnd_927677 := by exact prefixLift 927677
  have htrace : WordTrace (prefixWord ++ tailWord_927677) baseStart_927677 baseEnd_927677 := by
    simpa [prefixWord, tailWord_927677, baseEnd_927677] using wordTrace_append hprefix tailTrace_927677
  have hstable : (prefixWord ++ tailWord_927677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927677).length < 2 ^ (prefixWord ++ tailWord_927677).sum := by decide
  have hdescent : baseEnd_927677 < baseStart_927677 := by decide
  rcases family_descends (prefixWord ++ tailWord_927677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927678 : List Nat := [4, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_927678 : Nat := 118140960795 + 927678 * 2 ^ 59
def prefixEnd_927678 : Nat := 4983230072969 + 3 ^ 40 * 927678 * 2
def baseEnd_927678 : Nat := 476344706601726689258693

theorem tailTrace_927678 : CollatzResearch.WordTrace tailWord_927678 prefixEnd_927678 476344706601726689258693 := by
  unfold tailWord_927678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4229399541648564454233961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22556797555459010422581125 4229399541648564454233961)
  ·
    refine ⟨3172049656236423340675471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4229399541648564454233961 3172049656236423340675471)
    ·
      refine ⟨4758074484354635011013207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3172049656236423340675471 4758074484354635011013207)
      ·
        refine ⟨7137111726531952516519811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4758074484354635011013207 7137111726531952516519811)
        ·
          refine ⟨10705667589797928774779717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7137111726531952516519811 10705667589797928774779717)
          ·
            refine ⟨2007312673087111645271197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10705667589797928774779717 2007312673087111645271197)
            ·
              refine ⟨752742252407666866976699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2007312673087111645271197 752742252407666866976699)
              ·
                refine ⟨1129113378611500300465049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752742252407666866976699 1129113378611500300465049)
                ·
                  refine ⟨846835033958625225348787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1129113378611500300465049 846835033958625225348787)
                  ·
                    refine ⟨1270252550937937838023181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 846835033958625225348787 1270252550937937838023181)
                    ·
                      refine ⟨476344706601726689258693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1270252550937937838023181 476344706601726689258693)
                      ·
                        rfl

theorem cell23_927678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_927678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927678 prefixEnd_927678 := by exact prefixLift 927678
  have htrace : WordTrace (prefixWord ++ tailWord_927678) baseStart_927678 baseEnd_927678 := by
    simpa [prefixWord, tailWord_927678, baseEnd_927678] using wordTrace_append hprefix tailTrace_927678
  have hstable : (prefixWord ++ tailWord_927678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927678).length < 2 ^ (prefixWord ++ tailWord_927678).sum := by decide
  have hdescent : baseEnd_927678 < baseStart_927678 := by decide
  rcases family_descends (prefixWord ++ tailWord_927678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927701 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 4, 2, 2]
def baseStart_927701 : Nat := 118140960795 + 927701 * 2 ^ 59
def prefixEnd_927701 : Nat := 4983230072969 + 3 ^ 40 * 927701 * 2
def baseEnd_927701 : Nat := 476356516656780099271087

theorem tailTrace_927701 : CollatzResearch.WordTrace tailWord_927701 prefixEnd_927701 476356516656780099271087 := by
  unfold tailWord_927701
  simp only [CollatzResearch.WordTrace]
  refine ⟨33836035212105190561958957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22557356808070127041305971 33836035212105190561958957)
  ·
    refine ⟨12688513204539446460734609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33836035212105190561958957 12688513204539446460734609)
    ·
      refine ⟨9516384903404584845550957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12688513204539446460734609 9516384903404584845550957)
      ·
        refine ⟨3568644338776719317081609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9516384903404584845550957 3568644338776719317081609)
        ·
          refine ⟨2676483254082539487811207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3568644338776719317081609 2676483254082539487811207)
          ·
            refine ⟨4014724881123809231716811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2676483254082539487811207 4014724881123809231716811)
            ·
              refine ⟨6022087321685713847575217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4014724881123809231716811 6022087321685713847575217)
              ·
                refine ⟨4516565491264285385681413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6022087321685713847575217 4516565491264285385681413)
                ·
                  refine ⟨846856029612053509815265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4516565491264285385681413 846856029612053509815265)
                  ·
                    refine ⟨635142022209040132361449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 846856029612053509815265 635142022209040132361449)
                    ·
                      refine ⟨476356516656780099271087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 635142022209040132361449 476356516656780099271087)
                      ·
                        rfl

theorem cell23_927701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_927701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927701 prefixEnd_927701 := by exact prefixLift 927701
  have htrace : WordTrace (prefixWord ++ tailWord_927701) baseStart_927701 baseEnd_927701 := by
    simpa [prefixWord, tailWord_927701, baseEnd_927701] using wordTrace_append hprefix tailTrace_927701
  have hstable : (prefixWord ++ tailWord_927701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927701).length < 2 ^ (prefixWord ++ tailWord_927701).sum := by decide
  have hdescent : baseEnd_927701 < baseStart_927701 := by decide
  rcases family_descends (prefixWord ++ tailWord_927701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927801 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 3, 4]
def baseStart_927801 : Nat := 118140960795 + 927801 * 2 ^ 59
def prefixEnd_927801 : Nat := 4983230072969 + 3 ^ 40 * 927801 * 2
def baseEnd_927801 : Nat := 158802621574076569340209

theorem tailTrace_927801 : CollatzResearch.WordTrace tailWord_927801 prefixEnd_927801 158802621574076569340209 := by
  unfold tailWord_927801
  simp only [CollatzResearch.WordTrace]
  refine ⟨33839682511742907640599257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22559788341161938427066171 33839682511742907640599257)
  ·
    refine ⟨25379761883807180730449443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33839682511742907640599257 25379761883807180730449443)
    ·
      refine ⟨38069642825710771095674165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25379761883807180730449443 38069642825710771095674165)
      ·
        refine ⟨3569029014910384790219453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38069642825710771095674165 3569029014910384790219453)
        ·
          refine ⟨1338385880591394296332295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3569029014910384790219453 1338385880591394296332295)
          ·
            refine ⟨2007578820887091444498443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338385880591394296332295 2007578820887091444498443)
            ·
              refine ⟨3011368231330637166747665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007578820887091444498443 3011368231330637166747665)
              ·
                refine ⟨2258526173497977875060749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3011368231330637166747665 2258526173497977875060749)
                ·
                  refine ⟨846947315061741703147781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2258526173497977875060749 846947315061741703147781)
                  ·
                    refine ⟨158802621574076569340209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 846947315061741703147781 158802621574076569340209)
                    ·
                      rfl

theorem cell23_927801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 4].length) (baseStart_927801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927801 prefixEnd_927801 := by exact prefixLift 927801
  have htrace : WordTrace (prefixWord ++ tailWord_927801) baseStart_927801 baseEnd_927801 := by
    simpa [prefixWord, tailWord_927801, baseEnd_927801] using wordTrace_append hprefix tailTrace_927801
  have hstable : (prefixWord ++ tailWord_927801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927801).length < 2 ^ (prefixWord ++ tailWord_927801).sum := by decide
  have hdescent : baseEnd_927801 < baseStart_927801 := by decide
  rcases family_descends (prefixWord ++ tailWord_927801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927864 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 1, 8, 2]
def baseStart_927864 : Nat := 118140960795 + 927864 * 2 ^ 59
def prefixEnd_927864 : Nat := 4983230072969 + 3 ^ 40 * 927864 * 2
def baseEnd_927864 : Nat := 476440214003462961532837

theorem tailTrace_927864 : CollatzResearch.WordTrace tailWord_927864 prefixEnd_927864 476440214003462961532837 := by
  unfold tailWord_927864
  simp only [CollatzResearch.WordTrace]
  refine ⟨16920990155257334700071323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22561320207009779600095097 16920990155257334700071323)
  ·
    refine ⟨25381485232886002050106985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16920990155257334700071323 25381485232886002050106985)
    ·
      refine ⟨19036113924664501537580239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25381485232886002050106985 19036113924664501537580239)
      ·
        refine ⟨28554170886996752306370359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19036113924664501537580239 28554170886996752306370359)
        ·
          refine ⟨42831256330495128459555539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28554170886996752306370359 42831256330495128459555539)
          ·
            refine ⟨64246884495742692689333309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42831256330495128459555539 64246884495742692689333309)
            ·
              refine ⟨24092581685903509758499991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64246884495742692689333309 24092581685903509758499991)
              ·
                refine ⟨36138872528855264637749987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24092581685903509758499991 36138872528855264637749987)
                ·
                  refine ⟨54208308793282896956624981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36138872528855264637749987 54208308793282896956624981)
                  ·
                    refine ⟨635253618671283948710449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54208308793282896956624981 635253618671283948710449)
                    ·
                      refine ⟨476440214003462961532837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 635253618671283948710449 476440214003462961532837)
                      ·
                        rfl

theorem cell23_927864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 8, 2].length) (baseStart_927864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927864 prefixEnd_927864 := by exact prefixLift 927864
  have htrace : WordTrace (prefixWord ++ tailWord_927864) baseStart_927864 baseEnd_927864 := by
    simpa [prefixWord, tailWord_927864, baseEnd_927864] using wordTrace_append hprefix tailTrace_927864
  have hstable : (prefixWord ++ tailWord_927864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927864).length < 2 ^ (prefixWord ++ tailWord_927864).sum := by decide
  have hdescent : baseEnd_927864 < baseStart_927864 := by decide
  rcases family_descends (prefixWord ++ tailWord_927864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927875 : List Nat := [1, 1, 1, 3, 3, 5, 1, 3, 1, 1, 3]
def baseStart_927875 : Nat := 118140960795 + 927875 * 2 ^ 59
def prefixEnd_927875 : Nat := 4983230072969 + 3 ^ 40 * 927875 * 2
def baseEnd_927875 : Nat := 476445862290662418495287

theorem tailTrace_927875 : CollatzResearch.WordTrace tailWord_927875 prefixEnd_927875 476445862290662418495287 := by
  unfold tailWord_927875
  simp only [CollatzResearch.WordTrace]
  refine ⟨33842381513474818278793079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22561587675649878852528719 33842381513474818278793079)
  ·
    refine ⟨50763572270212227418189619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33842381513474818278793079 50763572270212227418189619)
    ·
      refine ⟨76145358405318341127284429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50763572270212227418189619 76145358405318341127284429)
      ·
        refine ⟨28554509401994377922731661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76145358405318341127284429 28554509401994377922731661)
        ·
          refine ⟨10707941025747891721024373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28554509401994377922731661 10707941025747891721024373)
          ·
            refine ⟨1003869471163864848846035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10707941025747891721024373 1003869471163864848846035)
            ·
              refine ⟨1505804206745797273269053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003869471163864848846035 1505804206745797273269053)
              ·
                refine ⟨564676577529673977475895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1505804206745797273269053 564676577529673977475895)
                ·
                  refine ⟨847014866294510966213843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 564676577529673977475895 847014866294510966213843)
                  ·
                    refine ⟨1270522299441766449320765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 847014866294510966213843 1270522299441766449320765)
                    ·
                      refine ⟨476445862290662418495287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1270522299441766449320765 476445862290662418495287)
                      ·
                        rfl

theorem cell23_927875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 1, 1, 3].length) (baseStart_927875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927875 prefixEnd_927875 := by exact prefixLift 927875
  have htrace : WordTrace (prefixWord ++ tailWord_927875) baseStart_927875 baseEnd_927875 := by
    simpa [prefixWord, tailWord_927875, baseEnd_927875] using wordTrace_append hprefix tailTrace_927875
  have hstable : (prefixWord ++ tailWord_927875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927875).length < 2 ^ (prefixWord ++ tailWord_927875).sum := by decide
  have hdescent : baseEnd_927875 < baseStart_927875 := by decide
  rcases family_descends (prefixWord ++ tailWord_927875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927884 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 7, 2, 3]
def baseStart_927884 : Nat := 118140960795 + 927884 * 2 ^ 59
def prefixEnd_927884 : Nat := 4983230072969 + 3 ^ 40 * 927884 * 2
def baseEnd_927884 : Nat := 476450483616552883282745

theorem tailTrace_927884 : CollatzResearch.WordTrace tailWord_927884 prefixEnd_927884 476450483616552883282745 := by
  unfold tailWord_927884
  simp only [CollatzResearch.WordTrace]
  refine ⟨16921354885221106407935353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22561806513628141877247137 16921354885221106407935353)
  ·
    refine ⟨12691016163915829805951515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16921354885221106407935353 12691016163915829805951515)
    ·
      refine ⟨19036524245873744708927273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12691016163915829805951515 19036524245873744708927273)
      ·
        refine ⟨14277393184405308531695455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19036524245873744708927273 14277393184405308531695455)
        ·
          refine ⟨21416089776607962797543183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14277393184405308531695455 21416089776607962797543183)
          ·
            refine ⟨32124134664911944196314775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21416089776607962797543183 32124134664911944196314775)
            ·
              refine ⟨48186201997367916294472163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32124134664911944196314775 48186201997367916294472163)
              ·
                refine ⟨72279302996051874441708245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48186201997367916294472163 72279302996051874441708245)
                ·
                  refine ⟨1694046163969965807227537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 72279302996051874441708245 1694046163969965807227537)
                  ·
                    refine ⟨1270534622977474355420653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1694046163969965807227537 1270534622977474355420653)
                    ·
                      refine ⟨476450483616552883282745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1270534622977474355420653 476450483616552883282745)
                      ·
                        rfl

theorem cell23_927884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_927884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927884 prefixEnd_927884 := by exact prefixLift 927884
  have htrace : WordTrace (prefixWord ++ tailWord_927884) baseStart_927884 baseEnd_927884 := by
    simpa [prefixWord, tailWord_927884, baseEnd_927884] using wordTrace_append hprefix tailTrace_927884
  have hstable : (prefixWord ++ tailWord_927884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927884).length < 2 ^ (prefixWord ++ tailWord_927884).sum := by decide
  have hdescent : baseEnd_927884 < baseStart_927884 := by decide
  rcases family_descends (prefixWord ++ tailWord_927884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927892 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_927892 : Nat := 118140960795 + 927892 * 2 ^ 59
def prefixEnd_927892 : Nat := 4983230072969 + 3 ^ 40 * 927892 * 2
def baseEnd_927892 : Nat := 476454591461788851982709

theorem tailTrace_927892 : CollatzResearch.WordTrace tailWord_927892 prefixEnd_927892 476454591461788851982709 := by
  unfold tailWord_927892
  simp only [CollatzResearch.WordTrace]
  refine ⟨16921500777206615091080965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22562001036275486788107953 16921500777206615091080965)
  ·
    refine ⟨3172781395726240329577681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16921500777206615091080965 3172781395726240329577681)
    ·
      refine ⟨2379586046794680247183261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3172781395726240329577681 2379586046794680247183261)
      ·
        refine ⟨892344767548005092693723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2379586046794680247183261 892344767548005092693723)
        ·
          refine ⟨1338517151322007639040585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892344767548005092693723 1338517151322007639040585)
          ·
            refine ⟨1003887863491505729280439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338517151322007639040585 1003887863491505729280439)
            ·
              refine ⟨1505831795237258593920659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003887863491505729280439 1505831795237258593920659)
              ·
                refine ⟨2258747692855887890880989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1505831795237258593920659 2258747692855887890880989)
                ·
                  refine ⟨847030384820957959080371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2258747692855887890880989 847030384820957959080371)
                  ·
                    refine ⟨1270545577231436938620557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 847030384820957959080371 1270545577231436938620557)
                    ·
                      refine ⟨476454591461788851982709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1270545577231436938620557 476454591461788851982709)
                      ·
                        rfl

theorem cell23_927892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_927892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927892 prefixEnd_927892 := by exact prefixLift 927892
  have htrace : WordTrace (prefixWord ++ tailWord_927892) baseStart_927892 baseEnd_927892 := by
    simpa [prefixWord, tailWord_927892, baseEnd_927892] using wordTrace_append hprefix tailTrace_927892
  have hstable : (prefixWord ++ tailWord_927892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927892).length < 2 ^ (prefixWord ++ tailWord_927892).sum := by decide
  have hdescent : baseEnd_927892 < baseStart_927892 := by decide
  rcases family_descends (prefixWord ++ tailWord_927892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927904 : List Nat := [2, 1, 1, 4, 2, 3, 2, 8]
def baseStart_927904 : Nat := 118140960795 + 927904 * 2 ^ 59
def prefixEnd_927904 : Nat := 4983230072969 + 3 ^ 40 * 927904 * 2
def baseEnd_927904 : Nat := 17646694564060844630839

theorem tailTrace_927904 : CollatzResearch.WordTrace tailWord_927904 prefixEnd_927904 17646694564060844630839 := by
  unfold tailWord_927904
  simp only [CollatzResearch.WordTrace]
  refine ⟨16921719615184878115799383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22562292820246504154399177 16921719615184878115799383)
  ·
    refine ⟨25382579422777317173699075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16921719615184878115799383 25382579422777317173699075)
    ·
      refine ⟨38073869134165975760548613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25382579422777317173699075 38073869134165975760548613)
      ·
        refine ⟨7138850462656120455102865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38073869134165975760548613 7138850462656120455102865)
        ·
          refine ⟨5354137846992090341327149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7138850462656120455102865 5354137846992090341327149)
          ·
            refine ⟨2007801692622033877997681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5354137846992090341327149 2007801692622033877997681)
            ·
              refine ⟨1505851269466525408498261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2007801692622033877997681 1505851269466525408498261)
              ·
                refine ⟨17646694564060844630839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1505851269466525408498261 17646694564060844630839)
                ·
                  rfl

theorem cell23_927904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 8].length) (baseStart_927904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927904 prefixEnd_927904 := by exact prefixLift 927904
  have htrace : WordTrace (prefixWord ++ tailWord_927904) baseStart_927904 baseEnd_927904 := by
    simpa [prefixWord, tailWord_927904, baseEnd_927904] using wordTrace_append hprefix tailTrace_927904
  have hstable : (prefixWord ++ tailWord_927904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927904).length < 2 ^ (prefixWord ++ tailWord_927904).sum := by decide
  have hdescent : baseEnd_927904 < baseStart_927904 := by decide
  rcases family_descends (prefixWord ++ tailWord_927904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927908 : List Nat := [2, 3, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_927908 : Nat := 118140960795 + 927908 * 2 ^ 59
def prefixEnd_927908 : Nat := 4983230072969 + 3 ^ 40 * 927908 * 2
def baseEnd_927908 : Nat := 158820935717420263127545

theorem tailTrace_927908 : CollatzResearch.WordTrace tailWord_927908 prefixEnd_927908 158820935717420263127545 := by
  unfold tailWord_927908
  simp only [CollatzResearch.WordTrace]
  refine ⟨16921792561177632457372189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22562390081570176609829585 16921792561177632457372189)
  ·
    refine ⟨6345672210441612171514571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16921792561177632457372189 6345672210441612171514571)
    ·
      refine ⟨9518508315662418257271857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6345672210441612171514571 9518508315662418257271857)
      ·
        refine ⟨7138881236746813692953893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9518508315662418257271857 7138881236746813692953893)
        ·
          refine ⟨1338540231890027567428855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7138881236746813692953893 1338540231890027567428855)
          ·
            refine ⟨2007810347835041351143283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338540231890027567428855 2007810347835041351143283)
            ·
              refine ⟨3011715521752562026714925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007810347835041351143283 3011715521752562026714925)
              ·
                refine ⟨1129393320657210760018097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3011715521752562026714925 1129393320657210760018097)
                ·
                  refine ⟨847044990492908070013573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1129393320657210760018097 847044990492908070013573)
                  ·
                    refine ⟨158820935717420263127545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 847044990492908070013573 158820935717420263127545)
                    ·
                      rfl

theorem cell23_927908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_927908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927908 prefixEnd_927908 := by exact prefixLift 927908
  have htrace : WordTrace (prefixWord ++ tailWord_927908) baseStart_927908 baseEnd_927908 := by
    simpa [prefixWord, tailWord_927908, baseEnd_927908] using wordTrace_append hprefix tailTrace_927908
  have hstable : (prefixWord ++ tailWord_927908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927908).length < 2 ^ (prefixWord ++ tailWord_927908).sum := by decide
  have hdescent : baseEnd_927908 < baseStart_927908 := by decide
  rcases family_descends (prefixWord ++ tailWord_927908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927965 : List Nat := [1, 4, 3, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_927965 : Nat := 118140960795 + 927965 * 2 ^ 59
def prefixEnd_927965 : Nat := 4983230072969 + 3 ^ 40 * 927965 * 2
def baseEnd_927965 : Nat := 476492075549567066369873

theorem tailTrace_927965 : CollatzResearch.WordTrace tailWord_927965 prefixEnd_927965 476492075549567066369873 := by
  unfold tailWord_927965
  simp only [CollatzResearch.WordTrace]
  refine ⟨33845664083148763649569349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22563776055432509099712899 33845664083148763649569349)
  ·
    refine ⟨6346062015590393184294253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33845664083148763649569349 6346062015590393184294253)
    ·
      refine ⟨2379773255846397444110345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6346062015590393184294253 2379773255846397444110345)
      ·
        refine ⟨1784829941884798083082759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2379773255846397444110345 1784829941884798083082759)
        ·
          refine ⟨2677244912827197124624139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1784829941884798083082759 2677244912827197124624139)
          ·
            refine ⟨4015867369240795686936209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677244912827197124624139 4015867369240795686936209)
            ·
              refine ⟨3011900526930596765202157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4015867369240795686936209 3011900526930596765202157)
              ·
                refine ⟨1129462697598973786950809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3011900526930596765202157 1129462697598973786950809)
                ·
                  refine ⟨847097023199230340213107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1129462697598973786950809 847097023199230340213107)
                  ·
                    refine ⟨1270645534798845510319661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 847097023199230340213107 1270645534798845510319661)
                    ·
                      refine ⟨476492075549567066369873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1270645534798845510319661 476492075549567066369873)
                      ·
                        rfl

theorem cell23_927965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_927965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_927965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_927965 prefixEnd_927965 := by exact prefixLift 927965
  have htrace : WordTrace (prefixWord ++ tailWord_927965) baseStart_927965 baseEnd_927965 := by
    simpa [prefixWord, tailWord_927965, baseEnd_927965] using wordTrace_append hprefix tailTrace_927965
  have hstable : (prefixWord ++ tailWord_927965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927965).length < 2 ^ (prefixWord ++ tailWord_927965).sum := by decide
  have hdescent : baseEnd_927965 < baseStart_927965 := by decide
  rcases family_descends (prefixWord ++ tailWord_927965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928011 : List Nat := [1, 1, 1, 1, 5, 2, 1, 6, 5]
def baseStart_928011 : Nat := 118140960795 + 928011 * 2 ^ 59
def prefixEnd_928011 : Nat := 4983230072969 + 3 ^ 40 * 928011 * 2
def baseEnd_928011 : Nat := 52946188406630431821629

theorem tailTrace_928011 : CollatzResearch.WordTrace tailWord_928011 prefixEnd_928011 52946188406630431821629 := by
  unfold tailWord_928011
  simp only [CollatzResearch.WordTrace]
  refine ⟨33847341840982113505743887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22564894560654742337162591 33847341840982113505743887)
  ·
    refine ⟨50771012761473170258615831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33847341840982113505743887 50771012761473170258615831)
    ·
      refine ⟨76156519142209755387923747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50771012761473170258615831 76156519142209755387923747)
      ·
        refine ⟨114234778713314633081885621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76156519142209755387923747 114234778713314633081885621)
        ·
          refine ⟨10709510504373246851426777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114234778713314633081885621 10709510504373246851426777)
          ·
            refine ⟨8032132878279935138570083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10709510504373246851426777 8032132878279935138570083)
            ·
              refine ⟨12048199317419902707855125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8032132878279935138570083 12048199317419902707855125)
              ·
                refine ⟨564759343004057939430709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12048199317419902707855125 564759343004057939430709)
                ·
                  refine ⟨52946188406630431821629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 564759343004057939430709 52946188406630431821629)
                  ·
                    rfl

theorem cell23_928011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 5].length) (baseStart_928011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928011 prefixEnd_928011 := by exact prefixLift 928011
  have htrace : WordTrace (prefixWord ++ tailWord_928011) baseStart_928011 baseEnd_928011 := by
    simpa [prefixWord, tailWord_928011, baseEnd_928011] using wordTrace_append hprefix tailTrace_928011
  have hstable : (prefixWord ++ tailWord_928011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928011).length < 2 ^ (prefixWord ++ tailWord_928011).sum := by decide
  have hdescent : baseEnd_928011 < baseStart_928011 := by decide
  rcases family_descends (prefixWord ++ tailWord_928011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928021 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_928021 : Nat := 118140960795 + 928021 * 2 ^ 59
def prefixEnd_928021 : Nat := 4983230072969 + 3 ^ 40 * 928021 * 2
def baseEnd_928021 : Nat := 476520830466218847269615

theorem tailTrace_928021 : CollatzResearch.WordTrace tailWord_928021 prefixEnd_928021 476520830466218847269615 := by
  unfold tailWord_928021
  simp only [CollatzResearch.WordTrace]
  refine ⟨33847706570945885213607917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22565137713963923475738611 33847706570945885213607917)
  ·
    refine ⟨12692889964104706955102969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33847706570945885213607917 12692889964104706955102969)
    ·
      refine ⟨9519667473078530216327227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12692889964104706955102969 9519667473078530216327227)
      ·
        refine ⟨14279501209617795324490841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9519667473078530216327227 14279501209617795324490841)
        ·
          refine ⟨10709625907213346493368131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14279501209617795324490841 10709625907213346493368131)
          ·
            refine ⟨16064438860820019740052197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10709625907213346493368131 16064438860820019740052197)
            ·
              refine ⟨3012082286403753701259787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16064438860820019740052197 3012082286403753701259787)
              ·
                refine ⟨4518123429605630551889681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012082286403753701259787 4518123429605630551889681)
                ·
                  refine ⟨3388592572204222913917261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4518123429605630551889681 3388592572204222913917261)
                  ·
                    refine ⟨1270722214576583592718973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3388592572204222913917261 1270722214576583592718973)
                    ·
                      refine ⟨476520830466218847269615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1270722214576583592718973 476520830466218847269615)
                      ·
                        rfl

theorem cell23_928021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_928021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928021 prefixEnd_928021 := by exact prefixLift 928021
  have htrace : WordTrace (prefixWord ++ tailWord_928021) baseStart_928021 baseEnd_928021 := by
    simpa [prefixWord, tailWord_928021, baseEnd_928021] using wordTrace_append hprefix tailTrace_928021
  have hstable : (prefixWord ++ tailWord_928021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928021).length < 2 ^ (prefixWord ++ tailWord_928021).sum := by decide
  have hdescent : baseEnd_928021 < baseStart_928021 := by decide
  rcases family_descends (prefixWord ++ tailWord_928021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928024 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 3, 7]
def baseStart_928024 : Nat := 118140960795 + 928024 * 2 ^ 59
def prefixEnd_928024 : Nat := 4983230072969 + 3 ^ 40 * 928024 * 2
def baseEnd_928024 : Nat := 158840790302727445177367

theorem tailTrace_928024 : CollatzResearch.WordTrace tailWord_928024 prefixEnd_928024 158840790302727445177367 := by
  unfold tailWord_928024
  simp only [CollatzResearch.WordTrace]
  refine ⟨16923907994967508362983563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22565210659956677817311417 16923907994967508362983563)
  ·
    refine ⟨25385861992451262544475345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16923907994967508362983563 25385861992451262544475345)
    ·
      refine ⟨19039396494338446908356509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25385861992451262544475345 19039396494338446908356509)
      ·
        refine ⟨7139773685376917590633691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19039396494338446908356509 7139773685376917590633691)
        ·
          refine ⟨10709660528065376385950537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139773685376917590633691 10709660528065376385950537)
          ·
            refine ⟨8032245396049032289462903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10709660528065376385950537 8032245396049032289462903)
            ·
              refine ⟨12048368094073548434194355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8032245396049032289462903 12048368094073548434194355)
              ·
                refine ⟨18072552141110322651291533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12048368094073548434194355 18072552141110322651291533)
                ·
                  refine ⟨6777207052916370994234325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18072552141110322651291533 6777207052916370994234325)
                  ·
                    refine ⟨158840790302727445177367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6777207052916370994234325 158840790302727445177367)
                    ·
                      rfl

theorem cell23_928024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_928024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928024 prefixEnd_928024 := by exact prefixLift 928024
  have htrace : WordTrace (prefixWord ++ tailWord_928024) baseStart_928024 baseEnd_928024 := by
    simpa [prefixWord, tailWord_928024, baseEnd_928024] using wordTrace_append hprefix tailTrace_928024
  have hstable : (prefixWord ++ tailWord_928024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928024).length < 2 ^ (prefixWord ++ tailWord_928024).sum := by decide
  have hdescent : baseEnd_928024 < baseStart_928024 := by decide
  rcases family_descends (prefixWord ++ tailWord_928024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928064 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 5]
def baseStart_928064 : Nat := 118140960795 + 928064 * 2 ^ 59
def prefixEnd_928064 : Nat := 4983230072969 + 3 ^ 40 * 928064 * 2
def baseEnd_928064 : Nat := 476542910134362179031917

theorem tailTrace_928064 : CollatzResearch.WordTrace tailWord_928064 prefixEnd_928064 476542910134362179031917 := by
  unfold tailWord_928064
  simp only [CollatzResearch.WordTrace]
  refine ⟨16924637454895051778711623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22566183273193402371615497 16924637454895051778711623)
  ·
    refine ⟨25386956182342577668067435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16924637454895051778711623 25386956182342577668067435)
    ·
      refine ⟨38080434273513866502101153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25386956182342577668067435 38080434273513866502101153)
      ·
        refine ⟨28560325705135399876575865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38080434273513866502101153 28560325705135399876575865)
        ·
          refine ⟨21420244278851549907431899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28560325705135399876575865 21420244278851549907431899)
          ·
            refine ⟨32130366418277324861147849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21420244278851549907431899 32130366418277324861147849)
            ·
              refine ⟨24097774813707993645860887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32130366418277324861147849 24097774813707993645860887)
              ·
                refine ⟨36146662220561990468791331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24097774813707993645860887 36146662220561990468791331)
                ·
                  refine ⟨54219993330842985703186997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36146662220561990468791331 54219993330842985703186997)
                  ·
                    refine ⟨5083124374766529909673781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54219993330842985703186997 5083124374766529909673781)
                    ·
                      refine ⟨476542910134362179031917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5083124374766529909673781 476542910134362179031917)
                      ·
                        rfl

theorem cell23_928064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_928064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928064 prefixEnd_928064 := by exact prefixLift 928064
  have htrace : WordTrace (prefixWord ++ tailWord_928064) baseStart_928064 baseEnd_928064 := by
    simpa [prefixWord, tailWord_928064, baseEnd_928064] using wordTrace_append hprefix tailTrace_928064
  have hstable : (prefixWord ++ tailWord_928064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928064).length < 2 ^ (prefixWord ++ tailWord_928064).sum := by decide
  have hdescent : baseEnd_928064 < baseStart_928064 := by decide
  rcases family_descends (prefixWord ++ tailWord_928064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928178 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_928178 : Nat := 118140960795 + 928178 * 2 ^ 59
def prefixEnd_928178 : Nat := 4983230072969 + 3 ^ 40 * 928178 * 2
def baseEnd_928178 : Nat := 158867148976324911002131

theorem tailTrace_928178 : CollatzResearch.WordTrace tailWord_928178 prefixEnd_928178 158867148976324911002131 := by
  unfold tailWord_928178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8463358207844275256768297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22568955220918067351382125 8463358207844275256768297)
  ·
    refine ⟨6347518655883206442576223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8463358207844275256768297 6347518655883206442576223)
    ·
      refine ⟨9521277983824809663864335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6347518655883206442576223 9521277983824809663864335)
      ·
        refine ⟨14281916975737214495796503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9521277983824809663864335 14281916975737214495796503)
        ·
          refine ⟨21422875463605821743694755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14281916975737214495796503 21422875463605821743694755)
          ·
            refine ⟨32134313195408732615542133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21422875463605821743694755 32134313195408732615542133)
            ·
              refine ⟨3012591862069568682707075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32134313195408732615542133 3012591862069568682707075)
              ·
                refine ⟨4518887793104353024060613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012591862069568682707075 4518887793104353024060613)
                ·
                  refine ⟨847291461207066192011365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4518887793104353024060613 847291461207066192011365)
                  ·
                    refine ⟨158867148976324911002131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 847291461207066192011365 158867148976324911002131)
                    ·
                      rfl

theorem cell23_928178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_928178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928178 prefixEnd_928178 := by exact prefixLift 928178
  have htrace : WordTrace (prefixWord ++ tailWord_928178) baseStart_928178 baseEnd_928178 := by
    simpa [prefixWord, tailWord_928178, baseEnd_928178] using wordTrace_append hprefix tailTrace_928178
  have hstable : (prefixWord ++ tailWord_928178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928178).length < 2 ^ (prefixWord ++ tailWord_928178).sum := by decide
  have hdescent : baseEnd_928178 < baseStart_928178 := by decide
  rcases family_descends (prefixWord ++ tailWord_928178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928188 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_928188 : Nat := 118140960795 + 928188 * 2 ^ 59
def prefixEnd_928188 : Nat := 4983230072969 + 3 ^ 40 * 928188 * 2
def baseEnd_928188 : Nat := 476606581735519693881347

theorem tailTrace_928188 : CollatzResearch.WordTrace tailWord_928188 prefixEnd_928188 476606581735519693881347 := by
  unfold tailWord_928188
  simp only [CollatzResearch.WordTrace]
  refine ⟨16926898780670436367468609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22569198374227248489958145 16926898780670436367468609)
  ·
    refine ⟨12695174085502827275601457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16926898780670436367468609 12695174085502827275601457)
    ·
      refine ⟨9521380564127120456701093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12695174085502827275601457 9521380564127120456701093)
      ·
        refine ⟨1785258855773835085631455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9521380564127120456701093 1785258855773835085631455)
        ·
          refine ⟨2677888283660752628447183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785258855773835085631455 2677888283660752628447183)
          ·
            refine ⟨4016832425491128942670775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677888283660752628447183 4016832425491128942670775)
            ·
              refine ⟨6025248638236693414006163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4016832425491128942670775 6025248638236693414006163)
              ·
                refine ⟨9037872957355040121009245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6025248638236693414006163 9037872957355040121009245)
                ·
                  refine ⟨3389202359008140045378467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9037872957355040121009245 3389202359008140045378467)
                  ·
                    refine ⟨5083803538512210068067701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3389202359008140045378467 5083803538512210068067701)
                    ·
                      refine ⟨476606581735519693881347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5083803538512210068067701 476606581735519693881347)
                      ·
                        rfl

theorem cell23_928188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_928188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928188 prefixEnd_928188 := by exact prefixLift 928188
  have htrace : WordTrace (prefixWord ++ tailWord_928188) baseStart_928188 baseEnd_928188 := by
    simpa [prefixWord, tailWord_928188, baseEnd_928188] using wordTrace_append hprefix tailTrace_928188
  have hstable : (prefixWord ++ tailWord_928188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928188).length < 2 ^ (prefixWord ++ tailWord_928188).sum := by decide
  have hdescent : baseEnd_928188 < baseStart_928188 := by decide
  rcases family_descends (prefixWord ++ tailWord_928188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928218 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3]
def baseStart_928218 : Nat := 118140960795 + 928218 * 2 ^ 59
def prefixEnd_928218 : Nat := 4983230072969 + 3 ^ 40 * 928218 * 2
def baseEnd_928218 : Nat := 476621986155154576506209

theorem tailTrace_928218 : CollatzResearch.WordTrace tailWord_928218 prefixEnd_928218 476621986155154576506209 := by
  unfold tailWord_928218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8463722937808046964632327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22569927834154791905686205 8463722937808046964632327)
  ·
    refine ⟨12695584406712070446948491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8463722937808046964632327 12695584406712070446948491)
    ·
      refine ⟨19043376610068105670422737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12695584406712070446948491 19043376610068105670422737)
      ·
        refine ⟨14282532457551079252817053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19043376610068105670422737 14282532457551079252817053)
        ·
          refine ⟨5355949671581654719806395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14282532457551079252817053 5355949671581654719806395)
          ·
            refine ⟨8033924507372482079709593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5355949671581654719806395 8033924507372482079709593)
            ·
              refine ⟨6025443380529361559782195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8033924507372482079709593 6025443380529361559782195)
              ·
                refine ⟨9038165070794042339673293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6025443380529361559782195 9038165070794042339673293)
                ·
                  refine ⟨3389311901547765877377485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9038165070794042339673293 3389311901547765877377485)
                  ·
                    refine ⟨1270991963080412204016557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3389311901547765877377485 1270991963080412204016557)
                    ·
                      refine ⟨476621986155154576506209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1270991963080412204016557 476621986155154576506209)
                      ·
                        rfl

theorem cell23_928218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_928218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928218 prefixEnd_928218 := by exact prefixLift 928218
  have htrace : WordTrace (prefixWord ++ tailWord_928218) baseStart_928218 baseEnd_928218 := by
    simpa [prefixWord, tailWord_928218, baseEnd_928218] using wordTrace_append hprefix tailTrace_928218
  have hstable : (prefixWord ++ tailWord_928218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928218).length < 2 ^ (prefixWord ++ tailWord_928218).sum := by decide
  have hdescent : baseEnd_928218 < baseStart_928218 := by decide
  rcases family_descends (prefixWord ++ tailWord_928218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928235 : List Nat := [1, 1, 1, 1, 2, 3, 4, 4, 2, 1, 3]
def baseStart_928235 : Nat := 118140960795 + 928235 * 2 ^ 59
def prefixEnd_928235 : Nat := 4983230072969 + 3 ^ 40 * 928235 * 2
def baseEnd_928235 : Nat := 476630715326281009993631

theorem tailTrace_928235 : CollatzResearch.WordTrace tailWord_928235 prefixEnd_928235 476630715326281009993631 := by
  unfold tailWord_928235
  simp only [CollatzResearch.WordTrace]
  refine ⟨33855511792170599761898159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22570341194780399841265439 33855511792170599761898159)
  ·
    refine ⟨50783267688255899642847239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33855511792170599761898159 50783267688255899642847239)
    ·
      refine ⟨76174901532383849464270859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50783267688255899642847239 76174901532383849464270859)
      ·
        refine ⟨114262352298575774196406289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76174901532383849464270859 114262352298575774196406289)
        ·
          refine ⟨85696764223931830647304717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114262352298575774196406289 85696764223931830647304717)
          ·
            refine ⟨32136286583974436492739269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85696764223931830647304717 32136286583974436492739269)
            ·
              refine ⟨6025553734495206842388613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32136286583974436492739269 6025553734495206842388613)
              ·
                refine ⟨1129791325217851282947865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6025553734495206842388613 1129791325217851282947865)
                ·
                  refine ⟨847343493913388462210899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1129791325217851282947865 847343493913388462210899)
                  ·
                    refine ⟨1271015240870082693316349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 847343493913388462210899 1271015240870082693316349)
                    ·
                      refine ⟨476630715326281009993631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1271015240870082693316349 476630715326281009993631)
                      ·
                        rfl

theorem cell23_928235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 1, 3].length) (baseStart_928235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_928235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_928235 prefixEnd_928235 := by exact prefixLift 928235
  have htrace : WordTrace (prefixWord ++ tailWord_928235) baseStart_928235 baseEnd_928235 := by
    simpa [prefixWord, tailWord_928235, baseEnd_928235] using wordTrace_append hprefix tailTrace_928235
  have hstable : (prefixWord ++ tailWord_928235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928235).length < 2 ^ (prefixWord ++ tailWord_928235).sum := by decide
  have hdescent : baseEnd_928235 < baseStart_928235 := by decide
  rcases family_descends (prefixWord ++ tailWord_928235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
