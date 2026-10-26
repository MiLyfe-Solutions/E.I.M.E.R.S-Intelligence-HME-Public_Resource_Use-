import V185TrunkScan23Chunk1108

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6567667 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 5]
def baseStart_6567667 : Nat := 118140960795 + 6567667 * 2 ^ 59
def prefixEnd_6567667 : Nat := 4983230072969 + 3 ^ 40 * 6567667 * 2
def baseEnd_6567667 : Nat := 3372369949672460706358355

theorem tailTrace_6567667 : CollatzResearch.WordTrace tailWord_6567667 prefixEnd_6567667 3372369949672460706358355 := by
  unfold tailWord_6567667
  simp only [CollatzResearch.WordTrace]
  refine ⟨239542494697471602068141255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159694996464981068045427503 239542494697471602068141255)
  ·
    refine ⟨359313742046207403102211883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239542494697471602068141255 359313742046207403102211883)
    ·
      refine ⟨538970613069311104653317825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359313742046207403102211883 538970613069311104653317825)
      ·
        refine ⟨404227959801983328489988369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538970613069311104653317825 404227959801983328489988369)
        ·
          refine ⟨303170969851487496367491277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404227959801983328489988369 303170969851487496367491277)
          ·
            refine ⟨113689113694307811137809229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303170969851487496367491277 113689113694307811137809229)
            ·
              refine ⟨42633417635365429176678461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113689113694307811137809229 42633417635365429176678461)
              ·
                refine ⟨15987531613262035941254423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42633417635365429176678461 15987531613262035941254423)
                ·
                  refine ⟨23981297419893053911881635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15987531613262035941254423 23981297419893053911881635)
                  ·
                    refine ⟨35971946129839580867822453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23981297419893053911881635 35971946129839580867822453)
                    ·
                      refine ⟨3372369949672460706358355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35971946129839580867822453 3372369949672460706358355)
                      ·
                        rfl

theorem cell23_6567667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_6567667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567667 prefixEnd_6567667 := by exact prefixLift 6567667
  have htrace : WordTrace (prefixWord ++ tailWord_6567667) baseStart_6567667 baseEnd_6567667 := by
    simpa [prefixWord, tailWord_6567667, baseEnd_6567667] using wordTrace_append hprefix tailTrace_6567667
  have hstable : (prefixWord ++ tailWord_6567667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567667).length < 2 ^ (prefixWord ++ tailWord_6567667).sum := by decide
  have hdescent : baseEnd_6567667 < baseStart_6567667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567674 : List Nat := [3, 1, 1, 1, 1, 3, 1, 6, 2, 4]
def baseStart_6567674 : Nat := 118140960795 + 6567674 * 2 ^ 59
def prefixEnd_6567674 : Nat := 4983230072969 + 3 ^ 40 * 6567674 * 2
def baseEnd_6567674 : Nat := 1124124514679014059656941

theorem tailTrace_6567674 : CollatzResearch.WordTrace tailWord_6567674 prefixEnd_6567674 1124124514679014059656941 := by
  unfold tailWord_6567674
  simp only [CollatzResearch.WordTrace]
  refine ⟨59885687502111560565911519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159695166672297494842430717 59885687502111560565911519)
  ·
    refine ⟨89828531253167340848867279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59885687502111560565911519 89828531253167340848867279)
    ·
      refine ⟨134742796879751011273300919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89828531253167340848867279 134742796879751011273300919)
      ·
        refine ⟨202114195319626516909951379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134742796879751011273300919 202114195319626516909951379)
        ·
          refine ⟨303171292979439775364927069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202114195319626516909951379 303171292979439775364927069)
          ·
            refine ⟨113689234867289915761847651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303171292979439775364927069 113689234867289915761847651)
            ·
              refine ⟨170533852300934873642771477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113689234867289915761847651 170533852300934873642771477)
              ·
                refine ⟨7993774326606322202004913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170533852300934873642771477 7993774326606322202004913)
                ·
                  refine ⟨5995330744954741651503685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7993774326606322202004913 5995330744954741651503685)
                  ·
                    refine ⟨1124124514679014059656941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5995330744954741651503685 1124124514679014059656941)
                    ·
                      rfl

theorem cell23_6567674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_6567674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567674 prefixEnd_6567674 := by exact prefixLift 6567674
  have htrace : WordTrace (prefixWord ++ tailWord_6567674) baseStart_6567674 baseEnd_6567674 := by
    simpa [prefixWord, tailWord_6567674, baseEnd_6567674] using wordTrace_append hprefix tailTrace_6567674
  have hstable : (prefixWord ++ tailWord_6567674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567674).length < 2 ^ (prefixWord ++ tailWord_6567674).sum := by decide
  have hdescent : baseEnd_6567674 < baseStart_6567674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567677 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_6567677 : Nat := 118140960795 + 6567677 * 2 ^ 59
def prefixEnd_6567677 : Nat := 4983230072969 + 3 ^ 40 * 6567677 * 2
def baseEnd_6567677 : Nat := 3372375084479005667233309

theorem tailTrace_6567677 : CollatzResearch.WordTrace tailWord_6567677 prefixEnd_6567677 3372375084479005667233309 := by
  unfold tailWord_6567677
  simp only [CollatzResearch.WordTrace]
  refine ⟨239542859427435373776005285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159695239618290249184003523 239542859427435373776005285)
  ·
    refine ⟨44914286142644132583000991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239542859427435373776005285 44914286142644132583000991)
    ·
      refine ⟨67371429213966198874501487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44914286142644132583000991 67371429213966198874501487)
      ·
        refine ⟨101057143820949298311752231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67371429213966198874501487 101057143820949298311752231)
        ·
          refine ⟨151585715731423947467628347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101057143820949298311752231 151585715731423947467628347)
          ·
            refine ⟨227378573597135921201442521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151585715731423947467628347 227378573597135921201442521)
            ·
              refine ⟨170533930197851940901081891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227378573597135921201442521 170533930197851940901081891)
              ·
                refine ⟨255800895296777911351622837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170533930197851940901081891 255800895296777911351622837)
                ·
                  refine ⟨23981333934072929189214641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255800895296777911351622837 23981333934072929189214641)
                  ·
                    refine ⟨17986000450554696891910981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23981333934072929189214641 17986000450554696891910981)
                    ·
                      refine ⟨3372375084479005667233309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17986000450554696891910981 3372375084479005667233309)
                      ·
                        rfl

theorem cell23_6567677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_6567677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567677 prefixEnd_6567677 := by exact prefixLift 6567677
  have htrace : WordTrace (prefixWord ++ tailWord_6567677) baseStart_6567677 baseEnd_6567677 := by
    simpa [prefixWord, tailWord_6567677, baseEnd_6567677] using wordTrace_append hprefix tailTrace_6567677
  have hstable : (prefixWord ++ tailWord_6567677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567677).length < 2 ^ (prefixWord ++ tailWord_6567677).sum := by decide
  have hdescent : baseEnd_6567677 < baseStart_6567677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567684 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_6567684 : Nat := 118140960795 + 6567684 * 2 ^ 59
def prefixEnd_6567684 : Nat := 4983230072969 + 3 ^ 40 * 6567684 * 2
def baseEnd_6567684 : Nat := 3372378678843587139845777

theorem tailTrace_6567684 : CollatzResearch.WordTrace tailWord_6567684 prefixEnd_6567684 3372378678843587139845777 := by
  unfold tailWord_6567684
  simp only [CollatzResearch.WordTrace]
  refine ⟨119771557369205006985755053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159695409825606675981006737 119771557369205006985755053)
  ·
    refine ⟨44914334013451877619658145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119771557369205006985755053 44914334013451877619658145)
    ·
      refine ⟨33685750510088908214743609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44914334013451877619658145 33685750510088908214743609)
      ·
        refine ⟨25264312882566681161057707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33685750510088908214743609 25264312882566681161057707)
        ·
          refine ⟨37896469323850021741586561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25264312882566681161057707 37896469323850021741586561)
          ·
            refine ⟨28422351992887516306189921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37896469323850021741586561 28422351992887516306189921)
            ·
              refine ⟨21316763994665637229642441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28422351992887516306189921 21316763994665637229642441)
              ·
                refine ⟨15987572995999227922231831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21316763994665637229642441 15987572995999227922231831)
                ·
                  refine ⟨23981359493998841883347747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15987572995999227922231831 23981359493998841883347747)
                  ·
                    refine ⟨35972039240998262825021621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23981359493998841883347747 35972039240998262825021621)
                    ·
                      refine ⟨3372378678843587139845777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35972039240998262825021621 3372378678843587139845777)
                      ·
                        rfl

theorem cell23_6567684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_6567684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567684 prefixEnd_6567684 := by exact prefixLift 6567684
  have htrace : WordTrace (prefixWord ++ tailWord_6567684) baseStart_6567684 baseEnd_6567684 := by
    simpa [prefixWord, tailWord_6567684, baseEnd_6567684] using wordTrace_append hprefix tailTrace_6567684
  have hstable : (prefixWord ++ tailWord_6567684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567684).length < 2 ^ (prefixWord ++ tailWord_6567684).sum := by decide
  have hdescent : baseEnd_6567684 < baseStart_6567684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567691 : List Nat := [1, 1, 1, 1, 5, 1, 6, 1, 2, 4]
def baseStart_6567691 : Nat := 118140960795 + 6567691 * 2 ^ 59
def prefixEnd_6567691 : Nat := 4983230072969 + 3 ^ 40 * 6567691 * 2
def baseEnd_6567691 : Nat := 1124127424402722870819415

theorem tailTrace_6567691 : CollatzResearch.WordTrace tailWord_6567691 prefixEnd_6567691 1124127424402722870819415 := by
  unfold tailWord_6567691
  simp only [CollatzResearch.WordTrace]
  refine ⟨239543370049384654167014927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159695580032923102778009951 239543370049384654167014927)
  ·
    refine ⟨359315055074076981250522391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239543370049384654167014927 359315055074076981250522391)
    ·
      refine ⟨538972582611115471875783587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359315055074076981250522391 538972582611115471875783587)
      ·
        refine ⟨808458873916673207813675381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538972582611115471875783587 808458873916673207813675381)
        ·
          refine ⟨75793019429688113232532067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 808458873916673207813675381 75793019429688113232532067)
          ·
            refine ⟨113689529144532169848798101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75793019429688113232532067 113689529144532169848798101)
            ·
              refine ⟨5329196678649945461662411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113689529144532169848798101 5329196678649945461662411)
              ·
                refine ⟨7993795017974918192493617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5329196678649945461662411 7993795017974918192493617)
                ·
                  refine ⟨5995346263481188644370213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7993795017974918192493617 5995346263481188644370213)
                  ·
                    refine ⟨1124127424402722870819415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5995346263481188644370213 1124127424402722870819415)
                    ·
                      rfl

theorem cell23_6567691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 2, 4].length) (baseStart_6567691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567691 prefixEnd_6567691 := by exact prefixLift 6567691
  have htrace : WordTrace (prefixWord ++ tailWord_6567691) baseStart_6567691 baseEnd_6567691 := by
    simpa [prefixWord, tailWord_6567691, baseEnd_6567691] using wordTrace_append hprefix tailTrace_6567691
  have hstable : (prefixWord ++ tailWord_6567691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567691).length < 2 ^ (prefixWord ++ tailWord_6567691).sum := by decide
  have hdescent : baseEnd_6567691 < baseStart_6567691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567698 : List Nat := [3, 2, 4, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_6567698 : Nat := 118140960795 + 6567698 * 2 ^ 59
def prefixEnd_6567698 : Nat := 4983230072969 + 3 ^ 40 * 6567698 * 2
def baseEnd_6567698 : Nat := 3372385867572750085070713

theorem tailTrace_6567698 : CollatzResearch.WordTrace tailWord_6567698 prefixEnd_6567698 3372385867572750085070713 := by
  unfold tailWord_6567698
  simp only [CollatzResearch.WordTrace]
  refine ⟨59885906340089823590629937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159695750240239529575013165 59885906340089823590629937)
  ·
    refine ⟨44914429755067367692972453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59885906340089823590629937 44914429755067367692972453)
    ·
      refine ⟨8421455579075131442432335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44914429755067367692972453 8421455579075131442432335)
      ·
        refine ⟨12632183368612697163648503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8421455579075131442432335 12632183368612697163648503)
        ·
          refine ⟨18948275052919045745472755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12632183368612697163648503 18948275052919045745472755)
          ·
            refine ⟨28422412579378568618209133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18948275052919045745472755 28422412579378568618209133)
            ·
              refine ⟨10658404717266963231828425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28422412579378568618209133 10658404717266963231828425)
              ·
                refine ⟨7993803537950222423871319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10658404717266963231828425 7993803537950222423871319)
                ·
                  refine ⟨11990705306925333635806979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7993803537950222423871319 11990705306925333635806979)
                  ·
                    refine ⟨17986057960388000453710469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11990705306925333635806979 17986057960388000453710469)
                    ·
                      refine ⟨3372385867572750085070713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17986057960388000453710469 3372385867572750085070713)
                      ·
                        rfl

theorem cell23_6567698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_6567698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567698 prefixEnd_6567698 := by exact prefixLift 6567698
  have htrace : WordTrace (prefixWord ++ tailWord_6567698) baseStart_6567698 baseEnd_6567698 := by
    simpa [prefixWord, tailWord_6567698, baseEnd_6567698] using wordTrace_append hprefix tailTrace_6567698
  have hstable : (prefixWord ++ tailWord_6567698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567698).length < 2 ^ (prefixWord ++ tailWord_6567698).sum := by decide
  have hdescent : baseEnd_6567698 < baseStart_6567698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567701 : List Nat := [1, 3, 2, 1, 2, 3, 3, 2, 1, 2, 3]
def baseStart_6567701 : Nat := 118140960795 + 6567701 * 2 ^ 59
def prefixEnd_6567701 : Nat := 4983230072969 + 3 ^ 40 * 6567701 * 2
def baseEnd_6567701 : Nat := 3372387408014713573333199

theorem tailTrace_6567701 : CollatzResearch.WordTrace tailWord_6567701 prefixEnd_6567701 3372387408014713573333199 := by
  unfold tailWord_6567701
  simp only [CollatzResearch.WordTrace]
  refine ⟨239543734779348425874878957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159695823186232283916585971 239543734779348425874878957)
  ·
    refine ⟨89828900542255659703079609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239543734779348425874878957 89828900542255659703079609)
    ·
      refine ⟨67371675406691744777309707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89828900542255659703079609 67371675406691744777309707)
      ·
        refine ⟨101057513110037617165964561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67371675406691744777309707 101057513110037617165964561)
        ·
          refine ⟨75793134832528212874473421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101057513110037617165964561 75793134832528212874473421)
          ·
            refine ⟨28422425562198079827927533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75793134832528212874473421 28422425562198079827927533)
            ·
              refine ⟨10658409585824279935472825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28422425562198079827927533 10658409585824279935472825)
              ·
                refine ⟨7993807189368209951604619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10658409585824279935472825 7993807189368209951604619)
                ·
                  refine ⟨11990710784052314927406929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7993807189368209951604619 11990710784052314927406929)
                  ·
                    refine ⟨8993033088039236195555197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11990710784052314927406929 8993033088039236195555197)
                    ·
                      refine ⟨3372387408014713573333199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8993033088039236195555197 3372387408014713573333199)
                      ·
                        rfl

theorem cell23_6567701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_6567701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567701 prefixEnd_6567701 := by exact prefixLift 6567701
  have htrace : WordTrace (prefixWord ++ tailWord_6567701) baseStart_6567701 baseEnd_6567701 := by
    simpa [prefixWord, tailWord_6567701, baseEnd_6567701] using wordTrace_append hprefix tailTrace_6567701
  have hstable : (prefixWord ++ tailWord_6567701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567701).length < 2 ^ (prefixWord ++ tailWord_6567701).sum := by decide
  have hdescent : baseEnd_6567701 < baseStart_6567701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567732 : List Nat := [2, 5, 1, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_6567732 : Nat := 118140960795 + 6567732 * 2 ^ 59
def prefixEnd_6567732 : Nat := 4983230072969 + 3 ^ 40 * 6567732 * 2
def baseEnd_6567732 : Nat := 3372403325915002952045557

theorem tailTrace_6567732 : CollatzResearch.WordTrace tailWord_6567732 prefixEnd_6567732 3372403325915002952045557 := by
  unfold tailWord_6567732
  simp only [CollatzResearch.WordTrace]
  refine ⟨119772432721118059084628725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159696576961490745446171633 119772432721118059084628725)
  ·
    refine ⟨11228665567604818039183943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119772432721118059084628725 11228665567604818039183943)
    ·
      refine ⟨16842998351407227058775915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11228665567604818039183943 16842998351407227058775915)
      ·
        refine ⟨25264497527110840588163873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16842998351407227058775915 25264497527110840588163873)
        ·
          refine ⟨18948373145333130441122905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25264497527110840588163873 18948373145333130441122905)
          ·
            refine ⟨14211279858999847830842179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18948373145333130441122905 14211279858999847830842179)
            ·
              refine ⟨21316919788499771746263269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14211279858999847830842179 21316919788499771746263269)
              ·
                refine ⟨3996922460343707202424363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21316919788499771746263269 3996922460343707202424363)
                ·
                  refine ⟨5995383690515560803636545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996922460343707202424363 5995383690515560803636545)
                  ·
                    refine ⟨4496537767886670602727409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5995383690515560803636545 4496537767886670602727409)
                    ·
                      refine ⟨3372403325915002952045557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496537767886670602727409 3372403325915002952045557)
                      ·
                        rfl

theorem cell23_6567732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_6567732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567732 prefixEnd_6567732 := by exact prefixLift 6567732
  have htrace : WordTrace (prefixWord ++ tailWord_6567732) baseStart_6567732 baseEnd_6567732 := by
    simpa [prefixWord, tailWord_6567732, baseEnd_6567732] using wordTrace_append hprefix tailTrace_6567732
  have hstable : (prefixWord ++ tailWord_6567732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567732).length < 2 ^ (prefixWord ++ tailWord_6567732).sum := by decide
  have hdescent : baseEnd_6567732 < baseStart_6567732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567747 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 1, 8]
def baseStart_6567747 : Nat := 118140960795 + 6567747 * 2 ^ 59
def prefixEnd_6567747 : Nat := 4983230072969 + 3 ^ 40 * 6567747 * 2
def baseEnd_6567747 : Nat := 1124137009374940131119329

theorem tailTrace_6567747 : CollatzResearch.WordTrace tailWord_6567747 prefixEnd_6567747 1124137009374940131119329 := by
  unfold tailWord_6567747
  simp only [CollatzResearch.WordTrace]
  refine ⟨239545412537181775731053495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159696941691454517154035663 239545412537181775731053495)
  ·
    refine ⟨359318118805772663596580243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239545412537181775731053495 359318118805772663596580243)
    ·
      refine ⟨538977178208658995394870365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359318118805772663596580243 538977178208658995394870365)
      ·
        refine ⟨202116441828247123273076387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 538977178208658995394870365 202116441828247123273076387)
        ·
          refine ⟨303174662742370684909614581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202116441828247123273076387 303174662742370684909614581)
          ·
            refine ⟨28422624632097251710276367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 303174662742370684909614581 28422624632097251710276367)
            ·
              refine ⟨42633936948145877565414551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28422624632097251710276367 42633936948145877565414551)
              ·
                refine ⟨63950905422218816348121827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42633936948145877565414551 63950905422218816348121827)
                ·
                  refine ⟨95926358133328224522182741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63950905422218816348121827 95926358133328224522182741)
                  ·
                    refine ⟨1124137009374940131119329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95926358133328224522182741 1124137009374940131119329)
                    ·
                      rfl

theorem cell23_6567747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 8].length) (baseStart_6567747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567747 prefixEnd_6567747 := by exact prefixLift 6567747
  have htrace : WordTrace (prefixWord ++ tailWord_6567747) baseStart_6567747 baseEnd_6567747 := by
    simpa [prefixWord, tailWord_6567747, baseEnd_6567747] using wordTrace_append hprefix tailTrace_6567747
  have hstable : (prefixWord ++ tailWord_6567747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567747).length < 2 ^ (prefixWord ++ tailWord_6567747).sum := by decide
  have hdescent : baseEnd_6567747 < baseStart_6567747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567775 : List Nat := [1, 1, 2, 3, 1, 6, 2, 1, 1, 3, 2]
def baseStart_6567775 : Nat := 118140960795 + 6567775 * 2 ^ 59
def prefixEnd_6567775 : Nat := 4983230072969 + 3 ^ 40 * 6567775 * 2
def baseEnd_6567775 : Nat := 3372425405583146283807859

theorem tailTrace_6567775 : CollatzResearch.WordTrace tailWord_6567775 prefixEnd_6567775 3372425405583146283807859 := by
  unfold tailWord_6567775
  simp only [CollatzResearch.WordTrace]
  refine ⟨239546433781080336513072779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159697622520720224342048519 239546433781080336513072779)
  ·
    refine ⟨359319650671620504769609169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239546433781080336513072779 359319650671620504769609169)
    ·
      refine ⟨269489738003715378577206877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359319650671620504769609169 269489738003715378577206877)
      ·
        refine ⟨101058651751393266966452579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269489738003715378577206877 101058651751393266966452579)
        ·
          refine ⟨151587977627089900449678869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101058651751393266966452579 151587977627089900449678869)
          ·
            refine ⟨7105686451269839083578697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 151587977627089900449678869 7105686451269839083578697)
            ·
              refine ⟨5329264838452379312684023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7105686451269839083578697 5329264838452379312684023)
              ·
                refine ⟨7993897257678568969026035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5329264838452379312684023 7993897257678568969026035)
                ·
                  refine ⟨11990845886517853453539053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7993897257678568969026035 11990845886517853453539053)
                  ·
                    refine ⟨4496567207444195045077145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11990845886517853453539053 4496567207444195045077145)
                    ·
                      refine ⟨3372425405583146283807859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496567207444195045077145 3372425405583146283807859)
                      ·
                        rfl

theorem cell23_6567775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_6567775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567775 prefixEnd_6567775 := by exact prefixLift 6567775
  have htrace : WordTrace (prefixWord ++ tailWord_6567775) baseStart_6567775 baseEnd_6567775 := by
    simpa [prefixWord, tailWord_6567775, baseEnd_6567775] using wordTrace_append hprefix tailTrace_6567775
  have hstable : (prefixWord ++ tailWord_6567775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567775).length < 2 ^ (prefixWord ++ tailWord_6567775).sum := by decide
  have hdescent : baseEnd_6567775 < baseStart_6567775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567777 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 9]
def baseStart_6567777 : Nat := 118140960795 + 6567777 * 2 ^ 59
def prefixEnd_6567777 : Nat := 4983230072969 + 3 ^ 40 * 6567777 * 2
def baseEnd_6567777 : Nat := 374714048060495030664761

theorem tailTrace_6567777 : CollatzResearch.WordTrace tailWord_6567777 prefixEnd_6567777 374714048060495030664761 := by
  unfold tailWord_6567777
  simp only [CollatzResearch.WordTrace]
  refine ⟨239546506727073090854645585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159697671151382060569763723 239546506727073090854645585)
  ·
    refine ⟨179659880045304818140984189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239546506727073090854645585 179659880045304818140984189)
    ·
      refine ⟨67372455016989306802869071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179659880045304818140984189 67372455016989306802869071)
      ·
        refine ⟨101058682525483960204303607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67372455016989306802869071 101058682525483960204303607)
        ·
          refine ⟨151588023788225940306455411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101058682525483960204303607 151588023788225940306455411)
          ·
            refine ⟨227382035682338910459683117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151588023788225940306455411 227382035682338910459683117)
            ·
              refine ⟨85268263380877091422381169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227382035682338910459683117 85268263380877091422381169)
              ·
                refine ⟨63951197535657818566785877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85268263380877091422381169 63951197535657818566785877)
                ·
                  refine ⟨374714048060495030664761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63951197535657818566785877 374714048060495030664761)
                  ·
                    rfl

theorem cell23_6567777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 9].length) (baseStart_6567777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567777 prefixEnd_6567777 := by exact prefixLift 6567777
  have htrace : WordTrace (prefixWord ++ tailWord_6567777) baseStart_6567777 baseEnd_6567777 := by
    simpa [prefixWord, tailWord_6567777, baseEnd_6567777] using wordTrace_append hprefix tailTrace_6567777
  have hstable : (prefixWord ++ tailWord_6567777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567777).length < 2 ^ (prefixWord ++ tailWord_6567777).sum := by decide
  have hdescent : baseEnd_6567777 < baseStart_6567777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567784 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_6567784 : Nat := 118140960795 + 6567784 * 2 ^ 59
def prefixEnd_6567784 : Nat := 4983230072969 + 3 ^ 40 * 6567784 * 2
def baseEnd_6567784 : Nat := 3372430026909036748595317

theorem tailTrace_6567784 : CollatzResearch.WordTrace tailWord_6567784 prefixEnd_6567784 3372430026909036748595317 := by
  unfold tailWord_6567784
  simp only [CollatzResearch.WordTrace]
  refine ⟨119773381019023865525075203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159697841358698487366766937 119773381019023865525075203)
  ·
    refine ⟨179660071528535798287612805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119773381019023865525075203 179660071528535798287612805)
    ·
      refine ⟨33686263411600462178927401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179660071528535798287612805 33686263411600462178927401)
      ·
        refine ⟨25264697558700346634195551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33686263411600462178927401 25264697558700346634195551)
        ·
          refine ⟨37897046338050519951293327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25264697558700346634195551 37897046338050519951293327)
          ·
            refine ⟨56845569507075779926939991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37897046338050519951293327 56845569507075779926939991)
            ·
              refine ⟨85268354260613669890409987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56845569507075779926939991 85268354260613669890409987)
              ·
                refine ⟨127902531390920504835614981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85268354260613669890409987 127902531390920504835614981)
                ·
                  refine ⟨23981724635797594656677809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127902531390920504835614981 23981724635797594656677809)
                  ·
                    refine ⟨17986293476848195992508357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23981724635797594656677809 17986293476848195992508357)
                    ·
                      refine ⟨3372430026909036748595317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17986293476848195992508357 3372430026909036748595317)
                      ·
                        rfl

theorem cell23_6567784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_6567784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567784 prefixEnd_6567784 := by exact prefixLift 6567784
  have htrace : WordTrace (prefixWord ++ tailWord_6567784) baseStart_6567784 baseEnd_6567784 := by
    simpa [prefixWord, tailWord_6567784, baseEnd_6567784] using wordTrace_append hprefix tailTrace_6567784
  have hstable : (prefixWord ++ tailWord_6567784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567784).length < 2 ^ (prefixWord ++ tailWord_6567784).sum := by decide
  have hdescent : baseEnd_6567784 < baseStart_6567784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567788 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 4, 2, 2]
def baseStart_6567788 : Nat := 118140960795 + 6567788 * 2 ^ 59
def prefixEnd_6567788 : Nat := 4983230072969 + 3 ^ 40 * 6567788 * 2
def baseEnd_6567788 : Nat := 3372432080831654732945299

theorem tailTrace_6567788 : CollatzResearch.WordTrace tailWord_6567788 prefixEnd_6567788 3372432080831654732945299 := by
  unfold tailWord_6567788
  simp only [CollatzResearch.WordTrace]
  refine ⟨119773453965016619866648009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159697938620022159822197345 119773453965016619866648009)
  ·
    refine ⟨89830090473762464899986007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119773453965016619866648009 89830090473762464899986007)
    ·
      refine ⟨134745135710643697349979011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89830090473762464899986007 134745135710643697349979011)
      ·
        refine ⟨202117703565965546024968517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134745135710643697349979011 202117703565965546024968517)
        ·
          refine ⟨37897069418618539879681597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202117703565965546024968517 37897069418618539879681597)
          ·
            refine ⟨14211401031981952454880599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37897069418618539879681597 14211401031981952454880599)
            ·
              refine ⟨21317101547972928682320899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14211401031981952454880599 21317101547972928682320899)
              ·
                refine ⟨31975652321959393023481349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21317101547972928682320899 31975652321959393023481349)
                ·
                  refine ⟨5995434810367386191902753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31975652321959393023481349 5995434810367386191902753)
                  ·
                    refine ⟨4496576107775539643927065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5995434810367386191902753 4496576107775539643927065)
                    ·
                      refine ⟨3372432080831654732945299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496576107775539643927065 3372432080831654732945299)
                      ·
                        rfl

theorem cell23_6567788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 2, 2].length) (baseStart_6567788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567788 prefixEnd_6567788 := by exact prefixLift 6567788
  have htrace : WordTrace (prefixWord ++ tailWord_6567788) baseStart_6567788 baseEnd_6567788 := by
    simpa [prefixWord, tailWord_6567788, baseEnd_6567788] using wordTrace_append hprefix tailTrace_6567788
  have hstable : (prefixWord ++ tailWord_6567788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567788).length < 2 ^ (prefixWord ++ tailWord_6567788).sum := by decide
  have hdescent : baseEnd_6567788 < baseStart_6567788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567827 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 8]
def baseStart_6567827 : Nat := 118140960795 + 6567827 * 2 ^ 59
def prefixEnd_6567827 : Nat := 4983230072969 + 3 ^ 40 * 6567827 * 2
def baseEnd_6567827 : Nat := 3372452106577180080357619

theorem tailTrace_6567827 : CollatzResearch.WordTrace tailWord_6567827 prefixEnd_6567827 3372452106577180080357619 := by
  unfold tailWord_6567827
  simp only [CollatzResearch.WordTrace]
  refine ⟨239548330376891949393965735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159698886917927966262643823 239548330376891949393965735)
  ·
    refine ⟨359322495565337924090948603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239548330376891949393965735 359322495565337924090948603)
    ·
      refine ⟨538983743348006886136422905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359322495565337924090948603 538983743348006886136422905)
      ·
        refine ⟨404237807511005164602317179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538983743348006886136422905 404237807511005164602317179)
        ·
          refine ⟨606356711266507746903475769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404237807511005164602317179 606356711266507746903475769)
          ·
            refine ⟨454767533449880810177606827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 606356711266507746903475769 454767533449880810177606827)
            ·
              refine ⟨682151300174821215266410241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454767533449880810177606827 682151300174821215266410241)
              ·
                refine ⟨511613475131115911449807681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682151300174821215266410241 511613475131115911449807681)
                ·
                  refine ⟨383710106348336933587355761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511613475131115911449807681 383710106348336933587355761)
                  ·
                    refine ⟨287782579761252700190516821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 383710106348336933587355761 287782579761252700190516821)
                    ·
                      refine ⟨3372452106577180080357619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 287782579761252700190516821 3372452106577180080357619)
                      ·
                        rfl

theorem cell23_6567827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_6567827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567827 prefixEnd_6567827 := by exact prefixLift 6567827
  have htrace : WordTrace (prefixWord ++ tailWord_6567827) baseStart_6567827 baseEnd_6567827 := by
    simpa [prefixWord, tailWord_6567827, baseEnd_6567827] using wordTrace_append hprefix tailTrace_6567827
  have hstable : (prefixWord ++ tailWord_6567827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567827).length < 2 ^ (prefixWord ++ tailWord_6567827).sum := by decide
  have hdescent : baseEnd_6567827 < baseStart_6567827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567828 : List Nat := [2, 4, 2, 1, 1, 2, 3, 3, 5]
def baseStart_6567828 : Nat := 118140960795 + 6567828 * 2 ^ 59
def prefixEnd_6567828 : Nat := 4983230072969 + 3 ^ 40 * 6567828 * 2
def baseEnd_6567828 : Nat := 374716957784203841827235

theorem tailTrace_6567828 : CollatzResearch.WordTrace tailWord_6567828 prefixEnd_6567828 374716957784203841827235 := by
  unfold tailWord_6567828
  simp only [CollatzResearch.WordTrace]
  refine ⟨119774183424944163282376069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159698911233258884376501425 119774183424944163282376069)
  ·
    refine ⟨22457659392177030615445513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119774183424944163282376069 22457659392177030615445513)
    ·
      refine ⟨16843244544132772961584135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22457659392177030615445513 16843244544132772961584135)
      ·
        refine ⟨25264866816199159442376203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16843244544132772961584135 25264866816199159442376203)
        ·
          refine ⟨37897300224298739163564305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25264866816199159442376203 37897300224298739163564305)
          ·
            refine ⟨28422975168224054372673229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37897300224298739163564305 28422975168224054372673229)
            ·
              refine ⟨10658615688084020389752461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28422975168224054372673229 10658615688084020389752461)
              ·
                refine ⟨3996980883031507646157173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10658615688084020389752461 3996980883031507646157173)
                ·
                  refine ⟨374716957784203841827235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3996980883031507646157173 374716957784203841827235)
                  ·
                    rfl

theorem cell23_6567828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_6567828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567828 prefixEnd_6567828 := by exact prefixLift 6567828
  have htrace : WordTrace (prefixWord ++ tailWord_6567828) baseStart_6567828 baseEnd_6567828 := by
    simpa [prefixWord, tailWord_6567828, baseEnd_6567828] using wordTrace_append hprefix tailTrace_6567828
  have hstable : (prefixWord ++ tailWord_6567828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567828).length < 2 ^ (prefixWord ++ tailWord_6567828).sum := by decide
  have hdescent : baseEnd_6567828 < baseStart_6567828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567905 : List Nat := [1, 2, 3, 1, 2, 1, 6, 2, 1, 4]
def baseStart_6567905 : Nat := 118140960795 + 6567905 * 2 ^ 59
def prefixEnd_6567905 : Nat := 4983230072969 + 3 ^ 40 * 6567905 * 2
def baseEnd_6567905 : Nat := 1124164052689410258394087

theorem tailTrace_6567905 : CollatzResearch.WordTrace tailWord_6567905 prefixEnd_6567905 1124164052689410258394087 := by
  unfold tailWord_6567905
  simp only [CollatzResearch.WordTrace]
  refine ⟨239551175270609368715305169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159700783513739579143536779 239551175270609368715305169)
  ·
    refine ⟨179663381452957026536478877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239551175270609368715305169 179663381452957026536478877)
    ·
      refine ⟨67373768044858884951179579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179663381452957026536478877 67373768044858884951179579)
      ·
        refine ⟨101060652067288327426769369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67373768044858884951179579 101060652067288327426769369)
        ·
          refine ⟨75795489050466245570077027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101060652067288327426769369 75795489050466245570077027)
          ·
            refine ⟨113693233575699368355115541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75795489050466245570077027 113693233575699368355115541)
            ·
              refine ⟨5329370323860907891646041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113693233575699368355115541 5329370323860907891646041)
              ·
                refine ⟨3997027742895680918734531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5329370323860907891646041 3997027742895680918734531)
                ·
                  refine ⟨5995541614343521378101797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3997027742895680918734531 5995541614343521378101797)
                  ·
                    refine ⟨1124164052689410258394087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5995541614343521378101797 1124164052689410258394087)
                    ·
                      rfl

theorem cell23_6567905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_6567905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567905 prefixEnd_6567905 := by exact prefixLift 6567905
  have htrace : WordTrace (prefixWord ++ tailWord_6567905) baseStart_6567905 baseEnd_6567905 := by
    simpa [prefixWord, tailWord_6567905, baseEnd_6567905] using wordTrace_append hprefix tailTrace_6567905
  have hstable : (prefixWord ++ tailWord_6567905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567905).length < 2 ^ (prefixWord ++ tailWord_6567905).sum := by decide
  have hdescent : baseEnd_6567905 < baseStart_6567905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567971 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 5]
def baseStart_6567971 : Nat := 118140960795 + 6567971 * 2 ^ 59
def prefixEnd_6567971 : Nat := 4983230072969 + 3 ^ 40 * 6567971 * 2
def baseEnd_6567971 : Nat := 3372526047791427516956957

theorem tailTrace_6567971 : CollatzResearch.WordTrace tailWord_6567971 prefixEnd_6567971 3372526047791427516956957 := by
  unfold tailWord_6567971
  simp only [CollatzResearch.WordTrace]
  refine ⟨239553582488370261987207767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159702388325580174658138511 239553582488370261987207767)
  ·
    refine ⟨359330373732555392980811651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239553582488370261987207767 359330373732555392980811651)
    ·
      refine ⟨538995560598833089471217477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359330373732555392980811651 538995560598833089471217477)
      ·
        refine ⟨101061667612281204275853277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 538995560598833089471217477 101061667612281204275853277)
        ·
          refine ⟨37898125354605451603444979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101061667612281204275853277 37898125354605451603444979)
          ·
            refine ⟨56847188031908177405167469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37898125354605451603444979 56847188031908177405167469)
            ·
              refine ⟨21317695511965566526937801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56847188031908177405167469 21317695511965566526937801)
              ·
                refine ⟨15988271633974174895203351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21317695511965566526937801 15988271633974174895203351)
                ·
                  refine ⟨23982407450961262342805027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15988271633974174895203351 23982407450961262342805027)
                  ·
                    refine ⟨35973611176441893514207541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23982407450961262342805027 35973611176441893514207541)
                    ·
                      refine ⟨3372526047791427516956957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35973611176441893514207541 3372526047791427516956957)
                      ·
                        rfl

theorem cell23_6567971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_6567971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567971 prefixEnd_6567971 := by exact prefixLift 6567971
  have htrace : WordTrace (prefixWord ++ tailWord_6567971) baseStart_6567971 baseEnd_6567971 := by
    simpa [prefixWord, tailWord_6567971, baseEnd_6567971] using wordTrace_append hprefix tailTrace_6567971
  have hstable : (prefixWord ++ tailWord_6567971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567971).length < 2 ^ (prefixWord ++ tailWord_6567971).sum := by decide
  have hdescent : baseEnd_6567971 < baseStart_6567971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567978 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 1, 6]
def baseStart_6567978 : Nat := 118140960795 + 6567978 * 2 ^ 59
def prefixEnd_6567978 : Nat := 4983230072969 + 3 ^ 40 * 6567978 * 2
def baseEnd_6567978 : Nat := 1124176547385336329856475

theorem tailTrace_6567978 : CollatzResearch.WordTrace tailWord_6567978 prefixEnd_6567978 1124176547385336329856475 := by
  unfold tailWord_6567978
  simp only [CollatzResearch.WordTrace]
  refine ⟨59888459449836225545678147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159702558532896601455141725 59888459449836225545678147)
  ·
    refine ⟨89832689174754338318517221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59888459449836225545678147 89832689174754338318517221)
    ·
      refine ⟨16843629220266438434721979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89832689174754338318517221 16843629220266438434721979)
      ·
        refine ⟨25265443830399657652082969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16843629220266438434721979 25265443830399657652082969)
        ·
          refine ⟨18949082872799743239062227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25265443830399657652082969 18949082872799743239062227)
          ·
            refine ⟨28423624309199614858593341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18949082872799743239062227 28423624309199614858593341)
            ·
              refine ⟨10658859115949855571972503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28423624309199614858593341 10658859115949855571972503)
              ·
                refine ⟨15988288673924783357958755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10658859115949855571972503 15988288673924783357958755)
                ·
                  refine ⟨23982433010887175036938133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15988288673924783357958755 23982433010887175036938133)
                  ·
                    refine ⟨1124176547385336329856475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23982433010887175036938133 1124176547385336329856475)
                    ·
                      rfl

theorem cell23_6567978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_6567978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567978 prefixEnd_6567978 := by exact prefixLift 6567978
  have htrace : WordTrace (prefixWord ++ tailWord_6567978) baseStart_6567978 baseEnd_6567978 := by
    simpa [prefixWord, tailWord_6567978, baseEnd_6567978] using wordTrace_append hprefix tailTrace_6567978
  have hstable : (prefixWord ++ tailWord_6567978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567978).length < 2 ^ (prefixWord ++ tailWord_6567978).sum := by decide
  have hdescent : baseEnd_6567978 < baseStart_6567978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567985 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 3, 2, 2]
def baseStart_6567985 : Nat := 118140960795 + 6567985 * 2 ^ 59
def prefixEnd_6567985 : Nat := 4983230072969 + 3 ^ 40 * 6567985 * 2
def baseEnd_6567985 : Nat := 3372533236520590462181893

theorem tailTrace_6567985 : CollatzResearch.WordTrace tailWord_6567985 prefixEnd_6567985 3372533236520590462181893 := by
  unfold tailWord_6567985
  simp only [CollatzResearch.WordTrace]
  refine ⟨239554093110319542378217409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159702728740213028252144939 239554093110319542378217409)
  ·
    refine ⟨179665569832739656783663057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239554093110319542378217409 179665569832739656783663057)
    ·
      refine ⟨134749177374554742587747293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179665569832739656783663057 134749177374554742587747293)
      ·
        refine ⟨50530941515458028470405235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134749177374554742587747293 50530941515458028470405235)
        ·
          refine ⟨75796412273187042705607853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50530941515458028470405235 75796412273187042705607853)
          ·
            refine ⟨28423654602445141014602945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75796412273187042705607853 28423654602445141014602945)
            ·
              refine ⟨21317740951833855760952209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28423654602445141014602945 21317740951833855760952209)
              ·
                refine ⟨15988305713875391820714157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21317740951833855760952209 15988305713875391820714157)
                ·
                  refine ⟨5995614642703271932767809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15988305713875391820714157 5995614642703271932767809)
                  ·
                    refine ⟨4496710982027453949575857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5995614642703271932767809 4496710982027453949575857)
                    ·
                      refine ⟨3372533236520590462181893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496710982027453949575857 3372533236520590462181893)
                      ·
                        rfl

theorem cell23_6567985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_6567985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567985 prefixEnd_6567985 := by exact prefixLift 6567985
  have htrace : WordTrace (prefixWord ++ tailWord_6567985) baseStart_6567985 baseEnd_6567985 := by
    simpa [prefixWord, tailWord_6567985, baseEnd_6567985] using wordTrace_append hprefix tailTrace_6567985
  have hstable : (prefixWord ++ tailWord_6567985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567985).length < 2 ^ (prefixWord ++ tailWord_6567985).sum := by decide
  have hdescent : baseEnd_6567985 < baseStart_6567985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567991 : List Nat := [1, 1, 3, 1, 2, 2, 6, 7]
def baseStart_6567991 : Nat := 118140960795 + 6567991 * 2 ^ 59
def prefixEnd_6567991 : Nat := 4983230072969 + 3 ^ 40 * 6567991 * 2
def baseEnd_6567991 : Nat := 124908752496463608840995

theorem tailTrace_6567991 : CollatzResearch.WordTrace tailWord_6567991 prefixEnd_6567991 124908752496463608840995 := by
  unfold tailWord_6567991
  simp only [CollatzResearch.WordTrace]
  refine ⟨239554311948297805402935827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159702874632198536935290551 239554311948297805402935827)
  ·
    refine ⟨359331467922446708104403741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239554311948297805402935827 359331467922446708104403741)
    ·
      refine ⟨134749300470917515539151403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359331467922446708104403741 134749300470917515539151403)
      ·
        refine ⟨202123950706376273308727105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134749300470917515539151403 202123950706376273308727105)
        ·
          refine ⟨151592963029782204981545329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202123950706376273308727105 151592963029782204981545329)
          ·
            refine ⟨113694722272336653736158997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151592963029782204981545329 113694722272336653736158997)
            ·
              refine ⟨5329440106515780643882453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113694722272336653736158997 5329440106515780643882453)
              ·
                refine ⟨124908752496463608840995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5329440106515780643882453 124908752496463608840995)
                ·
                  rfl

theorem cell23_6567991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 7].length) (baseStart_6567991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567991 prefixEnd_6567991 := by exact prefixLift 6567991
  have htrace : WordTrace (prefixWord ++ tailWord_6567991) baseStart_6567991 baseEnd_6567991 := by
    simpa [prefixWord, tailWord_6567991, baseEnd_6567991] using wordTrace_append hprefix tailTrace_6567991
  have hstable : (prefixWord ++ tailWord_6567991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567991).length < 2 ^ (prefixWord ++ tailWord_6567991).sum := by decide
  have hdescent : baseEnd_6567991 < baseStart_6567991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568029 : List Nat := [1, 4, 4, 1, 1, 3, 2, 1, 2, 4]
def baseStart_6568029 : Nat := 118140960795 + 6568029 * 2 ^ 59
def prefixEnd_6568029 : Nat := 4983230072969 + 3 ^ 40 * 6568029 * 2
def baseEnd_6568029 : Nat := 1124185276556462763343897

theorem tailTrace_6568029 : CollatzResearch.WordTrace tailWord_6568029 prefixEnd_6568029 1124185276556462763343897 := by
  unfold tailWord_6568029
  simp only [CollatzResearch.WordTrace]
  refine ⟨239555697922160137892819141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159703798614773425261879427 239555697922160137892819141)
  ·
    refine ⟨44916693360405025854903589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239555697922160137892819141 44916693360405025854903589)
    ·
      refine ⟨8421880005075942347794423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44916693360405025854903589 8421880005075942347794423)
      ·
        refine ⟨12632820007613913521691635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8421880005075942347794423 12632820007613913521691635)
        ·
          refine ⟨18949230011420870282537453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12632820007613913521691635 18949230011420870282537453)
          ·
            refine ⟨7105961254282826355951545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18949230011420870282537453 7105961254282826355951545)
            ·
              refine ⟨5329470940712119766963659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7105961254282826355951545 5329470940712119766963659)
              ·
                refine ⟨7994206411068179650445489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5329470940712119766963659 7994206411068179650445489)
                ·
                  refine ⟨5995654808301134737834117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7994206411068179650445489 5995654808301134737834117)
                  ·
                    refine ⟨1124185276556462763343897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5995654808301134737834117 1124185276556462763343897)
                    ·
                      rfl

theorem cell23_6568029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_6568029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568029 prefixEnd_6568029 := by exact prefixLift 6568029
  have htrace : WordTrace (prefixWord ++ tailWord_6568029) baseStart_6568029 baseEnd_6568029 := by
    simpa [prefixWord, tailWord_6568029, baseEnd_6568029] using wordTrace_append hprefix tailTrace_6568029
  have hstable : (prefixWord ++ tailWord_6568029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568029).length < 2 ^ (prefixWord ++ tailWord_6568029).sum := by decide
  have hdescent : baseEnd_6568029 < baseStart_6568029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568045 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_6568045 : Nat := 118140960795 + 6568045 * 2 ^ 59
def prefixEnd_6568045 : Nat := 4983230072969 + 3 ^ 40 * 6568045 * 2
def baseEnd_6568045 : Nat := 3372564045359860227431617

theorem tailTrace_6568045 : CollatzResearch.WordTrace tailWord_6568045 prefixEnd_6568045 3372564045359860227431617 := by
  unfold tailWord_6568045
  simp only [CollatzResearch.WordTrace]
  refine ⟨239556281490102172625401589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159704187660068115083601059 239556281490102172625401589)
  ·
    refine ⟨22458401389697078683631399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239556281490102172625401589 22458401389697078683631399)
    ·
      refine ⟨33687602084545618025447099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22458401389697078683631399 33687602084545618025447099)
      ·
        refine ⟨50531403126818427038170649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33687602084545618025447099 50531403126818427038170649)
        ·
          refine ⟨37898552345113820278627987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50531403126818427038170649 37898552345113820278627987)
          ·
            refine ⟨56847828517670730417941981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37898552345113820278627987 56847828517670730417941981)
            ·
              refine ⟨21317935694126523906728243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56847828517670730417941981 21317935694126523906728243)
              ·
                refine ⟨31976903541189785860092365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21317935694126523906728243 31976903541189785860092365)
                ·
                  refine ⟨11991338827946169697534637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31976903541189785860092365 11991338827946169697534637)
                  ·
                    refine ⟨4496752060479813636575489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11991338827946169697534637 4496752060479813636575489)
                    ·
                      refine ⟨3372564045359860227431617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496752060479813636575489 3372564045359860227431617)
                      ·
                        rfl

theorem cell23_6568045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_6568045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568045 prefixEnd_6568045 := by exact prefixLift 6568045
  have htrace : WordTrace (prefixWord ++ tailWord_6568045) baseStart_6568045 baseEnd_6568045 := by
    simpa [prefixWord, tailWord_6568045, baseEnd_6568045] using wordTrace_append hprefix tailTrace_6568045
  have hstable : (prefixWord ++ tailWord_6568045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568045).length < 2 ^ (prefixWord ++ tailWord_6568045).sum := by decide
  have hdescent : baseEnd_6568045 < baseStart_6568045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568092 : List Nat := [2, 2, 3, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_6568092 : Nat := 118140960795 + 6568092 * 2 ^ 59
def prefixEnd_6568092 : Nat := 4983230072969 + 3 ^ 40 * 6568092 * 2
def baseEnd_6568092 : Nat := 3372588178950621543543901

theorem tailTrace_6568092 : CollatzResearch.WordTrace tailWord_6568092 prefixEnd_6568092 3372588178950621543543901 := by
  unfold tailWord_6568092
  simp only [CollatzResearch.WordTrace]
  refine ⟨119778997860465949826181265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159705330480621266434908353 119778997860465949826181265)
  ·
    refine ⟨89834248395349462369635949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119778997860465949826181265 89834248395349462369635949)
    ·
      refine ⟨33687843148256048388613481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89834248395349462369635949 33687843148256048388613481)
      ·
        refine ⟨25265882361192036291460111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33687843148256048388613481 25265882361192036291460111)
        ·
          refine ⟨37898823541788054437190167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25265882361192036291460111 37898823541788054437190167)
          ·
            refine ⟨56848235312682081655785251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37898823541788054437190167 56848235312682081655785251)
            ·
              refine ⟨85272352969023122483677877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56848235312682081655785251 85272352969023122483677877)
              ·
                refine ⟨7994283090845917732844801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85272352969023122483677877 7994283090845917732844801)
                ·
                  refine ⟨5995712318134438299633601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7994283090845917732844801 5995712318134438299633601)
                  ·
                    refine ⟨4496784238600828724725201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5995712318134438299633601 4496784238600828724725201)
                    ·
                      refine ⟨3372588178950621543543901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496784238600828724725201 3372588178950621543543901)
                      ·
                        rfl

theorem cell23_6568092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_6568092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568092 prefixEnd_6568092 := by exact prefixLift 6568092
  have htrace : WordTrace (prefixWord ++ tailWord_6568092) baseStart_6568092 baseEnd_6568092 := by
    simpa [prefixWord, tailWord_6568092, baseEnd_6568092] using wordTrace_append hprefix tailTrace_6568092
  have hstable : (prefixWord ++ tailWord_6568092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568092).length < 2 ^ (prefixWord ++ tailWord_6568092).sum := by decide
  have hdescent : baseEnd_6568092 < baseStart_6568092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568098 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 9]
def baseStart_6568098 : Nat := 118140960795 + 6568098 * 2 ^ 59
def prefixEnd_6568098 : Nat := 4983230072969 + 3 ^ 40 * 6568098 * 2
def baseEnd_6568098 : Nat := 374732362203838724452097

theorem tailTrace_6568098 : CollatzResearch.WordTrace tailWord_6568098 prefixEnd_6568098 374732362203838724452097 := by
  unfold tailWord_6568098
  simp only [CollatzResearch.WordTrace]
  refine ⟨59889553639727540669270237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159705476372606775118053965 59889553639727540669270237)
  ·
    refine ⟨22458582614897827750976339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59889553639727540669270237 22458582614897827750976339)
    ·
      refine ⟨33687873922346741626464509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22458582614897827750976339 33687873922346741626464509)
      ·
        refine ⟨12632952720880028109924191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33687873922346741626464509 12632952720880028109924191)
        ·
          refine ⟨18949429081320042164886287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12632952720880028109924191 18949429081320042164886287)
          ·
            refine ⟨28424143621980063247329431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18949429081320042164886287 28424143621980063247329431)
            ·
              refine ⟨42636215432970094870994147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28424143621980063247329431 42636215432970094870994147)
              ·
                refine ⟨63954323149455142306491221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42636215432970094870994147 63954323149455142306491221)
                ·
                  refine ⟨374732362203838724452097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63954323149455142306491221 374732362203838724452097)
                  ·
                    rfl

theorem cell23_6568098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_6568098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568098 prefixEnd_6568098 := by exact prefixLift 6568098
  have htrace : WordTrace (prefixWord ++ tailWord_6568098) baseStart_6568098 baseEnd_6568098 := by
    simpa [prefixWord, tailWord_6568098, baseEnd_6568098] using wordTrace_append hprefix tailTrace_6568098
  have hstable : (prefixWord ++ tailWord_6568098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568098).length < 2 ^ (prefixWord ++ tailWord_6568098).sum := by decide
  have hdescent : baseEnd_6568098 < baseStart_6568098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568126 : List Nat := [4, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_6568126 : Nat := 118140960795 + 6568126 * 2 ^ 59
def prefixEnd_6568126 : Nat := 4983230072969 + 3 ^ 40 * 6568126 * 2
def baseEnd_6568126 : Nat := 3372605637292874410518745

theorem tailTrace_6568126 : CollatzResearch.WordTrace tailWord_6568126 prefixEnd_6568126 3372605637292874410518745 := by
  unfold tailWord_6568126
  simp only [CollatzResearch.WordTrace]
  refine ⟨29944904475351090432387529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159706157201872482306066821 29944904475351090432387529)
  ·
    refine ⟨22458678356513317824290647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29944904475351090432387529 22458678356513317824290647)
    ·
      refine ⟨33688017534769976736435971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22458678356513317824290647 33688017534769976736435971)
      ·
        refine ⟨50532026302154965104653957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33688017534769976736435971 50532026302154965104653957)
        ·
          refine ⟨9474754931654055957122617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50532026302154965104653957 9474754931654055957122617)
          ·
            refine ⟨7106066198740541967841963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9474754931654055957122617 7106066198740541967841963)
            ·
              refine ⟨10659099298110812951762945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7106066198740541967841963 10659099298110812951762945)
              ·
                refine ⟨7994324473583109713822209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10659099298110812951762945 7994324473583109713822209)
                ·
                  refine ⟨5995743355187332285366657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7994324473583109713822209 5995743355187332285366657)
                  ·
                    refine ⟨4496807516390499214024993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5995743355187332285366657 4496807516390499214024993)
                    ·
                      refine ⟨3372605637292874410518745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496807516390499214024993 3372605637292874410518745)
                      ·
                        rfl

theorem cell23_6568126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_6568126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568126 prefixEnd_6568126 := by exact prefixLift 6568126
  have htrace : WordTrace (prefixWord ++ tailWord_6568126) baseStart_6568126 baseEnd_6568126 := by
    simpa [prefixWord, tailWord_6568126, baseEnd_6568126] using wordTrace_append hprefix tailTrace_6568126
  have hstable : (prefixWord ++ tailWord_6568126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568126).length < 2 ^ (prefixWord ++ tailWord_6568126).sum := by decide
  have hdescent : baseEnd_6568126 < baseStart_6568126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568171 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 10]
def baseStart_6568171 : Nat := 118140960795 + 6568171 * 2 ^ 59
def prefixEnd_6568171 : Nat := 4983230072969 + 3 ^ 40 * 6568171 * 2
def baseEnd_6568171 : Nat := 374736527102480748272893

theorem tailTrace_6568171 : CollatzResearch.WordTrace tailWord_6568171 prefixEnd_6568171 374736527102480748272893 := by
  unfold tailWord_6568171
  simp only [CollatzResearch.WordTrace]
  refine ⟨239560877087645696144488367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159707251391763797429658911 239560877087645696144488367)
  ·
    refine ⟨359341315631468544216732551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239560877087645696144488367 359341315631468544216732551)
    ·
      refine ⟨539011973447202816325098827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359341315631468544216732551 539011973447202816325098827)
      ·
        refine ⟨808517960170804224487648241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539011973447202816325098827 808517960170804224487648241)
        ·
          refine ⟨606388470128103168365736181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 808517960170804224487648241 606388470128103168365736181)
          ·
            refine ⟨56848919074509672034287767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 606388470128103168365736181 56848919074509672034287767)
            ·
              refine ⟨85273378611764508051431651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56848919074509672034287767 85273378611764508051431651)
              ·
                refine ⟨127910067917646762077147477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85273378611764508051431651 127910067917646762077147477)
                ·
                  refine ⟨374736527102480748272893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 127910067917646762077147477 374736527102480748272893)
                  ·
                    rfl

theorem cell23_6568171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 10].length) (baseStart_6568171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568171 prefixEnd_6568171 := by exact prefixLift 6568171
  have htrace : WordTrace (prefixWord ++ tailWord_6568171) baseStart_6568171 baseEnd_6568171 := by
    simpa [prefixWord, tailWord_6568171, baseEnd_6568171] using wordTrace_append hprefix tailTrace_6568171
  have hstable : (prefixWord ++ tailWord_6568171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568171).length < 2 ^ (prefixWord ++ tailWord_6568171).sum := by decide
  have hdescent : baseEnd_6568171 < baseStart_6568171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568188 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 8]
def baseStart_6568188 : Nat := 118140960795 + 6568188 * 2 ^ 59
def prefixEnd_6568188 : Nat := 4983230072969 + 3 ^ 40 * 6568188 * 2
def baseEnd_6568188 : Nat := 374737497010383685327051

theorem tailTrace_6568188 : CollatzResearch.WordTrace tailWord_6568188 prefixEnd_6568188 374737497010383685327051 := by
  unfold tailWord_6568188
  simp only [CollatzResearch.WordTrace]
  refine ⟨119780748564292054023928609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159707664752389405365238145 119780748564292054023928609)
  ·
    refine ⟨89835561423219040517946457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119780748564292054023928609 89835561423219040517946457)
    ·
      refine ⟨67376671067414280388459843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89835561423219040517946457 67376671067414280388459843)
      ·
        refine ⟨101065006601121420582689765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67376671067414280388459843 101065006601121420582689765)
        ·
          refine ⟨18949688737710266359254331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101065006601121420582689765 18949688737710266359254331)
          ·
            refine ⟨28424533106565399538881497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18949688737710266359254331 28424533106565399538881497)
            ·
              refine ⟨21318399829924049654161123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28424533106565399538881497 21318399829924049654161123)
              ·
                refine ⟨31977599744886074481241685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21318399829924049654161123 31977599744886074481241685)
                ·
                  refine ⟨374737497010383685327051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31977599744886074481241685 374737497010383685327051)
                  ·
                    rfl

theorem cell23_6568188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_6568188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568188 prefixEnd_6568188 := by exact prefixLift 6568188
  have htrace : WordTrace (prefixWord ++ tailWord_6568188) baseStart_6568188 baseEnd_6568188 := by
    simpa [prefixWord, tailWord_6568188, baseEnd_6568188] using wordTrace_append hprefix tailTrace_6568188
  have hstable : (prefixWord ++ tailWord_6568188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568188).length < 2 ^ (prefixWord ++ tailWord_6568188).sum := by decide
  have hdescent : baseEnd_6568188 < baseStart_6568188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568225 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 1, 5, 2]
def baseStart_6568225 : Nat := 118140960795 + 6568225 * 2 ^ 59
def prefixEnd_6568225 : Nat := 4983230072969 + 3 ^ 40 * 6568225 * 2
def baseEnd_6568225 : Nat := 3372656471877669523180789

theorem tailTrace_6568225 : CollatzResearch.WordTrace tailWord_6568225 prefixEnd_6568225 3372656471877669523180789 := by
  unfold tailWord_6568225
  simp only [CollatzResearch.WordTrace]
  refine ⟨239562846629450063366954129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159708564419633375577969419 239562846629450063366954129)
  ·
    refine ⟨179672134972087547525215597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239562846629450063366954129 179672134972087547525215597)
    ·
      refine ⟨67377050614532830321955849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179672134972087547525215597 67377050614532830321955849)
      ·
        refine ⟨50532787960899622741466887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67377050614532830321955849 50532787960899622741466887)
        ·
          refine ⟨75799181941349434112200331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50532787960899622741466887 75799181941349434112200331)
          ·
            refine ⟨113698772912024151168300497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75799181941349434112200331 113698772912024151168300497)
            ·
              refine ⟨85274079684018113376225373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113698772912024151168300497 85274079684018113376225373)
              ·
                refine ⟨31977779881506792516084515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85274079684018113376225373 31977779881506792516084515)
                ·
                  refine ⟨47966669822260188774126773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31977779881506792516084515 47966669822260188774126773)
                  ·
                    refine ⟨4496875295836892697574385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47966669822260188774126773 4496875295836892697574385)
                    ·
                      refine ⟨3372656471877669523180789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496875295836892697574385 3372656471877669523180789)
                      ·
                        rfl

theorem cell23_6568225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_6568225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568225 prefixEnd_6568225 := by exact prefixLift 6568225
  have htrace : WordTrace (prefixWord ++ tailWord_6568225) baseStart_6568225 baseEnd_6568225 := by
    simpa [prefixWord, tailWord_6568225, baseEnd_6568225] using wordTrace_append hprefix tailTrace_6568225
  have hstable : (prefixWord ++ tailWord_6568225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568225).length < 2 ^ (prefixWord ++ tailWord_6568225).sum := by decide
  have hdescent : baseEnd_6568225 < baseStart_6568225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568272 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 5, 2, 2]
def baseStart_6568272 : Nat := 118140960795 + 6568272 * 2 ^ 59
def prefixEnd_6568272 : Nat := 4983230072969 + 3 ^ 40 * 6568272 * 2
def baseEnd_6568272 : Nat := 3372680605468430839293073

theorem tailTrace_6568272 : CollatzResearch.WordTrace tailWord_6568272 prefixEnd_6568272 3372680605468430839293073 := by
  unfold tailWord_6568272
  simp only [CollatzResearch.WordTrace]
  refine ⟨119782280430139895196957535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159709707240186526929276713 119782280430139895196957535)
  ·
    refine ⟨179673420645209842795436303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119782280430139895196957535 179673420645209842795436303)
    ·
      refine ⟨269510130967814764193154455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179673420645209842795436303 269510130967814764193154455)
      ·
        refine ⟨404265196451722146289731683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269510130967814764193154455 404265196451722146289731683)
        ·
          refine ⟨606397794677583219434597525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404265196451722146289731683 606397794677583219434597525)
          ·
            refine ⟨28424896625511713410996759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 606397794677583219434597525 28424896625511713410996759)
            ·
              refine ⟨42637344938267570116495139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28424896625511713410996759 42637344938267570116495139)
              ·
                refine ⟨63956017407401355174742709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42637344938267570116495139 63956017407401355174742709)
                ·
                  refine ⟨5995876631943877047632129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63956017407401355174742709 5995876631943877047632129)
                  ·
                    refine ⟨4496907473957907785724097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5995876631943877047632129 4496907473957907785724097)
                    ·
                      refine ⟨3372680605468430839293073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496907473957907785724097 3372680605468430839293073)
                      ·
                        rfl

theorem cell23_6568272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 5, 2, 2].length) (baseStart_6568272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568272 prefixEnd_6568272 := by exact prefixLift 6568272
  have htrace : WordTrace (prefixWord ++ tailWord_6568272) baseStart_6568272 baseEnd_6568272 := by
    simpa [prefixWord, tailWord_6568272, baseEnd_6568272] using wordTrace_append hprefix tailTrace_6568272
  have hstable : (prefixWord ++ tailWord_6568272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568272).length < 2 ^ (prefixWord ++ tailWord_6568272).sum := by decide
  have hdescent : baseEnd_6568272 < baseStart_6568272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568292 : List Nat := [2, 3, 1, 1, 3, 1, 3, 3, 1, 2, 3]
def baseStart_6568292 : Nat := 118140960795 + 6568292 * 2 ^ 59
def prefixEnd_6568292 : Nat := 4983230072969 + 3 ^ 40 * 6568292 * 2
def baseEnd_6568292 : Nat := 3372690875081520761042981

theorem tailTrace_6568292 : CollatzResearch.WordTrace tailWord_6568292 prefixEnd_6568292 3372690875081520761042981 := by
  unfold tailWord_6568292
  simp only [CollatzResearch.WordTrace]
  refine ⟨119782645160103666904821565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159710193546804889206428753 119782645160103666904821565)
  ·
    refine ⟨44918491935038875089308087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119782645160103666904821565 44918491935038875089308087)
    ·
      refine ⟨67377737902558312633962131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44918491935038875089308087 67377737902558312633962131)
      ·
        refine ⟨101066606853837468950943197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67377737902558312633962131 101066606853837468950943197)
        ·
          refine ⟨37899977570189050856603699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101066606853837468950943197 37899977570189050856603699)
          ·
            refine ⟨56849966355283576284905549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37899977570189050856603699 56849966355283576284905549)
            ·
              refine ⟨21318737383231341106839581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56849966355283576284905549 21318737383231341106839581)
              ·
                refine ⟨7994526518711752915064843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21318737383231341106839581 7994526518711752915064843)
                ·
                  refine ⟨11991789778067629372597265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7994526518711752915064843 11991789778067629372597265)
                  ·
                    refine ⟨8993842333550722029447949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11991789778067629372597265 8993842333550722029447949)
                    ·
                      refine ⟨3372690875081520761042981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8993842333550722029447949 3372690875081520761042981)
                      ·
                        rfl

theorem cell23_6568292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_6568292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568292 prefixEnd_6568292 := by exact prefixLift 6568292
  have htrace : WordTrace (prefixWord ++ tailWord_6568292) baseStart_6568292 baseEnd_6568292 := by
    simpa [prefixWord, tailWord_6568292, baseEnd_6568292] using wordTrace_append hprefix tailTrace_6568292
  have hstable : (prefixWord ++ tailWord_6568292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568292).length < 2 ^ (prefixWord ++ tailWord_6568292).sum := by decide
  have hdescent : baseEnd_6568292 < baseStart_6568292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568306 : List Nat := [3, 2, 1, 2, 1, 3, 2, 4, 1, 2, 2]
def baseStart_6568306 : Nat := 118140960795 + 6568306 * 2 ^ 59
def prefixEnd_6568306 : Nat := 4983230072969 + 3 ^ 40 * 6568306 * 2
def baseEnd_6568306 : Nat := 3372698063810683706267917

theorem tailTrace_6568306 : CollatzResearch.WordTrace tailWord_6568306 prefixEnd_6568306 3372698063810683706267917 := by
  unfold tailWord_6568306
  simp only [CollatzResearch.WordTrace]
  refine ⟨59891450235539153550163193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159710533961437742800435181 59891450235539153550163193)
  ·
    refine ⟨44918587676654365162622395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59891450235539153550163193 44918587676654365162622395)
    ·
      refine ⟨67377881514981547743933593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44918587676654365162622395 67377881514981547743933593)
      ·
        refine ⟨50533411136236160807950195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67377881514981547743933593 50533411136236160807950195)
        ·
          refine ⟨75800116704354241211925293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50533411136236160807950195 75800116704354241211925293)
          ·
            refine ⟨28425043764132840454471985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75800116704354241211925293 28425043764132840454471985)
            ·
              refine ⟨21318782823099630340853989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28425043764132840454471985 21318782823099630340853989)
              ·
                refine ⟨3997271779331180688910123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21318782823099630340853989 3997271779331180688910123)
                ·
                  refine ⟨5995907668996771033365185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3997271779331180688910123 5995907668996771033365185)
                  ·
                    refine ⟨4496930751747578275023889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5995907668996771033365185 4496930751747578275023889)
                    ·
                      refine ⟨3372698063810683706267917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496930751747578275023889 3372698063810683706267917)
                      ·
                        rfl

theorem cell23_6568306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_6568306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568306 prefixEnd_6568306 := by exact prefixLift 6568306
  have htrace : WordTrace (prefixWord ++ tailWord_6568306) baseStart_6568306 baseEnd_6568306 := by
    simpa [prefixWord, tailWord_6568306, baseEnd_6568306] using wordTrace_append hprefix tailTrace_6568306
  have hstable : (prefixWord ++ tailWord_6568306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568306).length < 2 ^ (prefixWord ++ tailWord_6568306).sum := by decide
  have hdescent : baseEnd_6568306 < baseStart_6568306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568340 : List Nat := [2, 4, 2, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_6568340 : Nat := 118140960795 + 6568340 * 2 ^ 59
def prefixEnd_6568340 : Nat := 4983230072969 + 3 ^ 40 * 6568340 * 2
def baseEnd_6568340 : Nat := 3372715522152936573242761

theorem tailTrace_6568340 : CollatzResearch.WordTrace tailWord_6568340 prefixEnd_6568340 3372715522152936573242761 := by
  unfold tailWord_6568340
  simp only [CollatzResearch.WordTrace]
  refine ⟨119783520512016719003695237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159711360682688958671593649 119783520512016719003695237)
  ·
    refine ⟨22459410096003134813192857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119783520512016719003695237 22459410096003134813192857)
    ·
      refine ⟨16844557572002351109894643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22459410096003134813192857 16844557572002351109894643)
      ·
        refine ⟨25266836358003526664841965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16844557572002351109894643 25266836358003526664841965)
        ·
          refine ⟨9475063634251322499315737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25266836358003526664841965 9475063634251322499315737)
          ·
            refine ⟨7106297725688491874486803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9475063634251322499315737 7106297725688491874486803)
            ·
              refine ⟨10659446588532737811730205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7106297725688491874486803 10659446588532737811730205)
              ·
                refine ⟨3997292470699776679398827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10659446588532737811730205 3997292470699776679398827)
                ·
                  refine ⟨5995938706049665019098241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3997292470699776679398827 5995938706049665019098241)
                  ·
                    refine ⟨4496954029537248764323681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5995938706049665019098241 4496954029537248764323681)
                    ·
                      refine ⟨3372715522152936573242761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496954029537248764323681 3372715522152936573242761)
                      ·
                        rfl

theorem cell23_6568340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_6568340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568340 prefixEnd_6568340 := by exact prefixLift 6568340
  have htrace : WordTrace (prefixWord ++ tailWord_6568340) baseStart_6568340 baseEnd_6568340 := by
    simpa [prefixWord, tailWord_6568340, baseEnd_6568340] using wordTrace_append hprefix tailTrace_6568340
  have hstable : (prefixWord ++ tailWord_6568340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568340).length < 2 ^ (prefixWord ++ tailWord_6568340).sum := by decide
  have hdescent : baseEnd_6568340 < baseStart_6568340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568373 : List Nat := [1, 3, 3, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_6568373 : Nat := 118140960795 + 6568373 * 2 ^ 59
def prefixEnd_6568373 : Nat := 4983230072969 + 3 ^ 40 * 6568373 * 2
def baseEnd_6568373 : Nat := 3372732467014534944130109

theorem tailTrace_6568373 : CollatzResearch.WordTrace tailWord_6568373 prefixEnd_6568373 3372732467014534944130109 := by
  unfold tailWord_6568373
  simp only [CollatzResearch.WordTrace]
  refine ⟨239568244632913884643341773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159712163088609256428894515 239568244632913884643341773)
  ·
    refine ⟨89838091737342706741253165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239568244632913884643341773 89838091737342706741253165)
    ·
      refine ⟨33689284401503515027969937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89838091737342706741253165 33689284401503515027969937)
      ·
        refine ⟨25266963301127636270977453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33689284401503515027969937 25266963301127636270977453)
        ·
          refine ⟨9475111237922863601616545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25266963301127636270977453 9475111237922863601616545)
          ·
            refine ⟨7106333428442147701212409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9475111237922863601616545 7106333428442147701212409)
            ·
              refine ⟨5329750071331610775909307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7106333428442147701212409 5329750071331610775909307)
              ·
                refine ⟨7994625106997416163863961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5329750071331610775909307 7994625106997416163863961)
                ·
                  refine ⟨5995968830248062122897971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7994625106997416163863961 5995968830248062122897971)
                  ·
                    refine ⟨8993953245372093184346957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5995968830248062122897971 8993953245372093184346957)
                    ·
                      refine ⟨3372732467014534944130109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8993953245372093184346957 3372732467014534944130109)
                      ·
                        rfl

theorem cell23_6568373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_6568373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568373 prefixEnd_6568373 := by exact prefixLift 6568373
  have htrace : WordTrace (prefixWord ++ tailWord_6568373) baseStart_6568373 baseEnd_6568373 := by
    simpa [prefixWord, tailWord_6568373, baseEnd_6568373] using wordTrace_append hprefix tailTrace_6568373
  have hstable : (prefixWord ++ tailWord_6568373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568373).length < 2 ^ (prefixWord ++ tailWord_6568373).sum := by decide
  have hdescent : baseEnd_6568373 < baseStart_6568373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568395 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 3]
def baseStart_6568395 : Nat := 118140960795 + 6568395 * 2 ^ 59
def prefixEnd_6568395 : Nat := 4983230072969 + 3 ^ 40 * 6568395 * 2
def baseEnd_6568395 : Nat := 3372743763588933858055007

theorem tailTrace_6568395 : CollatzResearch.WordTrace tailWord_6568395 prefixEnd_6568395 3372743763588933858055007 := by
  unfold tailWord_6568395
  simp only [CollatzResearch.WordTrace]
  refine ⟨239569047038834182400642639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159712698025889454933761759 239569047038834182400642639)
  ·
    refine ⟨359353570558251273600963959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239569047038834182400642639 359353570558251273600963959)
    ·
      refine ⟨539030355837376910401445939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359353570558251273600963959 539030355837376910401445939)
      ·
        refine ⟨808545533756065365602168909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539030355837376910401445939 808545533756065365602168909)
        ·
          refine ⟨303204575158524512100813341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 808545533756065365602168909 303204575158524512100813341)
          ·
            refine ⟨113701715684446692037805003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303204575158524512100813341 113701715684446692037805003)
            ·
              refine ⟨170552573526670038056707505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113701715684446692037805003 170552573526670038056707505)
              ·
                refine ⟨127914430145002528542530629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170552573526670038056707505 127914430145002528542530629)
                ·
                  refine ⟨23983955652187974101724493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127914430145002528542530629 23983955652187974101724493)
                  ·
                    refine ⟨8993983369570490288146685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23983955652187974101724493 8993983369570490288146685)
                    ·
                      refine ⟨3372743763588933858055007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8993983369570490288146685 3372743763588933858055007)
                      ·
                        rfl

theorem cell23_6568395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 3].length) (baseStart_6568395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568395 prefixEnd_6568395 := by exact prefixLift 6568395
  have htrace : WordTrace (prefixWord ++ tailWord_6568395) baseStart_6568395 baseEnd_6568395 := by
    simpa [prefixWord, tailWord_6568395, baseEnd_6568395] using wordTrace_append hprefix tailTrace_6568395
  have hstable : (prefixWord ++ tailWord_6568395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568395).length < 2 ^ (prefixWord ++ tailWord_6568395).sum := by decide
  have hdescent : baseEnd_6568395 < baseStart_6568395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568419 : List Nat := [1, 1, 1, 6, 3, 1, 1, 4, 5]
def baseStart_6568419 : Nat := 118140960795 + 6568419 * 2 ^ 59
def prefixEnd_6568419 : Nat := 4983230072969 + 3 ^ 40 * 6568419 * 2
def baseEnd_6568419 : Nat := 374750676347182418239433

theorem tailTrace_6568419 : CollatzResearch.WordTrace tailWord_6568419 prefixEnd_6568419 374750676347182418239433 := by
  unfold tailWord_6568419
  simp only [CollatzResearch.WordTrace]
  refine ⟨239569922390747234499516311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159713281593831489666344207 239569922390747234499516311)
  ·
    refine ⟨359354883586120851749274467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239569922390747234499516311 359354883586120851749274467)
    ·
      refine ⟨539032325379181277623911701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359354883586120851749274467 539032325379181277623911701)
      ·
        refine ⟨25267140252149122388620861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 539032325379181277623911701 25267140252149122388620861)
        ·
          refine ⟨9475177594555920895732823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25267140252149122388620861 9475177594555920895732823)
          ·
            refine ⟨14212766391833881343599235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9475177594555920895732823 14212766391833881343599235)
            ·
              refine ⟨21319149587750822015398853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14212766391833881343599235 21319149587750822015398853)
              ·
                refine ⟨3997340547703279127887285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21319149587750822015398853 3997340547703279127887285)
                ·
                  refine ⟨374750676347182418239433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3997340547703279127887285 374750676347182418239433)
                  ·
                    rfl

theorem cell23_6568419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 5].length) (baseStart_6568419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568419 prefixEnd_6568419 := by exact prefixLift 6568419
  have htrace : WordTrace (prefixWord ++ tailWord_6568419) baseStart_6568419 baseEnd_6568419 := by
    simpa [prefixWord, tailWord_6568419, baseEnd_6568419] using wordTrace_append hprefix tailTrace_6568419
  have hstable : (prefixWord ++ tailWord_6568419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568419).length < 2 ^ (prefixWord ++ tailWord_6568419).sum := by decide
  have hdescent : baseEnd_6568419 < baseStart_6568419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568429 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_6568429 : Nat := 118140960795 + 6568429 * 2 ^ 59
def prefixEnd_6568429 : Nat := 4983230072969 + 3 ^ 40 * 6568429 * 2
def baseEnd_6568429 : Nat := 3372761221931186725029851

theorem tailTrace_6568429 : CollatzResearch.WordTrace tailWord_6568429 prefixEnd_6568429 3372761221931186725029851 := by
  unfold tailWord_6568429
  simp only [CollatzResearch.WordTrace]
  refine ⟨239570287120711006207380341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159713524747140670804920227 239570287120711006207380341)
  ·
    refine ⟨22459714417566656831941907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239570287120711006207380341 22459714417566656831941907)
    ·
      refine ⟨33689571626349985247912861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22459714417566656831941907 33689571626349985247912861)
      ·
        refine ⟨12633589359881244467967323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33689571626349985247912861 12633589359881244467967323)
        ·
          refine ⟨18950384039821866701950985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12633589359881244467967323 18950384039821866701950985)
          ·
            refine ⟨14212788029866400026463239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18950384039821866701950985 14212788029866400026463239)
            ·
              refine ⟨21319182044799600039694859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14212788029866400026463239 21319182044799600039694859)
              ·
                refine ⟨31978773067199400059542289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21319182044799600039694859 31978773067199400059542289)
                ·
                  refine ⟨23984079800399550044656717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31978773067199400059542289 23984079800399550044656717)
                  ·
                    refine ⟨8994029925149831266746269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23984079800399550044656717 8994029925149831266746269)
                    ·
                      refine ⟨3372761221931186725029851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8994029925149831266746269 3372761221931186725029851)
                      ·
                        rfl

theorem cell23_6568429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_6568429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568429 prefixEnd_6568429 := by exact prefixLift 6568429
  have htrace : WordTrace (prefixWord ++ tailWord_6568429) baseStart_6568429 baseEnd_6568429 := by
    simpa [prefixWord, tailWord_6568429, baseEnd_6568429] using wordTrace_append hprefix tailTrace_6568429
  have hstable : (prefixWord ++ tailWord_6568429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568429).length < 2 ^ (prefixWord ++ tailWord_6568429).sum := by decide
  have hdescent : baseEnd_6568429 < baseStart_6568429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568435 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 4]
def baseStart_6568435 : Nat := 118140960795 + 6568435 * 2 ^ 59
def prefixEnd_6568435 : Nat := 4983230072969 + 3 ^ 40 * 6568435 * 2
def baseEnd_6568435 : Nat := 3372764302815113701554823

theorem tailTrace_6568435 : CollatzResearch.WordTrace tailWord_6568435 prefixEnd_6568435 3372764302815113701554823 := by
  unfold tailWord_6568435
  simp only [CollatzResearch.WordTrace]
  refine ⟨239570505958689269232098759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159713670639126179488065839 239570505958689269232098759)
  ·
    refine ⟨359355758938033903848148139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239570505958689269232098759 359355758938033903848148139)
    ·
      refine ⟨539033638407050855772222209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359355758938033903848148139 539033638407050855772222209)
      ·
        refine ⟨404275228805288141829166657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539033638407050855772222209 404275228805288141829166657)
        ·
          refine ⟨303206421603966106371874993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404275228805288141829166657 303206421603966106371874993)
          ·
            refine ⟨227404816202974579778906245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303206421603966106371874993 227404816202974579778906245)
            ·
              refine ⟨42638403038057733708544921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227404816202974579778906245 42638403038057733708544921)
              ·
                refine ⟨31978802278543300281408691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42638403038057733708544921 31978802278543300281408691)
                ·
                  refine ⟨47968203417814950422113037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31978802278543300281408691 47968203417814950422113037)
                  ·
                    refine ⟨17988076281680606408292389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47968203417814950422113037 17988076281680606408292389)
                    ·
                      refine ⟨3372764302815113701554823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17988076281680606408292389 3372764302815113701554823)
                      ·
                        rfl

theorem cell23_6568435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_6568435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568435 prefixEnd_6568435 := by exact prefixLift 6568435
  have htrace : WordTrace (prefixWord ++ tailWord_6568435) baseStart_6568435 baseEnd_6568435 := by
    simpa [prefixWord, tailWord_6568435, baseEnd_6568435] using wordTrace_append hprefix tailTrace_6568435
  have hstable : (prefixWord ++ tailWord_6568435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568435).length < 2 ^ (prefixWord ++ tailWord_6568435).sum := by decide
  have hdescent : baseEnd_6568435 < baseStart_6568435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568449 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 2, 5]
def baseStart_6568449 : Nat := 118140960795 + 6568449 * 2 ^ 59
def prefixEnd_6568449 : Nat := 4983230072969 + 3 ^ 40 * 6568449 * 2
def baseEnd_6568449 : Nat := 1124257163848092215593253

theorem tailTrace_6568449 : CollatzResearch.WordTrace tailWord_6568449 prefixEnd_6568449 1124257163848092215593253 := by
  unfold tailWord_6568449
  simp only [CollatzResearch.WordTrace]
  refine ⟨239571016580638549623108401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159714011053759033082072267 239571016580638549623108401)
  ·
    refine ⟨179678262435478912217331301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239571016580638549623108401 179678262435478912217331301)
    ·
      refine ⟨33689674206652296040749619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179678262435478912217331301 33689674206652296040749619)
      ·
        refine ⟨50534511309978444061124429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33689674206652296040749619 50534511309978444061124429)
        ·
          refine ⟨18950441741241916522921661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50534511309978444061124429 18950441741241916522921661)
          ·
            refine ⟨7106415652965718696095623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18950441741241916522921661 7106415652965718696095623)
            ·
              refine ⟨10659623479448578044143435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7106415652965718696095623 10659623479448578044143435)
              ·
                refine ⟨15989435219172867066215153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10659623479448578044143435 15989435219172867066215153)
                ·
                  refine ⟨11992076414379650299661365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15989435219172867066215153 11992076414379650299661365)
                  ·
                    refine ⟨1124257163848092215593253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11992076414379650299661365 1124257163848092215593253)
                    ·
                      rfl

theorem cell23_6568449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_6568449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568449 prefixEnd_6568449 := by exact prefixLift 6568449
  have htrace : WordTrace (prefixWord ++ tailWord_6568449) baseStart_6568449 baseEnd_6568449 := by
    simpa [prefixWord, tailWord_6568449, baseEnd_6568449] using wordTrace_append hprefix tailTrace_6568449
  have hstable : (prefixWord ++ tailWord_6568449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568449).length < 2 ^ (prefixWord ++ tailWord_6568449).sum := by decide
  have hdescent : baseEnd_6568449 < baseStart_6568449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568513 : List Nat := [1, 2, 5, 1, 1, 4, 1, 3, 1, 4]
def baseStart_6568513 : Nat := 118140960795 + 6568513 * 2 ^ 59
def prefixEnd_6568513 : Nat := 4983230072969 + 3 ^ 40 * 6568513 * 2
def baseEnd_6568513 : Nat := 1124268118102054798793155

theorem tailTrace_6568513 : CollatzResearch.WordTrace tailWord_6568513 prefixEnd_6568513 1124268118102054798793155 := by
  unfold tailWord_6568513
  simp only [CollatzResearch.WordTrace]
  refine ⟨239573350852406688553438193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159715567234937792368958795 239573350852406688553438193)
  ·
    refine ⟨179680013139305016415078645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239573350852406688553438193 179680013139305016415078645)
    ·
      refine ⟨16845001231809845288913623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179680013139305016415078645 16845001231809845288913623)
      ·
        refine ⟨25267501847714767933370435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16845001231809845288913623 25267501847714767933370435)
        ·
          refine ⟨37901252771572151900055653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25267501847714767933370435 37901252771572151900055653)
          ·
            refine ⟨7106484894669778481260435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37901252771572151900055653 7106484894669778481260435)
            ·
              refine ⟨10659727342004667721890653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7106484894669778481260435 10659727342004667721890653)
              ·
                refine ⟨3997397753251750395708995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10659727342004667721890653 3997397753251750395708995)
                ·
                  refine ⟨5996096629877625593563493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3997397753251750395708995 5996096629877625593563493)
                  ·
                    refine ⟨1124268118102054798793155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5996096629877625593563493 1124268118102054798793155)
                    ·
                      rfl

theorem cell23_6568513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_6568513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568513 prefixEnd_6568513 := by exact prefixLift 6568513
  have htrace : WordTrace (prefixWord ++ tailWord_6568513) baseStart_6568513 baseEnd_6568513 := by
    simpa [prefixWord, tailWord_6568513, baseEnd_6568513] using wordTrace_append hprefix tailTrace_6568513
  have hstable : (prefixWord ++ tailWord_6568513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568513).length < 2 ^ (prefixWord ++ tailWord_6568513).sum := by decide
  have hdescent : baseEnd_6568513 < baseStart_6568513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568529 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 4, 3, 2]
def baseStart_6568529 : Nat := 118140960795 + 6568529 * 2 ^ 59
def prefixEnd_6568529 : Nat := 4983230072969 + 3 ^ 40 * 6568529 * 2
def baseEnd_6568529 : Nat := 3372812569996636333779391

theorem tailTrace_6568529 : CollatzResearch.WordTrace tailWord_6568529 prefixEnd_6568529 3372812569996636333779391 := by
  unfold tailWord_6568529
  simp only [CollatzResearch.WordTrace]
  refine ⟨239573934420348723286020641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159715956280232482190680427 239573934420348723286020641)
  ·
    refine ⟨179680450815261542464515481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239573934420348723286020641 179680450815261542464515481)
    ·
      refine ⟨134760338111446156848386611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179680450815261542464515481 134760338111446156848386611)
      ·
        refine ⟨202140507167169235272579917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134760338111446156848386611 202140507167169235272579917)
        ·
          refine ⟨75802690187688463227217469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202140507167169235272579917 75802690187688463227217469)
          ·
            refine ⟨28426008820383173710206551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75802690187688463227217469 28426008820383173710206551)
            ·
              refine ⟨42639013230574760565309827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28426008820383173710206551 42639013230574760565309827)
              ·
                refine ⟨63958519845862140847964741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42639013230574760565309827 63958519845862140847964741)
                ·
                  refine ⟨11992222471099151408993389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63958519845862140847964741 11992222471099151408993389)
                  ·
                    refine ⟨4497083426662181778372521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11992222471099151408993389 4497083426662181778372521)
                    ·
                      refine ⟨3372812569996636333779391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4497083426662181778372521 3372812569996636333779391)
                      ·
                        rfl

theorem cell23_6568529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 3, 2].length) (baseStart_6568529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568529 prefixEnd_6568529 := by exact prefixLift 6568529
  have htrace : WordTrace (prefixWord ++ tailWord_6568529) baseStart_6568529 baseEnd_6568529 := by
    simpa [prefixWord, tailWord_6568529, baseEnd_6568529] using wordTrace_append hprefix tailTrace_6568529
  have hstable : (prefixWord ++ tailWord_6568529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568529).length < 2 ^ (prefixWord ++ tailWord_6568529).sum := by decide
  have hdescent : baseEnd_6568529 < baseStart_6568529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568536 : List Nat := [2, 1, 2, 2, 1, 2, 2, 6, 1, 1, 3]
def baseStart_6568536 : Nat := 118140960795 + 6568536 * 2 ^ 59
def prefixEnd_6568536 : Nat := 4983230072969 + 3 ^ 40 * 6568536 * 2
def baseEnd_6568536 : Nat := 3372816164361217806391859

theorem tailTrace_6568536 : CollatzResearch.WordTrace tailWord_6568536 prefixEnd_6568536 3372816164361217806391859 := by
  unfold tailWord_6568536
  simp only [CollatzResearch.WordTrace]
  refine ⟨119787094865661681740762731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159716126487548908987683641 119787094865661681740762731)
  ·
    refine ⟨179680642298492522611144097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119787094865661681740762731 179680642298492522611144097)
    ·
      refine ⟨134760481723869391958358073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179680642298492522611144097 134760481723869391958358073)
      ·
        refine ⟨101070361292902043968768555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134760481723869391958358073 101070361292902043968768555)
        ·
          refine ⟨151605541939353065953152833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101070361292902043968768555 151605541939353065953152833)
          ·
            refine ⟨113704156454514799464864625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151605541939353065953152833 113704156454514799464864625)
            ·
              refine ⟨85278117340886099598648469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113704156454514799464864625 85278117340886099598648469)
              ·
                refine ⟨3997411750354035918686647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85278117340886099598648469 3997411750354035918686647)
                ·
                  refine ⟨5996117625531053878029971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3997411750354035918686647 5996117625531053878029971)
                  ·
                    refine ⟨8994176438296580817044957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5996117625531053878029971 8994176438296580817044957)
                    ·
                      refine ⟨3372816164361217806391859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8994176438296580817044957 3372816164361217806391859)
                      ·
                        rfl

theorem cell23_6568536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_6568536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568536 prefixEnd_6568536 := by exact prefixLift 6568536
  have htrace : WordTrace (prefixWord ++ tailWord_6568536) baseStart_6568536 baseEnd_6568536 := by
    simpa [prefixWord, tailWord_6568536, baseEnd_6568536] using wordTrace_append hprefix tailTrace_6568536
  have hstable : (prefixWord ++ tailWord_6568536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568536).length < 2 ^ (prefixWord ++ tailWord_6568536).sum := by decide
  have hdescent : baseEnd_6568536 < baseStart_6568536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568559 : List Nat := [1, 1, 2, 1, 3, 2, 5, 2, 1, 1, 4]
def baseStart_6568559 : Nat := 118140960795 + 6568559 * 2 ^ 59
def prefixEnd_6568559 : Nat := 4983230072969 + 3 ^ 40 * 6568559 * 2
def baseEnd_6568559 : Nat := 3372827974416271216404253

theorem tailTrace_6568559 : CollatzResearch.WordTrace tailWord_6568559 prefixEnd_6568559 3372827974416271216404253 := by
  unfold tailWord_6568559
  simp only [CollatzResearch.WordTrace]
  refine ⟨239575028610240038409612731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159716685740160025606408487 239575028610240038409612731)
  ·
    refine ⟨359362542915360057614419097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239575028610240038409612731 359362542915360057614419097)
    ·
      refine ⟨269521907186520043210814323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359362542915360057614419097 269521907186520043210814323)
      ·
        refine ⟨404282860779780064816221485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269521907186520043210814323 404282860779780064816221485)
        ·
          refine ⟨151606072792417524306083057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404282860779780064816221485 151606072792417524306083057)
          ·
            refine ⟨113704554594313143229562293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151606072792417524306083057 113704554594313143229562293)
            ·
              refine ⟨10659801993216857177771465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113704554594313143229562293 10659801993216857177771465)
              ·
                refine ⟨7994851494912642883328599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10659801993216857177771465 7994851494912642883328599)
                ·
                  refine ⟨11992277242368964324992899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7994851494912642883328599 11992277242368964324992899)
                  ·
                    refine ⟨17988415863553446487489349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11992277242368964324992899 17988415863553446487489349)
                    ·
                      refine ⟨3372827974416271216404253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17988415863553446487489349 3372827974416271216404253)
                      ·
                        rfl

theorem cell23_6568559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 1, 4].length) (baseStart_6568559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568559 prefixEnd_6568559 := by exact prefixLift 6568559
  have htrace : WordTrace (prefixWord ++ tailWord_6568559) baseStart_6568559 baseEnd_6568559 := by
    simpa [prefixWord, tailWord_6568559, baseEnd_6568559] using wordTrace_append hprefix tailTrace_6568559
  have hstable : (prefixWord ++ tailWord_6568559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568559).length < 2 ^ (prefixWord ++ tailWord_6568559).sum := by decide
  have hdescent : baseEnd_6568559 < baseStart_6568559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568572 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_6568572 : Nat := 118140960795 + 6568572 * 2 ^ 59
def prefixEnd_6568572 : Nat := 4983230072969 + 3 ^ 40 * 6568572 * 2
def baseEnd_6568572 : Nat := 3372834649664779665541693

theorem tailTrace_6568572 : CollatzResearch.WordTrace tailWord_6568572 prefixEnd_6568572 3372834649664779665541693 := by
  unfold tailWord_6568572
  simp only [CollatzResearch.WordTrace]
  refine ⟨119787751379596470814917985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159717001839461961086557313 119787751379596470814917985)
  ·
    refine ⟨89840813534697353111188489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119787751379596470814917985 89840813534697353111188489)
    ·
      refine ⟨67380610151023014833391367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89840813534697353111188489 67380610151023014833391367)
      ·
        refine ⟨101070915226534522250087051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67380610151023014833391367 101070915226534522250087051)
        ·
          refine ⟨151606372839801783375130577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101070915226534522250087051 151606372839801783375130577)
          ·
            refine ⟨113704779629851337531347933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151606372839801783375130577 113704779629851337531347933)
            ·
              refine ⟨42639292361194251574255475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113704779629851337531347933 42639292361194251574255475)
              ·
                refine ⟨63958938541791377361383213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42639292361194251574255475 63958938541791377361383213)
                ·
                  refine ⟨23984601953171766510518705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63958938541791377361383213 23984601953171766510518705)
                  ·
                    refine ⟨17988451464878824882889029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23984601953171766510518705 17988451464878824882889029)
                    ·
                      refine ⟨3372834649664779665541693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17988451464878824882889029 3372834649664779665541693)
                      ·
                        rfl

theorem cell23_6568572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_6568572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568572 prefixEnd_6568572 := by exact prefixLift 6568572
  have htrace : WordTrace (prefixWord ++ tailWord_6568572) baseStart_6568572 baseEnd_6568572 := by
    simpa [prefixWord, tailWord_6568572, baseEnd_6568572] using wordTrace_append hprefix tailTrace_6568572
  have hstable : (prefixWord ++ tailWord_6568572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568572).length < 2 ^ (prefixWord ++ tailWord_6568572).sum := by decide
  have hdescent : baseEnd_6568572 < baseStart_6568572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568576 : List Nat := [2, 1, 1, 2, 1, 6, 3, 1, 1, 1, 4]
def baseStart_6568576 : Nat := 118140960795 + 6568576 * 2 ^ 59
def prefixEnd_6568576 : Nat := 4983230072969 + 3 ^ 40 * 6568576 * 2
def baseEnd_6568576 : Nat := 3372836703587397649891675

theorem tailTrace_6568576 : CollatzResearch.WordTrace tailWord_6568576 prefixEnd_6568576 3372836703587397649891675 := by
  unfold tailWord_6568576
  simp only [CollatzResearch.WordTrace]
  refine ⟨119787824325589225156490791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159717099100785633541987721 119787824325589225156490791)
  ·
    refine ⟨179681736488383837734736187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119787824325589225156490791 179681736488383837734736187)
    ·
      refine ⟨269522604732575756602104281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179681736488383837734736187 269522604732575756602104281)
      ·
        refine ⟨202141953549431817451578211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269522604732575756602104281 202141953549431817451578211)
        ·
          refine ⟨303212930324147726177367317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202141953549431817451578211 303212930324147726177367317)
          ·
            refine ⟨14213106108944424664564093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 303212930324147726177367317 14213106108944424664564093)
            ·
              refine ⟨5329914790854159249211535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14213106108944424664564093 5329914790854159249211535)
              ·
                refine ⟨7994872186281238873817303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5329914790854159249211535 7994872186281238873817303)
                ·
                  refine ⟨11992308279421858310725955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7994872186281238873817303 11992308279421858310725955)
                  ·
                    refine ⟨17988462419132787466088933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11992308279421858310725955 17988462419132787466088933)
                    ·
                      refine ⟨3372836703587397649891675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17988462419132787466088933 3372836703587397649891675)
                      ·
                        rfl

theorem cell23_6568576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 1, 1, 4].length) (baseStart_6568576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568576 prefixEnd_6568576 := by exact prefixLift 6568576
  have htrace : WordTrace (prefixWord ++ tailWord_6568576) baseStart_6568576 baseEnd_6568576 := by
    simpa [prefixWord, tailWord_6568576, baseEnd_6568576] using wordTrace_append hprefix tailTrace_6568576
  have hstable : (prefixWord ++ tailWord_6568576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568576).length < 2 ^ (prefixWord ++ tailWord_6568576).sum := by decide
  have hdescent : baseEnd_6568576 < baseStart_6568576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568579 : List Nat := [1, 1, 1, 3, 3, 1, 2, 5, 1, 2, 3]
def baseStart_6568579 : Nat := 118140960795 + 6568579 * 2 ^ 59
def prefixEnd_6568579 : Nat := 4983230072969 + 3 ^ 40 * 6568579 * 2
def baseEnd_6568579 : Nat := 3372838244029361138154161

theorem tailTrace_6568579 : CollatzResearch.WordTrace tailWord_6568579 prefixEnd_6568579 3372838244029361138154161 := by
  unfold tailWord_6568579
  simp only [CollatzResearch.WordTrace]
  refine ⟨239575758070167581825340791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159717172046778387883560527 239575758070167581825340791)
  ·
    refine ⟨359363637105251372738011187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239575758070167581825340791 359363637105251372738011187)
    ·
      refine ⟨539045455657877059107016781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359363637105251372738011187 539045455657877059107016781)
      ·
        refine ⟨202142045871703897165131293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 539045455657877059107016781 202142045871703897165131293)
        ·
          refine ⟨75803267201888961436924235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202142045871703897165131293 75803267201888961436924235)
          ·
            refine ⟨113704900802833442155386353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75803267201888961436924235 113704900802833442155386353)
            ·
              refine ⟨85278675602125081616539765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113704900802833442155386353 85278675602125081616539765)
              ·
                refine ⟨7994875837699226401550603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85278675602125081616539765 7994875837699226401550603)
                ·
                  refine ⟨11992313756548839602325905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7994875837699226401550603 11992313756548839602325905)
                  ·
                    refine ⟨8994235317411629701744429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11992313756548839602325905 8994235317411629701744429)
                    ·
                      refine ⟨3372838244029361138154161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8994235317411629701744429 3372838244029361138154161)
                      ·
                        rfl

theorem cell23_6568579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_6568579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568579 prefixEnd_6568579 := by exact prefixLift 6568579
  have htrace : WordTrace (prefixWord ++ tailWord_6568579) baseStart_6568579 baseEnd_6568579 := by
    simpa [prefixWord, tailWord_6568579, baseEnd_6568579] using wordTrace_append hprefix tailTrace_6568579
  have hstable : (prefixWord ++ tailWord_6568579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568579).length < 2 ^ (prefixWord ++ tailWord_6568579).sum := by decide
  have hdescent : baseEnd_6568579 < baseStart_6568579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568596 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_6568596 : Nat := 118140960795 + 6568596 * 2 ^ 59
def prefixEnd_6568596 : Nat := 4983230072969 + 3 ^ 40 * 6568596 * 2
def baseEnd_6568596 : Nat := 3372846973200487571641583

theorem tailTrace_6568596 : CollatzResearch.WordTrace tailWord_6568596 prefixEnd_6568596 3372846973200487571641583 := by
  unfold tailWord_6568596
  simp only [CollatzResearch.WordTrace]
  refine ⟨119788189055552996864354821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159717585407403995819139761 119788189055552996864354821)
  ·
    refine ⟨22460285447916186912066529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119788189055552996864354821 22460285447916186912066529)
    ·
      refine ⟨16845214085937140184049897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22460285447916186912066529 16845214085937140184049897)
      ·
        refine ⟨12633910564452855138037423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16845214085937140184049897 12633910564452855138037423)
        ·
          refine ⟨18950865846679282707056135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12633910564452855138037423 18950865846679282707056135)
          ·
            refine ⟨28426298770018924060584203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18950865846679282707056135 28426298770018924060584203)
            ·
              refine ⟨42639448155028386090876305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28426298770018924060584203 42639448155028386090876305)
              ·
                refine ⟨31979586116271289568157229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42639448155028386090876305 31979586116271289568157229)
                ·
                  refine ⟨11992344793601733588058961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31979586116271289568157229 11992344793601733588058961)
                  ·
                    refine ⟨8994258595201300191044221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11992344793601733588058961 8994258595201300191044221)
                    ·
                      refine ⟨3372846973200487571641583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8994258595201300191044221 3372846973200487571641583)
                      ·
                        rfl

theorem cell23_6568596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_6568596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568596 prefixEnd_6568596 := by exact prefixLift 6568596
  have htrace : WordTrace (prefixWord ++ tailWord_6568596) baseStart_6568596 baseEnd_6568596 := by
    simpa [prefixWord, tailWord_6568596, baseEnd_6568596] using wordTrace_append hprefix tailTrace_6568596
  have hstable : (prefixWord ++ tailWord_6568596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568596).length < 2 ^ (prefixWord ++ tailWord_6568596).sum := by decide
  have hdescent : baseEnd_6568596 < baseStart_6568596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568606 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_6568606 : Nat := 118140960795 + 6568606 * 2 ^ 59
def prefixEnd_6568606 : Nat := 4983230072969 + 3 ^ 40 * 6568606 * 2
def baseEnd_6568606 : Nat := 3372852108007032532516537

theorem tailTrace_6568606 : CollatzResearch.WordTrace tailWord_6568606 prefixEnd_6568606 3372852108007032532516537 := by
  unfold tailWord_6568606
  simp only [CollatzResearch.WordTrace]
  refine ⟨29947092855133720679571709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159717828560713176957715781 29947092855133720679571709)
  ·
    refine ⟨11230159820675145254839391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29947092855133720679571709 11230159820675145254839391)
    ·
      refine ⟨16845239731012717882259087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11230159820675145254839391 16845239731012717882259087)
      ·
        refine ⟨25267859596519076823388631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16845239731012717882259087 25267859596519076823388631)
        ·
          refine ⟨37901789394778615235082947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25267859596519076823388631 37901789394778615235082947)
          ·
            refine ⟨56852684092167922852624421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37901789394778615235082947 56852684092167922852624421)
            ·
              refine ⟨10659878267281485534867079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56852684092167922852624421 10659878267281485534867079)
              ·
                refine ⟨15989817400922228302300619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10659878267281485534867079 15989817400922228302300619)
                ·
                  refine ⟨23984726101383342453450929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15989817400922228302300619 23984726101383342453450929)
                  ·
                    refine ⟨17988544576037506840088197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23984726101383342453450929 17988544576037506840088197)
                    ·
                      refine ⟨3372852108007032532516537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17988544576037506840088197 3372852108007032532516537)
                      ·
                        rfl

theorem cell23_6568606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_6568606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568606 prefixEnd_6568606 := by exact prefixLift 6568606
  have htrace : WordTrace (prefixWord ++ tailWord_6568606) baseStart_6568606 baseEnd_6568606 := by
    simpa [prefixWord, tailWord_6568606, baseEnd_6568606] using wordTrace_append hprefix tailTrace_6568606
  have hstable : (prefixWord ++ tailWord_6568606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568606).length < 2 ^ (prefixWord ++ tailWord_6568606).sum := by decide
  have hdescent : baseEnd_6568606 < baseStart_6568606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568612 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_6568612 : Nat := 118140960795 + 6568612 * 2 ^ 59
def prefixEnd_6568612 : Nat := 4983230072969 + 3 ^ 40 * 6568612 * 2
def baseEnd_6568612 : Nat := 1124285062963653169680503

theorem tailTrace_6568612 : CollatzResearch.WordTrace tailWord_6568612 prefixEnd_6568612 1124285062963653169680503 := by
  unfold tailWord_6568612
  simp only [CollatzResearch.WordTrace]
  refine ⟨119788480839524014230646045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159717974452698685640861393 119788480839524014230646045)
  ·
    refine ⟨44920680314821505336492267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119788480839524014230646045 44920680314821505336492267)
    ·
      refine ⟨67381020472232258004738401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44920680314821505336492267 67381020472232258004738401)
      ·
        refine ⟨50535765354174193503553801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67381020472232258004738401 50535765354174193503553801)
        ·
          refine ⟨37901824015630645127665351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50535765354174193503553801 37901824015630645127665351)
          ·
            refine ⟨56852736023445967691498027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37901824015630645127665351 56852736023445967691498027)
            ·
              refine ⟨85279104035168951537247041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56852736023445967691498027 85279104035168951537247041)
              ·
                refine ⟨63959328026376713652935281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85279104035168951537247041 63959328026376713652935281)
                ·
                  refine ⟨47969496019782535239701461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63959328026376713652935281 47969496019782535239701461)
                  ·
                    refine ⟨1124285062963653169680503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47969496019782535239701461 1124285062963653169680503)
                    ·
                      rfl

theorem cell23_6568612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_6568612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568612 prefixEnd_6568612 := by exact prefixLift 6568612
  have htrace : WordTrace (prefixWord ++ tailWord_6568612) baseStart_6568612 baseEnd_6568612 := by
    simpa [prefixWord, tailWord_6568612, baseEnd_6568612] using wordTrace_append hprefix tailTrace_6568612
  have hstable : (prefixWord ++ tailWord_6568612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568612).length < 2 ^ (prefixWord ++ tailWord_6568612).sum := by decide
  have hdescent : baseEnd_6568612 < baseStart_6568612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568630 : List Nat := [5, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_6568630 : Nat := 118140960795 + 6568630 * 2 ^ 59
def prefixEnd_6568630 : Nat := 4983230072969 + 3 ^ 40 * 6568630 * 2
def baseEnd_6568630 : Nat := 3372864431542740438616427

theorem tailTrace_6568630 : CollatzResearch.WordTrace tailWord_6568630 prefixEnd_6568630 3372864431542740438616427 := by
  unfold tailWord_6568630
  simp only [CollatzResearch.WordTrace]
  refine ⟨14973601137061426095965459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159718412128655211690298229 14973601137061426095965459)
  ·
    refine ⟨22460401705592139143948189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14973601137061426095965459 22460401705592139143948189)
    ·
      refine ⟨8422650639597052178980571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22460401705592139143948189 8422650639597052178980571)
      ·
        refine ⟨12633975959395578268470857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8422650639597052178980571 12633975959395578268470857)
        ·
          refine ⟨9475481969546683701353143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12633975959395578268470857 9475481969546683701353143)
          ·
            refine ⟨14213222954320025552029715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9475481969546683701353143 14213222954320025552029715)
            ·
              refine ⟨21319834431480038328044573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14213222954320025552029715 21319834431480038328044573)
              ·
                refine ⟨7994937911805014373016715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21319834431480038328044573 7994937911805014373016715)
                ·
                  refine ⟨11992406867707521559525073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7994937911805014373016715 11992406867707521559525073)
                  ·
                    refine ⟨8994305150780641169643805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11992406867707521559525073 8994305150780641169643805)
                    ·
                      refine ⟨3372864431542740438616427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8994305150780641169643805 3372864431542740438616427)
                      ·
                        rfl

theorem cell23_6568630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_6568630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568630 prefixEnd_6568630 := by exact prefixLift 6568630
  have htrace : WordTrace (prefixWord ++ tailWord_6568630) baseStart_6568630 baseEnd_6568630 := by
    simpa [prefixWord, tailWord_6568630, baseEnd_6568630] using wordTrace_append hprefix tailTrace_6568630
  have hstable : (prefixWord ++ tailWord_6568630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568630).length < 2 ^ (prefixWord ++ tailWord_6568630).sum := by decide
  have hdescent : baseEnd_6568630 < baseStart_6568630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568660 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_6568660 : Nat := 118140960795 + 6568660 * 2 ^ 59
def prefixEnd_6568660 : Nat := 4983230072969 + 3 ^ 40 * 6568660 * 2
def baseEnd_6568660 : Nat := 3372879835962375321241289

theorem tailTrace_6568660 : CollatzResearch.WordTrace tailWord_6568660 prefixEnd_6568660 3372879835962375321241289 := by
  unfold tailWord_6568660
  simp only [CollatzResearch.WordTrace]
  refine ⟨119789356191437066329519717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159719141588582755106026289 119789356191437066329519717)
  ·
    refine ⟨22460504285894449936784947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119789356191437066329519717 22460504285894449936784947)
    ·
      refine ⟨33690756428841674905177421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22460504285894449936784947 33690756428841674905177421)
      ·
        refine ⟨12634033660815628089441533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33690756428841674905177421 12634033660815628089441533)
        ·
          refine ⟨4737762622805860533540575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12634033660815628089441533 4737762622805860533540575)
          ·
            refine ⟨7106643934208790800310863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4737762622805860533540575 7106643934208790800310863)
            ·
              refine ⟨10659965901313186200466295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7106643934208790800310863 10659965901313186200466295)
              ·
                refine ⟨15989948851969779300699443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10659965901313186200466295 15989948851969779300699443)
                ·
                  refine ⟨23984923277954668951049165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15989948851969779300699443 23984923277954668951049165)
                  ·
                    refine ⟨8994346229233000856643437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23984923277954668951049165 8994346229233000856643437)
                    ·
                      refine ⟨3372879835962375321241289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8994346229233000856643437 3372879835962375321241289)
                      ·
                        rfl

theorem cell23_6568660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_6568660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568660 prefixEnd_6568660 := by exact prefixLift 6568660
  have htrace : WordTrace (prefixWord ++ tailWord_6568660) baseStart_6568660 baseEnd_6568660 := by
    simpa [prefixWord, tailWord_6568660, baseEnd_6568660] using wordTrace_append hprefix tailTrace_6568660
  have hstable : (prefixWord ++ tailWord_6568660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568660).length < 2 ^ (prefixWord ++ tailWord_6568660).sum := by decide
  have hdescent : baseEnd_6568660 < baseStart_6568660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568706 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 7]
def baseStart_6568706 : Nat := 118140960795 + 6568706 * 2 ^ 59
def prefixEnd_6568706 : Nat := 4983230072969 + 3 ^ 40 * 6568706 * 2
def baseEnd_6568706 : Nat := 374767050674720237918453

theorem tailTrace_6568706 : CollatzResearch.WordTrace tailWord_6568706 prefixEnd_6568706 374767050674720237918453 := by
  unfold tailWord_6568706
  simp only [CollatzResearch.WordTrace]
  refine ⟨59895097535176870628803493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159720260093804988343475981 59895097535176870628803493)
  ·
    refine ⟨11230330787845663242900655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59895097535176870628803493 11230330787845663242900655)
    ·
      refine ⟨16845496181768494864350983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11230330787845663242900655 16845496181768494864350983)
      ·
        refine ⟨25268244272652742296526475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16845496181768494864350983 25268244272652742296526475)
        ·
          refine ⟨37902366408979113444789713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25268244272652742296526475 37902366408979113444789713)
          ·
            refine ⟨28426774806734335083592285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37902366408979113444789713 28426774806734335083592285)
            ·
              refine ⟨10660040552525375656347107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28426774806734335083592285 10660040552525375656347107)
              ·
                refine ⟨15990060828788063484520661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10660040552525375656347107 15990060828788063484520661)
                ·
                  refine ⟨374767050674720237918453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15990060828788063484520661 374767050674720237918453)
                  ·
                    rfl

theorem cell23_6568706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_6568706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568706 prefixEnd_6568706 := by exact prefixLift 6568706
  have htrace : WordTrace (prefixWord ++ tailWord_6568706) baseStart_6568706 baseEnd_6568706 := by
    simpa [prefixWord, tailWord_6568706, baseEnd_6568706] using wordTrace_append hprefix tailTrace_6568706
  have hstable : (prefixWord ++ tailWord_6568706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568706).length < 2 ^ (prefixWord ++ tailWord_6568706).sum := by decide
  have hdescent : baseEnd_6568706 < baseStart_6568706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568736 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 2, 5]
def baseStart_6568736 : Nat := 118140960795 + 6568736 * 2 ^ 59
def prefixEnd_6568736 : Nat := 4983230072969 + 3 ^ 40 * 6568736 * 2
def baseEnd_6568736 : Nat := 1124306286830705674630313

theorem tailTrace_6568736 : CollatzResearch.WordTrace tailWord_6568736 prefixEnd_6568736 1124306286830705674630313 := by
  unfold tailWord_6568736
  simp only [CollatzResearch.WordTrace]
  refine ⟨119790742165299398819403031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159720989553732531759204041 119790742165299398819403031)
  ·
    refine ⟨179686113247949098229104547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119790742165299398819403031 179686113247949098229104547)
    ·
      refine ⟨269529169871923647343656821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179686113247949098229104547 269529169871923647343656821)
      ·
        refine ⟨25268359675492841938467827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269529169871923647343656821 25268359675492841938467827)
        ·
          refine ⟨37902539513239262907701741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25268359675492841938467827 37902539513239262907701741)
          ·
            refine ⟨14213452317464723590388153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37902539513239262907701741 14213452317464723590388153)
            ·
              refine ⟨10660089238098542692791115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14213452317464723590388153 10660089238098542692791115)
              ·
                refine ⟨15990133857147814039186673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10660089238098542692791115 15990133857147814039186673)
                ·
                  refine ⟨11992600392860860529390005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15990133857147814039186673 11992600392860860529390005)
                  ·
                    refine ⟨1124306286830705674630313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11992600392860860529390005 1124306286830705674630313)
                    ·
                      rfl

theorem cell23_6568736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 2, 5].length) (baseStart_6568736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568736 prefixEnd_6568736 := by exact prefixLift 6568736
  have htrace : WordTrace (prefixWord ++ tailWord_6568736) baseStart_6568736 baseEnd_6568736 := by
    simpa [prefixWord, tailWord_6568736, baseEnd_6568736] using wordTrace_append hprefix tailTrace_6568736
  have hstable : (prefixWord ++ tailWord_6568736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568736).length < 2 ^ (prefixWord ++ tailWord_6568736).sum := by decide
  have hdescent : baseEnd_6568736 < baseStart_6568736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568793 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 2, 2, 3]
def baseStart_6568793 : Nat := 118140960795 + 6568793 * 2 ^ 59
def prefixEnd_6568793 : Nat := 4983230072969 + 3 ^ 40 * 6568793 * 2
def baseEnd_6568793 : Nat := 3372948128889423300878177

theorem tailTrace_6568793 : CollatzResearch.WordTrace tailWord_6568793 prefixEnd_6568793 3372948128889423300878177 := by
  unfold tailWord_6568793
  simp only [CollatzResearch.WordTrace]
  refine ⟨239583563291392296373631033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159722375527594864249087355 239583563291392296373631033)
  ·
    refine ⟨179687672468544222280223275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239583563291392296373631033 179687672468544222280223275)
    ·
      refine ⟨269531508702816333420334913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179687672468544222280223275 269531508702816333420334913)
      ·
        refine ⟨202148631527112250065251185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269531508702816333420334913 202148631527112250065251185)
        ·
          refine ⟨151611473645334187548938389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202148631527112250065251185 151611473645334187548938389)
          ·
            refine ⟨7106787827125040041356487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 151611473645334187548938389 7106787827125040041356487)
            ·
              refine ⟨10660181740687560062034731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7106787827125040041356487 10660181740687560062034731)
              ·
                refine ⟨15990272611031340093052097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10660181740687560062034731 15990272611031340093052097)
                ·
                  refine ⟨11992704458273505069789073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15990272611031340093052097 11992704458273505069789073)
                  ·
                    refine ⟨8994528343705128802341805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11992704458273505069789073 8994528343705128802341805)
                    ·
                      refine ⟨3372948128889423300878177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8994528343705128802341805 3372948128889423300878177)
                      ·
                        rfl

theorem cell23_6568793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_6568793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568793 prefixEnd_6568793 := by exact prefixLift 6568793
  have htrace : WordTrace (prefixWord ++ tailWord_6568793) baseStart_6568793 baseEnd_6568793 := by
    simpa [prefixWord, tailWord_6568793, baseEnd_6568793] using wordTrace_append hprefix tailTrace_6568793
  have hstable : (prefixWord ++ tailWord_6568793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568793).length < 2 ^ (prefixWord ++ tailWord_6568793).sum := by decide
  have hdescent : baseEnd_6568793 < baseStart_6568793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568849 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_6568849 : Nat := 118140960795 + 6568849 * 2 ^ 59
def prefixEnd_6568849 : Nat := 4983230072969 + 3 ^ 40 * 6568849 * 2
def baseEnd_6568849 : Nat := 3372976883806075081777919

theorem tailTrace_6568849 : CollatzResearch.WordTrace tailWord_6568849 prefixEnd_6568849 3372976883806075081777919 := by
  unfold tailWord_6568849
  simp only [CollatzResearch.WordTrace]
  refine ⟨239585605779189417937669601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159723737186126278625113067 239585605779189417937669601)
  ·
    refine ⟨179689204334392063453252201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239585605779189417937669601 179689204334392063453252201)
    ·
      refine ⟨134766903250794047589939151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179689204334392063453252201 134766903250794047589939151)
      ·
        refine ⟨202150354876191071384908727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134766903250794047589939151 202150354876191071384908727)
        ·
          refine ⟨303225532314286607077363091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202150354876191071384908727 303225532314286607077363091)
          ·
            refine ⟨454838298471429910616044637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303225532314286607077363091 454838298471429910616044637)
            ·
              refine ⟨170564361926786216481016739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 454838298471429910616044637 170564361926786216481016739)
              ·
                refine ⟨255846542890179324721525109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170564361926786216481016739 255846542890179324721525109)
                ·
                  refine ⟨23985613395954311692642979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255846542890179324721525109 23985613395954311692642979)
                  ·
                    refine ⟨35978420093931467538964469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23985613395954311692642979 35978420093931467538964469)
                    ·
                      refine ⟨3372976883806075081777919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35978420093931467538964469 3372976883806075081777919)
                      ·
                        rfl

theorem cell23_6568849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_6568849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568849 prefixEnd_6568849 := by exact prefixLift 6568849
  have htrace : WordTrace (prefixWord ++ tailWord_6568849) baseStart_6568849 baseEnd_6568849 := by
    simpa [prefixWord, tailWord_6568849, baseEnd_6568849] using wordTrace_append hprefix tailTrace_6568849
  have hstable : (prefixWord ++ tailWord_6568849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568849).length < 2 ^ (prefixWord ++ tailWord_6568849).sum := by decide
  have hdescent : baseEnd_6568849 < baseStart_6568849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568863 : List Nat := [1, 1, 2, 5, 2, 1, 2, 3, 1, 1, 4]
def baseStart_6568863 : Nat := 118140960795 + 6568863 * 2 ^ 59
def prefixEnd_6568863 : Nat := 4983230072969 + 3 ^ 40 * 6568863 * 2
def baseEnd_6568863 : Nat := 3372984072535238027002855

theorem tailTrace_6568863 : CollatzResearch.WordTrace tailWord_6568863 prefixEnd_6568863 3372984072535238027002855 := by
  unfold tailWord_6568863
  simp only [CollatzResearch.WordTrace]
  refine ⟨239586116401138698328679243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159724077600759132219119495 239586116401138698328679243)
  ·
    refine ⟨359379174601708047493018865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239586116401138698328679243 359379174601708047493018865)
    ·
      refine ⟨269534380951281035619764149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359379174601708047493018865 269534380951281035619764149)
      ·
        refine ⟨25268848214182597089352889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269534380951281035619764149 25268848214182597089352889)
        ·
          refine ⟨18951636160636947817014667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25268848214182597089352889 18951636160636947817014667)
          ·
            refine ⟨28427454240955421725522001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18951636160636947817014667 28427454240955421725522001)
            ·
              refine ⟨21320590680716566294141501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28427454240955421725522001 21320590680716566294141501)
              ·
                refine ⟨7995221505268712360303063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21320590680716566294141501 7995221505268712360303063)
                ·
                  refine ⟨11992832257903068540454595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7995221505268712360303063 11992832257903068540454595)
                  ·
                    refine ⟨17989248386854602810681893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11992832257903068540454595 17989248386854602810681893)
                    ·
                      refine ⟨3372984072535238027002855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17989248386854602810681893 3372984072535238027002855)
                      ·
                        rfl

theorem cell23_6568863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_6568863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568863 prefixEnd_6568863 := by exact prefixLift 6568863
  have htrace : WordTrace (prefixWord ++ tailWord_6568863) baseStart_6568863 baseEnd_6568863 := by
    simpa [prefixWord, tailWord_6568863, baseEnd_6568863] using wordTrace_append hprefix tailTrace_6568863
  have hstable : (prefixWord ++ tailWord_6568863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568863).length < 2 ^ (prefixWord ++ tailWord_6568863).sum := by decide
  have hdescent : baseEnd_6568863 < baseStart_6568863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568899 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 2, 7]
def baseStart_6568899 : Nat := 118140960795 + 6568899 * 2 ^ 59
def prefixEnd_6568899 : Nat := 4983230072969 + 3 ^ 40 * 6568899 * 2
def baseEnd_6568899 : Nat := 1124334185946266628717563

theorem tailTrace_6568899 : CollatzResearch.WordTrace tailWord_6568899 prefixEnd_6568899 1124334185946266628717563 := by
  unfold tailWord_6568899
  simp only [CollatzResearch.WordTrace]
  refine ⟨239587429429008276476989751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159724952952672184317993167 239587429429008276476989751)
  ·
    refine ⟨359381144143512414715484627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239587429429008276476989751 359381144143512414715484627)
    ·
      refine ⟨539071716215268622073226941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359381144143512414715484627 539071716215268622073226941)
      ·
        refine ⟨202151893580725733277460103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 539071716215268622073226941 202151893580725733277460103)
        ·
          refine ⟨303227840371088599916190155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202151893580725733277460103 303227840371088599916190155)
          ·
            refine ⟨454841760556632899874285233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303227840371088599916190155 454841760556632899874285233)
            ·
              refine ⟨341131320417474674905713925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454841760556632899874285233 341131320417474674905713925)
              ·
                refine ⟨63962122578276501544821361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341131320417474674905713925 63962122578276501544821361)
                ·
                  refine ⟨47971591933707376158616021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63962122578276501544821361 47971591933707376158616021)
                  ·
                    refine ⟨1124334185946266628717563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47971591933707376158616021 1124334185946266628717563)
                    ·
                      rfl

theorem cell23_6568899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 7].length) (baseStart_6568899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568899 prefixEnd_6568899 := by exact prefixLift 6568899
  have htrace : WordTrace (prefixWord ++ tailWord_6568899) baseStart_6568899 baseEnd_6568899 := by
    simpa [prefixWord, tailWord_6568899, baseEnd_6568899] using wordTrace_append hprefix tailTrace_6568899
  have hstable : (prefixWord ++ tailWord_6568899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568899).length < 2 ^ (prefixWord ++ tailWord_6568899).sum := by decide
  have hdescent : baseEnd_6568899 < baseStart_6568899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568917 : List Nat := [1, 3, 2, 3, 3, 1, 3, 1, 1, 2, 3]
def baseStart_6568917 : Nat := 118140960795 + 6568917 * 2 ^ 59
def prefixEnd_6568917 : Nat := 4983230072969 + 3 ^ 40 * 6568917 * 2
def baseEnd_6568917 : Nat := 3373011800490580815727607

theorem tailTrace_6568917 : CollatzResearch.WordTrace tailWord_6568917 prefixEnd_6568917 3373011800490580815727607 := by
  unfold tailWord_6568917
  simp only [CollatzResearch.WordTrace]
  refine ⟨239588085942943065551145005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159725390628628710367430003 239588085942943065551145005)
  ·
    refine ⟨89845532228603649581679377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239588085942943065551145005 89845532228603649581679377)
    ·
      refine ⟨67384149171452737186259533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89845532228603649581679377 67384149171452737186259533)
      ·
        refine ⟨25269055939294776444847325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67384149171452737186259533 25269055939294776444847325)
        ·
          refine ⟨9475895977235541166817747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25269055939294776444847325 9475895977235541166817747)
          ·
            refine ⟨14213843965853311750226621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9475895977235541166817747 14213843965853311750226621)
            ·
              refine ⟨5330191487194991906334983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14213843965853311750226621 5330191487194991906334983)
              ·
                refine ⟨7995287230792487859502475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5330191487194991906334983 7995287230792487859502475)
                ·
                  refine ⟨11992930846188731789253713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7995287230792487859502475 11992930846188731789253713)
                  ·
                    refine ⟨8994698134641548841940285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11992930846188731789253713 8994698134641548841940285)
                    ·
                      refine ⟨3373011800490580815727607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8994698134641548841940285 3373011800490580815727607)
                      ·
                        rfl

theorem cell23_6568917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_6568917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568917 prefixEnd_6568917 := by exact prefixLift 6568917
  have htrace : WordTrace (prefixWord ++ tailWord_6568917) baseStart_6568917 baseEnd_6568917 := by
    simpa [prefixWord, tailWord_6568917, baseEnd_6568917] using wordTrace_append hprefix tailTrace_6568917
  have hstable : (prefixWord ++ tailWord_6568917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568917).length < 2 ^ (prefixWord ++ tailWord_6568917).sum := by decide
  have hdescent : baseEnd_6568917 < baseStart_6568917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568936 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_6568936 : Nat := 118140960795 + 6568936 * 2 ^ 59
def prefixEnd_6568936 : Nat := 4983230072969 + 3 ^ 40 * 6568936 * 2
def baseEnd_6568936 : Nat := 3373021556623016241390019

theorem tailTrace_6568936 : CollatzResearch.WordTrace tailWord_6568936 prefixEnd_6568936 3373021556623016241390019 := by
  unfold tailWord_6568936
  simp only [CollatzResearch.WordTrace]
  refine ⟨119794389464937115898043331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159725852619916154530724441 119794389464937115898043331)
  ·
    refine ⟨179691584197405673847064997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119794389464937115898043331 179691584197405673847064997)
    ·
      refine ⟨33692172037013563846324687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179691584197405673847064997 33692172037013563846324687)
      ·
        refine ⟨50538258055520345769487031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33692172037013563846324687 50538258055520345769487031)
        ·
          refine ⟨75807387083280518654230547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50538258055520345769487031 75807387083280518654230547)
          ·
            refine ⟨113711080624920777981345821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75807387083280518654230547 113711080624920777981345821)
            ·
              refine ⟨42641655234345291743004683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113711080624920777981345821 42641655234345291743004683)
              ·
                refine ⟨63962482851517937614507025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42641655234345291743004683 63962482851517937614507025)
                ·
                  refine ⟨47971862138638453210880269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63962482851517937614507025 47971862138638453210880269)
                  ·
                    refine ⟨17989448301989419954080101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47971862138638453210880269 17989448301989419954080101)
                    ·
                      refine ⟨3373021556623016241390019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17989448301989419954080101 3373021556623016241390019)
                      ·
                        rfl

theorem cell23_6568936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_6568936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568936 prefixEnd_6568936 := by exact prefixLift 6568936
  have htrace : WordTrace (prefixWord ++ tailWord_6568936) baseStart_6568936 baseEnd_6568936 := by
    simpa [prefixWord, tailWord_6568936, baseEnd_6568936] using wordTrace_append hprefix tailTrace_6568936
  have hstable : (prefixWord ++ tailWord_6568936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568936).length < 2 ^ (prefixWord ++ tailWord_6568936).sum := by decide
  have hdescent : baseEnd_6568936 < baseStart_6568936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568948 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_6568948 : Nat := 118140960795 + 6568948 * 2 ^ 59
def prefixEnd_6568948 : Nat := 4983230072969 + 3 ^ 40 * 6568948 * 2
def baseEnd_6568948 : Nat := 3373027718390870194439965

theorem tailTrace_6568948 : CollatzResearch.WordTrace tailWord_6568948 prefixEnd_6568948 3373027718390870194439965 := by
  unfold tailWord_6568948
  simp only [CollatzResearch.WordTrace]
  refine ⟨119794608302915378922761749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159726144403887171897015665 119794608302915378922761749)
  ·
    refine ⟨5615372264199158387004457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119794608302915378922761749 5615372264199158387004457)
    ·
      refine ⟨4211529198149368790253343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5615372264199158387004457 4211529198149368790253343)
      ·
        refine ⟨6317293797224053185380015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4211529198149368790253343 6317293797224053185380015)
        ·
          refine ⟨9475940695836079778070023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6317293797224053185380015 9475940695836079778070023)
          ·
            refine ⟨14213911043754119667105035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9475940695836079778070023 14213911043754119667105035)
            ·
              refine ⟨21320866565631179500657553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14213911043754119667105035 21320866565631179500657553)
              ·
                refine ⟨15990649924223384625493165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21320866565631179500657553 15990649924223384625493165)
                ·
                  refine ⟨5996493721583769234559937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15990649924223384625493165 5996493721583769234559937)
                  ·
                    refine ⟨4497370291187826925919953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5996493721583769234559937 4497370291187826925919953)
                    ·
                      refine ⟨3373027718390870194439965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4497370291187826925919953 3373027718390870194439965)
                      ·
                        rfl

theorem cell23_6568948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_6568948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568948 prefixEnd_6568948 := by exact prefixLift 6568948
  have htrace : WordTrace (prefixWord ++ tailWord_6568948) baseStart_6568948 baseEnd_6568948 := by
    simpa [prefixWord, tailWord_6568948, baseEnd_6568948] using wordTrace_append hprefix tailTrace_6568948
  have hstable : (prefixWord ++ tailWord_6568948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568948).length < 2 ^ (prefixWord ++ tailWord_6568948).sum := by decide
  have hdescent : baseEnd_6568948 < baseStart_6568948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568970 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 1, 4, 2]
def baseStart_6568970 : Nat := 118140960795 + 6568970 * 2 ^ 59
def prefixEnd_6568970 : Nat := 4983230072969 + 3 ^ 40 * 6568970 * 2
def baseEnd_6568970 : Nat := 3373039014965269108364863

theorem tailTrace_6568970 : CollatzResearch.WordTrace tailWord_6568970 prefixEnd_6568970 3373039014965269108364863 := by
  unfold tailWord_6568970
  simp only [CollatzResearch.WordTrace]
  refine ⟨59897504752937763900706091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159726679341167370401882909 59897504752937763900706091)
  ·
    refine ⟨89846257129406645851059137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59897504752937763900706091 89846257129406645851059137)
    ·
      refine ⟨67384692847054984388294353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89846257129406645851059137 67384692847054984388294353)
      ·
        refine ⟨50538519635291238291220765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67384692847054984388294353 50538519635291238291220765)
        ·
          refine ⟨18951944863234214359207787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50538519635291238291220765 18951944863234214359207787)
          ·
            refine ⟨28427917294851321538811681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18951944863234214359207787 28427917294851321538811681)
            ·
              refine ⟨21320937971138491154108761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28427917294851321538811681 21320937971138491154108761)
              ·
                refine ⟨15990703478353868365581571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21320937971138491154108761 15990703478353868365581571)
                ·
                  refine ⟨23986055217530802548372357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15990703478353868365581571 23986055217530802548372357)
                  ·
                    refine ⟨4497385353287025477819817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23986055217530802548372357 4497385353287025477819817)
                    ·
                      refine ⟨3373039014965269108364863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4497385353287025477819817 3373039014965269108364863)
                      ·
                        rfl

theorem cell23_6568970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_6568970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568970 prefixEnd_6568970 := by exact prefixLift 6568970
  have htrace : WordTrace (prefixWord ++ tailWord_6568970) baseStart_6568970 baseEnd_6568970 := by
    simpa [prefixWord, tailWord_6568970, baseEnd_6568970] using wordTrace_append hprefix tailTrace_6568970
  have hstable : (prefixWord ++ tailWord_6568970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568970).length < 2 ^ (prefixWord ++ tailWord_6568970).sum := by decide
  have hdescent : baseEnd_6568970 < baseStart_6568970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568974 : List Nat := [4, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2]
def baseStart_6568974 : Nat := 118140960795 + 6568974 * 2 ^ 59
def prefixEnd_6568974 : Nat := 4983230072969 + 3 ^ 40 * 6568974 * 2
def baseEnd_6568974 : Nat := 3373041068887887092714845

theorem tailTrace_6568974 : CollatzResearch.WordTrace tailWord_6568974 prefixEnd_6568974 3373041068887887092714845 := by
  unfold tailWord_6568974
  simp only [CollatzResearch.WordTrace]
  refine ⟨29948770612967070535746247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159726776602491042857313317 29948770612967070535746247)
  ·
    refine ⟨44923155919450605803619371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29948770612967070535746247 44923155919450605803619371)
    ·
      refine ⟨67384733879175908705429057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44923155919450605803619371 67384733879175908705429057)
      ·
        refine ⟨50538550409381931529071793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67384733879175908705429057 50538550409381931529071793)
        ·
          refine ⟨37903912807036448646803845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50538550409381931529071793 37903912807036448646803845)
          ·
            refine ⟨7106983651319334121275721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37903912807036448646803845 7106983651319334121275721)
            ·
              refine ⟨5330237738489500590956791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7106983651319334121275721 5330237738489500590956791)
              ·
                refine ⟨7995356607734250886435187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5330237738489500590956791 7995356607734250886435187)
                ·
                  refine ⟨11993034911601376329652781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7995356607734250886435187 11993034911601376329652781)
                  ·
                    refine ⟨4497388091850516123619793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11993034911601376329652781 4497388091850516123619793)
                    ·
                      refine ⟨3373041068887887092714845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4497388091850516123619793 3373041068887887092714845)
                      ·
                        rfl

theorem cell23_6568974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_6568974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568974 prefixEnd_6568974 := by exact prefixLift 6568974
  have htrace : WordTrace (prefixWord ++ tailWord_6568974) baseStart_6568974 baseEnd_6568974 := by
    simpa [prefixWord, tailWord_6568974, baseEnd_6568974] using wordTrace_append hprefix tailTrace_6568974
  have hstable : (prefixWord ++ tailWord_6568974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568974).length < 2 ^ (prefixWord ++ tailWord_6568974).sum := by decide
  have hdescent : baseEnd_6568974 < baseStart_6568974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568983 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 4]
def baseStart_6568983 : Nat := 118140960795 + 6568983 * 2 ^ 59
def prefixEnd_6568983 : Nat := 4983230072969 + 3 ^ 40 * 6568983 * 2
def baseEnd_6568983 : Nat := 3373045690213777557502303

theorem tailTrace_6568983 : CollatzResearch.WordTrace tailWord_6568983 prefixEnd_6568983 3373045690213777557502303 := by
  unfold tailWord_6568983
  simp only [CollatzResearch.WordTrace]
  refine ⟨239590493160703958823047603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159726995440469305882031735 239590493160703958823047603)
  ·
    refine ⟨359385739741055938234571405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239590493160703958823047603 359385739741055938234571405)
    ·
      refine ⟨134769652402895976837964277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359385739741055938234571405 134769652402895976837964277)
      ·
        refine ⟨12634654912771497828559151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134769652402895976837964277 12634654912771497828559151)
        ·
          refine ⟨18951982369157246742838727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12634654912771497828559151 18951982369157246742838727)
          ·
            refine ⟨28427973553735870114258091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18951982369157246742838727 28427973553735870114258091)
            ·
              refine ⟨42641960330603805171387137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28427973553735870114258091 42641960330603805171387137)
              ·
                refine ⟨31981470247952853878540353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42641960330603805171387137 31981470247952853878540353)
                ·
                  refine ⟨23986102685964640408905265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31981470247952853878540353 23986102685964640408905265)
                  ·
                    refine ⟨17989577014473480306678949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23986102685964640408905265 17989577014473480306678949)
                    ·
                      refine ⟨3373045690213777557502303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17989577014473480306678949 3373045690213777557502303)
                      ·
                        rfl

theorem cell23_6568983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_6568983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568983 prefixEnd_6568983 := by exact prefixLift 6568983
  have htrace : WordTrace (prefixWord ++ tailWord_6568983) baseStart_6568983 baseEnd_6568983 := by
    simpa [prefixWord, tailWord_6568983, baseEnd_6568983] using wordTrace_append hprefix tailTrace_6568983
  have hstable : (prefixWord ++ tailWord_6568983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568983).length < 2 ^ (prefixWord ++ tailWord_6568983).sum := by decide
  have hdescent : baseEnd_6568983 < baseStart_6568983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6568993 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 7]
def baseStart_6568993 : Nat := 118140960795 + 6568993 * 2 ^ 59
def prefixEnd_6568993 : Nat := 4983230072969 + 3 ^ 40 * 6568993 * 2
def baseEnd_6568993 : Nat := 374783425002258057597473

theorem tailTrace_6568993 : CollatzResearch.WordTrace tailWord_6568993 prefixEnd_6568993 374783425002258057597473 := by
  unfold tailWord_6568993
  simp only [CollatzResearch.WordTrace]
  refine ⟨239590857890667730530911633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159727238593778487020607755 239590857890667730530911633)
  ·
    refine ⟨179693143418000797898183725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239590857890667730530911633 179693143418000797898183725)
    ·
      refine ⟨67384928781750299211818897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179693143418000797898183725 67384928781750299211818897)
      ·
        refine ⟨50538696586312724408864173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67384928781750299211818897 50538696586312724408864173)
        ·
          refine ⟨18952011219867271653324065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50538696586312724408864173 18952011219867271653324065)
          ·
            refine ⟨14214008414900453739993049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18952011219867271653324065 14214008414900453739993049)
            ·
              refine ⟨10660506311175340304994787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14214008414900453739993049 10660506311175340304994787)
              ·
                refine ⟨15990759466763010457492181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10660506311175340304994787 15990759466763010457492181)
                ·
                  refine ⟨374783425002258057597473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15990759466763010457492181 374783425002258057597473)
                  ·
                    rfl

theorem cell23_6568993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 7].length) (baseStart_6568993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6568993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6568993 prefixEnd_6568993 := by exact prefixLift 6568993
  have htrace : WordTrace (prefixWord ++ tailWord_6568993) baseStart_6568993 baseEnd_6568993 := by
    simpa [prefixWord, tailWord_6568993, baseEnd_6568993] using wordTrace_append hprefix tailTrace_6568993
  have hstable : (prefixWord ++ tailWord_6568993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6568993).length < 2 ^ (prefixWord ++ tailWord_6568993).sum := by decide
  have hdescent : baseEnd_6568993 < baseStart_6568993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6568993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569120 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 1, 5, 2]
def baseStart_6569120 : Nat := 118140960795 + 6569120 * 2 ^ 59
def prefixEnd_6569120 : Nat := 4983230072969 + 3 ^ 40 * 6569120 * 2
def baseEnd_6569120 : Nat := 3373116037063443521489173

theorem tailTrace_6569120 : CollatzResearch.WordTrace tailWord_6569120 prefixEnd_6569120 3373116037063443521489173 := by
  unfold tailWord_6569120
  simp only [CollatzResearch.WordTrace]
  refine ⟨119797744980603815610392407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159730326640805087480523209 119797744980603815610392407)
  ·
    refine ⟨179696617470905723415588611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119797744980603815610392407 179696617470905723415588611)
    ·
      refine ⟨269544926206358585123382917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179696617470905723415588611 269544926206358585123382917)
      ·
        refine ⟨50539673663692234710634297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269544926206358585123382917 50539673663692234710634297)
        ·
          refine ⟨37904755247769176032975723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50539673663692234710634297 37904755247769176032975723)
          ·
            refine ⟨56857132871653764049463585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37904755247769176032975723 56857132871653764049463585)
            ·
              refine ⟨42642849653740323037097689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56857132871653764049463585 42642849653740323037097689)
              ·
                refine ⟨31982137240305242277823267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42642849653740323037097689 31982137240305242277823267)
                ·
                  refine ⟨47973205860457863416734901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31982137240305242277823267 47973205860457863416734901)
                  ·
                    refine ⟨4497488049417924695318897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47973205860457863416734901 4497488049417924695318897)
                    ·
                      refine ⟨3373116037063443521489173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4497488049417924695318897 3373116037063443521489173)
                      ·
                        rfl

theorem cell23_6569120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_6569120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569120 prefixEnd_6569120 := by exact prefixLift 6569120
  have htrace : WordTrace (prefixWord ++ tailWord_6569120) baseStart_6569120 baseEnd_6569120 := by
    simpa [prefixWord, tailWord_6569120, baseEnd_6569120] using wordTrace_append hprefix tailTrace_6569120
  have hstable : (prefixWord ++ tailWord_6569120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569120).length < 2 ^ (prefixWord ++ tailWord_6569120).sum := by decide
  have hdescent : baseEnd_6569120 < baseStart_6569120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569127 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_6569127 : Nat := 118140960795 + 6569127 * 2 ^ 59
def prefixEnd_6569127 : Nat := 4983230072969 + 3 ^ 40 * 6569127 * 2
def baseEnd_6569127 : Nat := 3373119631428024994101641

theorem tailTrace_6569127 : CollatzResearch.WordTrace tailWord_6569127 prefixEnd_6569127 3373119631428024994101641 := by
  unfold tailWord_6569127
  simp only [CollatzResearch.WordTrace]
  refine ⟨239595745272182271416289635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159730496848121514277526423 239595745272182271416289635)
  ·
    refine ⟨359393617908273407124434453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239595745272182271416289635 359393617908273407124434453)
    ·
      refine ⟨16846575839450315958957865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 359393617908273407124434453 16846575839450315958957865)
      ·
        refine ⟨12634931879587736969218399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16846575839450315958957865 12634931879587736969218399)
        ·
          refine ⟨18952397819381605453827599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12634931879587736969218399 18952397819381605453827599)
          ·
            refine ⟨28428596729072408180741399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18952397819381605453827599 28428596729072408180741399)
            ·
              refine ⟨42642895093608612271112099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28428596729072408180741399 42642895093608612271112099)
              ·
                refine ⟨63964342640412918406668149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42642895093608612271112099 63964342640412918406668149)
                ·
                  refine ⟨5996657122538711100625139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63964342640412918406668149 5996657122538711100625139)
                  ·
                    refine ⟨8994985683808066650937709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5996657122538711100625139 8994985683808066650937709)
                    ·
                      refine ⟨3373119631428024994101641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8994985683808066650937709 3373119631428024994101641)
                      ·
                        rfl

theorem cell23_6569127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_6569127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569127 prefixEnd_6569127 := by exact prefixLift 6569127
  have htrace : WordTrace (prefixWord ++ tailWord_6569127) baseStart_6569127 baseEnd_6569127 := by
    simpa [prefixWord, tailWord_6569127, baseEnd_6569127] using wordTrace_append hprefix tailTrace_6569127
  have hstable : (prefixWord ++ tailWord_6569127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569127).length < 2 ^ (prefixWord ++ tailWord_6569127).sum := by decide
  have hdescent : baseEnd_6569127 < baseStart_6569127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569137 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 1, 5, 2]
def baseStart_6569137 : Nat := 118140960795 + 6569137 * 2 ^ 59
def prefixEnd_6569137 : Nat := 4983230072969 + 3 ^ 40 * 6569137 * 2
def baseEnd_6569137 : Nat := 3373124766234569954976595

theorem tailTrace_6569137 : CollatzResearch.WordTrace tailWord_6569137 prefixEnd_6569137 3373124766234569954976595 := by
  unfold tailWord_6569137
  simp only [CollatzResearch.WordTrace]
  refine ⟨239596110002146043124153665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159730740001430695416102443 239596110002146043124153665)
  ·
    refine ⟨179697082501609532343115249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239596110002146043124153665 179697082501609532343115249)
    ·
      refine ⟨134772811876207149257336437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179697082501609532343115249 134772811876207149257336437)
      ·
        refine ⟨12634951113394420242875291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134772811876207149257336437 12634951113394420242875291)
        ·
          refine ⟨18952426670091630364312937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12634951113394420242875291 18952426670091630364312937)
          ·
            refine ⟨14214320002568722773234703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18952426670091630364312937 14214320002568722773234703)
            ·
              refine ⟨21321480003853084159852055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14214320002568722773234703 21321480003853084159852055)
              ·
                refine ⟨31982220005779626239778083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21321480003853084159852055 31982220005779626239778083)
                ·
                  refine ⟨47973330008669439359667125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31982220005779626239778083 47973330008669439359667125)
                  ·
                    refine ⟨4497499688312759939968793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47973330008669439359667125 4497499688312759939968793)
                    ·
                      refine ⟨3373124766234569954976595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4497499688312759939968793 3373124766234569954976595)
                      ·
                        rfl

theorem cell23_6569137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_6569137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569137 prefixEnd_6569137 := by exact prefixLift 6569137
  have htrace : WordTrace (prefixWord ++ tailWord_6569137) baseStart_6569137 baseEnd_6569137 := by
    simpa [prefixWord, tailWord_6569137, baseEnd_6569137] using wordTrace_append hprefix tailTrace_6569137
  have hstable : (prefixWord ++ tailWord_6569137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569137).length < 2 ^ (prefixWord ++ tailWord_6569137).sum := by decide
  have hdescent : baseEnd_6569137 < baseStart_6569137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569143 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 1, 6]
def baseStart_6569143 : Nat := 118140960795 + 6569143 * 2 ^ 59
def prefixEnd_6569143 : Nat := 4983230072969 + 3 ^ 40 * 6569143 * 2
def baseEnd_6569143 : Nat := 1124375949039498977167189

theorem tailTrace_6569143 : CollatzResearch.WordTrace tailWord_6569143 prefixEnd_6569143 1124375949039498977167189 := by
  unfold tailWord_6569143
  simp only [CollatzResearch.WordTrace]
  refine ⟨239596328840124306148872083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159730885893416204099248055 239596328840124306148872083)
  ·
    refine ⟨359394493260186459223308125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239596328840124306148872083 359394493260186459223308125)
    ·
      refine ⟨134772934972569922208740547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359394493260186459223308125 134772934972569922208740547)
      ·
        refine ⟨202159402458854883313110821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134772934972569922208740547 202159402458854883313110821)
        ·
          refine ⟨37904887961035290621208279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202159402458854883313110821 37904887961035290621208279)
          ·
            refine ⟨56857331941552935931812419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37904887961035290621208279 56857331941552935931812419)
            ·
              refine ⟨85285997912329403897718629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56857331941552935931812419 85285997912329403897718629)
              ·
                refine ⟨15991124608561763230822243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85285997912329403897718629 15991124608561763230822243)
                ·
                  refine ⟨23986686912842644846233365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15991124608561763230822243 23986686912842644846233365)
                  ·
                    refine ⟨1124375949039498977167189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23986686912842644846233365 1124375949039498977167189)
                    ·
                      rfl

theorem cell23_6569143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_6569143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569143 prefixEnd_6569143 := by exact prefixLift 6569143
  have htrace : WordTrace (prefixWord ++ tailWord_6569143) baseStart_6569143 baseEnd_6569143 := by
    simpa [prefixWord, tailWord_6569143, baseEnd_6569143] using wordTrace_append hprefix tailTrace_6569143
  have hstable : (prefixWord ++ tailWord_6569143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569143).length < 2 ^ (prefixWord ++ tailWord_6569143).sum := by decide
  have hdescent : baseEnd_6569143 < baseStart_6569143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569170 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_6569170 : Nat := 118140960795 + 6569170 * 2 ^ 59
def prefixEnd_6569170 : Nat := 4983230072969 + 3 ^ 40 * 6569170 * 2
def baseEnd_6569170 : Nat := 3373141711096168325863943

theorem tailTrace_6569170 : CollatzResearch.WordTrace tailWord_6569170 prefixEnd_6569170 3373141711096168325863943 := by
  unfold tailWord_6569170
  simp only [CollatzResearch.WordTrace]
  refine ⟨59899328402756622440026241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159731542407350993173403309 59899328402756622440026241)
  ·
    refine ⟨44924496302067466830019681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59899328402756622440026241 44924496302067466830019681)
    ·
      refine ⟨33693372226550600122514761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44924496302067466830019681 33693372226550600122514761)
      ·
        refine ⟨25270029169912950091886071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33693372226550600122514761 25270029169912950091886071)
        ·
          refine ⟨37905043754869425137829107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25270029169912950091886071 37905043754869425137829107)
          ·
            refine ⟨56857565632304137706743661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37905043754869425137829107 56857565632304137706743661)
            ·
              refine ⟨21321587112114051640028873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56857565632304137706743661 21321587112114051640028873)
              ·
                refine ⟨15991190334085538730021655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21321587112114051640028873 15991190334085538730021655)
                ·
                  refine ⟨23986785501128308095032483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15991190334085538730021655 23986785501128308095032483)
                  ·
                    refine ⟨35980178251692462142548725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23986785501128308095032483 35980178251692462142548725)
                    ·
                      refine ⟨3373141711096168325863943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35980178251692462142548725 3373141711096168325863943)
                      ·
                        rfl

theorem cell23_6569170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_6569170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569170 prefixEnd_6569170 := by exact prefixLift 6569170
  have htrace : WordTrace (prefixWord ++ tailWord_6569170) baseStart_6569170 baseEnd_6569170 := by
    simpa [prefixWord, tailWord_6569170, baseEnd_6569170] using wordTrace_append hprefix tailTrace_6569170
  have hstable : (prefixWord ++ tailWord_6569170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569170).length < 2 ^ (prefixWord ++ tailWord_6569170).sum := by decide
  have hdescent : baseEnd_6569170 < baseStart_6569170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569217 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_6569217 : Nat := 118140960795 + 6569217 * 2 ^ 59
def prefixEnd_6569217 : Nat := 4983230072969 + 3 ^ 40 * 6569217 * 2
def baseEnd_6569217 : Nat := 3373165844686929641976227

theorem tailTrace_6569217 : CollatzResearch.WordTrace tailWord_6569217 prefixEnd_6569217 3373165844686929641976227 := by
  unfold tailWord_6569217
  simp only [CollatzResearch.WordTrace]
  refine ⟨239599027841856216787065905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159732685227904144524710603 239599027841856216787065905)
  ·
    refine ⟨179699270881392162590299429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239599027841856216787065905 179699270881392162590299429)
    ·
      refine ⟨33693613290261030485681143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179699270881392162590299429 33693613290261030485681143)
      ·
        refine ⟨50540419935391545728521715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33693613290261030485681143 50540419935391545728521715)
        ·
          refine ⟨75810629903087318592782573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50540419935391545728521715 75810629903087318592782573)
          ·
            refine ⟨28428986213657744472293465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75810629903087318592782573 28428986213657744472293465)
            ·
              refine ⟨21321739660243308354220099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28428986213657744472293465 21321739660243308354220099)
              ·
                refine ⟨31982609490364962531330149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21321739660243308354220099 31982609490364962531330149)
                ·
                  refine ⟨5996739279443430474624403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31982609490364962531330149 5996739279443430474624403)
                  ·
                    refine ⟨8995108919165145711936605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5996739279443430474624403 8995108919165145711936605)
                    ·
                      refine ⟨3373165844686929641976227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8995108919165145711936605 3373165844686929641976227)
                      ·
                        rfl

theorem cell23_6569217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_6569217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569217 prefixEnd_6569217 := by exact prefixLift 6569217
  have htrace : WordTrace (prefixWord ++ tailWord_6569217) baseStart_6569217 baseEnd_6569217 := by
    simpa [prefixWord, tailWord_6569217, baseEnd_6569217] using wordTrace_append hprefix tailTrace_6569217
  have hstable : (prefixWord ++ tailWord_6569217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569217).length < 2 ^ (prefixWord ++ tailWord_6569217).sum := by decide
  have hdescent : baseEnd_6569217 < baseStart_6569217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569218 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_6569218 : Nat := 118140960795 + 6569218 * 2 ^ 59
def prefixEnd_6569218 : Nat := 4983230072969 + 3 ^ 40 * 6569218 * 2
def baseEnd_6569218 : Nat := 3373166358167584138063723

theorem tailTrace_6569218 : CollatzResearch.WordTrace tailWord_6569218 prefixEnd_6569218 3373166358167584138063723 := by
  unfold tailWord_6569218
  simp only [CollatzResearch.WordTrace]
  refine ⟨59899766078713148489463077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159732709543235062638568205 59899766078713148489463077)
  ·
    refine ⟨11231206139758715341774327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59899766078713148489463077 11231206139758715341774327)
    ·
      refine ⟨16846809209638073012661491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11231206139758715341774327 16846809209638073012661491)
      ·
        refine ⟨25270213814457109518992237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16846809209638073012661491 25270213814457109518992237)
        ·
          refine ⟨9476330180421416069622089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25270213814457109518992237 9476330180421416069622089)
          ·
            refine ⟨7107247635316062052216567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9476330180421416069622089 7107247635316062052216567)
            ·
              refine ⟨10660871452974093078324851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7107247635316062052216567 10660871452974093078324851)
              ·
                refine ⟨15991307179461139617487277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10660871452974093078324851 15991307179461139617487277)
                ·
                  refine ⟨5996740192297927356557729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15991307179461139617487277 5996740192297927356557729)
                  ·
                    refine ⟨4497555144223445517418297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5996740192297927356557729 4497555144223445517418297)
                    ·
                      refine ⟨3373166358167584138063723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4497555144223445517418297 3373166358167584138063723)
                      ·
                        rfl

theorem cell23_6569218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_6569218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569218 prefixEnd_6569218 := by exact prefixLift 6569218
  have htrace : WordTrace (prefixWord ++ tailWord_6569218) baseStart_6569218 baseEnd_6569218 := by
    simpa [prefixWord, tailWord_6569218, baseEnd_6569218] using wordTrace_append hprefix tailTrace_6569218
  have hstable : (prefixWord ++ tailWord_6569218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569218).length < 2 ^ (prefixWord ++ tailWord_6569218).sum := by decide
  have hdescent : baseEnd_6569218 < baseStart_6569218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569233 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 1, 8]
def baseStart_6569233 : Nat := 118140960795 + 6569233 * 2 ^ 59
def prefixEnd_6569233 : Nat := 4983230072969 + 3 ^ 40 * 6569233 * 2
def baseEnd_6569233 : Nat := 1124391353459133859792051

theorem tailTrace_6569233 : CollatzResearch.WordTrace tailWord_6569233 prefixEnd_6569233 1124391353459133859792051 := by
  unfold tailWord_6569233
  simp only [CollatzResearch.WordTrace]
  refine ⟨239599611409798251519648353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159733074273198834346432235 239599611409798251519648353)
  ·
    refine ⟨179699708557348688639736265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239599611409798251519648353 179699708557348688639736265)
    ·
      refine ⟨134774781418011516479802199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179699708557348688639736265 134774781418011516479802199)
      ·
        refine ⟨202162172127017274719703299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134774781418011516479802199 202162172127017274719703299)
        ·
          refine ⟨303243258190525912079554949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202162172127017274719703299 303243258190525912079554949)
          ·
            refine ⟨56858110910723608514916553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 303243258190525912079554949 56858110910723608514916553)
            ·
              refine ⟨42643583183042706386187415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56858110910723608514916553 42643583183042706386187415)
              ·
                refine ⟨63965374774564059579281123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42643583183042706386187415 63965374774564059579281123)
                ·
                  refine ⟨95948062161846089368921685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63965374774564059579281123 95948062161846089368921685)
                  ·
                    refine ⟨1124391353459133859792051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95948062161846089368921685 1124391353459133859792051)
                    ·
                      rfl

theorem cell23_6569233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_6569233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569233 prefixEnd_6569233 := by exact prefixLift 6569233
  have htrace : WordTrace (prefixWord ++ tailWord_6569233) baseStart_6569233 baseEnd_6569233 := by
    simpa [prefixWord, tailWord_6569233, baseEnd_6569233] using wordTrace_append hprefix tailTrace_6569233
  have hstable : (prefixWord ++ tailWord_6569233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569233).length < 2 ^ (prefixWord ++ tailWord_6569233).sum := by decide
  have hdescent : baseEnd_6569233 < baseStart_6569233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569244 : List Nat := [2, 2, 3, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_6569244 : Nat := 118140960795 + 6569244 * 2 ^ 59
def prefixEnd_6569244 : Nat := 4983230072969 + 3 ^ 40 * 6569244 * 2
def baseEnd_6569244 : Nat := 3373179708664601036338603

theorem tailTrace_6569244 : CollatzResearch.WordTrace tailWord_6569244 prefixEnd_6569244 3373179708664601036338603 := by
  unfold tailWord_6569244
  simp only [CollatzResearch.WordTrace]
  refine ⟨119800006306379200199149393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159733341741838933598865857 119800006306379200199149393)
  ·
    refine ⟨89850004729784400149362045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119800006306379200199149393 89850004729784400149362045)
    ·
      refine ⟨33693751773669150056010767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89850004729784400149362045 33693751773669150056010767)
      ·
        refine ⟨50540627660503725084016151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33693751773669150056010767 50540627660503725084016151)
        ·
          refine ⟨75810941490755587626024227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50540627660503725084016151 75810941490755587626024227)
          ·
            refine ⟨113716412236133381439036341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75810941490755587626024227 113716412236133381439036341)
            ·
              refine ⟨10660913647137504509909657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113716412236133381439036341 10660913647137504509909657)
              ·
                refine ⟨7995685235353128382432243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10660913647137504509909657 7995685235353128382432243)
                ·
                  refine ⟨11993527853029692573648365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7995685235353128382432243 11993527853029692573648365)
                  ·
                    refine ⟨4497572944886134715118137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11993527853029692573648365 4497572944886134715118137)
                    ·
                      refine ⟨3373179708664601036338603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4497572944886134715118137 3373179708664601036338603)
                      ·
                        rfl

theorem cell23_6569244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_6569244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569244 prefixEnd_6569244 := by exact prefixLift 6569244
  have htrace : WordTrace (prefixWord ++ tailWord_6569244) baseStart_6569244 baseEnd_6569244 := by
    simpa [prefixWord, tailWord_6569244, baseEnd_6569244] using wordTrace_append hprefix tailTrace_6569244
  have hstable : (prefixWord ++ tailWord_6569244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569244).length < 2 ^ (prefixWord ++ tailWord_6569244).sum := by decide
  have hdescent : baseEnd_6569244 < baseStart_6569244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569283 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 8]
def baseStart_6569283 : Nat := 118140960795 + 6569283 * 2 ^ 59
def prefixEnd_6569283 : Nat := 4983230072969 + 3 ^ 40 * 6569283 * 2
def baseEnd_6569283 : Nat := 3373199734410126383750923

theorem tailTrace_6569283 : CollatzResearch.WordTrace tailWord_6569283 prefixEnd_6569283 3373199734410126383750923 := by
  unfold tailWord_6569283
  simp only [CollatzResearch.WordTrace]
  refine ⟨239601435059617110058968503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159734290039744740039312335 239601435059617110058968503)
  ·
    refine ⟨359402152589425665088452755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239601435059617110058968503 359402152589425665088452755)
    ·
      refine ⟨539103228884138497632679133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359402152589425665088452755 539103228884138497632679133)
      ·
        refine ⟨202163710831551936612254675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 539103228884138497632679133 202163710831551936612254675)
        ·
          refine ⟨303245566247327904918382013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202163710831551936612254675 303245566247327904918382013)
          ·
            refine ⟨113717087342747964344393255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303245566247327904918382013 113717087342747964344393255)
            ·
              refine ⟨170575631014121946516589883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113717087342747964344393255 170575631014121946516589883)
              ·
                refine ⟨255863446521182919774884825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170575631014121946516589883 255863446521182919774884825)
                ·
                  refine ⟨191897584890887189831163619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 255863446521182919774884825 191897584890887189831163619)
                  ·
                    refine ⟨287846377336330784746745429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 191897584890887189831163619 287846377336330784746745429)
                    ·
                      refine ⟨3373199734410126383750923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 287846377336330784746745429 3373199734410126383750923)
                      ·
                        rfl

theorem cell23_6569283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_6569283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569283 prefixEnd_6569283 := by exact prefixLift 6569283
  have htrace : WordTrace (prefixWord ++ tailWord_6569283) baseStart_6569283 baseEnd_6569283 := by
    simpa [prefixWord, tailWord_6569283, baseEnd_6569283] using wordTrace_append hprefix tailTrace_6569283
  have hstable : (prefixWord ++ tailWord_6569283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569283).length < 2 ^ (prefixWord ++ tailWord_6569283).sum := by decide
  have hdescent : baseEnd_6569283 < baseStart_6569283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569314 : List Nat := [3, 3, 2, 1, 1, 1, 4, 3, 5]
def baseStart_6569314 : Nat := 118140960795 + 6569314 * 2 ^ 59
def prefixEnd_6569314 : Nat := 4983230072969 + 3 ^ 40 * 6569314 * 2
def baseEnd_6569314 : Nat := 374801739145601751384809

theorem tailTrace_6569314 : CollatzResearch.WordTrace tailWord_6569314 prefixEnd_6569314 374801739145601751384809 := by
  unfold tailWord_6569314
  simp only [CollatzResearch.WordTrace]
  refine ⟨59900641430626200588336749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159735043815003201568897997 59900641430626200588336749)
  ·
    refine ⟨22462740536484825220626281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59900641430626200588336749 22462740536484825220626281)
    ·
      refine ⟨16847055402363618915469711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22462740536484825220626281 16847055402363618915469711)
      ·
        refine ⟨25270583103545428373204567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16847055402363618915469711 25270583103545428373204567)
        ·
          refine ⟨37905874655318142559806851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25270583103545428373204567 37905874655318142559806851)
          ·
            refine ⟨56858811982977213839710277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37905874655318142559806851 56858811982977213839710277)
            ·
              refine ⟨10661027246808227594945677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56858811982977213839710277 10661027246808227594945677)
              ·
                refine ⟨3997885217553085348104629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10661027246808227594945677 3997885217553085348104629)
                ·
                  refine ⟨374801739145601751384809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3997885217553085348104629 374801739145601751384809)
                  ·
                    rfl

theorem cell23_6569314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_6569314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569314 prefixEnd_6569314 := by exact prefixLift 6569314
  have htrace : WordTrace (prefixWord ++ tailWord_6569314) baseStart_6569314 baseEnd_6569314 := by
    simpa [prefixWord, tailWord_6569314, baseEnd_6569314] using wordTrace_append hprefix tailTrace_6569314
  have hstable : (prefixWord ++ tailWord_6569314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569314).length < 2 ^ (prefixWord ++ tailWord_6569314).sum := by decide
  have hdescent : baseEnd_6569314 < baseStart_6569314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569342 : List Nat := [4, 2, 3, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6569342 : Nat := 118140960795 + 6569342 * 2 ^ 59
def prefixEnd_6569342 : Nat := 4983230072969 + 3 ^ 40 * 6569342 * 2
def baseEnd_6569342 : Nat := 3373230029768741652913153

theorem tailTrace_6569342 : CollatzResearch.WordTrace tailWord_6569342 prefixEnd_6569342 3373230029768741652913153 := by
  unfold tailWord_6569342
  simp only [CollatzResearch.WordTrace]
  refine ⟨29950448370800420391920785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159735724644268908756910853 29950448370800420391920785)
  ·
    refine ⟨22462836278100315293940589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29950448370800420391920785 22462836278100315293940589)
    ·
      refine ⟨8423563604287618235227721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22462836278100315293940589 8423563604287618235227721)
      ·
        refine ⟨6317672703215713676420791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8423563604287618235227721 6317672703215713676420791)
        ·
          refine ⟨9476509054823570514631187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6317672703215713676420791 9476509054823570514631187)
          ·
            refine ⟨14214763582235355771946781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9476509054823570514631187 14214763582235355771946781)
            ·
              refine ⟨5330536343338258414480043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14214763582235355771946781 5330536343338258414480043)
              ·
                refine ⟨7995804515007387621720065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5330536343338258414480043 7995804515007387621720065)
                ·
                  refine ⟨5996853386255540716290049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7995804515007387621720065 5996853386255540716290049)
                  ·
                    refine ⟨4497640039691655537217537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5996853386255540716290049 4497640039691655537217537)
                    ·
                      refine ⟨3373230029768741652913153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4497640039691655537217537 3373230029768741652913153)
                      ·
                        rfl

theorem cell23_6569342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6569342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569342 prefixEnd_6569342 := by exact prefixLift 6569342
  have htrace : WordTrace (prefixWord ++ tailWord_6569342) baseStart_6569342 baseEnd_6569342 := by
    simpa [prefixWord, tailWord_6569342, baseEnd_6569342] using wordTrace_append hprefix tailTrace_6569342
  have hstable : (prefixWord ++ tailWord_6569342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569342).length < 2 ^ (prefixWord ++ tailWord_6569342).sum := by decide
  have hdescent : baseEnd_6569342 < baseStart_6569342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569367 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 3]
def baseStart_6569367 : Nat := 118140960795 + 6569367 * 2 ^ 59
def prefixEnd_6569367 : Nat := 4983230072969 + 3 ^ 40 * 6569367 * 2
def baseEnd_6569367 : Nat := 3373242866785104055100537

theorem tailTrace_6569367 : CollatzResearch.WordTrace tailWord_6569367 prefixEnd_6569367 3373242866785104055100537 := by
  unfold tailWord_6569367
  simp only [CollatzResearch.WordTrace]
  refine ⟨239604498791312792405026355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159736332527541861603350903 239604498791312792405026355)
  ·
    refine ⟨359406748186969188607539533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239604498791312792405026355 359406748186969188607539533)
    ·
      refine ⟨134777530570113445727827325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359406748186969188607539533 134777530570113445727827325)
      ·
        refine ⟨50541573963792542147935247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134777530570113445727827325 50541573963792542147935247)
        ·
          refine ⟨75812360945688813221902871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50541573963792542147935247 75812360945688813221902871)
          ·
            refine ⟨113718541418533219832854307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75812360945688813221902871 113718541418533219832854307)
            ·
              refine ⟨170577812127799829749281461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113718541418533219832854307 170577812127799829749281461)
              ·
                refine ⟨15991669886981234038995137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170577812127799829749281461 15991669886981234038995137)
                ·
                  refine ⟨11993752415235925529246353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15991669886981234038995137 11993752415235925529246353)
                  ·
                    refine ⟨8995314311426944146934765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11993752415235925529246353 8995314311426944146934765)
                    ·
                      refine ⟨3373242866785104055100537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8995314311426944146934765 3373242866785104055100537)
                      ·
                        rfl

theorem cell23_6569367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_6569367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569367 prefixEnd_6569367 := by exact prefixLift 6569367
  have htrace : WordTrace (prefixWord ++ tailWord_6569367) baseStart_6569367 baseEnd_6569367 := by
    simpa [prefixWord, tailWord_6569367, baseEnd_6569367] using wordTrace_append hprefix tailTrace_6569367
  have hstable : (prefixWord ++ tailWord_6569367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569367).length < 2 ^ (prefixWord ++ tailWord_6569367).sum := by decide
  have hdescent : baseEnd_6569367 < baseStart_6569367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569370 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 10]
def baseStart_6569370 : Nat := 118140960795 + 6569370 * 2 ^ 59
def prefixEnd_6569370 : Nat := 4983230072969 + 3 ^ 40 * 6569370 * 2
def baseEnd_6569370 : Nat := 374804934136340838151447

theorem tailTrace_6569370 : CollatzResearch.WordTrace tailWord_6569370 prefixEnd_6569370 374804934136340838151447 := by
  unfold tailWord_6569370
  simp only [CollatzResearch.WordTrace]
  refine ⟨59901152052575480979346391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159736405473534615944923709 59901152052575480979346391)
  ·
    refine ⟨89851728078863221469019587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59901152052575480979346391 89851728078863221469019587)
    ·
      refine ⟨134777592118294832203529381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89851728078863221469019587 134777592118294832203529381)
      ·
        refine ⟨25270798522180281038161759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134777592118294832203529381 25270798522180281038161759)
        ·
          refine ⟨37906197783270421557242639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25270798522180281038161759 37906197783270421557242639)
          ·
            refine ⟨56859296674905632335863959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37906197783270421557242639 56859296674905632335863959)
            ·
              refine ⟨85288945012358448503795939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56859296674905632335863959 85288945012358448503795939)
              ·
                refine ⟨127933417518537672755693909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85288945012358448503795939 127933417518537672755693909)
                ·
                  refine ⟨374804934136340838151447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 127933417518537672755693909 374804934136340838151447)
                  ·
                    rfl

theorem cell23_6569370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_6569370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569370 prefixEnd_6569370 := by exact prefixLift 6569370
  have htrace : WordTrace (prefixWord ++ tailWord_6569370) baseStart_6569370 baseEnd_6569370 := by
    simpa [prefixWord, tailWord_6569370, baseEnd_6569370] using wordTrace_append hprefix tailTrace_6569370
  have hstable : (prefixWord ++ tailWord_6569370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569370).length < 2 ^ (prefixWord ++ tailWord_6569370).sum := by decide
  have hdescent : baseEnd_6569370 < baseStart_6569370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569404 : List Nat := [2, 2, 2, 4, 2, 1, 1, 3, 6]
def baseStart_6569404 : Nat := 118140960795 + 6569404 * 2 ^ 59
def prefixEnd_6569404 : Nat := 4983230072969 + 3 ^ 40 * 6569404 * 2
def baseEnd_6569404 : Nat := 374806873952146712259763

theorem tailTrace_6569404 : CollatzResearch.WordTrace tailWord_6569404 prefixEnd_6569404 374806873952146712259763 := by
  unfold tailWord_6569404
  simp only [CollatzResearch.WordTrace]
  refine ⟨119802924146089373862061633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159737232194785831816082177 119802924146089373862061633)
  ·
    refine ⟨89852193109567030396546225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119802924146089373862061633 89852193109567030396546225)
    ·
      refine ⟨67389144832175272797409669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89852193109567030396546225 67389144832175272797409669)
      ·
        refine ⟨12635464656032863649514313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67389144832175272797409669 12635464656032863649514313)
        ·
          refine ⟨9476598492024647737135735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12635464656032863649514313 9476598492024647737135735)
          ·
            refine ⟨14214897738036971605703603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9476598492024647737135735 14214897738036971605703603)
            ·
              refine ⟨21322346607055457408555405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14214897738036971605703603 21322346607055457408555405)
              ·
                refine ⟨7995879977645796528208277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21322346607055457408555405 7995879977645796528208277)
                ·
                  refine ⟨374806873952146712259763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7995879977645796528208277 374806873952146712259763)
                  ·
                    rfl

theorem cell23_6569404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 6].length) (baseStart_6569404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569404 prefixEnd_6569404 := by exact prefixLift 6569404
  have htrace : WordTrace (prefixWord ++ tailWord_6569404) baseStart_6569404 baseEnd_6569404 := by
    simpa [prefixWord, tailWord_6569404, baseEnd_6569404] using wordTrace_append hprefix tailTrace_6569404
  have hstable : (prefixWord ++ tailWord_6569404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569404).length < 2 ^ (prefixWord ++ tailWord_6569404).sum := by decide
  have hdescent : baseEnd_6569404 < baseStart_6569404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569407 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 3, 5, 2]
def baseStart_6569407 : Nat := 118140960795 + 6569407 * 2 ^ 59
def prefixEnd_6569407 : Nat := 4983230072969 + 3 ^ 40 * 6569407 * 2
def baseEnd_6569407 : Nat := 3373263406011283898600353

theorem tailTrace_6569407 : CollatzResearch.WordTrace tailWord_6569407 prefixEnd_6569407 3373263406011283898600353 := by
  unfold tailWord_6569407
  simp only [CollatzResearch.WordTrace]
  refine ⟨239605957711167879236482475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159737305140778586157654983 239605957711167879236482475)
  ·
    refine ⟨359408936566751818854723713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239605957711167879236482475 359408936566751818854723713)
    ·
      refine ⟨269556702425063864141042785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359408936566751818854723713 269556702425063864141042785)
      ·
        refine ⟨202167526818797898105782089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269556702425063864141042785 202167526818797898105782089)
        ·
          refine ⟨151625645114098423579336567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202167526818797898105782089 151625645114098423579336567)
          ·
            refine ⟨227438467671147635369004851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151625645114098423579336567 227438467671147635369004851)
            ·
              refine ⟨341157701506721453053507277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227438467671147635369004851 341157701506721453053507277)
              ·
                refine ⟨127934138065020544895065229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 341157701506721453053507277 127934138065020544895065229)
                ·
                  refine ⟨47975301774382704335649461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127934138065020544895065229 47975301774382704335649461)
                  ·
                    refine ⟨4497684541348378531467137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47975301774382704335649461 4497684541348378531467137)
                    ·
                      refine ⟨3373263406011283898600353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4497684541348378531467137 3373263406011283898600353)
                      ·
                        rfl

theorem cell23_6569407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 5, 2].length) (baseStart_6569407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569407 prefixEnd_6569407 := by exact prefixLift 6569407
  have htrace : WordTrace (prefixWord ++ tailWord_6569407) baseStart_6569407 baseEnd_6569407 := by
    simpa [prefixWord, tailWord_6569407, baseEnd_6569407] using wordTrace_append hprefix tailTrace_6569407
  have hstable : (prefixWord ++ tailWord_6569407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569407).length < 2 ^ (prefixWord ++ tailWord_6569407).sum := by decide
  have hdescent : baseEnd_6569407 < baseStart_6569407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569464 : List Nat := [2, 1, 2, 1, 1, 5, 2, 3, 2, 4]
def baseStart_6569464 : Nat := 118140960795 + 6569464 * 2 ^ 59
def prefixEnd_6569464 : Nat := 4983230072969 + 3 ^ 40 * 6569464 * 2
def baseEnd_6569464 : Nat := 1124430891469530058529197

theorem tailTrace_6569464 : CollatzResearch.WordTrace tailWord_6569464 prefixEnd_6569464 1124430891469530058529197 := by
  unfold tailWord_6569464
  simp only [CollatzResearch.WordTrace]
  refine ⟨119804018335980688985653723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159738691114640918647538297 119804018335980688985653723)
  ·
    refine ⟨179706027503971033478480585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119804018335980688985653723 179706027503971033478480585)
    ·
      refine ⟨134779520627978275108860439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179706027503971033478480585 134779520627978275108860439)
      ·
        refine ⟨202169280941967412663290659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134779520627978275108860439 202169280941967412663290659)
        ·
          refine ⟨303253921412951118994935989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202169280941967412663290659 303253921412951118994935989)
          ·
            refine ⟨28430055132464167405775249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 303253921412951118994935989 28430055132464167405775249)
            ·
              refine ⟨21322541349348125554331437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28430055132464167405775249 21322541349348125554331437)
              ·
                refine ⟨7995953006005547082874289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21322541349348125554331437 7995953006005547082874289)
                ·
                  refine ⟨5996964754504160312155717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7995953006005547082874289 5996964754504160312155717)
                  ·
                    refine ⟨1124430891469530058529197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5996964754504160312155717 1124430891469530058529197)
                    ·
                      rfl

theorem cell23_6569464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_6569464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569464 prefixEnd_6569464 := by exact prefixLift 6569464
  have htrace : WordTrace (prefixWord ++ tailWord_6569464) baseStart_6569464 baseEnd_6569464 := by
    simpa [prefixWord, tailWord_6569464, baseEnd_6569464] using wordTrace_append hprefix tailTrace_6569464
  have hstable : (prefixWord ++ tailWord_6569464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569464).length < 2 ^ (prefixWord ++ tailWord_6569464).sum := by decide
  have hdescent : baseEnd_6569464 < baseStart_6569464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569491 : List Nat := [1, 1, 1, 2, 1, 6, 4, 1, 1, 2, 3]
def baseStart_6569491 : Nat := 118140960795 + 6569491 * 2 ^ 59
def prefixEnd_6569491 : Nat := 4983230072969 + 3 ^ 40 * 6569491 * 2
def baseEnd_6569491 : Nat := 3373306538386261569949967

theorem tailTrace_6569491 : CollatzResearch.WordTrace tailWord_6569491 prefixEnd_6569491 3373306538386261569949967 := by
  unfold tailWord_6569491
  simp only [CollatzResearch.WordTrace]
  refine ⟨239609021442863561582540327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159739347628575707721693551 239609021442863561582540327)
  ·
    refine ⟨359413532164295342373810491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239609021442863561582540327 359413532164295342373810491)
    ·
      refine ⟨539120298246443013560715737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359413532164295342373810491 539120298246443013560715737)
      ·
        refine ⟨404340223684832260170536803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539120298246443013560715737 404340223684832260170536803)
        ·
          refine ⟨606510335527248390255805205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404340223684832260170536803 606510335527248390255805205)
          ·
            refine ⟨28430171977839768293240869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 606510335527248390255805205 28430171977839768293240869)
            ·
              refine ⟨5330657245844956554982663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28430171977839768293240869 5330657245844956554982663)
              ·
                refine ⟨7995985868767434832473995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5330657245844956554982663 7995985868767434832473995)
                ·
                  refine ⟨11993978803151152248710993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7995985868767434832473995 11993978803151152248710993)
                  ·
                    refine ⟨8995484102363364186533245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11993978803151152248710993 8995484102363364186533245)
                    ·
                      refine ⟨3373306538386261569949967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8995484102363364186533245 3373306538386261569949967)
                      ·
                        rfl

theorem cell23_6569491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 1, 2, 3].length) (baseStart_6569491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569491 prefixEnd_6569491 := by exact prefixLift 6569491
  have htrace : WordTrace (prefixWord ++ tailWord_6569491) baseStart_6569491 baseEnd_6569491 := by
    simpa [prefixWord, tailWord_6569491, baseEnd_6569491] using wordTrace_append hprefix tailTrace_6569491
  have hstable : (prefixWord ++ tailWord_6569491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569491).length < 2 ^ (prefixWord ++ tailWord_6569491).sum := by decide
  have hdescent : baseEnd_6569491 < baseStart_6569491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569547 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 3]
def baseStart_6569547 : Nat := 118140960795 + 6569547 * 2 ^ 59
def prefixEnd_6569547 : Nat := 4983230072969 + 3 ^ 40 * 6569547 * 2
def baseEnd_6569547 : Nat := 3373335293302913350849709

theorem tailTrace_6569547 : CollatzResearch.WordTrace tailWord_6569547 prefixEnd_6569547 3373335293302913350849709 := by
  unfold tailWord_6569547
  simp only [CollatzResearch.WordTrace]
  refine ⟨239611063930660683146578895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159740709287107122097719263 239611063930660683146578895)
  ·
    refine ⟨359416595895991024719868343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239611063930660683146578895 359416595895991024719868343)
    ·
      refine ⟨539124893843986537079802515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359416595895991024719868343 539124893843986537079802515)
      ·
        refine ⟨808687340765979805619703773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539124893843986537079802515 808687340765979805619703773)
        ·
          refine ⟨303257752787242427107388915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 808687340765979805619703773 303257752787242427107388915)
          ·
            refine ⟨454886629180863640661083373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303257752787242427107388915 454886629180863640661083373)
            ·
              refine ⟨170582485942823865247906265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 454886629180863640661083373 170582485942823865247906265)
              ·
                refine ⟨127936864457117898935929699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170582485942823865247906265 127936864457117898935929699)
                ·
                  refine ⟨191905296685676848403894549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127936864457117898935929699 191905296685676848403894549)
                  ·
                    refine ⟨8995560782141102268932557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 191905296685676848403894549 8995560782141102268932557)
                    ·
                      refine ⟨3373335293302913350849709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8995560782141102268932557 3373335293302913350849709)
                      ·
                        rfl

theorem cell23_6569547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 3].length) (baseStart_6569547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569547 prefixEnd_6569547 := by exact prefixLift 6569547
  have htrace : WordTrace (prefixWord ++ tailWord_6569547) baseStart_6569547 baseEnd_6569547 := by
    simpa [prefixWord, tailWord_6569547, baseEnd_6569547] using wordTrace_append hprefix tailTrace_6569547
  have hstable : (prefixWord ++ tailWord_6569547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569547).length < 2 ^ (prefixWord ++ tailWord_6569547).sum := by decide
  have hdescent : baseEnd_6569547 < baseStart_6569547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569582 : List Nat := [4, 1, 2, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_6569582 : Nat := 118140960795 + 6569582 * 2 ^ 59
def prefixEnd_6569582 : Nat := 4983230072969 + 3 ^ 40 * 6569582 * 2
def baseEnd_6569582 : Nat := 3373353265125820713912049

theorem tailTrace_6569582 : CollatzResearch.WordTrace tailWord_6569582 prefixEnd_6569582 3373353265125820713912049 := by
  unfold tailWord_6569582
  simp only [CollatzResearch.WordTrace]
  refine ⟨29951542560691735515512875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159741560323689256082735333 29951542560691735515512875)
  ·
    refine ⟨44927313841037603273269313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29951542560691735515512875 44927313841037603273269313)
    ·
      refine ⟨33695485380778202454951985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44927313841037603273269313 33695485380778202454951985)
      ·
        refine ⟨25271614035583651841213989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33695485380778202454951985 25271614035583651841213989)
        ·
          refine ⟨4738427631671934720227623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25271614035583651841213989 4738427631671934720227623)
          ·
            refine ⟨7107641447507902080341435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4738427631671934720227623 7107641447507902080341435)
            ·
              refine ⟨10661462171261853120512153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7107641447507902080341435 10661462171261853120512153)
              ·
                refine ⟨7996096628446389840384115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10661462171261853120512153 7996096628446389840384115)
                ·
                  refine ⟨11994144942669584760576173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7996096628446389840384115 11994144942669584760576173)
                  ·
                    refine ⟨4497804353501094285216065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11994144942669584760576173 4497804353501094285216065)
                    ·
                      refine ⟨3373353265125820713912049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4497804353501094285216065 3373353265125820713912049)
                      ·
                        rfl

theorem cell23_6569582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_6569582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569582 prefixEnd_6569582 := by exact prefixLift 6569582
  have htrace : WordTrace (prefixWord ++ tailWord_6569582) baseStart_6569582 baseEnd_6569582 := by
    simpa [prefixWord, tailWord_6569582, baseEnd_6569582] using wordTrace_append hprefix tailTrace_6569582
  have hstable : (prefixWord ++ tailWord_6569582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569582).length < 2 ^ (prefixWord ++ tailWord_6569582).sum := by decide
  have hdescent : baseEnd_6569582 < baseStart_6569582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569618 : List Nat := [3, 2, 3, 1, 3, 1, 1, 4, 5]
def baseStart_6569618 : Nat := 118140960795 + 6569618 * 2 ^ 59
def prefixEnd_6569618 : Nat := 4983230072969 + 3 ^ 40 * 6569618 * 2
def baseEnd_6569618 : Nat := 374819083381042508117987

theorem tailTrace_6569618 : CollatzResearch.WordTrace tailWord_6569618 prefixEnd_6569618 374819083381042508117987 := by
  unfold tailWord_6569618
  simp only [CollatzResearch.WordTrace]
  refine ⟨59903413378350865568103377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159742435675602308181609005 59903413378350865568103377)
  ·
    refine ⟨44927560033763149176077533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59903413378350865568103377 44927560033763149176077533)
    ·
      refine ⟨16847835012661180941029075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44927560033763149176077533 16847835012661180941029075)
      ·
        refine ⟨25271752518991771411543613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16847835012661180941029075 25271752518991771411543613)
        ·
          refine ⟨9476907194621914279328855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25271752518991771411543613 9476907194621914279328855)
          ·
            refine ⟨14215360791932871418993283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9476907194621914279328855 14215360791932871418993283)
            ·
              refine ⟨21323041187899307128489925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14215360791932871418993283 21323041187899307128489925)
              ·
                refine ⟨3998070222731120086591861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21323041187899307128489925 3998070222731120086591861)
                ·
                  refine ⟨374819083381042508117987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3998070222731120086591861 374819083381042508117987)
                  ·
                    rfl

theorem cell23_6569618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_6569618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569618 prefixEnd_6569618 := by exact prefixLift 6569618
  have htrace : WordTrace (prefixWord ++ tailWord_6569618) baseStart_6569618 baseEnd_6569618 := by
    simpa [prefixWord, tailWord_6569618, baseEnd_6569618] using wordTrace_append hprefix tailTrace_6569618
  have hstable : (prefixWord ++ tailWord_6569618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569618).length < 2 ^ (prefixWord ++ tailWord_6569618).sum := by decide
  have hdescent : baseEnd_6569618 < baseStart_6569618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569624 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_6569624 : Nat := 118140960795 + 6569624 * 2 ^ 59
def prefixEnd_6569624 : Nat := 4983230072969 + 3 ^ 40 * 6569624 * 2
def baseEnd_6569624 : Nat := 3373374831313309549586855

theorem tailTrace_6569624 : CollatzResearch.WordTrace tailWord_6569624 prefixEnd_6569624 3373374831313309549586855 := by
  unfold tailWord_6569624
  simp only [CollatzResearch.WordTrace]
  refine ⟨119806936175690862648565963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159742581567587816864754617 119806936175690862648565963)
  ·
    refine ⟨179710404263536293972848945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119806936175690862648565963 179710404263536293972848945)
    ·
      refine ⟨134782803197652220479636709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179710404263536293972848945 134782803197652220479636709)
      ·
        refine ⟨25271775599559791339931883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134782803197652220479636709 25271775599559791339931883)
        ·
          refine ⟨37907663399339687009897825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25271775599559791339931883 37907663399339687009897825)
          ·
            refine ⟨28430747549504765257423369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37907663399339687009897825 28430747549504765257423369)
            ·
              refine ⟨21323060662128573943067527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28430747549504765257423369 21323060662128573943067527)
              ·
                refine ⟨31984590993192860914601291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21323060662128573943067527 31984590993192860914601291)
                ·
                  refine ⟨47976886489789291371901937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31984590993192860914601291 47976886489789291371901937)
                  ·
                    refine ⟨35982664867341968528926453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47976886489789291371901937 35982664867341968528926453)
                    ·
                      refine ⟨3373374831313309549586855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35982664867341968528926453 3373374831313309549586855)
                      ·
                        rfl

theorem cell23_6569624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_6569624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569624 prefixEnd_6569624 := by exact prefixLift 6569624
  have htrace : WordTrace (prefixWord ++ tailWord_6569624) baseStart_6569624 baseEnd_6569624 := by
    simpa [prefixWord, tailWord_6569624, baseEnd_6569624] using wordTrace_append hprefix tailTrace_6569624
  have hstable : (prefixWord ++ tailWord_6569624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569624).length < 2 ^ (prefixWord ++ tailWord_6569624).sum := by decide
  have hdescent : baseEnd_6569624 < baseStart_6569624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569667 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 7]
def baseStart_6569667 : Nat := 118140960795 + 6569667 * 2 ^ 59
def prefixEnd_6569667 : Nat := 4983230072969 + 3 ^ 40 * 6569667 * 2
def baseEnd_6569667 : Nat := 3373396910981452881349157

theorem tailTrace_6569667 : CollatzResearch.WordTrace tailWord_6569667 prefixEnd_6569667 3373396910981452881349157 := by
  unfold tailWord_6569667
  simp only [CollatzResearch.WordTrace]
  refine ⟨239615440690225943640947255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159743627126817295760631503 239615440690225943640947255)
  ·
    refine ⟨359423161035338915461420883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239615440690225943640947255 359423161035338915461420883)
    ·
      refine ⟨539134741553008373192131325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359423161035338915461420883 539134741553008373192131325)
      ·
        refine ⟨202175528082378139947049247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 539134741553008373192131325 202175528082378139947049247)
        ·
          refine ⟨303263292123567209920573871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202175528082378139947049247 303263292123567209920573871)
          ·
            refine ⟨454894938185350814880860807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303263292123567209920573871 454894938185350814880860807)
            ·
              refine ⟨682342407278026222321291211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454894938185350814880860807 682342407278026222321291211)
              ·
                refine ⟨1023513610917039333481936817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682342407278026222321291211 1023513610917039333481936817)
                ·
                  refine ⟨767635208187779500111452613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1023513610917039333481936817 767635208187779500111452613)
                  ·
                    refine ⟨143931601535208656270897365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 767635208187779500111452613 143931601535208656270897365)
                    ·
                      refine ⟨3373396910981452881349157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143931601535208656270897365 3373396910981452881349157)
                      ·
                        rfl

theorem cell23_6569667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_6569667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569667 prefixEnd_6569667 := by exact prefixLift 6569667
  have htrace : WordTrace (prefixWord ++ tailWord_6569667) baseStart_6569667 baseEnd_6569667 := by
    simpa [prefixWord, tailWord_6569667, baseEnd_6569667] using wordTrace_append hprefix tailTrace_6569667
  have hstable : (prefixWord ++ tailWord_6569667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569667).length < 2 ^ (prefixWord ++ tailWord_6569667).sum := by decide
  have hdescent : baseEnd_6569667 < baseStart_6569667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569678 : List Nat := [4, 1, 1, 1, 3, 1, 1, 6, 1, 4]
def baseStart_6569678 : Nat := 118140960795 + 6569678 * 2 ^ 59
def prefixEnd_6569678 : Nat := 4983230072969 + 3 ^ 40 * 6569678 * 2
def baseEnd_6569678 : Nat := 1124467519756217446103869

theorem tailTrace_6569678 : CollatzResearch.WordTrace tailWord_6569678 prefixEnd_6569678 1124467519756217446103869 := by
  unfold tailWord_6569678
  simp only [CollatzResearch.WordTrace]
  refine ⟨29951980236648261564949711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159743894595457395013065125 29951980236648261564949711)
  ·
    refine ⟨44927970354972392347424567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29951980236648261564949711 44927970354972392347424567)
    ·
      refine ⟨67391955532458588521136851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44927970354972392347424567 67391955532458588521136851)
      ·
        refine ⟨101087933298687882781705277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67391955532458588521136851 101087933298687882781705277)
        ·
          refine ⟨37907974987007956043139479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101087933298687882781705277 37907974987007956043139479)
          ·
            refine ⟨56861962480511934064709219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37907974987007956043139479 56861962480511934064709219)
            ·
              refine ⟨85292943720767901097063829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56861962480511934064709219 85292943720767901097063829)
              ·
                refine ⟨3998106736910995363924867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85292943720767901097063829 3998106736910995363924867)
                ·
                  refine ⟨5997160105366493045887301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998106736910995363924867 5997160105366493045887301)
                  ·
                    refine ⟨1124467519756217446103869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5997160105366493045887301 1124467519756217446103869)
                    ·
                      rfl

theorem cell23_6569678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_6569678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569678 prefixEnd_6569678 := by exact prefixLift 6569678
  have htrace : WordTrace (prefixWord ++ tailWord_6569678) baseStart_6569678 baseEnd_6569678 := by
    simpa [prefixWord, tailWord_6569678, baseEnd_6569678] using wordTrace_append hprefix tailTrace_6569678
  have hstable : (prefixWord ++ tailWord_6569678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569678).length < 2 ^ (prefixWord ++ tailWord_6569678).sum := by decide
  have hdescent : baseEnd_6569678 < baseStart_6569678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569711 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 1, 5, 2]
def baseStart_6569711 : Nat := 118140960795 + 6569711 * 2 ^ 59
def prefixEnd_6569711 : Nat := 4983230072969 + 3 ^ 40 * 6569711 * 2
def baseEnd_6569711 : Nat := 3373419504130250709198955

theorem tailTrace_6569711 : CollatzResearch.WordTrace tailWord_6569711 prefixEnd_6569711 3373419504130250709198955 := by
  unfold tailWord_6569711
  simp only [CollatzResearch.WordTrace]
  refine ⟨239617045502066539155548987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159744697001377692770365991 239617045502066539155548987)
  ·
    refine ⟨359425568253099808733323481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239617045502066539155548987 359425568253099808733323481)
    ·
      refine ⟨269569176189824856549992611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359425568253099808733323481 269569176189824856549992611)
      ·
        refine ⟨404353764284737284824988917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269569176189824856549992611 404353764284737284824988917)
        ·
          refine ⟨37908165401694120452342711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 404353764284737284824988917 37908165401694120452342711)
          ·
            refine ⟨56862248102541180678514067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37908165401694120452342711 56862248102541180678514067)
            ·
              refine ⟨85293372153811771017771101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56862248102541180678514067 85293372153811771017771101)
              ·
                refine ⟨31985014557679414131664163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85293372153811771017771101 31985014557679414131664163)
                ·
                  refine ⟨47977521836519121197496245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31985014557679414131664163 47977521836519121197496245)
                  ·
                    refine ⟨4497892672173667612265273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47977521836519121197496245 4497892672173667612265273)
                    ·
                      refine ⟨3373419504130250709198955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4497892672173667612265273 3373419504130250709198955)
                      ·
                        rfl

theorem cell23_6569711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 5, 2].length) (baseStart_6569711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569711 prefixEnd_6569711 := by exact prefixLift 6569711
  have htrace : WordTrace (prefixWord ++ tailWord_6569711) baseStart_6569711 baseEnd_6569711 := by
    simpa [prefixWord, tailWord_6569711, baseEnd_6569711] using wordTrace_append hprefix tailTrace_6569711
  have hstable : (prefixWord ++ tailWord_6569711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569711).length < 2 ^ (prefixWord ++ tailWord_6569711).sum := by decide
  have hdescent : baseEnd_6569711 < baseStart_6569711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569778 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5]
def baseStart_6569778 : Nat := 118140960795 + 6569778 * 2 ^ 59
def prefixEnd_6569778 : Nat := 4983230072969 + 3 ^ 40 * 6569778 * 2
def baseEnd_6569778 : Nat := 3373453907334101947061147

theorem tailTrace_6569778 : CollatzResearch.WordTrace tailWord_6569778 prefixEnd_6569778 3373453907334101947061147 := by
  unfold tailWord_6569778
  simp only [CollatzResearch.WordTrace]
  refine ⟨59904872298205952399559497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159746326128549206398825325 59904872298205952399559497)
  ·
    refine ⟨44928654223654464299669623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59904872298205952399559497 44928654223654464299669623)
    ·
      refine ⟨67392981335481696449504435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44928654223654464299669623 67392981335481696449504435)
      ·
        refine ⟨101089472003222544674256653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67392981335481696449504435 101089472003222544674256653)
        ·
          refine ⟨37908552001208454252846245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101089472003222544674256653 37908552001208454252846245)
          ·
            refine ⟨7107853500226585172408671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37908552001208454252846245 7107853500226585172408671)
            ·
              refine ⟨10661780250339877758613007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7107853500226585172408671 10661780250339877758613007)
              ·
                refine ⟨15992670375509816637919511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10661780250339877758613007 15992670375509816637919511)
                ·
                  refine ⟨23989005563264724956879267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15992670375509816637919511 23989005563264724956879267)
                  ·
                    refine ⟨35983508344897087435318901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23989005563264724956879267 35983508344897087435318901)
                    ·
                      refine ⟨3373453907334101947061147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35983508344897087435318901 3373453907334101947061147)
                      ·
                        rfl

theorem cell23_6569778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_6569778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569778 prefixEnd_6569778 := by exact prefixLift 6569778
  have htrace : WordTrace (prefixWord ++ tailWord_6569778) baseStart_6569778 baseEnd_6569778 := by
    simpa [prefixWord, tailWord_6569778, baseEnd_6569778] using wordTrace_append hprefix tailTrace_6569778
  have hstable : (prefixWord ++ tailWord_6569778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569778).length < 2 ^ (prefixWord ++ tailWord_6569778).sum := by decide
  have hdescent : baseEnd_6569778 < baseStart_6569778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569781 : List Nat := [1, 3, 3, 1, 5, 10]
def baseStart_6569781 : Nat := 118140960795 + 6569781 * 2 ^ 59
def prefixEnd_6569781 : Nat := 4983230072969 + 3 ^ 40 * 6569781 * 2
def baseEnd_6569781 : Nat := 13882532706897388622731

theorem tailTrace_6569781 : CollatzResearch.WordTrace tailWord_6569781 prefixEnd_6569781 13882532706897388622731 := by
  unfold tailWord_6569781
  simp only [CollatzResearch.WordTrace]
  refine ⟨239619598611812941110597197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159746399074541960740398131 239619598611812941110597197)
  ·
    refine ⟨89857349479429852916473949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239619598611812941110597197 89857349479429852916473949)
    ·
      refine ⟨33696506054786194843677731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89857349479429852916473949 33696506054786194843677731)
      ·
        refine ⟨50544759082179292265516597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33696506054786194843677731 50544759082179292265516597)
        ·
          refine ⟨4738571163954308649892181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50544759082179292265516597 4738571163954308649892181)
          ·
            refine ⟨13882532706897388622731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4738571163954308649892181 13882532706897388622731)
            ·
              rfl

theorem cell23_6569781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 10].length) (baseStart_6569781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569781 prefixEnd_6569781 := by exact prefixLift 6569781
  have htrace : WordTrace (prefixWord ++ tailWord_6569781) baseStart_6569781 baseEnd_6569781 := by
    simpa [prefixWord, tailWord_6569781, baseEnd_6569781] using wordTrace_append hprefix tailTrace_6569781
  have hstable : (prefixWord ++ tailWord_6569781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569781).length < 2 ^ (prefixWord ++ tailWord_6569781).sum := by decide
  have hdescent : baseEnd_6569781 < baseStart_6569781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569805 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_6569805 : Nat := 118140960795 + 6569805 * 2 ^ 59
def prefixEnd_6569805 : Nat := 4983230072969 + 3 ^ 40 * 6569805 * 2
def baseEnd_6569805 : Nat := 3373467771311773341423523

theorem tailTrace_6569805 : CollatzResearch.WordTrace tailWord_6569805 prefixEnd_6569805 3373467771311773341423523 := by
  unfold tailWord_6569805
  simp only [CollatzResearch.WordTrace]
  refine ⟨239620473963725993209470869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159746982642483995472980579 239620473963725993209470869)
  ·
    refine ⟨11232209717049655931693947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 239620473963725993209470869 11232209717049655931693947)
    ·
      refine ⟨16848314575574483897540921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11232209717049655931693947 16848314575574483897540921)
      ·
        refine ⟨12636235931680862923155691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16848314575574483897540921 12636235931680862923155691)
        ·
          refine ⟨18954353897521294384733537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12636235931680862923155691 18954353897521294384733537)
          ·
            refine ⟨14215765423140970788550153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18954353897521294384733537 14215765423140970788550153)
            ·
              refine ⟨10661824067355728091412615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14215765423140970788550153 10661824067355728091412615)
              ·
                refine ⟨15992736101033592137118923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10661824067355728091412615 15992736101033592137118923)
                ·
                  refine ⟨23989104151550388205678385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15992736101033592137118923 23989104151550388205678385)
                  ·
                    refine ⟨17991828113662791154258789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23989104151550388205678385 17991828113662791154258789)
                    ·
                      refine ⟨3373467771311773341423523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17991828113662791154258789 3373467771311773341423523)
                      ·
                        rfl

theorem cell23_6569805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_6569805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569805 prefixEnd_6569805 := by exact prefixLift 6569805
  have htrace : WordTrace (prefixWord ++ tailWord_6569805) baseStart_6569805 baseEnd_6569805 := by
    simpa [prefixWord, tailWord_6569805, baseEnd_6569805] using wordTrace_append hprefix tailTrace_6569805
  have hstable : (prefixWord ++ tailWord_6569805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569805).length < 2 ^ (prefixWord ++ tailWord_6569805).sum := by decide
  have hdescent : baseEnd_6569805 < baseStart_6569805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569818 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2]
def baseStart_6569818 : Nat := 118140960795 + 6569818 * 2 ^ 59
def prefixEnd_6569818 : Nat := 4983230072969 + 3 ^ 40 * 6569818 * 2
def baseEnd_6569818 : Nat := 3373474446560281790560963

theorem tailTrace_6569818 : CollatzResearch.WordTrace tailWord_6569818 prefixEnd_6569818 3373474446560281790560963 := by
  unfold tailWord_6569818
  simp only [CollatzResearch.WordTrace]
  refine ⟨59905237028169724107423527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159747298741785930953129405 59905237028169724107423527)
  ·
    refine ⟨89857855542254586161135291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59905237028169724107423527 89857855542254586161135291)
    ·
      refine ⟨134786783313381879241702937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89857855542254586161135291 134786783313381879241702937)
      ·
        refine ⟨101090087485036409431277203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134786783313381879241702937 101090087485036409431277203)
        ·
          refine ⟨151635131227554614146915805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101090087485036409431277203 151635131227554614146915805)
          ·
            refine ⟨56863174210332980305093427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151635131227554614146915805 56863174210332980305093427)
            ·
              refine ⟨85294761315499470457640141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56863174210332980305093427 85294761315499470457640141)
              ·
                refine ⟨31985535493312301421615053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85294761315499470457640141 31985535493312301421615053)
                ·
                  refine ⟨11994575809992113033105645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31985535493312301421615053 11994575809992113033105645)
                  ·
                    refine ⟨4497965928747042387414617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11994575809992113033105645 4497965928747042387414617)
                    ·
                      refine ⟨3373474446560281790560963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4497965928747042387414617 3373474446560281790560963)
                      ·
                        rfl

theorem cell23_6569818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_6569818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569818 prefixEnd_6569818 := by exact prefixLift 6569818
  have htrace : WordTrace (prefixWord ++ tailWord_6569818) baseStart_6569818 baseEnd_6569818 := by
    simpa [prefixWord, tailWord_6569818, baseEnd_6569818] using wordTrace_append hprefix tailTrace_6569818
  have hstable : (prefixWord ++ tailWord_6569818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569818).length < 2 ^ (prefixWord ++ tailWord_6569818).sum := by decide
  have hdescent : baseEnd_6569818 < baseStart_6569818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569861 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_6569861 : Nat := 118140960795 + 6569861 * 2 ^ 59
def prefixEnd_6569861 : Nat := 4983230072969 + 3 ^ 40 * 6569861 * 2
def baseEnd_6569861 : Nat := 3373496526228425122323265

theorem tailTrace_6569861 : CollatzResearch.WordTrace tailWord_6569861 prefixEnd_6569861 3373496526228425122323265 := by
  unfold tailWord_6569861
  simp only [CollatzResearch.WordTrace]
  refine ⟨239622516451523114773509437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159748344301015409849006291 239622516451523114773509437)
  ·
    refine ⟨89858443669321168040066039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239622516451523114773509437 89858443669321168040066039)
    ·
      refine ⟨134787665503981752060099059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89858443669321168040066039 134787665503981752060099059)
      ·
        refine ⟨202181498255972628090148589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134787665503981752060099059 202181498255972628090148589)
        ·
          refine ⟨75818061845989735533805721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202181498255972628090148589 75818061845989735533805721)
          ·
            refine ⟨56863546384492301650354291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75818061845989735533805721 56863546384492301650354291)
            ·
              refine ⟨85295319576738452475531437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56863546384492301650354291 85295319576738452475531437)
              ·
                refine ⟨31985744841276919678324289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85295319576738452475531437 31985744841276919678324289)
                ·
                  refine ⟨23989308630957689758743217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31985744841276919678324289 23989308630957689758743217)
                  ·
                    refine ⟨17991981473218267319057413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23989308630957689758743217 17991981473218267319057413)
                    ·
                      refine ⟨3373496526228425122323265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17991981473218267319057413 3373496526228425122323265)
                      ·
                        rfl

theorem cell23_6569861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_6569861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569861 prefixEnd_6569861 := by exact prefixLift 6569861
  have htrace : WordTrace (prefixWord ++ tailWord_6569861) baseStart_6569861 baseEnd_6569861 := by
    simpa [prefixWord, tailWord_6569861, baseEnd_6569861] using wordTrace_append hprefix tailTrace_6569861
  have hstable : (prefixWord ++ tailWord_6569861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569861).length < 2 ^ (prefixWord ++ tailWord_6569861).sum := by decide
  have hdescent : baseEnd_6569861 < baseStart_6569861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569881 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 1, 5, 3]
def baseStart_6569881 : Nat := 118140960795 + 6569881 * 2 ^ 59
def prefixEnd_6569881 : Nat := 4983230072969 + 3 ^ 40 * 6569881 * 2
def baseEnd_6569881 : Nat := 3373506795841515044073173

theorem tailTrace_6569881 : CollatzResearch.WordTrace tailWord_6569881 prefixEnd_6569881 3373506795841515044073173 := by
  unfold tailWord_6569881
  simp only [CollatzResearch.WordTrace]
  refine ⟨239623245911450658189237497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159748830607633772126158331 239623245911450658189237497)
  ·
    refine ⟨179717434433587993641928123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239623245911450658189237497 179717434433587993641928123)
    ·
      refine ⟨269576151650381990462892185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179717434433587993641928123 269576151650381990462892185)
      ·
        refine ⟨202182113737786492847169139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269576151650381990462892185 202182113737786492847169139)
        ·
          refine ⟨303273170606679739270753709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202182113737786492847169139 303273170606679739270753709)
          ·
            refine ⟨113727438977504902226532641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303273170606679739270753709 113727438977504902226532641)
            ·
              refine ⟨85295579233128676669899481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113727438977504902226532641 85295579233128676669899481)
              ·
                refine ⟨63971684424846507502424611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85295579233128676669899481 63971684424846507502424611)
                ·
                  refine ⟨95957526637269761253636917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63971684424846507502424611 95957526637269761253636917)
                  ·
                    refine ⟨8996018122244040117528461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95957526637269761253636917 8996018122244040117528461)
                    ·
                      refine ⟨3373506795841515044073173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8996018122244040117528461 3373506795841515044073173)
                      ·
                        rfl

theorem cell23_6569881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_6569881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569881 prefixEnd_6569881 := by exact prefixLift 6569881
  have htrace : WordTrace (prefixWord ++ tailWord_6569881) baseStart_6569881 baseEnd_6569881 := by
    simpa [prefixWord, tailWord_6569881, baseEnd_6569881] using wordTrace_append hprefix tailTrace_6569881
  have hstable : (prefixWord ++ tailWord_6569881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569881).length < 2 ^ (prefixWord ++ tailWord_6569881).sum := by decide
  have hdescent : baseEnd_6569881 < baseStart_6569881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6569982 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_6569982 : Nat := 118140960795 + 6569982 * 2 ^ 59
def prefixEnd_6569982 : Nat := 4983230072969 + 3 ^ 40 * 6569982 * 2
def baseEnd_6569982 : Nat := 1124519552462539716303403

theorem tailTrace_6569982 : CollatzResearch.WordTrace tailWord_6569982 prefixEnd_6569982 1124519552462539716303403 := by
  unfold tailWord_6569982
  simp only [CollatzResearch.WordTrace]
  refine ⟨29953366210510594054833025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159751286456056501625776133 29953366210510594054833025)
  ·
    refine ⟨22465024657882945541124769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29953366210510594054833025 22465024657882945541124769)
    ·
      refine ⟨16848768493412209155843577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22465024657882945541124769 16848768493412209155843577)
      ·
        refine ⟨12636576370059156866882683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16848768493412209155843577 12636576370059156866882683)
        ·
          refine ⟨18954864555088735300324025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12636576370059156866882683 18954864555088735300324025)
          ·
            refine ⟨14216148416316551475243019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18954864555088735300324025 14216148416316551475243019)
            ·
              refine ⟨21324222624474827212864529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14216148416316551475243019 21324222624474827212864529)
              ·
                refine ⟨15993166968356120409648397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21324222624474827212864529 15993166968356120409648397)
                ·
                  refine ⟨5997437613133545153618149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15993166968356120409648397 5997437613133545153618149)
                  ·
                    refine ⟨1124519552462539716303403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5997437613133545153618149 1124519552462539716303403)
                    ·
                      rfl

theorem cell23_6569982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_6569982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6569982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6569982 prefixEnd_6569982 := by exact prefixLift 6569982
  have htrace : WordTrace (prefixWord ++ tailWord_6569982) baseStart_6569982 baseEnd_6569982 := by
    simpa [prefixWord, tailWord_6569982, baseEnd_6569982] using wordTrace_append hprefix tailTrace_6569982
  have hstable : (prefixWord ++ tailWord_6569982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6569982).length < 2 ^ (prefixWord ++ tailWord_6569982).sum := by decide
  have hdescent : baseEnd_6569982 < baseStart_6569982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6569982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570001 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_6570001 : Nat := 118140960795 + 6570001 * 2 ^ 59
def prefixEnd_6570001 : Nat := 4983230072969 + 3 ^ 40 * 6570001 * 2
def baseEnd_6570001 : Nat := 3373568413520054574572621

theorem tailTrace_6570001 : CollatzResearch.WordTrace tailWord_6570001 prefixEnd_6570001 3373568413520054574572621 := by
  unfold tailWord_6570001
  simp only [CollatzResearch.WordTrace]
  refine ⟨239627622671015918683605857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159751748447343945789070571 239627622671015918683605857)
  ·
    refine ⟨179720717003261939012704393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239627622671015918683605857 179720717003261939012704393)
    ·
      refine ⟨134790537752446454259528295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179720717003261939012704393 134790537752446454259528295)
      ·
        refine ⟨202185806628669681389292443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134790537752446454259528295 202185806628669681389292443)
        ·
          refine ⟨303278709943004522083938665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202185806628669681389292443 303278709943004522083938665)
          ·
            refine ⟨227459032457253391562953999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303278709943004522083938665 227459032457253391562953999)
            ·
              refine ⟨341188548685880087344430999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227459032457253391562953999 341188548685880087344430999)
              ·
                refine ⟨511782823028820131016646499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341188548685880087344430999 511782823028820131016646499)
                ·
                  refine ⟨767674234543230196524969749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511782823028820131016646499 767674234543230196524969749)
                  ·
                    refine ⟨35984729744213915462107957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 767674234543230196524969749 35984729744213915462107957)
                    ·
                      refine ⟨3373568413520054574572621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35984729744213915462107957 3373568413520054574572621)
                      ·
                        rfl

theorem cell23_6570001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_6570001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570001 prefixEnd_6570001 := by exact prefixLift 6570001
  have htrace : WordTrace (prefixWord ++ tailWord_6570001) baseStart_6570001 baseEnd_6570001 := by
    simpa [prefixWord, tailWord_6570001, baseEnd_6570001] using wordTrace_append hprefix tailTrace_6570001
  have hstable : (prefixWord ++ tailWord_6570001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570001).length < 2 ^ (prefixWord ++ tailWord_6570001).sum := by decide
  have hdescent : baseEnd_6570001 < baseStart_6570001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570015 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 4, 3, 2]
def baseStart_6570015 : Nat := 118140960795 + 6570015 * 2 ^ 59
def prefixEnd_6570015 : Nat := 4983230072969 + 3 ^ 40 * 6570015 * 2
def baseEnd_6570015 : Nat := 3373575602249217519797557

theorem tailTrace_6570015 : CollatzResearch.WordTrace tailWord_6570015 prefixEnd_6570015 3373575602249217519797557 := by
  unfold tailWord_6570015
  simp only [CollatzResearch.WordTrace]
  refine ⟨239628133292965199074615499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159752088861976799383076999 239628133292965199074615499)
  ·
    refine ⟨359442199939447798611923249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239628133292965199074615499 359442199939447798611923249)
    ·
      refine ⟨269581649954585848958942437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359442199939447798611923249 269581649954585848958942437)
      ·
        refine ⟨50546559366484846679801707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269581649954585848958942437 50546559366484846679801707)
        ·
          refine ⟨75819839049727270019702561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50546559366484846679801707 75819839049727270019702561)
          ·
            refine ⟨56864879287295452514776921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75819839049727270019702561 56864879287295452514776921)
            ·
              refine ⟨42648659465471589386082691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56864879287295452514776921 42648659465471589386082691)
              ·
                refine ⟨63972989198207384079124037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42648659465471589386082691 63972989198207384079124037)
                ·
                  refine ⟨11994935474663884514835757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63972989198207384079124037 11994935474663884514835757)
                  ·
                    refine ⟨4498100802998956693063409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11994935474663884514835757 4498100802998956693063409)
                    ·
                      refine ⟨3373575602249217519797557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4498100802998956693063409 3373575602249217519797557)
                      ·
                        rfl

theorem cell23_6570015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_6570015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570015 prefixEnd_6570015 := by exact prefixLift 6570015
  have htrace : WordTrace (prefixWord ++ tailWord_6570015) baseStart_6570015 baseEnd_6570015 := by
    simpa [prefixWord, tailWord_6570015, baseEnd_6570015] using wordTrace_append hprefix tailTrace_6570015
  have hstable : (prefixWord ++ tailWord_6570015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570015).length < 2 ^ (prefixWord ++ tailWord_6570015).sum := by decide
  have hdescent : baseEnd_6570015 < baseStart_6570015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570028 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 4]
def baseStart_6570028 : Nat := 118140960795 + 6570028 * 2 ^ 59
def prefixEnd_6570028 : Nat := 4983230072969 + 3 ^ 40 * 6570028 * 2
def baseEnd_6570028 : Nat := 3373582277497725968934997

theorem tailTrace_6570028 : CollatzResearch.WordTrace tailWord_6570028 prefixEnd_6570028 3373582277497725968934997 := by
  unfold tailWord_6570028
  simp only [CollatzResearch.WordTrace]
  refine ⟨119814303720959051147419369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159752404961278734863225825 119814303720959051147419369)
  ·
    refine ⟨89860727790719288360564527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119814303720959051147419369 89860727790719288360564527)
    ·
      refine ⟨134791091686078932540846791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89860727790719288360564527 134791091686078932540846791)
      ·
        refine ⟨202186637529118398811270187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134791091686078932540846791 202186637529118398811270187)
        ·
          refine ⟨303279956293677598216905281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202186637529118398811270187 303279956293677598216905281)
          ·
            refine ⟨227459967220258198662678961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303279956293677598216905281 227459967220258198662678961)
            ·
              refine ⟨170594975415193648997009221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227459967220258198662678961 170594975415193648997009221)
              ·
                refine ⟨31986557890348809186939229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170594975415193648997009221 31986557890348809186939229)
                ·
                  refine ⟨11994959208880803445102211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31986557890348809186939229 11994959208880803445102211)
                  ·
                    refine ⟨17992438813321205167653317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11994959208880803445102211 17992438813321205167653317)
                    ·
                      refine ⟨3373582277497725968934997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17992438813321205167653317 3373582277497725968934997)
                      ·
                        rfl

theorem cell23_6570028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_6570028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570028 prefixEnd_6570028 := by exact prefixLift 6570028
  have htrace : WordTrace (prefixWord ++ tailWord_6570028) baseStart_6570028 baseEnd_6570028 := by
    simpa [prefixWord, tailWord_6570028, baseEnd_6570028] using wordTrace_append hprefix tailTrace_6570028
  have hstable : (prefixWord ++ tailWord_6570028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570028).length < 2 ^ (prefixWord ++ tailWord_6570028).sum := by decide
  have hdescent : baseEnd_6570028 < baseStart_6570028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570045 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 2, 6, 2]
def baseStart_6570045 : Nat := 118140960795 + 6570045 * 2 ^ 59
def prefixEnd_6570045 : Nat := 4983230072969 + 3 ^ 40 * 6570045 * 2
def baseEnd_6570045 : Nat := 3373591006668852402422419

theorem tailTrace_6570045 : CollatzResearch.WordTrace tailWord_6570045 prefixEnd_6570045 3373591006668852402422419 := by
  unfold tailWord_6570045
  simp only [CollatzResearch.WordTrace]
  refine ⟨239629227482856514198207589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159752818321904342798805059 239629227482856514198207589)
  ·
    refine ⟨44930480153035596412163923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239629227482856514198207589 44930480153035596412163923)
    ·
      refine ⟨67395720229553394618245885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44930480153035596412163923 67395720229553394618245885)
      ·
        refine ⟨25273395086082522981842207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67395720229553394618245885 25273395086082522981842207)
        ·
          refine ⟨37910092629123784472763311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25273395086082522981842207 37910092629123784472763311)
          ·
            refine ⟨56865138943685676709144967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37910092629123784472763311 56865138943685676709144967)
            ·
              refine ⟨85297708415528515063717451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56865138943685676709144967 85297708415528515063717451)
              ·
                refine ⟨127946562623292772595576177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85297708415528515063717451 127946562623292772595576177)
                ·
                  refine ⟨95959921967469579446682133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127946562623292772595576177 95959921967469579446682133)
                  ·
                    refine ⟨4498121342225136536563225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95959921967469579446682133 4498121342225136536563225)
                    ·
                      refine ⟨3373591006668852402422419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4498121342225136536563225 3373591006668852402422419)
                      ·
                        rfl

theorem cell23_6570045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_6570045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570045 prefixEnd_6570045 := by exact prefixLift 6570045
  have htrace : WordTrace (prefixWord ++ tailWord_6570045) baseStart_6570045 baseEnd_6570045 := by
    simpa [prefixWord, tailWord_6570045, baseEnd_6570045] using wordTrace_append hprefix tailTrace_6570045
  have hstable : (prefixWord ++ tailWord_6570045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570045).length < 2 ^ (prefixWord ++ tailWord_6570045).sum := by decide
  have hdescent : baseEnd_6570045 < baseStart_6570045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570058 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_6570058 : Nat := 118140960795 + 6570058 * 2 ^ 59
def prefixEnd_6570058 : Nat := 4983230072969 + 3 ^ 40 * 6570058 * 2
def baseEnd_6570058 : Nat := 3373597681917360851559859

theorem tailTrace_6570058 : CollatzResearch.WordTrace tailWord_6570058 prefixEnd_6570058 3373597681917360851559859 := by
  unfold tailWord_6570058
  simp only [CollatzResearch.WordTrace]
  refine ⟨59907425407952354354607707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159753134421206278278953885 59907425407952354354607707)
  ·
    refine ⟨89861138111928531531911561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59907425407952354354607707 89861138111928531531911561)
    ·
      refine ⟨67395853583946398648933671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89861138111928531531911561 67395853583946398648933671)
      ·
        refine ⟨101093780375919597973400507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67395853583946398648933671 101093780375919597973400507)
        ·
          refine ⟨151640670563879396960100761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101093780375919597973400507 151640670563879396960100761)
          ·
            refine ⟨113730502922909547720075571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151640670563879396960100761 113730502922909547720075571)
            ·
              refine ⟨170595754384364321580113357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113730502922909547720075571 170595754384364321580113357)
              ·
                refine ⟨63973407894136620592542509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170595754384364321580113357 63973407894136620592542509)
                ·
                  refine ⟨23990027960301232722203441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63973407894136620592542509 23990027960301232722203441)
                  ·
                    refine ⟨17992520970225924541652581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23990027960301232722203441 17992520970225924541652581)
                    ·
                      refine ⟨3373597681917360851559859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17992520970225924541652581 3373597681917360851559859)
                      ·
                        rfl

theorem cell23_6570058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_6570058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570058 prefixEnd_6570058 := by exact prefixLift 6570058
  have htrace : WordTrace (prefixWord ++ tailWord_6570058) baseStart_6570058 baseEnd_6570058 := by
    simpa [prefixWord, tailWord_6570058, baseEnd_6570058] using wordTrace_append hprefix tailTrace_6570058
  have hstable : (prefixWord ++ tailWord_6570058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570058).length < 2 ^ (prefixWord ++ tailWord_6570058).sum := by decide
  have hdescent : baseEnd_6570058 < baseStart_6570058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570128 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 2, 6]
def baseStart_6570128 : Nat := 118140960795 + 6570128 * 2 ^ 59
def prefixEnd_6570128 : Nat := 4983230072969 + 3 ^ 40 * 6570128 * 2
def baseEnd_6570128 : Nat := 1124544541854391859228179

theorem tailTrace_6570128 : CollatzResearch.WordTrace tailWord_6570128 prefixEnd_6570128 1124544541854391859228179 := by
  unfold tailWord_6570128
  simp only [CollatzResearch.WordTrace]
  refine ⟨119816127370777909686739519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159754836494370546248986025 119816127370777909686739519)
  ·
    refine ⟨179724191056166864530109279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119816127370777909686739519 179724191056166864530109279)
    ·
      refine ⟨269586286584250296795163919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179724191056166864530109279 269586286584250296795163919)
      ·
        refine ⟨404379429876375445192745879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269586286584250296795163919 404379429876375445192745879)
        ·
          refine ⟨606569144814563167789118819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404379429876375445192745879 606569144814563167789118819)
          ·
            refine ⟨909853717221844751683678229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606569144814563167789118819 909853717221844751683678229)
            ·
              refine ⟨42649392994773972735172417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 909853717221844751683678229 42649392994773972735172417)
              ·
                refine ⟨31987044746080479551379313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42649392994773972735172417 31987044746080479551379313)
                ·
                  refine ⟨23990283559560359663534485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31987044746080479551379313 23990283559560359663534485)
                  ·
                    refine ⟨1124544541854391859228179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23990283559560359663534485 1124544541854391859228179)
                    ·
                      rfl

theorem cell23_6570128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2, 6].length) (baseStart_6570128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570128 prefixEnd_6570128 := by exact prefixLift 6570128
  have htrace : WordTrace (prefixWord ++ tailWord_6570128) baseStart_6570128 baseEnd_6570128 := by
    simpa [prefixWord, tailWord_6570128, baseEnd_6570128] using wordTrace_append hprefix tailTrace_6570128
  have hstable : (prefixWord ++ tailWord_6570128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570128).length < 2 ^ (prefixWord ++ tailWord_6570128).sum := by decide
  have hdescent : baseEnd_6570128 < baseStart_6570128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570145 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 2, 6]
def baseStart_6570145 : Nat := 118140960795 + 6570145 * 2 ^ 59
def prefixEnd_6570145 : Nat := 4983230072969 + 3 ^ 40 * 6570145 * 2
def baseEnd_6570145 : Nat := 1124547451578100670390653

theorem tailTrace_6570145 : CollatzResearch.WordTrace tailWord_6570145 prefixEnd_6570145 1124547451578100670390653 := by
  unfold tailWord_6570145
  simp only [CollatzResearch.WordTrace]
  refine ⟨239632874782494231276847889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159755249854996154184565259 239632874782494231276847889)
  ·
    refine ⟨179724656086870673457635917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239632874782494231276847889 179724656086870673457635917)
    ·
      refine ⟨67396746032576502546613469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179724656086870673457635917 67396746032576502546613469)
      ·
        refine ⟨25273779762216188454980051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67396746032576502546613469 25273779762216188454980051)
        ·
          refine ⟨37910669643324282682470077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25273779762216188454980051 37910669643324282682470077)
          ·
            refine ⟨14216501116246606005926279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37910669643324282682470077 14216501116246606005926279)
            ·
              refine ⟨21324751674369909008889419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14216501116246606005926279 21324751674369909008889419)
              ·
                refine ⟨31987127511554863513334129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21324751674369909008889419 31987127511554863513334129)
                ·
                  refine ⟨23990345633666147635000597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31987127511554863513334129 23990345633666147635000597)
                  ·
                    refine ⟨1124547451578100670390653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23990345633666147635000597 1124547451578100670390653)
                    ·
                      rfl

theorem cell23_6570145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_6570145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570145 prefixEnd_6570145 := by exact prefixLift 6570145
  have htrace : WordTrace (prefixWord ++ tailWord_6570145) baseStart_6570145 baseEnd_6570145 := by
    simpa [prefixWord, tailWord_6570145, baseEnd_6570145] using wordTrace_append hprefix tailTrace_6570145
  have hstable : (prefixWord ++ tailWord_6570145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570145).length < 2 ^ (prefixWord ++ tailWord_6570145).sum := by decide
  have hdescent : baseEnd_6570145 < baseStart_6570145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570225 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_6570225 : Nat := 118140960795 + 6570225 * 2 ^ 59
def prefixEnd_6570225 : Nat := 4983230072969 + 3 ^ 40 * 6570225 * 2
def baseEnd_6570225 : Nat := 3373683433186661698171591

theorem tailTrace_6570225 : CollatzResearch.WordTrace tailWord_6570225 prefixEnd_6570225 3373683433186661698171591 := by
  unfold tailWord_6570225
  simp only [CollatzResearch.WordTrace]
  refine ⟨239635792622204404939760129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159757195081469603293173419 239635792622204404939760129)
  ·
    refine ⟨179726844466653303704820097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239635792622204404939760129 179726844466653303704820097)
    ·
      refine ⟨134795133349989977778615073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179726844466653303704820097 134795133349989977778615073)
      ·
        refine ⟨101096350012492483333961305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134795133349989977778615073 101096350012492483333961305)
        ·
          refine ⟨75822262509369362500470979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101096350012492483333961305 75822262509369362500470979)
          ·
            refine ⟨113733393764054043750706469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75822262509369362500470979 113733393764054043750706469)
            ·
              refine ⟨21325011330760133203257463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113733393764054043750706469 21325011330760133203257463)
              ·
                refine ⟨31987516996140199804886195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21325011330760133203257463 31987516996140199804886195)
                ·
                  refine ⟨47981275494210299707329293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31987516996140199804886195 47981275494210299707329293)
                  ·
                    refine ⟨17992978310328862390248485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47981275494210299707329293 17992978310328862390248485)
                    ·
                      refine ⟨3373683433186661698171591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17992978310328862390248485 3373683433186661698171591)
                      ·
                        rfl

theorem cell23_6570225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_6570225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570225 prefixEnd_6570225 := by exact prefixLift 6570225
  have htrace : WordTrace (prefixWord ++ tailWord_6570225) baseStart_6570225 baseEnd_6570225 := by
    simpa [prefixWord, tailWord_6570225, baseEnd_6570225] using wordTrace_append hprefix tailTrace_6570225
  have hstable : (prefixWord ++ tailWord_6570225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570225).length < 2 ^ (prefixWord ++ tailWord_6570225).sum := by decide
  have hdescent : baseEnd_6570225 < baseStart_6570225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570245 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 3, 4, 3]
def baseStart_6570245 : Nat := 118140960795 + 6570245 * 2 ^ 59
def prefixEnd_6570245 : Nat := 4983230072969 + 3 ^ 40 * 6570245 * 2
def baseEnd_6570245 : Nat := 3373693702799751619921499

theorem tailTrace_6570245 : CollatzResearch.WordTrace tailWord_6570245 prefixEnd_6570245 3373693702799751619921499 := by
  unfold tailWord_6570245
  simp only [CollatzResearch.WordTrace]
  refine ⟨239636522082131948355488189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159757681388087965570325459 239636522082131948355488189)
  ·
    refine ⟨89863695780799480633308071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239636522082131948355488189 89863695780799480633308071)
    ·
      refine ⟨134795543671199220949962107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89863695780799480633308071 134795543671199220949962107)
      ·
        refine ⟨202193315506798831424943161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134795543671199220949962107 202193315506798831424943161)
        ·
          refine ⟨151644986630099123568707371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202193315506798831424943161 151644986630099123568707371)
          ·
            refine ⟨227467479945148685353061057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151644986630099123568707371 227467479945148685353061057)
            ·
              refine ⟨170600609958861514014795793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227467479945148685353061057 170600609958861514014795793)
              ·
                refine ⟨127950457469146135511096845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170600609958861514014795793 127950457469146135511096845)
                ·
                  refine ⟨47981421550929800816661317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127950457469146135511096845 47981421550929800816661317)
                  ·
                    refine ⟨8996516540799337653123997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47981421550929800816661317 8996516540799337653123997)
                    ·
                      refine ⟨3373693702799751619921499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8996516540799337653123997 3373693702799751619921499)
                      ·
                        rfl

theorem cell23_6570245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_6570245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570245 prefixEnd_6570245 := by exact prefixLift 6570245
  have htrace : WordTrace (prefixWord ++ tailWord_6570245) baseStart_6570245 baseEnd_6570245 := by
    simpa [prefixWord, tailWord_6570245, baseEnd_6570245] using wordTrace_append hprefix tailTrace_6570245
  have hstable : (prefixWord ++ tailWord_6570245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570245).length < 2 ^ (prefixWord ++ tailWord_6570245).sum := by decide
  have hdescent : baseEnd_6570245 < baseStart_6570245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570343 : List Nat := [1, 1, 5, 1, 3, 2, 2, 3, 1, 1, 3]
def baseStart_6570343 : Nat := 118140960795 + 6570343 * 2 ^ 59
def prefixEnd_6570343 : Nat := 4983230072969 + 3 ^ 40 * 6570343 * 2
def baseEnd_6570343 : Nat := 3373744023903892236496049

theorem tailTrace_6570343 : CollatzResearch.WordTrace tailWord_6570343 prefixEnd_6570343 3373744023903892236496049 := by
  unfold tailWord_6570343
  simp only [CollatzResearch.WordTrace]
  refine ⟨239640096435776911092555683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159760064290517940728370455 239640096435776911092555683)
  ·
    refine ⟨359460144653665366638833525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239640096435776911092555683 359460144653665366638833525)
    ·
      refine ⟨33699388561281128122390643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 359460144653665366638833525 33699388561281128122390643)
      ·
        refine ⟨50549082841921692183585965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33699388561281128122390643 50549082841921692183585965)
        ·
          refine ⟨18955906065720634568844737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50549082841921692183585965 18955906065720634568844737)
          ·
            refine ⟨14216929549290475926633553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18955906065720634568844737 14216929549290475926633553)
            ·
              refine ⟨10662697161967856944975165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14216929549290475926633553 10662697161967856944975165)
              ·
                refine ⟨3998511435737946354365687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10662697161967856944975165 3998511435737946354365687)
                ·
                  refine ⟨5997767153606919531548531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998511435737946354365687 5997767153606919531548531)
                  ·
                    refine ⟨8996650730410379297322797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5997767153606919531548531 8996650730410379297322797)
                    ·
                      refine ⟨3373744023903892236496049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8996650730410379297322797 3373744023903892236496049)
                      ·
                        rfl

theorem cell23_6570343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_6570343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570343 prefixEnd_6570343 := by exact prefixLift 6570343
  have htrace : WordTrace (prefixWord ++ tailWord_6570343) baseStart_6570343 baseEnd_6570343 := by
    simpa [prefixWord, tailWord_6570343, baseEnd_6570343] using wordTrace_append hprefix tailTrace_6570343
  have hstable : (prefixWord ++ tailWord_6570343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570343).length < 2 ^ (prefixWord ++ tailWord_6570343).sum := by decide
  have hdescent : baseEnd_6570343 < baseStart_6570343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570346 : List Nat := [3, 1, 3, 3, 1, 1, 4, 1, 1, 5]
def baseStart_6570346 : Nat := 118140960795 + 6570346 * 2 ^ 59
def prefixEnd_6570346 : Nat := 4983230072969 + 3 ^ 40 * 6570346 * 2
def baseEnd_6570346 : Nat := 1124581854781951908252845

theorem tailTrace_6570346 : CollatzResearch.WordTrace tailWord_6570346 prefixEnd_6570346 1124581854781951908252845 := by
  unfold tailWord_6570346
  simp only [CollatzResearch.WordTrace]
  refine ⟨59910051463691510651228723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159760137236510695069943261 59910051463691510651228723)
  ·
    refine ⟨89865077195537265976843085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59910051463691510651228723 89865077195537265976843085)
    ·
      refine ⟨33699403948326474741316157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89865077195537265976843085 33699403948326474741316157)
      ·
        refine ⟨12637276480622428027993559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33699403948326474741316157 12637276480622428027993559)
        ·
          refine ⟨18955914720933642041990339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12637276480622428027993559 18955914720933642041990339)
          ·
            refine ⟨28433872081400463062985509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18955914720933642041990339 28433872081400463062985509)
            ·
              refine ⟨5331351015262586824309783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28433872081400463062985509 5331351015262586824309783)
              ·
                refine ⟨7997026522893880236464675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5331351015262586824309783 7997026522893880236464675)
                ·
                  refine ⟨11995539784340820354697013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7997026522893880236464675 11995539784340820354697013)
                  ·
                    refine ⟨1124581854781951908252845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11995539784340820354697013 1124581854781951908252845)
                    ·
                      rfl

theorem cell23_6570346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_6570346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570346 prefixEnd_6570346 := by exact prefixLift 6570346
  have htrace : WordTrace (prefixWord ++ tailWord_6570346) baseStart_6570346 baseEnd_6570346 := by
    simpa [prefixWord, tailWord_6570346, baseEnd_6570346] using wordTrace_append hprefix tailTrace_6570346
  have hstable : (prefixWord ++ tailWord_6570346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570346).length < 2 ^ (prefixWord ++ tailWord_6570346).sum := by decide
  have hdescent : baseEnd_6570346 < baseStart_6570346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570349 : List Nat := [1, 5, 1, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_6570349 : Nat := 118140960795 + 6570349 * 2 ^ 59
def prefixEnd_6570349 : Nat := 4983230072969 + 3 ^ 40 * 6570349 * 2
def baseEnd_6570349 : Nat := 3373747104787819213021021

theorem tailTrace_6570349 : CollatzResearch.WordTrace tailWord_6570349 prefixEnd_6570349 3373747104787819213021021 := by
  unfold tailWord_6570349
  simp only [CollatzResearch.WordTrace]
  refine ⟨239640315273755174117274101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159760210182503449411516067 239640315273755174117274101)
  ·
    refine ⟨22466279556914547573494447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239640315273755174117274101 22466279556914547573494447)
    ·
      refine ⟨33699419335371821360241671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22466279556914547573494447 33699419335371821360241671)
      ·
        refine ⟨50549129003057732040362507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33699419335371821360241671 50549129003057732040362507)
        ·
          refine ⟨75823693504586598060543761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50549129003057732040362507 75823693504586598060543761)
          ·
            refine ⟨56867770128439948545407821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75823693504586598060543761 56867770128439948545407821)
            ·
              refine ⟨21325413798164980704527933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56867770128439948545407821 21325413798164980704527933)
              ·
                refine ⟨7997030174311867764197975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21325413798164980704527933 7997030174311867764197975)
                ·
                  refine ⟨11995545261467801646296963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7997030174311867764197975 11995545261467801646296963)
                  ·
                    refine ⟨17993317892201702469445445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11995545261467801646296963 17993317892201702469445445)
                    ·
                      refine ⟨3373747104787819213021021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17993317892201702469445445 3373747104787819213021021)
                      ·
                        rfl

theorem cell23_6570349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_6570349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570349 prefixEnd_6570349 := by exact prefixLift 6570349
  have htrace : WordTrace (prefixWord ++ tailWord_6570349) baseStart_6570349 baseEnd_6570349 := by
    simpa [prefixWord, tailWord_6570349, baseEnd_6570349] using wordTrace_append hprefix tailTrace_6570349
  have hstable : (prefixWord ++ tailWord_6570349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570349).length < 2 ^ (prefixWord ++ tailWord_6570349).sum := by decide
  have hdescent : baseEnd_6570349 < baseStart_6570349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570369 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_6570369 : Nat := 118140960795 + 6570369 * 2 ^ 59
def prefixEnd_6570369 : Nat := 4983230072969 + 3 ^ 40 * 6570369 * 2
def baseEnd_6570369 : Nat := 3373757374400909134770929

theorem tailTrace_6570369 : CollatzResearch.WordTrace tailWord_6570369 prefixEnd_6570369 3373757374400909134770929 := by
  unfold tailWord_6570369
  simp only [CollatzResearch.WordTrace]
  refine ⟨239641044733682717533002161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159760696489121811688668107 239641044733682717533002161)
  ·
    refine ⟨179730783550262038149751621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239641044733682717533002161 179730783550262038149751621)
    ·
      refine ⟨33699521915674132153078429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179730783550262038149751621 33699521915674132153078429)
      ·
        refine ⟨12637320718377799557404411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33699521915674132153078429 12637320718377799557404411)
        ·
          refine ⟨18955981077566699336106617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12637320718377799557404411 18955981077566699336106617)
          ·
            refine ⟨14216985808175024502079963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18955981077566699336106617 14216985808175024502079963)
            ·
              refine ⟨21325478712262536753119945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14216985808175024502079963 21325478712262536753119945)
              ·
                refine ⟨15994109034196902564839959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21325478712262536753119945 15994109034196902564839959)
                ·
                  refine ⟨23991163551295353847259939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15994109034196902564839959 23991163551295353847259939)
                  ·
                    refine ⟨35986745326943030770889909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23991163551295353847259939 35986745326943030770889909)
                    ·
                      refine ⟨3373757374400909134770929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35986745326943030770889909 3373757374400909134770929)
                      ·
                        rfl

theorem cell23_6570369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_6570369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570369 prefixEnd_6570369 := by exact prefixLift 6570369
  have htrace : WordTrace (prefixWord ++ tailWord_6570369) baseStart_6570369 baseEnd_6570369 := by
    simpa [prefixWord, tailWord_6570369, baseEnd_6570369] using wordTrace_append hprefix tailTrace_6570369
  have hstable : (prefixWord ++ tailWord_6570369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570369).length < 2 ^ (prefixWord ++ tailWord_6570369).sum := by decide
  have hdescent : baseEnd_6570369 < baseStart_6570369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570376 : List Nat := [2, 1, 3, 3, 1, 1, 5, 1, 2, 4]
def baseStart_6570376 : Nat := 118140960795 + 6570376 * 2 ^ 59
def prefixEnd_6570376 : Nat := 4983230072969 + 3 ^ 40 * 6570376 * 2
def baseEnd_6570376 : Nat := 1124586989588496869127799

theorem tailTrace_6570376 : CollatzResearch.WordTrace tailWord_6570376 prefixEnd_6570376 1124586989588496869127799 := by
  unfold tailWord_6570376
  simp only [CollatzResearch.WordTrace]
  refine ⟨119820650022328678864253491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159760866696438238485671321 119820650022328678864253491)
  ·
    refine ⟨179730975033493018296380237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119820650022328678864253491 179730975033493018296380237)
    ·
      refine ⟨67399115637559881861142589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179730975033493018296380237 67399115637559881861142589)
      ·
        refine ⟨25274668364084955697928471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67399115637559881861142589 25274668364084955697928471)
        ·
          refine ⟨37912002546127433546892707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25274668364084955697928471 37912002546127433546892707)
          ·
            refine ⟨56868003819191150320339061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37912002546127433546892707 56868003819191150320339061)
            ·
              refine ⟨5331375358049170342531787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56868003819191150320339061 5331375358049170342531787)
              ·
                refine ⟨7997063037073755513797681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5331375358049170342531787 7997063037073755513797681)
                ·
                  refine ⟨5997797277805316635348261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7997063037073755513797681 5997797277805316635348261)
                  ·
                    refine ⟨1124586989588496869127799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5997797277805316635348261 1124586989588496869127799)
                    ·
                      rfl

theorem cell23_6570376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_6570376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570376 prefixEnd_6570376 := by exact prefixLift 6570376
  have htrace : WordTrace (prefixWord ++ tailWord_6570376) baseStart_6570376 baseEnd_6570376 := by
    simpa [prefixWord, tailWord_6570376, baseEnd_6570376] using wordTrace_append hprefix tailTrace_6570376
  have hstable : (prefixWord ++ tailWord_6570376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570376).length < 2 ^ (prefixWord ++ tailWord_6570376).sum := by decide
  have hdescent : baseEnd_6570376 < baseStart_6570376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570379 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 1, 2, 4]
def baseStart_6570379 : Nat := 118140960795 + 6570379 * 2 ^ 59
def prefixEnd_6570379 : Nat := 4983230072969 + 3 ^ 40 * 6570379 * 2
def baseEnd_6570379 : Nat := 3373762509207454095645883

theorem tailTrace_6570379 : CollatzResearch.WordTrace tailWord_6570379 prefixEnd_6570379 3373762509207454095645883 := by
  unfold tailWord_6570379
  simp only [CollatzResearch.WordTrace]
  refine ⟨239641409463646489240866191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159760939642430992827244127 239641409463646489240866191)
  ·
    refine ⟨359462114195469733861299287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239641409463646489240866191 359462114195469733861299287)
    ·
      refine ⟨539193171293204600791948931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359462114195469733861299287 539193171293204600791948931)
      ·
        refine ⟨808789756939806901187923397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539193171293204600791948931 808789756939806901187923397)
        ·
          refine ⟨151648079426213793972735637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 808789756939806901187923397 151648079426213793972735637)
          ·
            refine ⟨7108503723103771592471983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 151648079426213793972735637 7108503723103771592471983)
            ·
              refine ⟨10662755584655657388707975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7108503723103771592471983 10662755584655657388707975)
              ·
                refine ⟨15994133376983486083061963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10662755584655657388707975 15994133376983486083061963)
                ·
                  refine ⟨23991200065475229124592945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15994133376983486083061963 23991200065475229124592945)
                  ·
                    refine ⟨17993400049106421843444709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23991200065475229124592945 17993400049106421843444709)
                    ·
                      refine ⟨3373762509207454095645883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17993400049106421843444709 3373762509207454095645883)
                      ·
                        rfl

theorem cell23_6570379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 2, 4].length) (baseStart_6570379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570379 prefixEnd_6570379 := by exact prefixLift 6570379
  have htrace : WordTrace (prefixWord ++ tailWord_6570379) baseStart_6570379 baseEnd_6570379 := by
    simpa [prefixWord, tailWord_6570379, baseEnd_6570379] using wordTrace_append hprefix tailTrace_6570379
  have hstable : (prefixWord ++ tailWord_6570379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570379).length < 2 ^ (prefixWord ++ tailWord_6570379).sum := by decide
  have hdescent : baseEnd_6570379 < baseStart_6570379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570399 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 6, 1, 3]
def baseStart_6570399 : Nat := 118140960795 + 6570399 * 2 ^ 59
def prefixEnd_6570399 : Nat := 4983230072969 + 3 ^ 40 * 6570399 * 2
def baseEnd_6570399 : Nat := 3373772778820544017395791

theorem tailTrace_6570399 : CollatzResearch.WordTrace tailWord_6570399 prefixEnd_6570399 3373772778820544017395791 := by
  unfold tailWord_6570399
  simp only [CollatzResearch.WordTrace]
  refine ⟨239642138923574032656594251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159761425949049355104396167 239642138923574032656594251)
  ·
    refine ⟨359463208385361048984891377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239642138923574032656594251 359463208385361048984891377)
    ·
      refine ⟨269597406289020786738668533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359463208385361048984891377 269597406289020786738668533)
      ·
        refine ⟨25274756839595698756750175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269597406289020786738668533 25274756839595698756750175)
        ·
          refine ⟨37912135259393548135125263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25274756839595698756750175 37912135259393548135125263)
          ·
            refine ⟨56868202889090322202687895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37912135259393548135125263 56868202889090322202687895)
            ·
              refine ⟨85302304333635483304031843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56868202889090322202687895 85302304333635483304031843)
              ·
                refine ⟨127953456500453224956047765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85302304333635483304031843 127953456500453224956047765)
                ·
                  refine ⟨5997818273458744919814739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127953456500453224956047765 5997818273458744919814739)
                  ·
                    refine ⟨8996727410188117379722109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5997818273458744919814739 8996727410188117379722109)
                    ·
                      refine ⟨3373772778820544017395791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8996727410188117379722109 3373772778820544017395791)
                      ·
                        rfl

theorem cell23_6570399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_6570399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570399 prefixEnd_6570399 := by exact prefixLift 6570399
  have htrace : WordTrace (prefixWord ++ tailWord_6570399) baseStart_6570399 baseEnd_6570399 := by
    simpa [prefixWord, tailWord_6570399, baseEnd_6570399] using wordTrace_append hprefix tailTrace_6570399
  have hstable : (prefixWord ++ tailWord_6570399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570399).length < 2 ^ (prefixWord ++ tailWord_6570399).sum := by decide
  have hdescent : baseEnd_6570399 < baseStart_6570399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570400 : List Nat := [2, 1, 1, 4, 1, 5, 1, 3, 1, 2, 2]
def baseStart_6570400 : Nat := 118140960795 + 6570400 * 2 ^ 59
def prefixEnd_6570400 : Nat := 4983230072969 + 3 ^ 40 * 6570400 * 2
def baseEnd_6570400 : Nat := 3373773292301198513483287

theorem tailTrace_6570400 : CollatzResearch.WordTrace tailWord_6570400 prefixEnd_6570400 3373773292301198513483287 := by
  unfold tailWord_6570400
  simp only [CollatzResearch.WordTrace]
  refine ⟨119821087698285204913690327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159761450264380273218253769 119821087698285204913690327)
  ·
    refine ⟨179731631547427807370535491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119821087698285204913690327 179731631547427807370535491)
    ·
      refine ⟨269597447321141711055803237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179731631547427807370535491 269597447321141711055803237)
      ·
        refine ⟨50549521372714070822963107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269597447321141711055803237 50549521372714070822963107)
        ·
          refine ⟨75824282059071106234444661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50549521372714070822963107 75824282059071106234444661)
          ·
            refine ⟨7108526443037916209479187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75824282059071106234444661 7108526443037916209479187)
            ·
              refine ⟨10662789664556874314218781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7108526443037916209479187 10662789664556874314218781)
              ·
                refine ⟨3998546124208827867832043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10662789664556874314218781 3998546124208827867832043)
                ·
                  refine ⟨5997819186313241801748065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998546124208827867832043 5997819186313241801748065)
                  ·
                    refine ⟨4498364389734931351311049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5997819186313241801748065 4498364389734931351311049)
                    ·
                      refine ⟨3373773292301198513483287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4498364389734931351311049 3373773292301198513483287)
                      ·
                        rfl

theorem cell23_6570400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_6570400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570400 prefixEnd_6570400 := by exact prefixLift 6570400
  have htrace : WordTrace (prefixWord ++ tailWord_6570400) baseStart_6570400 baseEnd_6570400 := by
    simpa [prefixWord, tailWord_6570400, baseEnd_6570400] using wordTrace_append hprefix tailTrace_6570400
  have hstable : (prefixWord ++ tailWord_6570400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570400).length < 2 ^ (prefixWord ++ tailWord_6570400).sum := by decide
  have hdescent : baseEnd_6570400 < baseStart_6570400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570442 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_6570442 : Nat := 118140960795 + 6570442 * 2 ^ 59
def prefixEnd_6570442 : Nat := 4983230072969 + 3 ^ 40 * 6570442 * 2
def baseEnd_6570442 : Nat := 3373794858488687349158093

theorem tailTrace_6570442 : CollatzResearch.WordTrace tailWord_6570442 prefixEnd_6570442 3373794858488687349158093 := by
  unfold tailWord_6570442
  simp only [CollatzResearch.WordTrace]
  refine ⟨59910926815604562750102395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159762471508278834000273053 59910926815604562750102395)
  ·
    refine ⟨89866390223406844125153593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59910926815604562750102395 89866390223406844125153593)
    ·
      refine ⟨67399792667555133093865195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89866390223406844125153593 67399792667555133093865195)
      ·
        refine ⟨101099689001332699640797793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67399792667555133093865195 101099689001332699640797793)
        ·
          refine ⟨75824766750999524730598345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101099689001332699640797793 75824766750999524730598345)
          ·
            refine ⟨56868575063249643547948759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75824766750999524730598345 56868575063249643547948759)
            ·
              refine ⟨85302862594874465321923139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56868575063249643547948759 85302862594874465321923139)
              ·
                refine ⟨127954293892311697982884709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85302862594874465321923139 127954293892311697982884709)
                ·
                  refine ⟨23991430104808443371790883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127954293892311697982884709 23991430104808443371790883)
                  ·
                    refine ⟨35987145157212665057686325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23991430104808443371790883 35987145157212665057686325)
                    ·
                      refine ⟨3373794858488687349158093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35987145157212665057686325 3373794858488687349158093)
                      ·
                        rfl

theorem cell23_6570442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_6570442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570442 prefixEnd_6570442 := by exact prefixLift 6570442
  have htrace : WordTrace (prefixWord ++ tailWord_6570442) baseStart_6570442 baseEnd_6570442 := by
    simpa [prefixWord, tailWord_6570442, baseEnd_6570442] using wordTrace_append hprefix tailTrace_6570442
  have hstable : (prefixWord ++ tailWord_6570442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570442).length < 2 ^ (prefixWord ++ tailWord_6570442).sum := by decide
  have hdescent : baseEnd_6570442 < baseStart_6570442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570492 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 1, 7]
def baseStart_6570492 : Nat := 118140960795 + 6570492 * 2 ^ 59
def prefixEnd_6570492 : Nat := 4983230072969 + 3 ^ 40 * 6570492 * 2
def baseEnd_6570492 : Nat := 1124606844173804051177621

theorem tailTrace_6570492 : CollatzResearch.WordTrace tailWord_6570492 prefixEnd_6570492 1124606844173804051177621 := by
  unfold tailWord_6570492
  simp only [CollatzResearch.WordTrace]
  refine ⟨119822765456118554769864865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159763687274824739693153153 119822765456118554769864865)
  ·
    refine ⟨89867074092088916077398649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119822765456118554769864865 89867074092088916077398649)
    ·
      refine ⟨67400305569066687058048987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89867074092088916077398649 67400305569066687058048987)
      ·
        refine ⟨101100458353600030587073481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67400305569066687058048987 101100458353600030587073481)
        ·
          refine ⟨75825343765200022940305111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101100458353600030587073481 75825343765200022940305111)
          ·
            refine ⟨113738015647800034410457667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75825343765200022940305111 113738015647800034410457667)
            ·
              refine ⟨170607023471700051615686501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113738015647800034410457667 170607023471700051615686501)
              ·
                refine ⟨31988816900943759677941219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170607023471700051615686501 31988816900943759677941219)
                ·
                  refine ⟨47983225351415639516911829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31988816900943759677941219 47983225351415639516911829)
                  ·
                    refine ⟨1124606844173804051177621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47983225351415639516911829 1124606844173804051177621)
                    ·
                      rfl

theorem cell23_6570492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_6570492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570492 prefixEnd_6570492 := by exact prefixLift 6570492
  have htrace : WordTrace (prefixWord ++ tailWord_6570492) baseStart_6570492 baseEnd_6570492 := by
    simpa [prefixWord, tailWord_6570492, baseEnd_6570492] using wordTrace_append hprefix tailTrace_6570492
  have hstable : (prefixWord ++ tailWord_6570492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570492).length < 2 ^ (prefixWord ++ tailWord_6570492).sum := by decide
  have hdescent : baseEnd_6570492 < baseStart_6570492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570499 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 2, 5, 2]
def baseStart_6570499 : Nat := 118140960795 + 6570499 * 2 ^ 59
def prefixEnd_6570499 : Nat := 4983230072969 + 3 ^ 40 * 6570499 * 2
def baseEnd_6570499 : Nat := 3373824126885993626145331

theorem tailTrace_6570499 : CollatzResearch.WordTrace tailWord_6570499 prefixEnd_6570499 3373824126885993626145331 := by
  unfold tailWord_6570499
  simp only [CollatzResearch.WordTrace]
  refine ⟨239645786223211749735234551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159763857482141166490156367 239645786223211749735234551)
  ·
    refine ⟨359468679334817624602851827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239645786223211749735234551 359468679334817624602851827)
    ·
      refine ⟨539203019002226436904277741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359468679334817624602851827 539203019002226436904277741)
      ·
        refine ⟨202201132125834913839104153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 539203019002226436904277741 202201132125834913839104153)
        ·
          refine ⟨151650849094376185379328115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202201132125834913839104153 151650849094376185379328115)
          ·
            refine ⟨227476273641564278068992173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151650849094376185379328115 227476273641564278068992173)
            ·
              refine ⟨85303602615586604275872065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227476273641564278068992173 85303602615586604275872065)
              ·
                refine ⟨63977701961689953206904049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85303602615586604275872065 63977701961689953206904049)
                ·
                  refine ⟨47983276471267464905178037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63977701961689953206904049 47983276471267464905178037)
                  ·
                    refine ⟨4498432169181324834860441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47983276471267464905178037 4498432169181324834860441)
                    ·
                      refine ⟨3373824126885993626145331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4498432169181324834860441 3373824126885993626145331)
                      ·
                        rfl

theorem cell23_6570499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 5, 2].length) (baseStart_6570499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570499 prefixEnd_6570499 := by exact prefixLift 6570499
  have htrace : WordTrace (prefixWord ++ tailWord_6570499) baseStart_6570499 baseEnd_6570499 := by
    simpa [prefixWord, tailWord_6570499, baseEnd_6570499] using wordTrace_append hprefix tailTrace_6570499
  have hstable : (prefixWord ++ tailWord_6570499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570499).length < 2 ^ (prefixWord ++ tailWord_6570499).sum := by decide
  have hdescent : baseEnd_6570499 < baseStart_6570499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570529 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_6570529 : Nat := 118140960795 + 6570529 * 2 ^ 59
def prefixEnd_6570529 : Nat := 4983230072969 + 3 ^ 40 * 6570529 * 2
def baseEnd_6570529 : Nat := 3373839531305628508770193

theorem tailTrace_6570529 : CollatzResearch.WordTrace tailWord_6570529 prefixEnd_6570529 3373839531305628508770193 := by
  unfold tailWord_6570529
  simp only [CollatzResearch.WordTrace]
  refine ⟨239646880413103064858826641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159764586942068709905884427 239646880413103064858826641)
  ·
    refine ⟨179735160309827298644119981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239646880413103064858826641 179735160309827298644119981)
    ·
      refine ⟨67400685116185236991544993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179735160309827298644119981 67400685116185236991544993)
      ·
        refine ⟨50550513837138927743658745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67400685116185236991544993 50550513837138927743658745)
        ·
          refine ⟨37912885377854195807744059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50550513837138927743658745 37912885377854195807744059)
          ·
            refine ⟨56869328066781293711616089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37912885377854195807744059 56869328066781293711616089)
            ·
              refine ⟨42651996050085970283712067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56869328066781293711616089 42651996050085970283712067)
              ·
                refine ⟨63977994075128955425568101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42651996050085970283712067 63977994075128955425568101)
                ·
                  refine ⟨11995873889086679142294019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63977994075128955425568101 11995873889086679142294019)
                  ·
                    refine ⟨17993810833630018713441029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11995873889086679142294019 17993810833630018713441029)
                    ·
                      refine ⟨3373839531305628508770193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17993810833630018713441029 3373839531305628508770193)
                      ·
                        rfl

theorem cell23_6570529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_6570529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570529 prefixEnd_6570529 := by exact prefixLift 6570529
  have htrace : WordTrace (prefixWord ++ tailWord_6570529) baseStart_6570529 baseEnd_6570529 := by
    simpa [prefixWord, tailWord_6570529, baseEnd_6570529] using wordTrace_append hprefix tailTrace_6570529
  have hstable : (prefixWord ++ tailWord_6570529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570529).length < 2 ^ (prefixWord ++ tailWord_6570529).sum := by decide
  have hdescent : baseEnd_6570529 < baseStart_6570529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570541 : List Nat := [1, 5, 4, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6570541 : Nat := 118140960795 + 6570541 * 2 ^ 59
def prefixEnd_6570541 : Nat := 4983230072969 + 3 ^ 40 * 6570541 * 2
def baseEnd_6570541 : Nat := 3373845693073482461820139

theorem tailTrace_6570541 : CollatzResearch.WordTrace tailWord_6570541 prefixEnd_6570541 3373845693073482461820139 := by
  unfold tailWord_6570541
  simp only [CollatzResearch.WordTrace]
  refine ⟨239647318089059590908263477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159764878726039727272175651 239647318089059590908263477)
  ·
    refine ⟨22466936070849336647649701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239647318089059590908263477 22466936070849336647649701)
    ·
      refine ⟨4212550513284250621434319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22466936070849336647649701 4212550513284250621434319)
      ·
        refine ⟨6318825769926375932151479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4212550513284250621434319 6318825769926375932151479)
        ·
          refine ⟨9478238654889563898227219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6318825769926375932151479 9478238654889563898227219)
          ·
            refine ⟨14217357982334345847340829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9478238654889563898227219 14217357982334345847340829)
            ·
              refine ⟨5331509243375379692752811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14217357982334345847340829 5331509243375379692752811)
              ·
                refine ⟨7997263865063069539129217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5331509243375379692752811 7997263865063069539129217)
                ·
                  refine ⟨5997947898797302154346913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7997263865063069539129217 5997947898797302154346913)
                  ·
                    refine ⟨4498460924097976615760185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5997947898797302154346913 4498460924097976615760185)
                    ·
                      refine ⟨3373845693073482461820139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4498460924097976615760185 3373845693073482461820139)
                      ·
                        rfl

theorem cell23_6570541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6570541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570541 prefixEnd_6570541 := by exact prefixLift 6570541
  have htrace : WordTrace (prefixWord ++ tailWord_6570541) baseStart_6570541 baseEnd_6570541 := by
    simpa [prefixWord, tailWord_6570541, baseEnd_6570541] using wordTrace_append hprefix tailTrace_6570541
  have hstable : (prefixWord ++ tailWord_6570541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570541).length < 2 ^ (prefixWord ++ tailWord_6570541).sum := by decide
  have hdescent : baseEnd_6570541 < baseStart_6570541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570546 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2]
def baseStart_6570546 : Nat := 118140960795 + 6570546 * 2 ^ 59
def prefixEnd_6570546 : Nat := 4983230072969 + 3 ^ 40 * 6570546 * 2
def baseEnd_6570546 : Nat := 3373848260476754942257615

theorem tailTrace_6570546 : CollatzResearch.WordTrace tailWord_6570546 prefixEnd_6570546 3373848260476754942257615 := by
  unfold tailWord_6570546
  simp only [CollatzResearch.WordTrace]
  refine ⟨59911875113510369190548873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159765000302694317841463661 59911875113510369190548873)
  ·
    refine ⟨44933906335132776892911655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59911875113510369190548873 44933906335132776892911655)
    ·
      refine ⟨67400859502699165339367483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44933906335132776892911655 67400859502699165339367483)
      ·
        refine ⟨101101289254048748009051225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67400859502699165339367483 101101289254048748009051225)
        ·
          refine ⟨75825966940536561006788419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101101289254048748009051225 75825966940536561006788419)
          ·
            refine ⟨113738950410804841510182629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75825966940536561006788419 113738950410804841510182629)
            ·
              refine ⟨21326053202025907783159243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113738950410804841510182629 21326053202025907783159243)
              ·
                refine ⟨31989079803038861674738865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21326053202025907783159243 31989079803038861674738865)
                ·
                  refine ⟨23991809852279146256054149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31989079803038861674738865 23991809852279146256054149)
                  ·
                    refine ⟨4498464347302339923010153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23991809852279146256054149 4498464347302339923010153)
                    ·
                      refine ⟨3373848260476754942257615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4498464347302339923010153 3373848260476754942257615)
                      ·
                        rfl

theorem cell23_6570546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_6570546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570546 prefixEnd_6570546 := by exact prefixLift 6570546
  have htrace : WordTrace (prefixWord ++ tailWord_6570546) baseStart_6570546 baseEnd_6570546 := by
    simpa [prefixWord, tailWord_6570546, baseEnd_6570546] using wordTrace_append hprefix tailTrace_6570546
  have hstable : (prefixWord ++ tailWord_6570546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570546).length < 2 ^ (prefixWord ++ tailWord_6570546).sum := by decide
  have hdescent : baseEnd_6570546 < baseStart_6570546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570549 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_6570549 : Nat := 118140960795 + 6570549 * 2 ^ 59
def prefixEnd_6570549 : Nat := 4983230072969 + 3 ^ 40 * 6570549 * 2
def baseEnd_6570549 : Nat := 3373849800918718430520101

theorem tailTrace_6570549 : CollatzResearch.WordTrace tailWord_6570549 prefixEnd_6570549 3373849800918718430520101 := by
  unfold tailWord_6570549
  simp only [CollatzResearch.WordTrace]
  refine ⟨239647609873030608274554701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159765073248687072183036467 239647609873030608274554701)
  ·
    refine ⟨89867853702386478102958013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239647609873030608274554701 89867853702386478102958013)
    ·
      refine ⟨33700445138394929288609255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89867853702386478102958013 33700445138394929288609255)
      ·
        refine ⟨50550667707592393932913883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33700445138394929288609255 50550667707592393932913883)
        ·
          refine ⟨75826001561388590899370825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50550667707592393932913883 75826001561388590899370825)
          ·
            refine ⟨56869501171041443174528119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75826001561388590899370825 56869501171041443174528119)
            ·
              refine ⟨85304251756562164761792179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56869501171041443174528119 85304251756562164761792179)
              ·
                refine ⟨127956377634843247142688269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85304251756562164761792179 127956377634843247142688269)
                ·
                  refine ⟨47983641613066217678508101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127956377634843247142688269 47983641613066217678508101)
                  ·
                    refine ⟨8996932802449915814720269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47983641613066217678508101 8996932802449915814720269)
                    ·
                      refine ⟨3373849800918718430520101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8996932802449915814720269 3373849800918718430520101)
                      ·
                        rfl

theorem cell23_6570549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_6570549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570549 prefixEnd_6570549 := by exact prefixLift 6570549
  have htrace : WordTrace (prefixWord ++ tailWord_6570549) baseStart_6570549 baseEnd_6570549 := by
    simpa [prefixWord, tailWord_6570549, baseEnd_6570549] using wordTrace_append hprefix tailTrace_6570549
  have hstable : (prefixWord ++ tailWord_6570549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570549).length < 2 ^ (prefixWord ++ tailWord_6570549).sum := by decide
  have hdescent : baseEnd_6570549 < baseStart_6570549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570556 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 3, 4]
def baseStart_6570556 : Nat := 118140960795 + 6570556 * 2 ^ 59
def prefixEnd_6570556 : Nat := 4983230072969 + 3 ^ 40 * 6570556 * 2
def baseEnd_6570556 : Nat := 1124617798427766634377523

theorem tailTrace_6570556 : CollatzResearch.WordTrace tailWord_6570556 prefixEnd_6570556 1124617798427766634377523 := by
  unfold tailWord_6570556
  simp only [CollatzResearch.WordTrace]
  refine ⟨119823932592002624235029761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159765243456003498980039681 119823932592002624235029761)
  ·
    refine ⟨89867949444001968176272321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119823932592002624235029761 89867949444001968176272321)
    ·
      refine ⟨67400962083001476132204241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89867949444001968176272321 67400962083001476132204241)
      ·
        refine ⟨50550721562251107099153181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67400962083001476132204241 50550721562251107099153181)
        ·
          refine ⟨18956520585844165162182443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50550721562251107099153181 18956520585844165162182443)
          ·
            refine ⟨28434780878766247743273665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18956520585844165162182443 28434780878766247743273665)
            ·
              refine ⟨21326085659074685807455249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28434780878766247743273665 21326085659074685807455249)
              ·
                refine ⟨15994564244306014355591437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21326085659074685807455249 15994564244306014355591437)
                ·
                  refine ⟨5997961591614755383346789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15994564244306014355591437 5997961591614755383346789)
                  ·
                    refine ⟨1124617798427766634377523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5997961591614755383346789 1124617798427766634377523)
                    ·
                      rfl

theorem cell23_6570556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_6570556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570556 prefixEnd_6570556 := by exact prefixLift 6570556
  have htrace : WordTrace (prefixWord ++ tailWord_6570556) baseStart_6570556 baseEnd_6570556 := by
    simpa [prefixWord, tailWord_6570556, baseEnd_6570556] using wordTrace_append hprefix tailTrace_6570556
  have hstable : (prefixWord ++ tailWord_6570556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570556).length < 2 ^ (prefixWord ++ tailWord_6570556).sum := by decide
  have hdescent : baseEnd_6570556 < baseStart_6570556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570564 : List Nat := [2, 3, 5, 1, 2, 1, 1, 3, 5]
def baseStart_6570564 : Nat := 118140960795 + 6570564 * 2 ^ 59
def prefixEnd_6570564 : Nat := 4983230072969 + 3 ^ 40 * 6570564 * 2
def baseEnd_6570564 : Nat := 374873055903170652425837

theorem tailTrace_6570564 : CollatzResearch.WordTrace tailWord_6570564 prefixEnd_6570564 374873055903170652425837 := by
  unfold tailWord_6570564
  simp only [CollatzResearch.WordTrace]
  refine ⟨119824078483988132918175373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159765437978650843890900497 119824078483988132918175373)
  ·
    refine ⟨44934029431495549844315765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119824078483988132918175373 44934029431495549844315765)
    ·
      refine ⟨4212565259202707797904603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44934029431495549844315765 4212565259202707797904603)
      ·
        refine ⟨6318847888804061696856905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4212565259202707797904603 6318847888804061696856905)
        ·
          refine ⟨4739135916603046272642679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6318847888804061696856905 4739135916603046272642679)
          ·
            refine ⟨7108703874904569408964019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4739135916603046272642679 7108703874904569408964019)
            ·
              refine ⟨10663055812356854113446029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7108703874904569408964019 10663055812356854113446029)
              ·
                refine ⟨3998645929633820292542261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10663055812356854113446029 3998645929633820292542261)
                ·
                  refine ⟨374873055903170652425837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3998645929633820292542261 374873055903170652425837)
                  ·
                    rfl

theorem cell23_6570564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_6570564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570564 prefixEnd_6570564 := by exact prefixLift 6570564
  have htrace : WordTrace (prefixWord ++ tailWord_6570564) baseStart_6570564 baseEnd_6570564 := by
    simpa [prefixWord, tailWord_6570564, baseEnd_6570564] using wordTrace_append hprefix tailTrace_6570564
  have hstable : (prefixWord ++ tailWord_6570564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570564).length < 2 ^ (prefixWord ++ tailWord_6570564).sum := by decide
  have hdescent : baseEnd_6570564 < baseStart_6570564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570599 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 3, 5]
def baseStart_6570599 : Nat := 118140960795 + 6570599 * 2 ^ 59
def prefixEnd_6570599 : Nat := 4983230072969 + 3 ^ 40 * 6570599 * 2
def baseEnd_6570599 : Nat := 1124625158317147744964957

theorem tailTrace_6570599 : CollatzResearch.WordTrace tailWord_6570599 prefixEnd_6570599 1124625158317147744964957 := by
  unfold tailWord_6570599
  simp only [CollatzResearch.WordTrace]
  refine ⟨239649433522849466813874851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159766289015232977875916567 239649433522849466813874851)
  ·
    refine ⟨359474150284274200220812277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239649433522849466813874851 359474150284274200220812277)
    ·
      refine ⟨33700701589150706270701151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 359474150284274200220812277 33700701589150706270701151)
      ·
        refine ⟨50551052383726059406051727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33700701589150706270701151 50551052383726059406051727)
        ·
          refine ⟨75826578575589089109077591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50551052383726059406051727 75826578575589089109077591)
          ·
            refine ⟨113739867863383633663616387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75826578575589089109077591 113739867863383633663616387)
            ·
              refine ⟨170609801795075450495424581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113739867863383633663616387 170609801795075450495424581)
              ·
                refine ⟨31989337836576646967892109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170609801795075450495424581 31989337836576646967892109)
                ·
                  refine ⟨11996001688716242612959541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31989337836576646967892109 11996001688716242612959541)
                  ·
                    refine ⟨1124625158317147744964957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11996001688716242612959541 1124625158317147744964957)
                    ·
                      rfl

theorem cell23_6570599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_6570599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570599 prefixEnd_6570599 := by exact prefixLift 6570599
  have htrace : WordTrace (prefixWord ++ tailWord_6570599) baseStart_6570599 baseEnd_6570599 := by
    simpa [prefixWord, tailWord_6570599, baseEnd_6570599] using wordTrace_append hprefix tailTrace_6570599
  have hstable : (prefixWord ++ tailWord_6570599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570599).length < 2 ^ (prefixWord ++ tailWord_6570599).sum := by decide
  have hdescent : baseEnd_6570599 < baseStart_6570599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570629 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 3, 6]
def baseStart_6570629 : Nat := 118140960795 + 6570629 * 2 ^ 59
def prefixEnd_6570629 : Nat := 4983230072969 + 3 ^ 40 * 6570629 * 2
def baseEnd_6570629 : Nat := 1124630293123692705839911

theorem tailTrace_6570629 : CollatzResearch.WordTrace tailWord_6570629 prefixEnd_6570629 1124630293123692705839911 := by
  unfold tailWord_6570629
  simp only [CollatzResearch.WordTrace]
  refine ⟨239650527712740781937466941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159767018475160521291644627 239650527712740781937466941)
  ·
    refine ⟨89868947892277793226550103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239650527712740781937466941 89868947892277793226550103)
    ·
      refine ⟨134803421838416689839825155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89868947892277793226550103 134803421838416689839825155)
      ·
        refine ⟨202205132757625034759737733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134803421838416689839825155 202205132757625034759737733)
        ·
          refine ⟨37913462392054694017450825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202205132757625034759737733 37913462392054694017450825)
          ·
            refine ⟨28435096794041020513088119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37913462392054694017450825 28435096794041020513088119)
            ·
              refine ⟨42652645191061530769632179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28435096794041020513088119 42652645191061530769632179)
              ·
                refine ⟨63978967786592296154448269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42652645191061530769632179 63978967786592296154448269)
                ·
                  refine ⟨23992112919972111057918101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63978967786592296154448269 23992112919972111057918101)
                  ·
                    refine ⟨1124630293123692705839911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23992112919972111057918101 1124630293123692705839911)
                    ·
                      rfl

theorem cell23_6570629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_6570629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570629 prefixEnd_6570629 := by exact prefixLift 6570629
  have htrace : WordTrace (prefixWord ++ tailWord_6570629) baseStart_6570629 baseEnd_6570629 := by
    simpa [prefixWord, tailWord_6570629, baseEnd_6570629] using wordTrace_append hprefix tailTrace_6570629
  have hstable : (prefixWord ++ tailWord_6570629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570629).length < 2 ^ (prefixWord ++ tailWord_6570629).sum := by decide
  have hdescent : baseEnd_6570629 < baseStart_6570629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570649 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 4]
def baseStart_6570649 : Nat := 118140960795 + 6570649 * 2 ^ 59
def prefixEnd_6570649 : Nat := 4983230072969 + 3 ^ 40 * 6570649 * 2
def baseEnd_6570649 : Nat := 3373901148984168039269641

theorem tailTrace_6570649 : CollatzResearch.WordTrace tailWord_6570649 prefixEnd_6570649 3373901148984168039269641 := by
  unfold tailWord_6570649
  simp only [CollatzResearch.WordTrace]
  refine ⟨239651257172668325353195001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159767504781778883568796667 239651257172668325353195001)
  ·
    refine ⟨179738442879501244014896251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239651257172668325353195001 179738442879501244014896251)
    ·
      refine ⟨269607664319251866022344377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179738442879501244014896251 269607664319251866022344377)
      ·
        refine ⟨202205748239438899516758283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269607664319251866022344377 202205748239438899516758283)
        ·
          refine ⟨303308622359158349275137425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202205748239438899516758283 303308622359158349275137425)
          ·
            refine ⟨227481466769368761956353069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303308622359158349275137425 227481466769368761956353069)
            ·
              refine ⟨85305550038513285733632401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227481466769368761956353069 85305550038513285733632401)
              ·
                refine ⟨63979162528884964300224301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85305550038513285733632401 63979162528884964300224301)
                ·
                  refine ⟨23992185948331861612584113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63979162528884964300224301 23992185948331861612584113)
                  ·
                    refine ⟨17994139461248896209438085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23992185948331861612584113 17994139461248896209438085)
                    ·
                      refine ⟨3373901148984168039269641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17994139461248896209438085 3373901148984168039269641)
                      ·
                        rfl

theorem cell23_6570649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_6570649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570649 prefixEnd_6570649 := by exact prefixLift 6570649
  have htrace : WordTrace (prefixWord ++ tailWord_6570649) baseStart_6570649 baseEnd_6570649 := by
    simpa [prefixWord, tailWord_6570649, baseEnd_6570649] using wordTrace_append hprefix tailTrace_6570649
  have hstable : (prefixWord ++ tailWord_6570649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570649).length < 2 ^ (prefixWord ++ tailWord_6570649).sum := by decide
  have hdescent : baseEnd_6570649 < baseStart_6570649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570687 : List Nat := [1, 1, 2, 2, 2, 5, 2, 3, 1, 2, 2]
def baseStart_6570687 : Nat := 118140960795 + 6570687 * 2 ^ 59
def prefixEnd_6570687 : Nat := 4983230072969 + 3 ^ 40 * 6570687 * 2
def baseEnd_6570687 : Nat := 3373920661249038890594467

theorem tailTrace_6570687 : CollatzResearch.WordTrace tailWord_6570687 prefixEnd_6570687 3373920661249038890594467 := by
  unfold tailWord_6570687
  simp only [CollatzResearch.WordTrace]
  refine ⟨239652643146530657843078315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159768428764353771895385543 239652643146530657843078315)
  ·
    refine ⟨359478964719795986764617473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239652643146530657843078315 359478964719795986764617473)
    ·
      refine ⟨269609223539846990073463105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359478964719795986764617473 269609223539846990073463105)
      ·
        refine ⟨202206917654885242555097329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269609223539846990073463105 202206917654885242555097329)
        ·
          refine ⟨151655188241163931916322997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202206917654885242555097329 151655188241163931916322997)
          ·
            refine ⟨14217673897609118617155281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151655188241163931916322997 14217673897609118617155281)
            ·
              refine ⟨10663255423206838962866461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14217673897609118617155281 10663255423206838962866461)
              ·
                refine ⟨3998720783702564611074923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10663255423206838962866461 3998720783702564611074923)
                ·
                  refine ⟨5998081175553846916612385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998720783702564611074923 5998081175553846916612385)
                  ·
                    refine ⟨4498560881665385187459289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5998081175553846916612385 4498560881665385187459289)
                    ·
                      refine ⟨3373920661249038890594467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4498560881665385187459289 3373920661249038890594467)
                      ·
                        rfl

theorem cell23_6570687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3, 1, 2, 2].length) (baseStart_6570687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570687 prefixEnd_6570687 := by exact prefixLift 6570687
  have htrace : WordTrace (prefixWord ++ tailWord_6570687) baseStart_6570687 baseEnd_6570687 := by
    simpa [prefixWord, tailWord_6570687, baseEnd_6570687] using wordTrace_append hprefix tailTrace_6570687
  have hstable : (prefixWord ++ tailWord_6570687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570687).length < 2 ^ (prefixWord ++ tailWord_6570687).sum := by decide
  have hdescent : baseEnd_6570687 < baseStart_6570687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570760 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 4, 2, 2]
def baseStart_6570760 : Nat := 118140960795 + 6570760 * 2 ^ 59
def prefixEnd_6570760 : Nat := 4983230072969 + 3 ^ 40 * 6570760 * 2
def baseEnd_6570760 : Nat := 3373958145336817104981631

theorem tailTrace_6570760 : CollatzResearch.WordTrace tailWord_6570760 prefixEnd_6570760 3373958145336817104981631 := by
  unfold tailWord_6570760
  simp only [CollatzResearch.WordTrace]
  refine ⟨119827652837633095655242867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159770203783510794206990489 119827652837633095655242867)
  ·
    refine ⟨179741479256449643482864301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119827652837633095655242867 179741479256449643482864301)
    ·
      refine ⟨67403054721168616306074113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179741479256449643482864301 67403054721168616306074113)
      ·
        refine ⟨50552291040876462229555585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67403054721168616306074113 50552291040876462229555585)
        ·
          refine ⟨37914218280657346672166689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50552291040876462229555585 37914218280657346672166689)
          ·
            refine ⟨28435663710493010004125017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37914218280657346672166689 28435663710493010004125017)
            ·
              refine ⟨21326747782869757503093763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28435663710493010004125017 21326747782869757503093763)
              ·
                refine ⟨31990121674304636254640645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21326747782869757503093763 31990121674304636254640645)
                ·
                  refine ⟨5998147813932119297745121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31990121674304636254640645 5998147813932119297745121)
                  ·
                    refine ⟨4498610860449089473308841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5998147813932119297745121 4498610860449089473308841)
                    ·
                      refine ⟨3373958145336817104981631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4498610860449089473308841 3373958145336817104981631)
                      ·
                        rfl

theorem cell23_6570760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_6570760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570760 prefixEnd_6570760 := by exact prefixLift 6570760
  have htrace : WordTrace (prefixWord ++ tailWord_6570760) baseStart_6570760 baseEnd_6570760 := by
    simpa [prefixWord, tailWord_6570760, baseEnd_6570760] using wordTrace_append hprefix tailTrace_6570760
  have hstable : (prefixWord ++ tailWord_6570760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570760).length < 2 ^ (prefixWord ++ tailWord_6570760).sum := by decide
  have hdescent : baseEnd_6570760 < baseStart_6570760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570776 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 1, 5, 3]
def baseStart_6570776 : Nat := 118140960795 + 6570776 * 2 ^ 59
def prefixEnd_6570776 : Nat := 4983230072969 + 3 ^ 40 * 6570776 * 2
def baseEnd_6570776 : Nat := 3373966361027289042381557

theorem tailTrace_6570776 : CollatzResearch.WordTrace tailWord_6570776 prefixEnd_6570776 3373966361027289042381557 := by
  unfold tailWord_6570776
  simp only [CollatzResearch.WordTrace]
  refine ⟨119827944621604113021534091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159770592828805484028712121 119827944621604113021534091)
  ·
    refine ⟨179741916932406169532301137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119827944621604113021534091 179741916932406169532301137)
    ·
      refine ⟨134806437699304627149225853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179741916932406169532301137 134806437699304627149225853)
      ·
        refine ⟨50552414137239235180959695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134806437699304627149225853 50552414137239235180959695)
        ·
          refine ⟨75828621205858852771439543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50552414137239235180959695 75828621205858852771439543)
          ·
            refine ⟨113742931808788279157159315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75828621205858852771439543 113742931808788279157159315)
            ·
              refine ⟨170614397713182418735738973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113742931808788279157159315 170614397713182418735738973)
              ·
                refine ⟨63980399142443407025902115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170614397713182418735738973 63980399142443407025902115)
                ·
                  refine ⟨95970598713665110538853173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63980399142443407025902115 95970598713665110538853173)
                  ·
                    refine ⟨8997243629406104113017485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95970598713665110538853173 8997243629406104113017485)
                    ·
                      refine ⟨3373966361027289042381557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8997243629406104113017485 3373966361027289042381557)
                      ·
                        rfl

theorem cell23_6570776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_6570776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570776 prefixEnd_6570776 := by exact prefixLift 6570776
  have htrace : WordTrace (prefixWord ++ tailWord_6570776) baseStart_6570776 baseEnd_6570776 := by
    simpa [prefixWord, tailWord_6570776, baseEnd_6570776] using wordTrace_append hprefix tailTrace_6570776
  have hstable : (prefixWord ++ tailWord_6570776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570776).length < 2 ^ (prefixWord ++ tailWord_6570776).sum := by decide
  have hdescent : baseEnd_6570776 < baseStart_6570776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570781 : List Nat := [1, 4, 2, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_6570781 : Nat := 118140960795 + 6570781 * 2 ^ 59
def prefixEnd_6570781 : Nat := 4983230072969 + 3 ^ 40 * 6570781 * 2
def baseEnd_6570781 : Nat := 3373968928430561522819035

theorem tailTrace_6570781 : CollatzResearch.WordTrace tailWord_6570781 prefixEnd_6570781 3373968928430561522819035 := by
  unfold tailWord_6570781
  simp only [CollatzResearch.WordTrace]
  refine ⟨239656071608190111897000197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159770714405460074598000131 239656071608190111897000197)
  ·
    refine ⟨44935513426535645980687537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239656071608190111897000197 44935513426535645980687537)
    ·
      refine ⟨33701635069901734485515653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44935513426535645980687537 33701635069901734485515653)
      ·
        refine ⟨6319056575606575216034185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33701635069901734485515653 6319056575606575216034185)
        ·
          refine ⟨4739292431704931412025639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6319056575606575216034185 4739292431704931412025639)
          ·
            refine ⟨7108938647557397118038459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4739292431704931412025639 7108938647557397118038459)
            ·
              refine ⟨10663407971336095677057689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7108938647557397118038459 10663407971336095677057689)
              ·
                refine ⟨7997555978502071757793267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10663407971336095677057689 7997555978502071757793267)
                ·
                  refine ⟨11996333967753107636689901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7997555978502071757793267 11996333967753107636689901)
                  ·
                    refine ⟨4498625237907415363758713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11996333967753107636689901 4498625237907415363758713)
                    ·
                      refine ⟨3373968928430561522819035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4498625237907415363758713 3373968928430561522819035)
                      ·
                        rfl

theorem cell23_6570781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_6570781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570781 prefixEnd_6570781 := by exact prefixLift 6570781
  have htrace : WordTrace (prefixWord ++ tailWord_6570781) baseStart_6570781 baseEnd_6570781 := by
    simpa [prefixWord, tailWord_6570781, baseEnd_6570781] using wordTrace_append hprefix tailTrace_6570781
  have hstable : (prefixWord ++ tailWord_6570781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570781).length < 2 ^ (prefixWord ++ tailWord_6570781).sum := by decide
  have hdescent : baseEnd_6570781 < baseStart_6570781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570817 : List Nat := [1, 2, 5, 3, 1, 1, 1, 4, 5]
def baseStart_6570817 : Nat := 118140960795 + 6570817 * 2 ^ 59
def prefixEnd_6570817 : Nat := 4983230072969 + 3 ^ 40 * 6570817 * 2
def baseEnd_6570817 : Nat := 374887490414902597996541

theorem tailTrace_6570817 : CollatzResearch.WordTrace tailWord_6570817 prefixEnd_6570817 374887490414902597996541 := by
  unfold tailWord_6570817
  simp only [CollatzResearch.WordTrace]
  refine ⟨239657384636059690045310705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159771589757373126696873803 239657384636059690045310705)
  ·
    refine ⟨179743038477044767533983029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239657384636059690045310705 179743038477044767533983029)
    ·
      refine ⟨16850909857222946956310909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179743038477044767533983029 16850909857222946956310909)
      ·
        refine ⟨6319091196458605108616591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16850909857222946956310909 6319091196458605108616591)
        ·
          refine ⟨9478636794687907662924887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6319091196458605108616591 9478636794687907662924887)
          ·
            refine ⟨14217955192031861494387331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9478636794687907662924887 14217955192031861494387331)
            ·
              refine ⟨21326932788047792241580997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14217955192031861494387331 21326932788047792241580997)
              ·
                refine ⟨3998799897758961045296437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21326932788047792241580997 3998799897758961045296437)
                ·
                  refine ⟨374887490414902597996541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3998799897758961045296437 374887490414902597996541)
                  ·
                    rfl

theorem cell23_6570817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 5].length) (baseStart_6570817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570817 prefixEnd_6570817 := by exact prefixLift 6570817
  have htrace : WordTrace (prefixWord ++ tailWord_6570817) baseStart_6570817 baseEnd_6570817 := by
    simpa [prefixWord, tailWord_6570817, baseEnd_6570817] using wordTrace_append hprefix tailTrace_6570817
  have hstable : (prefixWord ++ tailWord_6570817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570817).length < 2 ^ (prefixWord ++ tailWord_6570817).sum := by decide
  have hdescent : baseEnd_6570817 < baseStart_6570817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570850 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_6570850 : Nat := 118140960795 + 6570850 * 2 ^ 59
def prefixEnd_6570850 : Nat := 4983230072969 + 3 ^ 40 * 6570850 * 2
def baseEnd_6570850 : Nat := 3374004358595721752856217

theorem tailTrace_6570850 : CollatzResearch.WordTrace tailWord_6570850 prefixEnd_6570850 3374004358595721752856217 := by
  unfold tailWord_6570850
  simp only [CollatzResearch.WordTrace]
  refine ⟨59914647061235034170315501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159772392163293424454174669 59914647061235034170315501)
  ·
    refine ⟨22467992647963137813868313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59914647061235034170315501 22467992647963137813868313)
    ·
      refine ⟨16850994485972353360401235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22467992647963137813868313 16850994485972353360401235)
      ·
        refine ⟨25276491728958530040601853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16850994485972353360401235 25276491728958530040601853)
        ·
          refine ⟨9478684398359448765225695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25276491728958530040601853 9478684398359448765225695)
          ·
            refine ⟨14218026597539173147838543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9478684398359448765225695 14218026597539173147838543)
            ·
              refine ⟨21327039896308759721757815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14218026597539173147838543 21327039896308759721757815)
              ·
                refine ⟨31990559844463139582636723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21327039896308759721757815 31990559844463139582636723)
                ·
                  refine ⟨47985839766694709373955085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31990559844463139582636723 47985839766694709373955085)
                  ·
                    refine ⟨17994689912510516015233157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47985839766694709373955085 17994689912510516015233157)
                    ·
                      refine ⟨3374004358595721752856217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17994689912510516015233157 3374004358595721752856217)
                      ·
                        rfl

theorem cell23_6570850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_6570850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570850 prefixEnd_6570850 := by exact prefixLift 6570850
  have htrace : WordTrace (prefixWord ++ tailWord_6570850) baseStart_6570850 baseEnd_6570850 := by
    simpa [prefixWord, tailWord_6570850, baseEnd_6570850] using wordTrace_append hprefix tailTrace_6570850
  have hstable : (prefixWord ++ tailWord_6570850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570850).length < 2 ^ (prefixWord ++ tailWord_6570850).sum := by decide
  have hdescent : baseEnd_6570850 < baseStart_6570850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570873 : List Nat := [1, 2, 1, 3, 2, 3, 3, 2, 6]
def baseStart_6570873 : Nat := 118140960795 + 6570873 * 2 ^ 59
def prefixEnd_6570873 : Nat := 4983230072969 + 3 ^ 40 * 6570873 * 2
def baseEnd_6570873 : Nat := 374890685405641684763179

theorem tailTrace_6570873 : CollatzResearch.WordTrace tailWord_6570873 prefixEnd_6570873 374890685405641684763179 := by
  unfold tailWord_6570873
  simp only [CollatzResearch.WordTrace]
  refine ⟨239659427123856811609349273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159772951415904541072899515 239659427123856811609349273)
  ·
    refine ⟨179744570342892608707011955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239659427123856811609349273 179744570342892608707011955)
    ·
      refine ⟨269616855514338913060517933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179744570342892608707011955 269616855514338913060517933)
      ·
        refine ⟨101106320817877092397694225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269616855514338913060517933 101106320817877092397694225)
        ·
          refine ⟨75829740613407819298270669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101106320817877092397694225 75829740613407819298270669)
          ·
            refine ⟨28436152730027932236851501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75829740613407819298270669 28436152730027932236851501)
            ·
              refine ⟨10663557273760474588819313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28436152730027932236851501 10663557273760474588819313)
              ·
                refine ⟨7997667955320355941614485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10663557273760474588819313 7997667955320355941614485)
                ·
                  refine ⟨374890685405641684763179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7997667955320355941614485 374890685405641684763179)
                  ·
                    rfl

theorem cell23_6570873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 6].length) (baseStart_6570873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570873 prefixEnd_6570873 := by exact prefixLift 6570873
  have htrace : WordTrace (prefixWord ++ tailWord_6570873) baseStart_6570873 baseEnd_6570873 := by
    simpa [prefixWord, tailWord_6570873, baseEnd_6570873] using wordTrace_append hprefix tailTrace_6570873
  have hstable : (prefixWord ++ tailWord_6570873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570873).length < 2 ^ (prefixWord ++ tailWord_6570873).sum := by decide
  have hdescent : baseEnd_6570873 < baseStart_6570873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570923 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 1, 8, 2]
def baseStart_6570923 : Nat := 118140960795 + 6570923 * 2 ^ 59
def prefixEnd_6570923 : Nat := 4983230072969 + 3 ^ 40 * 6570923 * 2
def baseEnd_6570923 : Nat := 3374041842683499967243381

theorem tailTrace_6570923 : CollatzResearch.WordTrace tailWord_6570923 prefixEnd_6570923 3374041842683499967243381 := by
  unfold tailWord_6570923
  simp only [CollatzResearch.WordTrace]
  refine ⟨239661250773675670148669423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159774167182450446765779615 239661250773675670148669423)
  ·
    refine ⟨359491876160513505223004135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239661250773675670148669423 359491876160513505223004135)
    ·
      refine ⟨539237814240770257834506203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359491876160513505223004135 539237814240770257834506203)
      ·
        refine ⟨808856721361155386751759305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539237814240770257834506203 808856721361155386751759305)
        ·
          refine ⟨606642541020866540063819479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 808856721361155386751759305 606642541020866540063819479)
          ·
            refine ⟨909963811531299810095729219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606642541020866540063819479 909963811531299810095729219)
            ·
              refine ⟨1364945717296949715143593829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909963811531299810095729219 1364945717296949715143593829)
              ·
                refine ⟨255927321993178071589423843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1364945717296949715143593829 255927321993178071589423843)
                ·
                  refine ⟨383890982989767107384135765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255927321993178071589423843 383890982989767107384135765)
                  ·
                    refine ⟨4498722456911333289657841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 383890982989767107384135765 4498722456911333289657841)
                    ·
                      refine ⟨3374041842683499967243381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4498722456911333289657841 3374041842683499967243381)
                      ·
                        rfl

theorem cell23_6570923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 8, 2].length) (baseStart_6570923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570923 prefixEnd_6570923 := by exact prefixLift 6570923
  have htrace : WordTrace (prefixWord ++ tailWord_6570923) baseStart_6570923 baseEnd_6570923 := by
    simpa [prefixWord, tailWord_6570923, baseEnd_6570923] using wordTrace_append hprefix tailTrace_6570923
  have hstable : (prefixWord ++ tailWord_6570923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570923).length < 2 ^ (prefixWord ++ tailWord_6570923).sum := by decide
  have hdescent : baseEnd_6570923 < baseStart_6570923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570970 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4]
def baseStart_6570970 : Nat := 118140960795 + 6570970 * 2 ^ 59
def prefixEnd_6570970 : Nat := 4983230072969 + 3 ^ 40 * 6570970 * 2
def baseEnd_6570970 : Nat := 3374065976274261283355665

theorem tailTrace_6570970 : CollatzResearch.WordTrace tailWord_6570970 prefixEnd_6570970 3374065976274261283355665 := by
  unfold tailWord_6570970
  simp only [CollatzResearch.WordTrace]
  refine ⟨59915741251126349293907591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159775310003003598117086909 59915741251126349293907591)
  ·
    refine ⟨89873611876689523940861387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59915741251126349293907591 89873611876689523940861387)
    ·
      refine ⟨134810417815034285911292081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89873611876689523940861387 134810417815034285911292081)
      ·
        refine ⟨101107813361275714433469061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134810417815034285911292081 101107813361275714433469061)
        ·
          refine ⟨18957715005239196456275449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101107813361275714433469061 18957715005239196456275449)
          ·
            refine ⟨14218286253929397342206587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18957715005239196456275449 14218286253929397342206587)
            ·
              refine ⟨21327429380894096013309881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14218286253929397342206587 21327429380894096013309881)
              ·
                refine ⟨15995572035670572009982411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21327429380894096013309881 15995572035670572009982411)
                ·
                  refine ⟨23993358053505858014973617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15995572035670572009982411 23993358053505858014973617)
                  ·
                    refine ⟨17995018540129393511230213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23993358053505858014973617 17995018540129393511230213)
                    ·
                      refine ⟨3374065976274261283355665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17995018540129393511230213 3374065976274261283355665)
                      ·
                        rfl

theorem cell23_6570970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_6570970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570970 prefixEnd_6570970 := by exact prefixLift 6570970
  have htrace : WordTrace (prefixWord ++ tailWord_6570970) baseStart_6570970 baseEnd_6570970 := by
    simpa [prefixWord, tailWord_6570970, baseEnd_6570970] using wordTrace_append hprefix tailTrace_6570970
  have hstable : (prefixWord ++ tailWord_6570970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570970).length < 2 ^ (prefixWord ++ tailWord_6570970).sum := by decide
  have hdescent : baseEnd_6570970 < baseStart_6570970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570991 : List Nat := [1, 1, 2, 1, 4, 3, 4, 2, 1, 2, 2]
def baseStart_6570991 : Nat := 118140960795 + 6570991 * 2 ^ 59
def prefixEnd_6570991 : Nat := 4983230072969 + 3 ^ 40 * 6570991 * 2
def baseEnd_6570991 : Nat := 3374076759368005701193069

theorem tailTrace_6570991 : CollatzResearch.WordTrace tailWord_6570991 prefixEnd_6570991 3374076759368005701193069 := by
  unfold tailWord_6570991
  simp only [CollatzResearch.WordTrace]
  refine ⟨239663730937429317762144827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159775820624952878508096551 239663730937429317762144827)
  ·
    refine ⟨359495596406143976643217241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239663730937429317762144827 359495596406143976643217241)
    ·
      refine ⟨269621697304607982482412931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359495596406143976643217241 269621697304607982482412931)
      ·
        refine ⟨404432545956911973723619397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269621697304607982482412931 404432545956911973723619397)
        ·
          refine ⟨75831102366920995073178637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 404432545956911973723619397 75831102366920995073178637)
          ·
            refine ⟨28436663387595373152441989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75831102366920995073178637 28436663387595373152441989)
            ·
              refine ⟨5331874385174132466082873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28436663387595373152441989 5331874385174132466082873)
              ·
                refine ⟨3998905788880599349562155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5331874385174132466082873 3998905788880599349562155)
                ·
                  refine ⟨5998358683320899024343233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3998905788880599349562155 5998358683320899024343233)
                  ·
                    refine ⟨4498769012490674268257425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5998358683320899024343233 4498769012490674268257425)
                    ·
                      refine ⟨3374076759368005701193069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4498769012490674268257425 3374076759368005701193069)
                      ·
                        rfl

theorem cell23_6570991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 2, 1, 2, 2].length) (baseStart_6570991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570991 prefixEnd_6570991 := by exact prefixLift 6570991
  have htrace : WordTrace (prefixWord ++ tailWord_6570991) baseStart_6570991 baseEnd_6570991 := by
    simpa [prefixWord, tailWord_6570991, baseEnd_6570991] using wordTrace_append hprefix tailTrace_6570991
  have hstable : (prefixWord ++ tailWord_6570991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570991).length < 2 ^ (prefixWord ++ tailWord_6570991).sum := by decide
  have hdescent : baseEnd_6570991 < baseStart_6570991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6570993 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 2, 7]
def baseStart_6570993 : Nat := 118140960795 + 6570993 * 2 ^ 59
def prefixEnd_6570993 : Nat := 4983230072969 + 3 ^ 40 * 6570993 * 2
def baseEnd_6570993 : Nat := 1124692595443104897789353

theorem tailTrace_6570993 : CollatzResearch.WordTrace tailWord_6570993 prefixEnd_6570993 1124692595443104897789353 := by
  unfold tailWord_6570993
  simp only [CollatzResearch.WordTrace]
  refine ⟨239663803883422072103717633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159775869255614714735811755 239663803883422072103717633)
  ·
    refine ⟨179747852912566554077788225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239663803883422072103717633 179747852912566554077788225)
    ·
      refine ⟨134810889684424915558341169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179747852912566554077788225 134810889684424915558341169)
      ·
        refine ⟨101108167263318686668755877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134810889684424915558341169 101108167263318686668755877)
        ·
          refine ⟨18957781361872253750391727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101108167263318686668755877 18957781361872253750391727)
          ·
            refine ⟨28436672042808380625587591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18957781361872253750391727 28436672042808380625587591)
            ·
              refine ⟨42655008064212570938381387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28436672042808380625587591 42655008064212570938381387)
              ·
                refine ⟨63982512096318856407572081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42655008064212570938381387 63982512096318856407572081)
                ·
                  refine ⟨47986884072239142305679061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63982512096318856407572081 47986884072239142305679061)
                  ·
                    refine ⟨1124692595443104897789353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47986884072239142305679061 1124692595443104897789353)
                    ·
                      rfl

theorem cell23_6570993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_6570993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6570993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6570993 prefixEnd_6570993 := by exact prefixLift 6570993
  have htrace : WordTrace (prefixWord ++ tailWord_6570993) baseStart_6570993 baseEnd_6570993 := by
    simpa [prefixWord, tailWord_6570993, baseEnd_6570993] using wordTrace_append hprefix tailTrace_6570993
  have hstable : (prefixWord ++ tailWord_6570993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6570993).length < 2 ^ (prefixWord ++ tailWord_6570993).sum := by decide
  have hdescent : baseEnd_6570993 < baseStart_6570993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6570993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571013 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_6571013 : Nat := 118140960795 + 6571013 * 2 ^ 59
def prefixEnd_6571013 : Nat := 4983230072969 + 3 ^ 40 * 6571013 * 2
def baseEnd_6571013 : Nat := 3374088055942404615117967

theorem tailTrace_6571013 : CollatzResearch.WordTrace tailWord_6571013 prefixEnd_6571013 3374088055942404615117967 := by
  unfold tailWord_6571013
  simp only [CollatzResearch.WordTrace]
  refine ⟨239664533343349615519445693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159776355562233077012963795 239664533343349615519445693)
  ·
    refine ⟨89874200003756105819792135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239664533343349615519445693 89874200003756105819792135)
    ·
      refine ⟨134811300005634158729688203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89874200003756105819792135 134811300005634158729688203)
      ·
        refine ⟨202216950008451238094532305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134811300005634158729688203 202216950008451238094532305)
        ·
          refine ⟨151662712506338428570899229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202216950008451238094532305 151662712506338428570899229)
          ·
            refine ⟨56873517189876910714087211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151662712506338428570899229 56873517189876910714087211)
            ·
              refine ⟨85310275784815366071130817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56873517189876910714087211 85310275784815366071130817)
              ·
                refine ⟨63982706838611524553348113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85310275784815366071130817 63982706838611524553348113)
                ·
                  refine ⟨47987030128958643415011085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63982706838611524553348113 47987030128958643415011085)
                  ·
                    refine ⟨17995136298359491280629157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47987030128958643415011085 17995136298359491280629157)
                    ·
                      refine ⟨3374088055942404615117967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17995136298359491280629157 3374088055942404615117967)
                      ·
                        rfl

theorem cell23_6571013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_6571013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571013 prefixEnd_6571013 := by exact prefixLift 6571013
  have htrace : WordTrace (prefixWord ++ tailWord_6571013) baseStart_6571013 baseEnd_6571013 := by
    simpa [prefixWord, tailWord_6571013, baseEnd_6571013] using wordTrace_append hprefix tailTrace_6571013
  have hstable : (prefixWord ++ tailWord_6571013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571013).length < 2 ^ (prefixWord ++ tailWord_6571013).sum := by decide
  have hdescent : baseEnd_6571013 < baseStart_6571013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571033 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 2, 1, 5]
def baseStart_6571033 : Nat := 118140960795 + 6571033 * 2 ^ 59
def prefixEnd_6571033 : Nat := 4983230072969 + 3 ^ 40 * 6571033 * 2
def baseEnd_6571033 : Nat := 3374098325555494536867875

theorem tailTrace_6571033 : CollatzResearch.WordTrace tailWord_6571033 prefixEnd_6571033 3374098325555494536867875 := by
  unfold tailWord_6571033
  simp only [CollatzResearch.WordTrace]
  refine ⟨239665262803277158935173753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159776841868851439290115835 239665262803277158935173753)
  ·
    refine ⟨179748947102457869201380315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239665262803277158935173753 179748947102457869201380315)
    ·
      refine ⟨269623420653686803802070473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179748947102457869201380315 269623420653686803802070473)
      ·
        refine ⟨202217565490265102851552855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269623420653686803802070473 202217565490265102851552855)
        ·
          refine ⟨303326348235397654277329283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202217565490265102851552855 303326348235397654277329283)
          ·
            refine ⟨454989522353096481415993925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303326348235397654277329283 454989522353096481415993925)
            ·
              refine ⟨85310535441205590265498861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 454989522353096481415993925 85310535441205590265498861)
              ·
                refine ⟨31991450790452096349562073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85310535441205590265498861 31991450790452096349562073)
                ·
                  refine ⟨23993588092839072262171555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31991450790452096349562073 23993588092839072262171555)
                  ·
                    refine ⟨35990382139258608393257333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23993588092839072262171555 35990382139258608393257333)
                    ·
                      refine ⟨3374098325555494536867875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35990382139258608393257333 3374098325555494536867875)
                      ·
                        rfl

theorem cell23_6571033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_6571033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571033 prefixEnd_6571033 := by exact prefixLift 6571033
  have htrace : WordTrace (prefixWord ++ tailWord_6571033) baseStart_6571033 baseEnd_6571033 := by
    simpa [prefixWord, tailWord_6571033, baseEnd_6571033] using wordTrace_append hprefix tailTrace_6571033
  have hstable : (prefixWord ++ tailWord_6571033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571033).length < 2 ^ (prefixWord ++ tailWord_6571033).sum := by decide
  have hdescent : baseEnd_6571033 < baseStart_6571033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571064 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 1, 4, 2]
def baseStart_6571064 : Nat := 118140960795 + 6571064 * 2 ^ 59
def prefixEnd_6571064 : Nat := 4983230072969 + 3 ^ 40 * 6571064 * 2
def baseEnd_6571064 : Nat := 3374114243455783915580233

theorem tailTrace_6571064 : CollatzResearch.WordTrace tailWord_6571064 prefixEnd_6571064 3374114243455783915580233 := by
  unfold tailWord_6571064
  simp only [CollatzResearch.WordTrace]
  refine ⟨119833196733082425614776123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159777595644109900819701497 119833196733082425614776123)
  ·
    refine ⟨179749795099623638422164185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119833196733082425614776123 179749795099623638422164185)
    ·
      refine ⟨134812346324717728816623139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179749795099623638422164185 134812346324717728816623139)
      ·
        refine ⟨202218519487076593224934709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134812346324717728816623139 202218519487076593224934709)
        ·
          refine ⟨18957986201913430614837629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202218519487076593224934709 18957986201913430614837629)
          ·
            refine ⟨7109244825717536480564111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18957986201913430614837629 7109244825717536480564111)
            ·
              refine ⟨10663867238576304720846167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7109244825717536480564111 10663867238576304720846167)
              ·
                refine ⟨15995800857864457081269251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10663867238576304720846167 15995800857864457081269251)
                ·
                  refine ⟨23993701286796685621903877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15995800857864457081269251 23993701286796685621903877)
                  ·
                    refine ⟨4498818991274378554106977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23993701286796685621903877 4498818991274378554106977)
                    ·
                      refine ⟨3374114243455783915580233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4498818991274378554106977 3374114243455783915580233)
                      ·
                        rfl

theorem cell23_6571064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 1, 4, 2].length) (baseStart_6571064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571064 prefixEnd_6571064 := by exact prefixLift 6571064
  have htrace : WordTrace (prefixWord ++ tailWord_6571064) baseStart_6571064 baseEnd_6571064 := by
    simpa [prefixWord, tailWord_6571064, baseEnd_6571064] using wordTrace_append hprefix tailTrace_6571064
  have hstable : (prefixWord ++ tailWord_6571064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571064).length < 2 ^ (prefixWord ++ tailWord_6571064).sum := by decide
  have hdescent : baseEnd_6571064 < baseStart_6571064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571120 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 4]
def baseStart_6571120 : Nat := 118140960795 + 6571120 * 2 ^ 59
def prefixEnd_6571120 : Nat := 4983230072969 + 3 ^ 40 * 6571120 * 2
def baseEnd_6571120 : Nat := 3374142998372435696479975

theorem tailTrace_6571120 : CollatzResearch.WordTrace tailWord_6571120 prefixEnd_6571120 3374142998372435696479975 := by
  unfold tailWord_6571120
  simp only [CollatzResearch.WordTrace]
  refine ⟨119834217976980986396795407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159778957302641315195727209 119834217976980986396795407)
  ·
    refine ⟨179751326965471479595193111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119834217976980986396795407 179751326965471479595193111)
    ·
      refine ⟨269626990448207219392789667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179751326965471479595193111 269626990448207219392789667)
      ·
        refine ⟨404440485672310829089184501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269626990448207219392789667 404440485672310829089184501)
        ·
          refine ⟨37916295531779140227111047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 404440485672310829089184501 37916295531779140227111047)
          ·
            refine ⟨56874443297668710340666571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37916295531779140227111047 56874443297668710340666571)
            ·
              refine ⟨85311664946503065510999857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56874443297668710340666571 85311664946503065510999857)
              ·
                refine ⟨63983748709877299133249893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85311664946503065510999857 63983748709877299133249893)
                ·
                  refine ⟨11996952883101993587484355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63983748709877299133249893 11996952883101993587484355)
                  ·
                    refine ⟨17995429324652990381226533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11996952883101993587484355 17995429324652990381226533)
                    ·
                      refine ⟨3374142998372435696479975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17995429324652990381226533 3374142998372435696479975)
                      ·
                        rfl

theorem cell23_6571120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_6571120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571120 prefixEnd_6571120 := by exact prefixLift 6571120
  have htrace : WordTrace (prefixWord ++ tailWord_6571120) baseStart_6571120 baseEnd_6571120 := by
    simpa [prefixWord, tailWord_6571120, baseEnd_6571120] using wordTrace_append hprefix tailTrace_6571120
  have hstable : (prefixWord ++ tailWord_6571120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571120).length < 2 ^ (prefixWord ++ tailWord_6571120).sum := by decide
  have hdescent : baseEnd_6571120 < baseStart_6571120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571123 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 5]
def baseStart_6571123 : Nat := 118140960795 + 6571123 * 2 ^ 59
def prefixEnd_6571123 : Nat := 4983230072969 + 3 ^ 40 * 6571123 * 2
def baseEnd_6571123 : Nat := 3374144538814399184742461

theorem tailTrace_6571123 : CollatzResearch.WordTrace tailWord_6571123 prefixEnd_6571123 3374144538814399184742461 := by
  unfold tailWord_6571123
  simp only [CollatzResearch.WordTrace]
  refine ⟨239668545372951104305950023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159779030248634069537300015 239668545372951104305950023)
  ·
    refine ⟨359502818059426656458925035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239668545372951104305950023 359502818059426656458925035)
    ·
      refine ⟨539254227089139984688387553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359502818059426656458925035 539254227089139984688387553)
      ·
        refine ⟨404440670316854988516290665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539254227089139984688387553 404440670316854988516290665)
        ·
          refine ⟨303330502737641241387217999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404440670316854988516290665 303330502737641241387217999)
          ·
            refine ⟨454995754106461862080826999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303330502737641241387217999 454995754106461862080826999)
            ·
              refine ⟨682493631159692793121240499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454995754106461862080826999 682493631159692793121240499)
              ·
                refine ⟨1023740446739539189681860749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682493631159692793121240499 1023740446739539189681860749)
                ·
                  refine ⟨383902667527327196130697781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023740446739539189681860749 383902667527327196130697781)
                  ·
                    refine ⟨35990875080686924637252917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 383902667527327196130697781 35990875080686924637252917)
                    ·
                      refine ⟨3374144538814399184742461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35990875080686924637252917 3374144538814399184742461)
                      ·
                        rfl

theorem cell23_6571123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_6571123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571123 prefixEnd_6571123 := by exact prefixLift 6571123
  have htrace : WordTrace (prefixWord ++ tailWord_6571123) baseStart_6571123 baseEnd_6571123 := by
    simpa [prefixWord, tailWord_6571123, baseEnd_6571123] using wordTrace_append hprefix tailTrace_6571123
  have hstable : (prefixWord ++ tailWord_6571123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571123).length < 2 ^ (prefixWord ++ tailWord_6571123).sum := by decide
  have hdescent : baseEnd_6571123 < baseStart_6571123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571137 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_6571137 : Nat := 118140960795 + 6571137 * 2 ^ 59
def prefixEnd_6571137 : Nat := 4983230072969 + 3 ^ 40 * 6571137 * 2
def baseEnd_6571137 : Nat := 3374151727543562129967397

theorem tailTrace_6571137 : CollatzResearch.WordTrace tailWord_6571137 prefixEnd_6571137 3374151727543562129967397 := by
  unfold tailWord_6571137
  simp only [CollatzResearch.WordTrace]
  refine ⟨239669055994900384696959665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159779370663266923131306443 239669055994900384696959665)
  ·
    refine ⟨179751791996175288522719749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239669055994900384696959665 179751791996175288522719749)
    ·
      refine ⟨33703460999282866598009953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179751791996175288522719749 33703460999282866598009953)
      ·
        refine ⟨25277595749462149948507465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33703460999282866598009953 25277595749462149948507465)
        ·
          refine ⟨18958196812096612461380599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25277595749462149948507465 18958196812096612461380599)
          ·
            refine ⟨28437295218144918692070899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18958196812096612461380599 28437295218144918692070899)
            ·
              refine ⟨42655942827217378038106349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28437295218144918692070899 42655942827217378038106349)
              ·
                refine ⟨15995978560206516764289881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42655942827217378038106349 15995978560206516764289881)
                ·
                  refine ⟨11996983920154887573217411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15995978560206516764289881 11996983920154887573217411)
                  ·
                    refine ⟨17995475880232331359826117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11996983920154887573217411 17995475880232331359826117)
                    ·
                      refine ⟨3374151727543562129967397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17995475880232331359826117 3374151727543562129967397)
                      ·
                        rfl

theorem cell23_6571137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_6571137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571137 prefixEnd_6571137 := by exact prefixLift 6571137
  have htrace : WordTrace (prefixWord ++ tailWord_6571137) baseStart_6571137 baseEnd_6571137 := by
    simpa [prefixWord, tailWord_6571137, baseEnd_6571137] using wordTrace_append hprefix tailTrace_6571137
  have hstable : (prefixWord ++ tailWord_6571137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571137).length < 2 ^ (prefixWord ++ tailWord_6571137).sum := by decide
  have hdescent : baseEnd_6571137 < baseStart_6571137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571187 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 5, 1, 3]
def baseStart_6571187 : Nat := 118140960795 + 6571187 * 2 ^ 59
def prefixEnd_6571187 : Nat := 4983230072969 + 3 ^ 40 * 6571187 * 2
def baseEnd_6571187 : Nat := 3374177401576286934342167

theorem tailTrace_6571187 : CollatzResearch.WordTrace tailWord_6571187 prefixEnd_6571187 3374177401576286934342167 := by
  unfold tailWord_6571187
  simp only [CollatzResearch.WordTrace]
  refine ⟨239670879644719243236279815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159780586429812828824186543 239670879644719243236279815)
  ·
    refine ⟨359506319467078864854419723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239670879644719243236279815 359506319467078864854419723)
    ·
      refine ⟨539259479200618297281629585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359506319467078864854419723 539259479200618297281629585)
      ·
        refine ⟨404444609400463722961222189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539259479200618297281629585 404444609400463722961222189)
        ·
          refine ⟨151666728525173896110458321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404444609400463722961222189 151666728525173896110458321)
          ·
            refine ⟨113750046393880422082843741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151666728525173896110458321 113750046393880422082843741)
            ·
              refine ⟨42656267397705158281066403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113750046393880422082843741 42656267397705158281066403)
              ·
                refine ⟨63984401096557737421599605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42656267397705158281066403 63984401096557737421599605)
                ·
                  refine ⟨5998537602802287883274963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63984401096557737421599605 5998537602802287883274963)
                  ·
                    refine ⟨8997806404203431824912445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5998537602802287883274963 8997806404203431824912445)
                    ·
                      refine ⟨3374177401576286934342167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8997806404203431824912445 3374177401576286934342167)
                      ·
                        rfl

theorem cell23_6571187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 1, 3].length) (baseStart_6571187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571187 prefixEnd_6571187 := by exact prefixLift 6571187
  have htrace : WordTrace (prefixWord ++ tailWord_6571187) baseStart_6571187 baseEnd_6571187 := by
    simpa [prefixWord, tailWord_6571187, baseEnd_6571187] using wordTrace_append hprefix tailTrace_6571187
  have hstable : (prefixWord ++ tailWord_6571187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571187).length < 2 ^ (prefixWord ++ tailWord_6571187).sum := by decide
  have hdescent : baseEnd_6571187 < baseStart_6571187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571221 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 3, 1, 3]
def baseStart_6571221 : Nat := 118140960795 + 6571221 * 2 ^ 59
def prefixEnd_6571221 : Nat := 4983230072969 + 3 ^ 40 * 6571221 * 2
def baseEnd_6571221 : Nat := 3374194859918539801317011

theorem tailTrace_6571221 : CollatzResearch.WordTrace tailWord_6571221 prefixEnd_6571221 3374194859918539801317011 := by
  unfold tailWord_6571221
  simp only [CollatzResearch.WordTrace]
  refine ⟨239672119726596067043017517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159781413151064044695345011 239672119726596067043017517)
  ·
    refine ⟨89877044897473525141131569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239672119726596067043017517 89877044897473525141131569)
    ·
      refine ⟨67407783673105143855848677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89877044897473525141131569 67407783673105143855848677)
      ·
        refine ⟨12638959438707214472971627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67407783673105143855848677 12638959438707214472971627)
        ·
          refine ⟨18958439158060821709457441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12638959438707214472971627 18958439158060821709457441)
          ·
            refine ⟨14218829368545616282093081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18958439158060821709457441 14218829368545616282093081)
            ·
              refine ⟨10664122026409212211569811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14218829368545616282093081 10664122026409212211569811)
              ·
                refine ⟨15996183039613818317354717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10664122026409212211569811 15996183039613818317354717)
                ·
                  refine ⟨5998568639855181869008019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15996183039613818317354717 5998568639855181869008019)
                  ·
                    refine ⟨8997852959782772803512029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5998568639855181869008019 8997852959782772803512029)
                    ·
                      refine ⟨3374194859918539801317011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8997852959782772803512029 3374194859918539801317011)
                      ·
                        rfl

theorem cell23_6571221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_6571221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571221 prefixEnd_6571221 := by exact prefixLift 6571221
  have htrace : WordTrace (prefixWord ++ tailWord_6571221) baseStart_6571221 baseEnd_6571221 := by
    simpa [prefixWord, tailWord_6571221, baseEnd_6571221] using wordTrace_append hprefix tailTrace_6571221
  have hstable : (prefixWord ++ tailWord_6571221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571221).length < 2 ^ (prefixWord ++ tailWord_6571221).sum := by decide
  have hdescent : baseEnd_6571221 < baseStart_6571221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571244 : List Nat := [2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 4]
def baseStart_6571244 : Nat := 118140960795 + 6571244 * 2 ^ 59
def prefixEnd_6571244 : Nat := 4983230072969 + 3 ^ 40 * 6571244 * 2
def baseEnd_6571244 : Nat := 3374206669973593211329405

theorem tailTrace_6571244 : CollatzResearch.WordTrace tailWord_6571244 prefixEnd_6571244 3374206669973593211329405 := by
  unfold tailWord_6571244
  simp only [CollatzResearch.WordTrace]
  refine ⟨119836479302756370985552393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159781972403675161314069857 119836479302756370985552393)
  ·
    refine ⟨89877359477067278239164295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119836479302756370985552393 89877359477067278239164295)
    ·
      refine ⟨134816039215600917358746443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89877359477067278239164295 134816039215600917358746443)
      ·
        refine ⟨202224058823401376038119665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134816039215600917358746443 202224058823401376038119665)
        ·
          refine ⟨151668044117551032028589749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202224058823401376038119665 151668044117551032028589749)
          ·
            refine ⟨14218879136020409252680289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151668044117551032028589749 14218879136020409252680289)
            ·
              refine ⟨10664159352015306939510217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14218879136020409252680289 10664159352015306939510217)
              ·
                refine ⟨7998119514011480204632663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10664159352015306939510217 7998119514011480204632663)
                ·
                  refine ⟨11997179271017220306948995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7998119514011480204632663 11997179271017220306948995)
                  ·
                    refine ⟨17995768906525830460423493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11997179271017220306948995 17995768906525830460423493)
                    ·
                      refine ⟨3374206669973593211329405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17995768906525830460423493 3374206669973593211329405)
                      ·
                        rfl

theorem cell23_6571244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_6571244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571244 prefixEnd_6571244 := by exact prefixLift 6571244
  have htrace : WordTrace (prefixWord ++ tailWord_6571244) baseStart_6571244 baseEnd_6571244 := by
    simpa [prefixWord, tailWord_6571244, baseEnd_6571244] using wordTrace_append hprefix tailTrace_6571244
  have hstable : (prefixWord ++ tailWord_6571244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571244).length < 2 ^ (prefixWord ++ tailWord_6571244).sum := by decide
  have hdescent : baseEnd_6571244 < baseStart_6571244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571278 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2]
def baseStart_6571278 : Nat := 118140960795 + 6571278 * 2 ^ 59
def prefixEnd_6571278 : Nat := 4983230072969 + 3 ^ 40 * 6571278 * 2
def baseEnd_6571278 : Nat := 3374224128315846078304249

theorem tailTrace_6571278 : CollatzResearch.WordTrace tailWord_6571278 prefixEnd_6571278 3374224128315846078304249 := by
  unfold tailWord_6571278
  simp only [CollatzResearch.WordTrace]
  refine ⟨29959274835923695722230311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159782799124926377185228325 29959274835923695722230311)
  ·
    refine ⟨44938912253885543583345467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29959274835923695722230311 44938912253885543583345467)
    ·
      refine ⟨67408368380828315375018201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44938912253885543583345467 67408368380828315375018201)
      ·
        refine ⟨50556276285621236531263651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67408368380828315375018201 50556276285621236531263651)
        ·
          refine ⟨75834414428431854796895477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50556276285621236531263651 75834414428431854796895477)
          ·
            refine ⟨7109476352665486387208951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75834414428431854796895477 7109476352665486387208951)
            ·
              refine ⟨10664214528998229580813427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7109476352665486387208951 10664214528998229580813427)
              ·
                refine ⟨15996321793497344371220141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10664214528998229580813427 15996321793497344371220141)
                ·
                  refine ⟨5998620672561504139207553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15996321793497344371220141 5998620672561504139207553)
                  ·
                    refine ⟨4498965504421128104405665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5998620672561504139207553 4498965504421128104405665)
                    ·
                      refine ⟨3374224128315846078304249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4498965504421128104405665 3374224128315846078304249)
                      ·
                        rfl

theorem cell23_6571278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_6571278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571278 prefixEnd_6571278 := by exact prefixLift 6571278
  have htrace : WordTrace (prefixWord ++ tailWord_6571278) baseStart_6571278 baseEnd_6571278 := by
    simpa [prefixWord, tailWord_6571278, baseEnd_6571278] using wordTrace_append hprefix tailTrace_6571278
  have hstable : (prefixWord ++ tailWord_6571278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571278).length < 2 ^ (prefixWord ++ tailWord_6571278).sum := by decide
  have hdescent : baseEnd_6571278 < baseStart_6571278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571298 : List Nat := [3, 3, 1, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_6571298 : Nat := 118140960795 + 6571298 * 2 ^ 59
def prefixEnd_6571298 : Nat := 4983230072969 + 3 ^ 40 * 6571298 * 2
def baseEnd_6571298 : Nat := 3374234397928936000054157

theorem tailTrace_6571298 : CollatzResearch.WordTrace tailWord_6571298 prefixEnd_6571298 3374234397928936000054157 := by
  unfold tailWord_6571298
  simp only [CollatzResearch.WordTrace]
  refine ⟨59918732036829277298392637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159783285431544739462380365 59918732036829277298392637)
  ·
    refine ⟨22469524513810978986897239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59918732036829277298392637 22469524513810978986897239)
    ·
      refine ⟨33704286770716468480345859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22469524513810978986897239 33704286770716468480345859)
      ·
        refine ⟨50556430156074702720518789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33704286770716468480345859 50556430156074702720518789)
        ·
          refine ⟨9479330654264006760097273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50556430156074702720518789 9479330654264006760097273)
          ·
            refine ⟨7109497990698005070072955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9479330654264006760097273 7109497990698005070072955)
            ·
              refine ⟨10664246986047007605109433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7109497990698005070072955 10664246986047007605109433)
              ·
                refine ⟨7998185239535255703832075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10664246986047007605109433 7998185239535255703832075)
                ·
                  refine ⟨11997277859302883555748113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7998185239535255703832075 11997277859302883555748113)
                  ·
                    refine ⟨8997958394477162666811085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11997277859302883555748113 8997958394477162666811085)
                    ·
                      refine ⟨3374234397928936000054157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8997958394477162666811085 3374234397928936000054157)
                      ·
                        rfl

theorem cell23_6571298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_6571298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571298 prefixEnd_6571298 := by exact prefixLift 6571298
  have htrace : WordTrace (prefixWord ++ tailWord_6571298) baseStart_6571298 baseEnd_6571298 := by
    simpa [prefixWord, tailWord_6571298, baseEnd_6571298] using wordTrace_append hprefix tailTrace_6571298
  have hstable : (prefixWord ++ tailWord_6571298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571298).length < 2 ^ (prefixWord ++ tailWord_6571298).sum := by decide
  have hdescent : baseEnd_6571298 < baseStart_6571298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571337 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 2, 4, 3]
def baseStart_6571337 : Nat := 118140960795 + 6571337 * 2 ^ 59
def prefixEnd_6571337 : Nat := 4983230072969 + 3 ^ 40 * 6571337 * 2
def baseEnd_6571337 : Nat := 3374254423674461347466477

theorem tailTrace_6571337 : CollatzResearch.WordTrace tailWord_6571337 prefixEnd_6571337 3374254423674461347466477 := by
  unfold tailWord_6571337
  simp only [CollatzResearch.WordTrace]
  refine ⟨239676350594175818854240265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159784233729450545902826843 239676350594175818854240265)
  ·
    refine ⟨179757262945631864140680199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239676350594175818854240265 179757262945631864140680199)
    ·
      refine ⟨269635894418447796211020299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179757262945631864140680199 269635894418447796211020299)
      ·
        refine ⟨404453841627671694316530449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269635894418447796211020299 404453841627671694316530449)
        ·
          refine ⟨303340381220753770737397837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404453841627671694316530449 303340381220753770737397837)
          ·
            refine ⟨113752642957782664026524189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303340381220753770737397837 113752642957782664026524189)
            ·
              refine ⟨42657241109168499009946571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113752642957782664026524189 42657241109168499009946571)
              ·
                refine ⟨63985861663752748514919857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42657241109168499009946571 63985861663752748514919857)
                ·
                  refine ⟨47989396247814561386189893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63985861663752748514919857 47989396247814561386189893)
                  ·
                    refine ⟨8998011796465230259910605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47989396247814561386189893 8998011796465230259910605)
                    ·
                      refine ⟨3374254423674461347466477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8998011796465230259910605 3374254423674461347466477)
                      ·
                        rfl

theorem cell23_6571337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 4, 3].length) (baseStart_6571337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571337 prefixEnd_6571337 := by exact prefixLift 6571337
  have htrace : WordTrace (prefixWord ++ tailWord_6571337) baseStart_6571337 baseEnd_6571337 := by
    simpa [prefixWord, tailWord_6571337, baseEnd_6571337] using wordTrace_append hprefix tailTrace_6571337
  have hstable : (prefixWord ++ tailWord_6571337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571337).length < 2 ^ (prefixWord ++ tailWord_6571337).sum := by decide
  have hdescent : baseEnd_6571337 < baseStart_6571337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571347 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 4]
def baseStart_6571347 : Nat := 118140960795 + 6571347 * 2 ^ 59
def prefixEnd_6571347 : Nat := 4983230072969 + 3 ^ 40 * 6571347 * 2
def baseEnd_6571347 : Nat := 3374259558481006308341431

theorem tailTrace_6571347 : CollatzResearch.WordTrace tailWord_6571347 prefixEnd_6571347 3374259558481006308341431 := by
  unfold tailWord_6571347
  simp only [CollatzResearch.WordTrace]
  refine ⟨239676715324139590562104295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159784476882759727041402863 239676715324139590562104295)
  ·
    refine ⟨359515072986209385843156443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239676715324139590562104295 359515072986209385843156443)
    ·
      refine ⟨539272609479314078764734665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359515072986209385843156443 539272609479314078764734665)
      ·
        refine ⟨404454457109485559073550999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539272609479314078764734665 404454457109485559073550999)
        ·
          refine ⟨606681685664228338610326499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404454457109485559073550999 606681685664228338610326499)
          ·
            refine ⟨910022528496342507915489749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606681685664228338610326499 910022528496342507915489749)
            ·
              refine ⟨21328653011633027529269291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 910022528496342507915489749 21328653011633027529269291)
              ·
                refine ⟨31992979517449541293903937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21328653011633027529269291 31992979517449541293903937)
                ·
                  refine ⟨23994734638087155970427953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31992979517449541293903937 23994734638087155970427953)
                  ·
                    refine ⟨17996050978565366977820965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23994734638087155970427953 17996050978565366977820965)
                    ·
                      refine ⟨3374259558481006308341431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17996050978565366977820965 3374259558481006308341431)
                      ·
                        rfl

theorem cell23_6571347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_6571347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571347 prefixEnd_6571347 := by exact prefixLift 6571347
  have htrace : WordTrace (prefixWord ++ tailWord_6571347) baseStart_6571347 baseEnd_6571347 := by
    simpa [prefixWord, tailWord_6571347, baseEnd_6571347] using wordTrace_append hprefix tailTrace_6571347
  have hstable : (prefixWord ++ tailWord_6571347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571347).length < 2 ^ (prefixWord ++ tailWord_6571347).sum := by decide
  have hdescent : baseEnd_6571347 < baseStart_6571347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571351 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 1, 4, 2]
def baseStart_6571351 : Nat := 118140960795 + 6571351 * 2 ^ 59
def prefixEnd_6571351 : Nat := 4983230072969 + 3 ^ 40 * 6571351 * 2
def baseEnd_6571351 : Nat := 3374261612403624292691413

theorem tailTrace_6571351 : CollatzResearch.WordTrace tailWord_6571351 prefixEnd_6571351 3374261612403624292691413 := by
  unfold tailWord_6571351
  simp only [CollatzResearch.WordTrace]
  refine ⟨239676861216125099245249907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159784574144083399496833271 239676861216125099245249907)
  ·
    refine ⟨359515291824187648867874861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239676861216125099245249907 359515291824187648867874861)
    ·
      refine ⟨134818234434070368325453073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359515291824187648867874861 134818234434070368325453073)
      ·
        refine ⟨101113675825552776244089805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134818234434070368325453073 101113675825552776244089805)
        ·
          refine ⟨37917628434582291091533677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101113675825552776244089805 37917628434582291091533677)
          ·
            refine ⟨14219110662968359159325129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37917628434582291091533677 14219110662968359159325129)
            ·
              refine ⟨10664332997226269369493847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14219110662968359159325129 10664332997226269369493847)
              ·
                refine ⟨15996499495839404054240771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10664332997226269369493847 15996499495839404054240771)
                ·
                  refine ⟨23994749243759106081361157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15996499495839404054240771 23994749243759106081361157)
                  ·
                    refine ⟨4499015483204832390255217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23994749243759106081361157 4499015483204832390255217)
                    ·
                      refine ⟨3374261612403624292691413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4499015483204832390255217 3374261612403624292691413)
                      ·
                        rfl

theorem cell23_6571351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_6571351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571351 prefixEnd_6571351 := by exact prefixLift 6571351
  have htrace : WordTrace (prefixWord ++ tailWord_6571351) baseStart_6571351 baseEnd_6571351 := by
    simpa [prefixWord, tailWord_6571351, baseEnd_6571351] using wordTrace_append hprefix tailTrace_6571351
  have hstable : (prefixWord ++ tailWord_6571351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571351).length < 2 ^ (prefixWord ++ tailWord_6571351).sum := by decide
  have hdescent : baseEnd_6571351 < baseStart_6571351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571387 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 4, 5]
def baseStart_6571387 : Nat := 118140960795 + 6571387 * 2 ^ 59
def prefixEnd_6571387 : Nat := 4983230072969 + 3 ^ 40 * 6571387 * 2
def baseEnd_6571387 : Nat := 1124760032569062050613749

theorem tailTrace_6571387 : CollatzResearch.WordTrace tailWord_6571387 prefixEnd_6571387 1124760032569062050613749 := by
  unfold tailWord_6571387
  simp only [CollatzResearch.WordTrace]
  refine ⟨239678174243994677393560415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159785449495996451595706943 239678174243994677393560415)
  ·
    refine ⟨359517261365992016090340623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239678174243994677393560415 359517261365992016090340623)
    ·
      refine ⟨539275892048988024135510935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359517261365992016090340623 539275892048988024135510935)
      ·
        refine ⟨808913838073482036203266403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539275892048988024135510935 808913838073482036203266403)
        ·
          refine ⟨1213370757110223054304899605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808913838073482036203266403 1213370757110223054304899605)
          ·
            refine ⟨56876754239541705670542169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1213370757110223054304899605 56876754239541705670542169)
            ·
              refine ⟨42657565679656279252906627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56876754239541705670542169 42657565679656279252906627)
              ·
                refine ⟨63986348519484418879359941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42657565679656279252906627 63986348519484418879359941)
                ·
                  refine ⟨11997440347403328539879989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63986348519484418879359941 11997440347403328539879989)
                  ·
                    refine ⟨1124760032569062050613749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11997440347403328539879989 1124760032569062050613749)
                    ·
                      rfl

theorem cell23_6571387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 5].length) (baseStart_6571387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571387 prefixEnd_6571387 := by exact prefixLift 6571387
  have htrace : WordTrace (prefixWord ++ tailWord_6571387) baseStart_6571387 baseEnd_6571387 := by
    simpa [prefixWord, tailWord_6571387, baseEnd_6571387] using wordTrace_append hprefix tailTrace_6571387
  have hstable : (prefixWord ++ tailWord_6571387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571387).length < 2 ^ (prefixWord ++ tailWord_6571387).sum := by decide
  have hdescent : baseEnd_6571387 < baseStart_6571387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571397 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_6571397 : Nat := 118140960795 + 6571397 * 2 ^ 59
def prefixEnd_6571397 : Nat := 4983230072969 + 3 ^ 40 * 6571397 * 2
def baseEnd_6571397 : Nat := 3374285232513731112716201

theorem tailTrace_6571397 : CollatzResearch.WordTrace tailWord_6571397 prefixEnd_6571397 3374285232513731112716201 := by
  unfold tailWord_6571397
  simp only [CollatzResearch.WordTrace]
  refine ⟨239678538973958449101424445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159785692649305632734282963 239678538973958449101424445)
  ·
    refine ⟨89879452115234418413034167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239678538973958449101424445 89879452115234418413034167)
    ·
      refine ⟨134819178172851627619551251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89879452115234418413034167 134819178172851627619551251)
      ·
        refine ⟨202228767259277441429326877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134819178172851627619551251 202228767259277441429326877)
        ·
          refine ⟨75835787722229040535997579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202228767259277441429326877 75835787722229040535997579)
          ·
            refine ⟨113753681583343560803996369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75835787722229040535997579 113753681583343560803996369)
            ·
              refine ⟨85315261187507670602997277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113753681583343560803996369 85315261187507670602997277)
              ·
                refine ⟨31993222945315376476123979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85315261187507670602997277 31993222945315376476123979)
                ·
                  refine ⟨47989834417973064714185969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31993222945315376476123979 47989834417973064714185969)
                  ·
                    refine ⟨35992375813479798535639477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47989834417973064714185969 35992375813479798535639477)
                    ·
                      refine ⟨3374285232513731112716201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35992375813479798535639477 3374285232513731112716201)
                      ·
                        rfl

theorem cell23_6571397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_6571397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571397 prefixEnd_6571397 := by exact prefixLift 6571397
  have htrace : WordTrace (prefixWord ++ tailWord_6571397) baseStart_6571397 baseEnd_6571397 := by
    simpa [prefixWord, tailWord_6571397, baseEnd_6571397] using wordTrace_append hprefix tailTrace_6571397
  have hstable : (prefixWord ++ tailWord_6571397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571397).length < 2 ^ (prefixWord ++ tailWord_6571397).sum := by decide
  have hdescent : baseEnd_6571397 < baseStart_6571397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571424 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 4]
def baseStart_6571424 : Nat := 118140960795 + 6571424 * 2 ^ 59
def prefixEnd_6571424 : Nat := 4983230072969 + 3 ^ 40 * 6571424 * 2
def baseEnd_6571424 : Nat := 3374299096491402507078577

theorem tailTrace_6571424 : CollatzResearch.WordTrace tailWord_6571424 prefixEnd_6571424 3374299096491402507078577 := by
  unfold tailWord_6571424
  simp only [CollatzResearch.WordTrace]
  refine ⟨119839761872430316356328663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159786349163240421808438217 119839761872430316356328663)
  ·
    refine ⟨179759642808645474534492995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119839761872430316356328663 179759642808645474534492995)
    ·
      refine ⟨269639464212968211801739493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179759642808645474534492995 269639464212968211801739493)
      ·
        refine ⟨50557399539931539712826155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269639464212968211801739493 50557399539931539712826155)
        ·
          refine ⟨75836099309897309569239233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50557399539931539712826155 75836099309897309569239233)
          ·
            refine ⟨56877074482422982176929425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75836099309897309569239233 56877074482422982176929425)
            ·
              refine ⟨42657805861817236632697069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56877074482422982176929425 42657805861817236632697069)
              ·
                refine ⟨15996677198181463737261401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42657805861817236632697069 15996677198181463737261401)
                ·
                  refine ⟨11997507898636097802946051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15996677198181463737261401 11997507898636097802946051)
                  ·
                    refine ⟨17996261847954146704419077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11997507898636097802946051 17996261847954146704419077)
                    ·
                      refine ⟨3374299096491402507078577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17996261847954146704419077 3374299096491402507078577)
                      ·
                        rfl

theorem cell23_6571424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_6571424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571424 prefixEnd_6571424 := by exact prefixLift 6571424
  have htrace : WordTrace (prefixWord ++ tailWord_6571424) baseStart_6571424 baseEnd_6571424 := by
    simpa [prefixWord, tailWord_6571424, baseEnd_6571424] using wordTrace_append hprefix tailTrace_6571424
  have hstable : (prefixWord ++ tailWord_6571424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571424).length < 2 ^ (prefixWord ++ tailWord_6571424).sum := by decide
  have hdescent : baseEnd_6571424 < baseStart_6571424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571447 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 8]
def baseStart_6571447 : Nat := 118140960795 + 6571447 * 2 ^ 59
def prefixEnd_6571447 : Nat := 4983230072969 + 3 ^ 40 * 6571447 * 2
def baseEnd_6571447 : Nat := 374923434060717324121219

theorem tailTrace_6571447 : CollatzResearch.WordTrace tailWord_6571447 prefixEnd_6571447 374923434060717324121219 := by
  unfold tailWord_6571447
  simp only [CollatzResearch.WordTrace]
  refine ⟨239680362623777307640744595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159786908415851538427163063 239680362623777307640744595)
  ·
    refine ⟨359520543935665961461116893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239680362623777307640744595 359520543935665961461116893)
    ·
      refine ⟨134820203975874735547918835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359520543935665961461116893 134820203975874735547918835)
      ·
        refine ⟨202230305963812103321878253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134820203975874735547918835 202230305963812103321878253)
        ·
          refine ⟨75836364736429538745704345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202230305963812103321878253 75836364736429538745704345)
          ·
            refine ⟨56877273552322154059278259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75836364736429538745704345 56877273552322154059278259)
            ·
              refine ⟨85315910328483231088917389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56877273552322154059278259 85315910328483231088917389)
              ·
                refine ⟨31993466373181211658344021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85315910328483231088917389 31993466373181211658344021)
                ·
                  refine ⟨374923434060717324121219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31993466373181211658344021 374923434060717324121219)
                  ·
                    rfl

theorem cell23_6571447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 8].length) (baseStart_6571447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571447 prefixEnd_6571447 := by exact prefixLift 6571447
  have htrace : WordTrace (prefixWord ++ tailWord_6571447) baseStart_6571447 baseEnd_6571447 := by
    simpa [prefixWord, tailWord_6571447, baseEnd_6571447] using wordTrace_append hprefix tailTrace_6571447
  have hstable : (prefixWord ++ tailWord_6571447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571447).length < 2 ^ (prefixWord ++ tailWord_6571447).sum := by decide
  have hdescent : baseEnd_6571447 < baseStart_6571447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571464 : List Nat := [2, 1, 3, 1, 3, 1, 3, 3, 6]
def baseStart_6571464 : Nat := 118140960795 + 6571464 * 2 ^ 59
def prefixEnd_6571464 : Nat := 4983230072969 + 3 ^ 40 * 6571464 * 2
def baseEnd_6571464 : Nat := 374924403968620261175377

theorem tailTrace_6571464 : CollatzResearch.WordTrace tailWord_6571464 prefixEnd_6571464 374924403968620261175377 := by
  unfold tailWord_6571464
  simp only [CollatzResearch.WordTrace]
  refine ⟨119840491332357859772056723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159787321776477146362742297 119840491332357859772056723)
  ·
    refine ⟨179760736998536789658085085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119840491332357859772056723 179760736998536789658085085)
    ·
      refine ⟨67410276374451296121781907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179760736998536789658085085 67410276374451296121781907)
      ·
        refine ⟨101115414561676944182672861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67410276374451296121781907 101115414561676944182672861)
        ·
          refine ⟨37918280460628854068502323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101115414561676944182672861 37918280460628854068502323)
          ·
            refine ⟨56877420690943281102753485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37918280460628854068502323 56877420690943281102753485)
            ·
              refine ⟨21329032759103730413532557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56877420690943281102753485 21329032759103730413532557)
              ·
                refine ⟨7998387284663898905074709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21329032759103730413532557 7998387284663898905074709)
                ·
                  refine ⟨374924403968620261175377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7998387284663898905074709 374924403968620261175377)
                  ·
                    rfl

theorem cell23_6571464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 6].length) (baseStart_6571464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571464 prefixEnd_6571464 := by exact prefixLift 6571464
  have htrace : WordTrace (prefixWord ++ tailWord_6571464) baseStart_6571464 baseEnd_6571464 := by
    simpa [prefixWord, tailWord_6571464, baseEnd_6571464] using wordTrace_append hprefix tailTrace_6571464
  have hstable : (prefixWord ++ tailWord_6571464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571464).length < 2 ^ (prefixWord ++ tailWord_6571464).sum := by decide
  have hdescent : baseEnd_6571464 < baseStart_6571464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571467 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 6]
def baseStart_6571467 : Nat := 118140960795 + 6571467 * 2 ^ 59
def prefixEnd_6571467 : Nat := 4983230072969 + 3 ^ 40 * 6571467 * 2
def baseEnd_6571467 : Nat := 3374321176159545838840879

theorem tailTrace_6571467 : CollatzResearch.WordTrace tailWord_6571467 prefixEnd_6571467 3374321176159545838840879 := by
  unfold tailWord_6571467
  simp only [CollatzResearch.WordTrace]
  refine ⟨239681092083704851056472655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159787394722469900704315103 239681092083704851056472655)
  ·
    refine ⟨359521638125557276584708983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239681092083704851056472655 359521638125557276584708983)
    ·
      refine ⟨539282457188335914877063475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359521638125557276584708983 539282457188335914877063475)
      ·
        refine ⟨808923685782503872315595213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539282457188335914877063475 808923685782503872315595213)
        ·
          refine ⟨303346382168438952118348205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 808923685782503872315595213 303346382168438952118348205)
          ·
            refine ⟨113754893313164607044380577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303346382168438952118348205 113754893313164607044380577)
            ·
              refine ⟨85316169984873455283285433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113754893313164607044380577 85316169984873455283285433)
              ·
                refine ⟨63987127488655091462464075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85316169984873455283285433 63987127488655091462464075)
                ·
                  refine ⟨95980691232982637193696113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63987127488655091462464075 95980691232982637193696113)
                  ·
                    refine ⟨71985518424736977895272085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95980691232982637193696113 71985518424736977895272085)
                    ·
                      refine ⟨3374321176159545838840879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71985518424736977895272085 3374321176159545838840879)
                      ·
                        rfl

theorem cell23_6571467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 6].length) (baseStart_6571467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571467 prefixEnd_6571467 := by exact prefixLift 6571467
  have htrace : WordTrace (prefixWord ++ tailWord_6571467) baseStart_6571467 baseEnd_6571467 := by
    simpa [prefixWord, tailWord_6571467, baseEnd_6571467] using wordTrace_append hprefix tailTrace_6571467
  have hstable : (prefixWord ++ tailWord_6571467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571467).length < 2 ^ (prefixWord ++ tailWord_6571467).sum := by decide
  have hdescent : baseEnd_6571467 < baseStart_6571467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571478 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_6571478 : Nat := 118140960795 + 6571478 * 2 ^ 59
def prefixEnd_6571478 : Nat := 4983230072969 + 3 ^ 40 * 6571478 * 2
def baseEnd_6571478 : Nat := 3374326824446745295803329

theorem tailTrace_6571478 : CollatzResearch.WordTrace tailWord_6571478 prefixEnd_6571478 3374326824446745295803329 := by
  unfold tailWord_6571478
  simp only [CollatzResearch.WordTrace]
  refine ⟨14980093330416562495945193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159787662191109999956748725 14980093330416562495945193)
  ·
    refine ⟨11235069997812421871958895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14980093330416562495945193 11235069997812421871958895)
    ·
      refine ⟨16852604996718632807938343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11235069997812421871958895 16852604996718632807938343)
      ·
        refine ⟨25278907495077949211907515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16852604996718632807938343 25278907495077949211907515)
        ·
          refine ⟨37918361242616923817861273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25278907495077949211907515 37918361242616923817861273)
          ·
            refine ⟨28438770931962692863395955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37918361242616923817861273 28438770931962692863395955)
            ·
              refine ⟨42658156397944039295093933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28438770931962692863395955 42658156397944039295093933)
              ·
                refine ⟨15996808649229014735660225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42658156397944039295093933 15996808649229014735660225)
                ·
                  refine ⟨11997606486921761051745169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15996808649229014735660225 11997606486921761051745169)
                  ·
                    refine ⟨8998204865191320788808877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11997606486921761051745169 8998204865191320788808877)
                    ·
                      refine ⟨3374326824446745295803329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8998204865191320788808877 3374326824446745295803329)
                      ·
                        rfl

theorem cell23_6571478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_6571478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571478 prefixEnd_6571478 := by exact prefixLift 6571478
  have htrace : WordTrace (prefixWord ++ tailWord_6571478) baseStart_6571478 baseEnd_6571478 := by
    simpa [prefixWord, tailWord_6571478, baseEnd_6571478] using wordTrace_append hprefix tailTrace_6571478
  have hstable : (prefixWord ++ tailWord_6571478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571478).length < 2 ^ (prefixWord ++ tailWord_6571478).sum := by decide
  have hdescent : baseEnd_6571478 < baseStart_6571478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571514 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4]
def baseStart_6571514 : Nat := 118140960795 + 6571514 * 2 ^ 59
def prefixEnd_6571514 : Nat := 4983230072969 + 3 ^ 40 * 6571514 * 2
def baseEnd_6571514 : Nat := 3374345309750307154953163

theorem tailTrace_6571514 : CollatzResearch.WordTrace tailWord_6571514 prefixEnd_6571514 3374345309750307154953163 := by
  unfold tailWord_6571514
  simp only [CollatzResearch.WordTrace]
  refine ⟨59920701578633644520858399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159788537543023052055622397 59920701578633644520858399)
  ·
    refine ⟨89881052367950466781287599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59920701578633644520858399 89881052367950466781287599)
    ·
      refine ⟨134821578551925700171931399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89881052367950466781287599 134821578551925700171931399)
      ·
        refine ⟨202232367827888550257897099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134821578551925700171931399 202232367827888550257897099)
        ·
          refine ⟨303348551741832825386845649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202232367827888550257897099 303348551741832825386845649)
          ·
            refine ⟨227511413806374619040134237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303348551741832825386845649 227511413806374619040134237)
            ·
              refine ⟨85316780177390482140050339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227511413806374619040134237 85316780177390482140050339)
              ·
                refine ⟨127975170266085723210075509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85316780177390482140050339 127975170266085723210075509)
                ·
                  refine ⟨11997672212445536550944579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127975170266085723210075509 11997672212445536550944579)
                  ·
                    refine ⟨17996508318668304826416869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11997672212445536550944579 17996508318668304826416869)
                    ·
                      refine ⟨3374345309750307154953163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17996508318668304826416869 3374345309750307154953163)
                      ·
                        rfl

theorem cell23_6571514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_6571514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571514 prefixEnd_6571514 := by exact prefixLift 6571514
  have htrace : WordTrace (prefixWord ++ tailWord_6571514) baseStart_6571514 baseEnd_6571514 := by
    simpa [prefixWord, tailWord_6571514, baseEnd_6571514] using wordTrace_append hprefix tailTrace_6571514
  have hstable : (prefixWord ++ tailWord_6571514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571514).length < 2 ^ (prefixWord ++ tailWord_6571514).sum := by decide
  have hdescent : baseEnd_6571514 < baseStart_6571514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571548 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_6571548 : Nat := 118140960795 + 6571548 * 2 ^ 59
def prefixEnd_6571548 : Nat := 4983230072969 + 3 ^ 40 * 6571548 * 2
def baseEnd_6571548 : Nat := 3374362768092560021928007

theorem tailTrace_6571548 : CollatzResearch.WordTrace tailWord_6571548 prefixEnd_6571548 3374362768092560021928007 := by
  unfold tailWord_6571548
  simp only [CollatzResearch.WordTrace]
  refine ⟨119842023198205700945085649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159789364264274267926780865 119842023198205700945085649)
  ·
    refine ⟨89881517398654275708814237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119842023198205700945085649 89881517398654275708814237)
    ·
      refine ⟨33705569024495353390805339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89881517398654275708814237 33705569024495353390805339)
      ·
        refine ⟨50558353536743030086208009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33705569024495353390805339 50558353536743030086208009)
        ·
          refine ⟨37918765152557272564656007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50558353536743030086208009 37918765152557272564656007)
          ·
            refine ⟨56878147728835908846984011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37918765152557272564656007 56878147728835908846984011)
            ·
              refine ⟨85317221593253863270476017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56878147728835908846984011 85317221593253863270476017)
              ·
                refine ⟨63987916194940397452857013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85317221593253863270476017 63987916194940397452857013)
                ·
                  refine ⟨5998867143275662261205345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63987916194940397452857013 5998867143275662261205345)
                  ·
                    refine ⟨4499150357456746695904009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5998867143275662261205345 4499150357456746695904009)
                    ·
                      refine ⟨3374362768092560021928007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4499150357456746695904009 3374362768092560021928007)
                      ·
                        rfl

theorem cell23_6571548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_6571548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571548 prefixEnd_6571548 := by exact prefixLift 6571548
  have htrace : WordTrace (prefixWord ++ tailWord_6571548) baseStart_6571548 baseEnd_6571548 := by
    simpa [prefixWord, tailWord_6571548, baseEnd_6571548] using wordTrace_append hprefix tailTrace_6571548
  have hstable : (prefixWord ++ tailWord_6571548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571548).length < 2 ^ (prefixWord ++ tailWord_6571548).sum := by decide
  have hdescent : baseEnd_6571548 < baseStart_6571548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571564 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 3]
def baseStart_6571564 : Nat := 118140960795 + 6571564 * 2 ^ 59
def prefixEnd_6571564 : Nat := 4983230072969 + 3 ^ 40 * 6571564 * 2
def baseEnd_6571564 : Nat := 3374370983783031959327933

theorem tailTrace_6571564 : CollatzResearch.WordTrace tailWord_6571564 prefixEnd_6571564 3374370983783031959327933 := by
  unfold tailWord_6571564
  simp only [CollatzResearch.WordTrace]
  refine ⟨119842314982176718311376873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159789753309568957748502497 119842314982176718311376873)
  ·
    refine ⟨89881736236632538733532655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119842314982176718311376873 89881736236632538733532655)
    ·
      refine ⟨134822604354948808100298983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89881736236632538733532655 134822604354948808100298983)
      ·
        refine ⟨202233906532423212150448475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134822604354948808100298983 202233906532423212150448475)
        ·
          refine ⟨303350859798634818225672713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202233906532423212150448475 303350859798634818225672713)
          ·
            refine ⟨227513144848976113669254535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303350859798634818225672713 227513144848976113669254535)
            ·
              refine ⟨341269717273464170503881803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227513144848976113669254535 341269717273464170503881803)
              ·
                refine ⟨511904575910196255755822705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341269717273464170503881803 511904575910196255755822705)
                ·
                  refine ⟨383928431932647191816867029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511904575910196255755822705 383928431932647191816867029)
                  ·
                    refine ⟨8998322623421418558207821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 383928431932647191816867029 8998322623421418558207821)
                    ·
                      refine ⟨3374370983783031959327933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8998322623421418558207821 3374370983783031959327933)
                      ·
                        rfl

theorem cell23_6571564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_6571564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571564 prefixEnd_6571564 := by exact prefixLift 6571564
  have htrace : WordTrace (prefixWord ++ tailWord_6571564) baseStart_6571564 baseEnd_6571564 := by
    simpa [prefixWord, tailWord_6571564, baseEnd_6571564] using wordTrace_append hprefix tailTrace_6571564
  have hstable : (prefixWord ++ tailWord_6571564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571564).length < 2 ^ (prefixWord ++ tailWord_6571564).sum := by decide
  have hdescent : baseEnd_6571564 < baseStart_6571564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571594 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_6571594 : Nat := 118140960795 + 6571594 * 2 ^ 59
def prefixEnd_6571594 : Nat := 4983230072969 + 3 ^ 40 * 6571594 * 2
def baseEnd_6571594 : Nat := 3374386388202666841952795

theorem tailTrace_6571594 : CollatzResearch.WordTrace tailWord_6571594 prefixEnd_6571594 3374386388202666841952795 := by
  unfold tailWord_6571594
  simp only [CollatzResearch.WordTrace]
  refine ⟨59921431038561187936586459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159790482769496501164230557 59921431038561187936586459)
  ·
    refine ⟨89882146557841781904879689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59921431038561187936586459 89882146557841781904879689)
    ·
      refine ⟨67411609918381336428659767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89882146557841781904879689 67411609918381336428659767)
      ·
        refine ⟨101117414877572004642989651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67411609918381336428659767 101117414877572004642989651)
        ·
          refine ⟨151676122316358006964484477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101117414877572004642989651 151676122316358006964484477)
          ·
            refine ⟨56878545868634252611681679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151676122316358006964484477 56878545868634252611681679)
            ·
              refine ⟨85317818802951378917522519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56878545868634252611681679 85317818802951378917522519)
              ·
                refine ⟨127976728204427068376283779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85317818802951378917522519 127976728204427068376283779)
                ·
                  refine ⟨191965092306640602564425669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127976728204427068376283779 191965092306640602564425669)
                  ·
                    refine ⟨35993454807495112980829813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191965092306640602564425669 35993454807495112980829813)
                    ·
                      refine ⟨3374386388202666841952795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35993454807495112980829813 3374386388202666841952795)
                      ·
                        rfl

theorem cell23_6571594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_6571594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571594 prefixEnd_6571594 := by exact prefixLift 6571594
  have htrace : WordTrace (prefixWord ++ tailWord_6571594) baseStart_6571594 baseEnd_6571594 := by
    simpa [prefixWord, tailWord_6571594, baseEnd_6571594] using wordTrace_append hprefix tailTrace_6571594
  have hstable : (prefixWord ++ tailWord_6571594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571594).length < 2 ^ (prefixWord ++ tailWord_6571594).sum := by decide
  have hdescent : baseEnd_6571594 < baseStart_6571594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571632 : List Nat := [2, 1, 1, 1, 6, 3, 2, 1, 2, 1, 3]
def baseStart_6571632 : Nat := 118140960795 + 6571632 * 2 ^ 59
def prefixEnd_6571632 : Nat := 4983230072969 + 3 ^ 40 * 6571632 * 2
def baseEnd_6571632 : Nat := 3374405900467537693277621

theorem tailTrace_6571632 : CollatzResearch.WordTrace tailWord_6571632 prefixEnd_6571632 3374405900467537693277621 := by
  unfold tailWord_6571632
  simp only [CollatzResearch.WordTrace]
  refine ⟨119843555064053542118114575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159791406752071389490819433 119843555064053542118114575)
  ·
    refine ⟨179765332596080313177171863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119843555064053542118114575 179765332596080313177171863)
    ·
      refine ⟨269647998894120469765757795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179765332596080313177171863 269647998894120469765757795)
      ·
        refine ⟨404471998341180704648636693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269647998894120469765757795 404471998341180704648636693)
        ·
          refine ⟨18959624922242845530404845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 404471998341180704648636693 18959624922242845530404845)
          ·
            refine ⟨7109859345841067073901817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18959624922242845530404845 7109859345841067073901817)
            ·
              refine ⟨5332394509380800305426363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7109859345841067073901817 5332394509380800305426363)
              ·
                refine ⟨7998591764071200458139545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5332394509380800305426363 7998591764071200458139545)
                ·
                  refine ⟨5998943823053400343604659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7998591764071200458139545 5998943823053400343604659)
                  ·
                    refine ⟨8998415734580100515406989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5998943823053400343604659 8998415734580100515406989)
                    ·
                      refine ⟨3374405900467537693277621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8998415734580100515406989 3374405900467537693277621)
                      ·
                        rfl

theorem cell23_6571632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 2, 1, 3].length) (baseStart_6571632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571632 prefixEnd_6571632 := by exact prefixLift 6571632
  have htrace : WordTrace (prefixWord ++ tailWord_6571632) baseStart_6571632 baseEnd_6571632 := by
    simpa [prefixWord, tailWord_6571632, baseEnd_6571632] using wordTrace_append hprefix tailTrace_6571632
  have hstable : (prefixWord ++ tailWord_6571632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571632).length < 2 ^ (prefixWord ++ tailWord_6571632).sum := by decide
  have hdescent : baseEnd_6571632 < baseStart_6571632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571644 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 9]
def baseStart_6571644 : Nat := 118140960795 + 6571644 * 2 ^ 59
def prefixEnd_6571644 : Nat := 4983230072969 + 3 ^ 40 * 6571644 * 2
def baseEnd_6571644 : Nat := 374934673581710182925285

theorem tailTrace_6571644 : CollatzResearch.WordTrace tailWord_6571644 prefixEnd_6571644 374934673581710182925285 := by
  unfold tailWord_6571644
  simp only [CollatzResearch.WordTrace]
  refine ⟨119843773902031805142832993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159791698536042406857110657 119843773902031805142832993)
  ·
    refine ⟨89882830426523853857124745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119843773902031805142832993 89882830426523853857124745)
    ·
      refine ⟨67412122819892890392843559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89882830426523853857124745 67412122819892890392843559)
      ·
        refine ⟨101118184229839335589265339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67412122819892890392843559 101118184229839335589265339)
        ·
          refine ⟨151677276344759003383898009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101118184229839335589265339 151677276344759003383898009)
          ·
            refine ⟨113757957258569252537923507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151677276344759003383898009 113757957258569252537923507)
            ·
              refine ⟨170636935887853878806885261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113757957258569252537923507 170636935887853878806885261)
              ·
                refine ⟨63988850957945204552581973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170636935887853878806885261 63988850957945204552581973)
                ·
                  refine ⟨374934673581710182925285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63988850957945204552581973 374934673581710182925285)
                  ·
                    rfl

theorem cell23_6571644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_6571644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571644 prefixEnd_6571644 := by exact prefixLift 6571644
  have htrace : WordTrace (prefixWord ++ tailWord_6571644) baseStart_6571644 baseEnd_6571644 := by
    simpa [prefixWord, tailWord_6571644, baseEnd_6571644] using wordTrace_append hprefix tailTrace_6571644
  have hstable : (prefixWord ++ tailWord_6571644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571644).length < 2 ^ (prefixWord ++ tailWord_6571644).sum := by decide
  have hdescent : baseEnd_6571644 < baseStart_6571644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571672 : List Nat := [2, 1, 2, 4, 1, 3, 2, 2, 2, 2, 2]
def baseStart_6571672 : Nat := 118140960795 + 6571672 * 2 ^ 59
def prefixEnd_6571672 : Nat := 4983230072969 + 3 ^ 40 * 6571672 * 2
def baseEnd_6571672 : Nat := 3374426439693717536777437

theorem tailTrace_6571672 : CollatzResearch.WordTrace tailWord_6571672 prefixEnd_6571672 3374426439693717536777437 := by
  unfold tailWord_6571672
  simp only [CollatzResearch.WordTrace]
  refine ⟨119844284523981085533842635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159792379365308114045123513 119844284523981085533842635)
  ·
    refine ⟨179766426785971628300763953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119844284523981085533842635 179766426785971628300763953)
    ·
      refine ⟨134824820089478721225572965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179766426785971628300763953 134824820089478721225572965)
      ·
        refine ⟨25279653766777260229794931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134824820089478721225572965 25279653766777260229794931)
        ·
          refine ⟨37919480650165890344692397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25279653766777260229794931 37919480650165890344692397)
          ·
            refine ⟨14219805243812208879259649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37919480650165890344692397 14219805243812208879259649)
            ·
              refine ⟨10664853932859156659444737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14219805243812208879259649 10664853932859156659444737)
              ·
                refine ⟨7998640449644367494583553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10664853932859156659444737 7998640449644367494583553)
                ·
                  refine ⟨5998980337233275620937665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7998640449644367494583553 5998980337233275620937665)
                  ·
                    refine ⟨4499235252924956715703249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5998980337233275620937665 4499235252924956715703249)
                    ·
                      refine ⟨3374426439693717536777437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4499235252924956715703249 3374426439693717536777437)
                      ·
                        rfl

theorem cell23_6571672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_6571672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571672 prefixEnd_6571672 := by exact prefixLift 6571672
  have htrace : WordTrace (prefixWord ++ tailWord_6571672) baseStart_6571672 baseEnd_6571672 := by
    simpa [prefixWord, tailWord_6571672, baseEnd_6571672] using wordTrace_append hprefix tailTrace_6571672
  have hstable : (prefixWord ++ tailWord_6571672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571672).length < 2 ^ (prefixWord ++ tailWord_6571672).sum := by decide
  have hdescent : baseEnd_6571672 < baseStart_6571672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571708 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 2, 5]
def baseStart_6571708 : Nat := 118140960795 + 6571708 * 2 ^ 59
def prefixEnd_6571708 : Nat := 4983230072969 + 3 ^ 40 * 6571708 * 2
def baseEnd_6571708 : Nat := 1124814974999093131975757

theorem tailTrace_6571708 : CollatzResearch.WordTrace tailWord_6571708 prefixEnd_6571708 1124814974999093131975757 := by
  unfold tailWord_6571708
  simp only [CollatzResearch.WordTrace]
  refine ⟨119844941037915874607997889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159793254717221166143997185 119844941037915874607997889)
  ·
    refine ⟨89883705778436905955998417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119844941037915874607997889 89883705778436905955998417)
    ·
      refine ⟨67412779333827679466998813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89883705778436905955998417 67412779333827679466998813)
      ·
        refine ⟨25279792250185379800124555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67412779333827679466998813 25279792250185379800124555)
        ·
          refine ⟨37919688375278069700186833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25279792250185379800124555 37919688375278069700186833)
          ·
            refine ⟨28439766281458552275140125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37919688375278069700186833 28439766281458552275140125)
            ·
              refine ⟨10664912355546957103177547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28439766281458552275140125 10664912355546957103177547)
              ·
                refine ⟨15997368533320435654766321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10664912355546957103177547 15997368533320435654766321)
                ·
                  refine ⟨11998026399990326741074741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15997368533320435654766321 11998026399990326741074741)
                  ·
                    refine ⟨1124814974999093131975757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11998026399990326741074741 1124814974999093131975757)
                    ·
                      rfl

theorem cell23_6571708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_6571708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571708 prefixEnd_6571708 := by exact prefixLift 6571708
  have htrace : WordTrace (prefixWord ++ tailWord_6571708) baseStart_6571708 baseEnd_6571708 := by
    simpa [prefixWord, tailWord_6571708, baseEnd_6571708] using wordTrace_append hprefix tailTrace_6571708
  have hstable : (prefixWord ++ tailWord_6571708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571708).length < 2 ^ (prefixWord ++ tailWord_6571708).sum := by decide
  have hdescent : baseEnd_6571708 < baseStart_6571708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571711 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 4]
def baseStart_6571711 : Nat := 118140960795 + 6571711 * 2 ^ 59
def prefixEnd_6571711 : Nat := 4983230072969 + 3 ^ 40 * 6571711 * 2
def baseEnd_6571711 : Nat := 3374446465439242884189757

theorem tailTrace_6571711 : CollatzResearch.WordTrace tailWord_6571711 prefixEnd_6571711 3374446465439242884189757 := by
  unfold tailWord_6571711
  simp only [CollatzResearch.WordTrace]
  refine ⟨239689991494820880728354987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159793327663213920485569991 239689991494820880728354987)
  ·
    refine ⟨359534987242231321092532481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239689991494820880728354987 359534987242231321092532481)
    ·
      refine ⟨269651240431673490819399361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359534987242231321092532481 269651240431673490819399361)
      ·
        refine ⟨202238430323755118114549521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269651240431673490819399361 202238430323755118114549521)
        ·
          refine ⟨151678822742816338585912141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202238430323755118114549521 151678822742816338585912141)
          ·
            refine ⟨56879558528556126969717053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151678822742816338585912141 56879558528556126969717053)
            ·
              refine ⟨21329834448208547613643895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56879558528556126969717053 21329834448208547613643895)
              ·
                refine ⟨31994751672312821420465843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21329834448208547613643895 31994751672312821420465843)
                ·
                  refine ⟨47992127508469232130698765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31994751672312821420465843 47992127508469232130698765)
                  ·
                    refine ⟨17997047815675962049012037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47992127508469232130698765 17997047815675962049012037)
                    ·
                      refine ⟨3374446465439242884189757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17997047815675962049012037 3374446465439242884189757)
                      ·
                        rfl

theorem cell23_6571711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_6571711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571711 prefixEnd_6571711 := by exact prefixLift 6571711
  have htrace : WordTrace (prefixWord ++ tailWord_6571711) baseStart_6571711 baseEnd_6571711 := by
    simpa [prefixWord, tailWord_6571711, baseEnd_6571711] using wordTrace_append hprefix tailTrace_6571711
  have hstable : (prefixWord ++ tailWord_6571711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571711).length < 2 ^ (prefixWord ++ tailWord_6571711).sum := by decide
  have hdescent : baseEnd_6571711 < baseStart_6571711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571738 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 3, 4]
def baseStart_6571738 : Nat := 118140960795 + 6571738 * 2 ^ 59
def prefixEnd_6571738 : Nat := 4983230072969 + 3 ^ 40 * 6571738 * 2
def baseEnd_6571738 : Nat := 1124820109805638092850711

theorem tailTrace_6571738 : CollatzResearch.WordTrace tailWord_6571738 prefixEnd_6571738 1124820109805638092850711 := by
  unfold tailWord_6571738
  simp only [CollatzResearch.WordTrace]
  refine ⟨59922744066430766084896967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159793984177148709559725245 59922744066430766084896967)
  ·
    refine ⟨89884116099646149127345451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59922744066430766084896967 89884116099646149127345451)
    ·
      refine ⟨134826174149469223691018177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89884116099646149127345451 134826174149469223691018177)
      ·
        refine ⟨101119630612101917768263633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134826174149469223691018177 101119630612101917768263633)
        ·
          refine ⟨75839722959076438326197725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101119630612101917768263633 75839722959076438326197725)
          ·
            refine ⟨28439896109653664372324147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75839722959076438326197725 28439896109653664372324147)
            ·
              refine ⟨42659844164480496558486221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28439896109653664372324147 42659844164480496558486221)
              ·
                refine ⟨15997441561680186209432333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42659844164480496558486221 15997441561680186209432333)
                ·
                  refine ⟨5999040585630069828537125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15997441561680186209432333 5999040585630069828537125)
                  ·
                    refine ⟨1124820109805638092850711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5999040585630069828537125 1124820109805638092850711)
                    ·
                      rfl

theorem cell23_6571738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_6571738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571738 prefixEnd_6571738 := by exact prefixLift 6571738
  have htrace : WordTrace (prefixWord ++ tailWord_6571738) baseStart_6571738 baseEnd_6571738 := by
    simpa [prefixWord, tailWord_6571738, baseEnd_6571738] using wordTrace_append hprefix tailTrace_6571738
  have hstable : (prefixWord ++ tailWord_6571738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571738).length < 2 ^ (prefixWord ++ tailWord_6571738).sum := by decide
  have hdescent : baseEnd_6571738 < baseStart_6571738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571781 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 7, 5]
def baseStart_6571781 : Nat := 118140960795 + 6571781 * 2 ^ 59
def prefixEnd_6571781 : Nat := 4983230072969 + 3 ^ 40 * 6571781 * 2
def baseEnd_6571781 : Nat := 1124827469695019203438145

theorem tailTrace_6571781 : CollatzResearch.WordTrace tailWord_6571781 prefixEnd_6571781 1124827469695019203438145 := by
  unfold tailWord_6571781
  simp only [CollatzResearch.WordTrace]
  refine ⟨239692544604567282683403197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159795029736378188455602131 239692544604567282683403197)
  ·
    refine ⟨89884704226712731006276199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239692544604567282683403197 89884704226712731006276199)
    ·
      refine ⟨134827056340069096509414299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89884704226712731006276199 134827056340069096509414299)
      ·
        refine ⟨202240584510103644764121449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134827056340069096509414299 202240584510103644764121449)
        ·
          refine ⟨151680438382577733573091087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202240584510103644764121449 151680438382577733573091087)
          ·
            refine ⟨227520657573866600359636631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151680438382577733573091087 227520657573866600359636631)
            ·
              refine ⟨341280986360799900539454947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227520657573866600359636631 341280986360799900539454947)
              ·
                refine ⟨511921479541199850809182421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341280986360799900539454947 511921479541199850809182421)
                ·
                  refine ⟨11998159676746871503340213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 511921479541199850809182421 11998159676746871503340213)
                  ·
                    refine ⟨1124827469695019203438145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11998159676746871503340213 1124827469695019203438145)
                    ·
                      rfl

theorem cell23_6571781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_6571781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571781 prefixEnd_6571781 := by exact prefixLift 6571781
  have htrace : WordTrace (prefixWord ++ tailWord_6571781) baseStart_6571781 baseEnd_6571781 := by
    simpa [prefixWord, tailWord_6571781, baseEnd_6571781] using wordTrace_append hprefix tailTrace_6571781
  have hstable : (prefixWord ++ tailWord_6571781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571781).length < 2 ^ (prefixWord ++ tailWord_6571781).sum := by decide
  have hdescent : baseEnd_6571781 < baseStart_6571781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571831 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_6571831 : Nat := 118140960795 + 6571831 * 2 ^ 59
def prefixEnd_6571831 : Nat := 4983230072969 + 3 ^ 40 * 6571831 * 2
def baseEnd_6571831 : Nat := 3374508083117782414689205

theorem tailTrace_6571831 : CollatzResearch.WordTrace tailWord_6571831 prefixEnd_6571831 3374508083117782414689205 := by
  unfold tailWord_6571831
  simp only [CollatzResearch.WordTrace]
  refine ⟨239694368254386141222723347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159796245502924094148482231 239694368254386141222723347)
  ·
    refine ⟨359541552381579211834085021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239694368254386141222723347 359541552381579211834085021)
    ·
      refine ⟨134828082143092204437781883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359541552381579211834085021 134828082143092204437781883)
      ·
        refine ⟨202242123214638306656672825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134828082143092204437781883 202242123214638306656672825)
        ·
          refine ⟨151681592410978729992504619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202242123214638306656672825 151681592410978729992504619)
          ·
            refine ⟨227522388616468094988756929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151681592410978729992504619 227522388616468094988756929)
            ·
              refine ⟨170641791462351071241567697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227522388616468094988756929 170641791462351071241567697)
              ·
                refine ⟨127981343596763303431175773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170641791462351071241567697 127981343596763303431175773)
                ·
                  refine ⟨47993003848786238786690915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127981343596763303431175773 47993003848786238786690915)
                  ·
                    refine ⟨71989505773179358180036373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47993003848786238786690915 71989505773179358180036373)
                    ·
                      refine ⟨3374508083117782414689205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71989505773179358180036373 3374508083117782414689205)
                      ·
                        rfl

theorem cell23_6571831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_6571831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571831 prefixEnd_6571831 := by exact prefixLift 6571831
  have htrace : WordTrace (prefixWord ++ tailWord_6571831) baseStart_6571831 baseEnd_6571831 := by
    simpa [prefixWord, tailWord_6571831, baseEnd_6571831] using wordTrace_append hprefix tailTrace_6571831
  have hstable : (prefixWord ++ tailWord_6571831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571831).length < 2 ^ (prefixWord ++ tailWord_6571831).sum := by decide
  have hdescent : baseEnd_6571831 < baseStart_6571831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571841 : List Nat := [1, 2, 5, 15]
def baseStart_6571841 : Nat := 118140960795 + 6571841 * 2 ^ 59
def prefixEnd_6571841 : Nat := 4983230072969 + 3 ^ 40 * 6571841 * 2
def baseEnd_6571841 : Nat := 1542987296718942558557

theorem tailTrace_6571841 : CollatzResearch.WordTrace tailWord_6571841 prefixEnd_6571841 1542987296718942558557 := by
  unfold tailWord_6571841
  simp only [CollatzResearch.WordTrace]
  refine ⟨239694732984349912930587377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159796488656233275287058251 239694732984349912930587377)
  ·
    refine ⟨179771049738262434697940533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239694732984349912930587377 179771049738262434697940533)
    ·
      refine ⟨16853535912962103252931925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179771049738262434697940533 16853535912962103252931925)
      ·
        refine ⟨1542987296718942558557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 16853535912962103252931925 1542987296718942558557)
        ·
          rfl

theorem cell23_6571841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 15].length) (baseStart_6571841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571841 prefixEnd_6571841 := by exact prefixLift 6571841
  have htrace : WordTrace (prefixWord ++ tailWord_6571841) baseStart_6571841 baseEnd_6571841 := by
    simpa [prefixWord, tailWord_6571841, baseEnd_6571841] using wordTrace_append hprefix tailTrace_6571841
  have hstable : (prefixWord ++ tailWord_6571841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571841).length < 2 ^ (prefixWord ++ tailWord_6571841).sum := by decide
  have hdescent : baseEnd_6571841 < baseStart_6571841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571845 : List Nat := [1, 3, 1, 1, 1, 2, 6, 2, 2, 4]
def baseStart_6571845 : Nat := 118140960795 + 6571845 * 2 ^ 59
def prefixEnd_6571845 : Nat := 4983230072969 + 3 ^ 40 * 6571845 * 2
def baseEnd_6571845 : Nat := 1124838423948981786638047

theorem tailTrace_6571845 : CollatzResearch.WordTrace tailWord_6571845 prefixEnd_6571845 1124838423948981786638047 := by
  unfold tailWord_6571845
  simp only [CollatzResearch.WordTrace]
  refine ⟨239694878876335421613732989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159796585917556947742488659 239694878876335421613732989)
  ·
    refine ⟨89885579578625783105149871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239694878876335421613732989 89885579578625783105149871)
    ·
      refine ⟨134828369367938674657724807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89885579578625783105149871 134828369367938674657724807)
      ·
        refine ⟨202242554051908011986587211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134828369367938674657724807 202242554051908011986587211)
        ·
          refine ⟨303363831077862017979880817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202242554051908011986587211 303363831077862017979880817)
          ·
            refine ⟨227522873308396513484910613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303363831077862017979880817 227522873308396513484910613)
            ·
              refine ⟨10665134686331086569605185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 227522873308396513484910613 10665134686331086569605185)
              ·
                refine ⟨7998851014748314927203889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10665134686331086569605185 7998851014748314927203889)
                ·
                  refine ⟨5999138261061236195402917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7998851014748314927203889 5999138261061236195402917)
                  ·
                    refine ⟨1124838423948981786638047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5999138261061236195402917 1124838423948981786638047)
                    ·
                      rfl

theorem cell23_6571845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_6571845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571845 prefixEnd_6571845 := by exact prefixLift 6571845
  have htrace : WordTrace (prefixWord ++ tailWord_6571845) baseStart_6571845 baseEnd_6571845 := by
    simpa [prefixWord, tailWord_6571845, baseEnd_6571845] using wordTrace_append hprefix tailTrace_6571845
  have hstable : (prefixWord ++ tailWord_6571845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571845).length < 2 ^ (prefixWord ++ tailWord_6571845).sum := by decide
  have hdescent : baseEnd_6571845 < baseStart_6571845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571858 : List Nat := [3, 2, 2, 1, 1, 3, 3, 8]
def baseStart_6571858 : Nat := 118140960795 + 6571858 * 2 ^ 59
def prefixEnd_6571858 : Nat := 4983230072969 + 3 ^ 40 * 6571858 * 2
def baseEnd_6571858 : Nat := 124982294336868659594503

theorem tailTrace_6571858 : CollatzResearch.WordTrace tailWord_6571858 prefixEnd_6571858 124982294336868659594503 := by
  unfold tailWord_6571858
  simp only [CollatzResearch.WordTrace]
  refine ⟨59923838256322081208489057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159796902016858883222637485 59923838256322081208489057)
  ·
    refine ⟨44942878692241560906366793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59923838256322081208489057 44942878692241560906366793)
    ·
      refine ⟨33707159019181170679775095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44942878692241560906366793 33707159019181170679775095)
      ·
        refine ⟨50560738528771756019662643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33707159019181170679775095 50560738528771756019662643)
        ·
          refine ⟨75841107793157634029493965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50560738528771756019662643 75841107793157634029493965)
          ·
            refine ⟨28440415422434112761060237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75841107793157634029493965 28440415422434112761060237)
            ·
              refine ⟨10665155783412792285397589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28440415422434112761060237 10665155783412792285397589)
              ·
                refine ⟨124982294336868659594503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10665155783412792285397589 124982294336868659594503)
                ·
                  rfl

theorem cell23_6571858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 8].length) (baseStart_6571858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571858 prefixEnd_6571858 := by exact prefixLift 6571858
  have htrace : WordTrace (prefixWord ++ tailWord_6571858) baseStart_6571858 baseEnd_6571858 := by
    simpa [prefixWord, tailWord_6571858, baseEnd_6571858] using wordTrace_append hprefix tailTrace_6571858
  have hstable : (prefixWord ++ tailWord_6571858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571858).length < 2 ^ (prefixWord ++ tailWord_6571858).sum := by decide
  have hdescent : baseEnd_6571858 < baseStart_6571858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571875 : List Nat := [1, 1, 1, 5, 4, 1, 3, 7]
def baseStart_6571875 : Nat := 118140960795 + 6571875 * 2 ^ 59
def prefixEnd_6571875 : Nat := 4983230072969 + 3 ^ 40 * 6571875 * 2
def baseEnd_6571875 : Nat := 124982617639502971945889

theorem tailTrace_6571875 : CollatzResearch.WordTrace tailWord_6571875 prefixEnd_6571875 124982617639502971945889 := by
  unfold tailWord_6571875
  simp only [CollatzResearch.WordTrace]
  refine ⟨239695973066226736737325079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159797315377484491158216719 239695973066226736737325079)
  ·
    refine ⟨359543959599340105105987619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239695973066226736737325079 359543959599340105105987619)
    ·
      refine ⟨539315939399010157658981429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359543959599340105105987619 539315939399010157658981429)
      ·
        refine ⟨50560869318657202280529509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 539315939399010157658981429 50560869318657202280529509)
        ·
          refine ⟨9480162997248225427599283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50560869318657202280529509 9480162997248225427599283)
          ·
            refine ⟨14220244495872338141398925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9480162997248225427599283 14220244495872338141398925)
            ·
              refine ⟨5332591685952126803024597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14220244495872338141398925 5332591685952126803024597)
              ·
                refine ⟨124982617639502971945889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5332591685952126803024597 124982617639502971945889)
                ·
                  rfl

theorem cell23_6571875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 7].length) (baseStart_6571875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571875 prefixEnd_6571875 := by exact prefixLift 6571875
  have htrace : WordTrace (prefixWord ++ tailWord_6571875) baseStart_6571875 baseEnd_6571875 := by
    simpa [prefixWord, tailWord_6571875, baseEnd_6571875] using wordTrace_append hprefix tailTrace_6571875
  have hstable : (prefixWord ++ tailWord_6571875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571875).length < 2 ^ (prefixWord ++ tailWord_6571875).sum := by decide
  have hdescent : baseEnd_6571875 < baseStart_6571875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571885 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_6571885 : Nat := 118140960795 + 6571885 * 2 ^ 59
def prefixEnd_6571885 : Nat := 4983230072969 + 3 ^ 40 * 6571885 * 2
def baseEnd_6571885 : Nat := 3374535811073125203413957

theorem tailTrace_6571885 : CollatzResearch.WordTrace tailWord_6571885 prefixEnd_6571885 3374535811073125203413957 := by
  unfold tailWord_6571885
  simp only [CollatzResearch.WordTrace]
  refine ⟨239696337796190508445189109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159797558530793672296792739 239696337796190508445189109)
  ·
    refine ⟨22471531668392860166736479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239696337796190508445189109 22471531668392860166736479)
    ·
      refine ⟨33707297502589290250104719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22471531668392860166736479 33707297502589290250104719)
      ·
        refine ⟨50560946253883935375157079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33707297502589290250104719 50560946253883935375157079)
        ·
          refine ⟨75841419380825903062735619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50560946253883935375157079 75841419380825903062735619)
          ·
            refine ⟨113762129071238854594103429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75841419380825903062735619 113762129071238854594103429)
            ·
              refine ⟨21330399200857285236394393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113762129071238854594103429 21330399200857285236394393)
              ·
                refine ⟨15997799400642963927295795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21330399200857285236394393 15997799400642963927295795)
                ·
                  refine ⟨23996699100964445890943693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15997799400642963927295795 23996699100964445890943693)
                  ·
                    refine ⟨8998762162861667209103885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23996699100964445890943693 8998762162861667209103885)
                    ·
                      refine ⟨3374535811073125203413957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8998762162861667209103885 3374535811073125203413957)
                      ·
                        rfl

theorem cell23_6571885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_6571885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571885 prefixEnd_6571885 := by exact prefixLift 6571885
  have htrace : WordTrace (prefixWord ++ tailWord_6571885) baseStart_6571885 baseEnd_6571885 := by
    simpa [prefixWord, tailWord_6571885, baseEnd_6571885] using wordTrace_append hprefix tailTrace_6571885
  have hstable : (prefixWord ++ tailWord_6571885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571885).length < 2 ^ (prefixWord ++ tailWord_6571885).sum := by decide
  have hdescent : baseEnd_6571885 < baseStart_6571885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571886 : List Nat := [4, 1, 2, 3, 1, 1, 1, 5, 1, 2, 2]
def baseStart_6571886 : Nat := 118140960795 + 6571886 * 2 ^ 59
def prefixEnd_6571886 : Nat := 4983230072969 + 3 ^ 40 * 6571886 * 2
def baseEnd_6571886 : Nat := 3374536324553779699501453

theorem tailTrace_6571886 : CollatzResearch.WordTrace tailWord_6571886 prefixEnd_6571886 3374536324553779699501453 := by
  unfold tailWord_6571886
  simp only [CollatzResearch.WordTrace]
  refine ⟨29962046783648360701996939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159797582846124590410650341 29962046783648360701996939)
  ·
    refine ⟨44943070175472541052995409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29962046783648360701996939 44943070175472541052995409)
    ·
      refine ⟨33707302631604405789746557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44943070175472541052995409 33707302631604405789746557)
      ·
        refine ⟨12640238486851652171154959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33707302631604405789746557 12640238486851652171154959)
        ·
          refine ⟨18960357730277478256732439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12640238486851652171154959 18960357730277478256732439)
          ·
            refine ⟨28440536595416217385098659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18960357730277478256732439 28440536595416217385098659)
            ·
              refine ⟨42660804893124326077647989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28440536595416217385098659 42660804893124326077647989)
              ·
                refine ⟨3999450458730405569779499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42660804893124326077647989 3999450458730405569779499)
                ·
                  refine ⟨5999175688095608354669249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3999450458730405569779499 5999175688095608354669249)
                  ·
                    refine ⟨4499381766071706266001937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5999175688095608354669249 4499381766071706266001937)
                    ·
                      refine ⟨3374536324553779699501453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4499381766071706266001937 3374536324553779699501453)
                      ·
                        rfl

theorem cell23_6571886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_6571886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571886 prefixEnd_6571886 := by exact prefixLift 6571886
  have htrace : WordTrace (prefixWord ++ tailWord_6571886) baseStart_6571886 baseEnd_6571886 := by
    simpa [prefixWord, tailWord_6571886, baseEnd_6571886] using wordTrace_append hprefix tailTrace_6571886
  have hstable : (prefixWord ++ tailWord_6571886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571886).length < 2 ^ (prefixWord ++ tailWord_6571886).sum := by decide
  have hdescent : baseEnd_6571886 < baseStart_6571886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571908 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_6571908 : Nat := 118140960795 + 6571908 * 2 ^ 59
def prefixEnd_6571908 : Nat := 4983230072969 + 3 ^ 40 * 6571908 * 2
def baseEnd_6571908 : Nat := 3374547621128178613426351

theorem tailTrace_6571908 : CollatzResearch.WordTrace tailWord_6571908 prefixEnd_6571908 3374547621128178613426351 := by
  unfold tailWord_6571908
  simp only [CollatzResearch.WordTrace]
  refine ⟨119848588337553591686638189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159798117783404788915517585 119848588337553591686638189)
  ·
    refine ⟨44943220626582596882489321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119848588337553591686638189 44943220626582596882489321)
    ·
      refine ⟨33707415469936947661866991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44943220626582596882489321 33707415469936947661866991)
      ·
        refine ⟨50561123204905421492800487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33707415469936947661866991 50561123204905421492800487)
        ·
          refine ⟨75841684807358132239200731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50561123204905421492800487 75841684807358132239200731)
          ·
            refine ⟨113762527211037198358801097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75841684807358132239200731 113762527211037198358801097)
            ·
              refine ⟨85321895408277898769100823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113762527211037198358801097 85321895408277898769100823)
              ·
                refine ⟨127982843112416848153651235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85321895408277898769100823 127982843112416848153651235)
                ·
                  refine ⟨191974264668625272230476853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127982843112416848153651235 191974264668625272230476853)
                  ·
                    refine ⟨17997587312683619271607205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 191974264668625272230476853 17997587312683619271607205)
                    ·
                      refine ⟨3374547621128178613426351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17997587312683619271607205 3374547621128178613426351)
                      ·
                        rfl

theorem cell23_6571908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_6571908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571908 prefixEnd_6571908 := by exact prefixLift 6571908
  have htrace : WordTrace (prefixWord ++ tailWord_6571908) baseStart_6571908 baseEnd_6571908 := by
    simpa [prefixWord, tailWord_6571908, baseEnd_6571908] using wordTrace_append hprefix tailTrace_6571908
  have hstable : (prefixWord ++ tailWord_6571908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571908).length < 2 ^ (prefixWord ++ tailWord_6571908).sum := by decide
  have hdescent : baseEnd_6571908 < baseStart_6571908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571926 : List Nat := [5, 3, 1, 1, 2, 2, 2, 7]
def baseStart_6571926 : Nat := 118140960795 + 6571926 * 2 ^ 59
def prefixEnd_6571926 : Nat := 4983230072969 + 3 ^ 40 * 6571926 * 2
def baseEnd_6571926 : Nat := 124983587547405909000047

theorem tailTrace_6571926 : CollatzResearch.WordTrace tailWord_6571926 prefixEnd_6571926 124983587547405909000047 := by
  unfold tailWord_6571926
  simp only [CollatzResearch.WordTrace]
  refine ⟨14981114574315123277964477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159798555459361314964954421 14981114574315123277964477)
  ·
    refine ⟨5617917965368171229236679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14981114574315123277964477 5617917965368171229236679)
    ·
      refine ⟨8426876948052256843855019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5617917965368171229236679 8426876948052256843855019)
      ·
        refine ⟨12640315422078385265782529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8426876948052256843855019 12640315422078385265782529)
        ·
          refine ⟨9480236566558788949336897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12640315422078385265782529 9480236566558788949336897)
          ·
            refine ⟨7110177424919091712002673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9480236566558788949336897 7110177424919091712002673)
            ·
              refine ⟨5332633068689318784002005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7110177424919091712002673 5332633068689318784002005)
              ·
                refine ⟨124983587547405909000047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5332633068689318784002005 124983587547405909000047)
                ·
                  rfl

theorem cell23_6571926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_6571926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571926 prefixEnd_6571926 := by exact prefixLift 6571926
  have htrace : WordTrace (prefixWord ++ tailWord_6571926) baseStart_6571926 baseEnd_6571926 := by
    simpa [prefixWord, tailWord_6571926, baseEnd_6571926] using wordTrace_append hprefix tailTrace_6571926
  have hstable : (prefixWord ++ tailWord_6571926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571926).length < 2 ^ (prefixWord ++ tailWord_6571926).sum := by decide
  have hdescent : baseEnd_6571926 < baseStart_6571926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571965 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 7]
def baseStart_6571965 : Nat := 118140960795 + 6571965 * 2 ^ 59
def prefixEnd_6571965 : Nat := 4983230072969 + 3 ^ 40 * 6571965 * 2
def baseEnd_6571965 : Nat := 374952987725053876712621

theorem tailTrace_6571965 : CollatzResearch.WordTrace tailWord_6571965 prefixEnd_6571965 374952987725053876712621 := by
  unfold tailWord_6571965
  simp only [CollatzResearch.WordTrace]
  refine ⟨239699255635900682108101349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159799503757267121405400899 239699255635900682108101349)
  ·
    refine ⟨44943610431731377895269003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239699255635900682108101349 44943610431731377895269003)
    ·
      refine ⟨67415415647597066842903505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44943610431731377895269003 67415415647597066842903505)
      ·
        refine ⟨50561561735697800132177629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67415415647597066842903505 50561561735697800132177629)
        ·
          refine ⟨18960585650886675049566611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50561561735697800132177629 18960585650886675049566611)
          ·
            refine ⟨28440878476330012574349917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18960585650886675049566611 28440878476330012574349917)
            ·
              refine ⟨10665329428623754715381219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28440878476330012574349917 10665329428623754715381219)
              ·
                refine ⟨15997994142935632073071829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10665329428623754715381219 15997994142935632073071829)
                ·
                  refine ⟨374952987725053876712621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15997994142935632073071829 374952987725053876712621)
                  ·
                    rfl

theorem cell23_6571965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_6571965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571965 prefixEnd_6571965 := by exact prefixLift 6571965
  have htrace : WordTrace (prefixWord ++ tailWord_6571965) baseStart_6571965 baseEnd_6571965 := by
    simpa [prefixWord, tailWord_6571965, baseEnd_6571965] using wordTrace_append hprefix tailTrace_6571965
  have hstable : (prefixWord ++ tailWord_6571965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571965).length < 2 ^ (prefixWord ++ tailWord_6571965).sum := by decide
  have hdescent : baseEnd_6571965 < baseStart_6571965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571976 : List Nat := [2, 1, 3, 1, 4, 1, 4, 1, 2, 2, 2]
def baseStart_6571976 : Nat := 118140960795 + 6571976 * 2 ^ 59
def prefixEnd_6571976 : Nat := 4983230072969 + 3 ^ 40 * 6571976 * 2
def baseEnd_6571976 : Nat := 3374582537812684347376039

theorem tailTrace_6571976 : CollatzResearch.WordTrace tailWord_6571976 prefixEnd_6571976 3374582537812684347376039 := by
  unfold tailWord_6571976
  simp only [CollatzResearch.WordTrace]
  refine ⟨119849828419430415493375891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159799771225907220657834521 119849828419430415493375891)
  ·
    refine ⟨179774742629145623240063837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119849828419430415493375891 179774742629145623240063837)
    ·
      refine ⟨67415528485929608715023939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179774742629145623240063837 67415528485929608715023939)
      ·
        refine ⟨101123292728894413072535909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67415528485929608715023939 101123292728894413072535909)
        ·
          refine ⟨18960617386667702451100483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101123292728894413072535909 18960617386667702451100483)
          ·
            refine ⟨28440926080001553676650725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18960617386667702451100483 28440926080001553676650725)
            ·
              refine ⟨5332673640000291314372011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28440926080001553676650725 5332673640000291314372011)
              ·
                refine ⟨7999010460000436971558017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5332673640000291314372011 7999010460000436971558017)
                ·
                  refine ⟨5999257845000327728668513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7999010460000436971558017 5999257845000327728668513)
                  ·
                    refine ⟨4499443383750245796501385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5999257845000327728668513 4499443383750245796501385)
                    ·
                      refine ⟨3374582537812684347376039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4499443383750245796501385 3374582537812684347376039)
                      ·
                        rfl

theorem cell23_6571976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_6571976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571976 prefixEnd_6571976 := by exact prefixLift 6571976
  have htrace : WordTrace (prefixWord ++ tailWord_6571976) baseStart_6571976 baseEnd_6571976 := by
    simpa [prefixWord, tailWord_6571976, baseEnd_6571976] using wordTrace_append hprefix tailTrace_6571976
  have hstable : (prefixWord ++ tailWord_6571976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571976).length < 2 ^ (prefixWord ++ tailWord_6571976).sum := by decide
  have hdescent : baseEnd_6571976 < baseStart_6571976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571978 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 3, 7]
def baseStart_6571978 : Nat := 118140960795 + 6571978 * 2 ^ 59
def prefixEnd_6571978 : Nat := 4983230072969 + 3 ^ 40 * 6571978 * 2
def baseEnd_6571978 : Nat := 1124861188257997779850343

theorem tailTrace_6571978 : CollatzResearch.WordTrace tailWord_6571978 prefixEnd_6571978 1124861188257997779850343 := by
  unfold tailWord_6571978
  simp only [CollatzResearch.WordTrace]
  refine ⟨59924932446213396332081147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159799819856569056885549725 59924932446213396332081147)
  ·
    refine ⟨89887398669320094498121721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59924932446213396332081147 89887398669320094498121721)
    ·
      refine ⟨67415549001990070873591291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89887398669320094498121721 67415549001990070873591291)
      ·
        refine ⟨101123323502985106310386937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67415549001990070873591291 101123323502985106310386937)
        ·
          refine ⟨75842492627238829732790203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101123323502985106310386937 75842492627238829732790203)
          ·
            refine ⟨113763738940858244599185305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75842492627238829732790203 113763738940858244599185305)
            ·
              refine ⟨85322804205643683449388979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113763738940858244599185305 85322804205643683449388979)
              ·
                refine ⟨127984206308465525174083469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85322804205643683449388979 127984206308465525174083469)
                ·
                  refine ⟨47994077365674571940281301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127984206308465525174083469 47994077365674571940281301)
                  ·
                    refine ⟨1124861188257997779850343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47994077365674571940281301 1124861188257997779850343)
                    ·
                      rfl

theorem cell23_6571978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_6571978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571978 prefixEnd_6571978 := by exact prefixLift 6571978
  have htrace : WordTrace (prefixWord ++ tailWord_6571978) baseStart_6571978 baseEnd_6571978 := by
    simpa [prefixWord, tailWord_6571978, baseEnd_6571978] using wordTrace_append hprefix tailTrace_6571978
  have hstable : (prefixWord ++ tailWord_6571978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571978).length < 2 ^ (prefixWord ++ tailWord_6571978).sum := by decide
  have hdescent : baseEnd_6571978 < baseStart_6571978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6571985 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 4, 5, 2]
def baseStart_6571985 : Nat := 118140960795 + 6571985 * 2 ^ 59
def prefixEnd_6571985 : Nat := 4983230072969 + 3 ^ 40 * 6571985 * 2
def baseEnd_6571985 : Nat := 3374587159138574812163497

theorem tailTrace_6571985 : CollatzResearch.WordTrace tailWord_6571985 prefixEnd_6571985 3374587159138574812163497 := by
  unfold tailWord_6571985
  simp only [CollatzResearch.WordTrace]
  refine ⟨239699985095828225523829409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159799990063885483682552939 239699985095828225523829409)
  ·
    refine ⟨179774988821871169142872057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239699985095828225523829409 179774988821871169142872057)
    ·
      refine ⟨134831241616403376857154043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179774988821871169142872057 134831241616403376857154043)
      ·
        refine ⟨202246862424605065285731065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134831241616403376857154043 202246862424605065285731065)
        ·
          refine ⟨151685146818453798964298299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202246862424605065285731065 151685146818453798964298299)
          ·
            refine ⟨227527720227680698446447449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151685146818453798964298299 227527720227680698446447449)
            ·
              refine ⟨170645790170760523834835587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227527720227680698446447449 170645790170760523834835587)
              ·
                refine ⟨255968685256140785752253381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170645790170760523834835587 255968685256140785752253381)
                ·
                  refine ⟨47994128485526397328547509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255968685256140785752253381 47994128485526397328547509)
                  ·
                    refine ⟨4499449545518099749551329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47994128485526397328547509 4499449545518099749551329)
                    ·
                      refine ⟨3374587159138574812163497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4499449545518099749551329 3374587159138574812163497)
                      ·
                        rfl

theorem cell23_6571985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 5, 2].length) (baseStart_6571985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6571985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6571985 prefixEnd_6571985 := by exact prefixLift 6571985
  have htrace : WordTrace (prefixWord ++ tailWord_6571985) baseStart_6571985 baseEnd_6571985 := by
    simpa [prefixWord, tailWord_6571985, baseEnd_6571985] using wordTrace_append hprefix tailTrace_6571985
  have hstable : (prefixWord ++ tailWord_6571985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6571985).length < 2 ^ (prefixWord ++ tailWord_6571985).sum := by decide
  have hdescent : baseEnd_6571985 < baseStart_6571985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6571985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572015 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 4]
def baseStart_6572015 : Nat := 118140960795 + 6572015 * 2 ^ 59
def prefixEnd_6572015 : Nat := 4983230072969 + 3 ^ 40 * 6572015 * 2
def baseEnd_6572015 : Nat := 3374602563558209694788359

theorem tailTrace_6572015 : CollatzResearch.WordTrace tailWord_6572015 prefixEnd_6572015 3374602563558209694788359 := by
  unfold tailWord_6572015
  simp only [CollatzResearch.WordTrace]
  refine ⟨239701079285719540647421499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159800719523813027098280999 239701079285719540647421499)
  ·
    refine ⟨359551618928579310971132249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239701079285719540647421499 359551618928579310971132249)
    ·
      refine ⟨269663714196434483228349187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359551618928579310971132249 269663714196434483228349187)
      ·
        refine ⟨404495571294651724842523781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269663714196434483228349187 404495571294651724842523781)
        ·
          refine ⟨75842919617747198407973209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 404495571294651724842523781 75842919617747198407973209)
          ·
            refine ⟨56882189713310398805979907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75842919617747198407973209 56882189713310398805979907)
            ·
              refine ⟨85323284569965598208969861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56882189713310398805979907 85323284569965598208969861)
              ·
                refine ⟨15998115856868549664181849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85323284569965598208969861 15998115856868549664181849)
                ·
                  refine ⟨11998586892651412248136387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15998115856868549664181849 11998586892651412248136387)
                  ·
                    refine ⟨17997880338977118372204581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11998586892651412248136387 17997880338977118372204581)
                    ·
                      refine ⟨3374602563558209694788359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17997880338977118372204581 3374602563558209694788359)
                      ·
                        rfl

theorem cell23_6572015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_6572015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572015 prefixEnd_6572015 := by exact prefixLift 6572015
  have htrace : WordTrace (prefixWord ++ tailWord_6572015) baseStart_6572015 baseEnd_6572015 := by
    simpa [prefixWord, tailWord_6572015, baseEnd_6572015] using wordTrace_append hprefix tailTrace_6572015
  have hstable : (prefixWord ++ tailWord_6572015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572015).length < 2 ^ (prefixWord ++ tailWord_6572015).sum := by decide
  have hdescent : baseEnd_6572015 < baseStart_6572015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572035 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 3]
def baseStart_6572035 : Nat := 118140960795 + 6572035 * 2 ^ 59
def prefixEnd_6572035 : Nat := 4983230072969 + 3 ^ 40 * 6572035 * 2
def baseEnd_6572035 : Nat := 3374612833171299616538267

theorem tailTrace_6572035 : CollatzResearch.WordTrace tailWord_6572035 prefixEnd_6572035 3374612833171299616538267 := by
  unfold tailWord_6572035
  simp only [CollatzResearch.WordTrace]
  refine ⟨239701808745647084063149559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159801205830431389375433039 239701808745647084063149559)
  ·
    refine ⟨359552713118470626094724339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239701808745647084063149559 359552713118470626094724339)
    ·
      refine ⟨539329069677705939142086509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359552713118470626094724339 539329069677705939142086509)
      ·
        refine ⟨202248401129139727178282441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 539329069677705939142086509 202248401129139727178282441)
        ·
          refine ⟨151686300846854795383711831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202248401129139727178282441 151686300846854795383711831)
          ·
            refine ⟨227529451270282193075567747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151686300846854795383711831 227529451270282193075567747)
            ·
              refine ⟨341294176905423289613351621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227529451270282193075567747 341294176905423289613351621)
              ·
                refine ⟨63992658169766866802503429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341294176905423289613351621 63992658169766866802503429)
                ·
                  refine ⟨11998623406831287525469393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63992658169766866802503429 11998623406831287525469393)
                  ·
                    refine ⟨8998967555123465644102045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11998623406831287525469393 8998967555123465644102045)
                    ·
                      refine ⟨3374612833171299616538267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8998967555123465644102045 3374612833171299616538267)
                      ·
                        rfl

theorem cell23_6572035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_6572035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572035 prefixEnd_6572035 := by exact prefixLift 6572035
  have htrace : WordTrace (prefixWord ++ tailWord_6572035) baseStart_6572035 baseEnd_6572035 := by
    simpa [prefixWord, tailWord_6572035, baseEnd_6572035] using wordTrace_append hprefix tailTrace_6572035
  have hstable : (prefixWord ++ tailWord_6572035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572035).length < 2 ^ (prefixWord ++ tailWord_6572035).sum := by decide
  have hdescent : baseEnd_6572035 < baseStart_6572035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572085 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 5, 5]
def baseStart_6572085 : Nat := 118140960795 + 6572085 * 2 ^ 59
def prefixEnd_6572085 : Nat := 4983230072969 + 3 ^ 40 * 6572085 * 2
def baseEnd_6572085 : Nat := 1124879502401341473637679

theorem tailTrace_6572085 : CollatzResearch.WordTrace tailWord_6572085 prefixEnd_6572085 1124879502401341473637679 := by
  unfold tailWord_6572085
  simp only [CollatzResearch.WordTrace]
  refine ⟨239703632395465942602469709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159802421596977295068313139 239703632395465942602469709)
  ·
    refine ⟨89888862148299728475926141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239703632395465942602469709 89888862148299728475926141)
    ·
      refine ⟨33708323305612398178472303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89888862148299728475926141 33708323305612398178472303)
      ·
        refine ⟨50562484958418597267708455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33708323305612398178472303 50562484958418597267708455)
        ·
          refine ⟨75843727437627895901562683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50562484958418597267708455 75843727437627895901562683)
          ·
            refine ⟨113765591156441843852344025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75843727437627895901562683 113765591156441843852344025)
            ·
              refine ⟨85324193367331382889258019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113765591156441843852344025 85324193367331382889258019)
              ·
                refine ⟨127986290050997074333887029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85324193367331382889258019 127986290050997074333887029)
                ·
                  refine ⟨11998714692280975718801909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127986290050997074333887029 11998714692280975718801909)
                  ·
                    refine ⟨1124879502401341473637679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11998714692280975718801909 1124879502401341473637679)
                    ·
                      rfl

theorem cell23_6572085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_6572085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572085 prefixEnd_6572085 := by exact prefixLift 6572085
  have htrace : WordTrace (prefixWord ++ tailWord_6572085) baseStart_6572085 baseEnd_6572085 := by
    simpa [prefixWord, tailWord_6572085, baseEnd_6572085] using wordTrace_append hprefix tailTrace_6572085
  have hstable : (prefixWord ++ tailWord_6572085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572085).length < 2 ^ (prefixWord ++ tailWord_6572085).sum := by decide
  have hdescent : baseEnd_6572085 < baseStart_6572085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572089 : List Nat := [1, 2, 1, 5, 3, 1, 3, 1, 6]
def baseStart_6572089 : Nat := 118140960795 + 6572089 * 2 ^ 59
def prefixEnd_6572089 : Nat := 4983230072969 + 3 ^ 40 * 6572089 * 2
def baseEnd_6572089 : Nat := 374960062347404711695891

theorem tailTrace_6572089 : CollatzResearch.WordTrace tailWord_6572089 prefixEnd_6572089 374960062347404711695891 := by
  unfold tailWord_6572089
  simp only [CollatzResearch.WordTrace]
  refine ⟨239703778287451451285615321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159802518858300967523743547 239703778287451451285615321)
  ·
    refine ⟨179777833715588588464211491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239703778287451451285615321 179777833715588588464211491)
    ·
      refine ⟨269666750573382882696317237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179777833715588588464211491 269666750573382882696317237)
      ·
        refine ⟨25281257866254645252779741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269666750573382882696317237 25281257866254645252779741)
        ·
          refine ⟨9480471699845491969792403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25281257866254645252779741 9480471699845491969792403)
          ·
            refine ⟨14220707549768237954688605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9480471699845491969792403 14220707549768237954688605)
            ·
              refine ⟨5332765331163089233008227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14220707549768237954688605 5332765331163089233008227)
              ·
                refine ⟨7999147996744633849512341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5332765331163089233008227 7999147996744633849512341)
                ·
                  refine ⟨374960062347404711695891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7999147996744633849512341 374960062347404711695891)
                  ·
                    rfl

theorem cell23_6572089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 6].length) (baseStart_6572089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572089 prefixEnd_6572089 := by exact prefixLift 6572089
  have htrace : WordTrace (prefixWord ++ tailWord_6572089) baseStart_6572089 baseEnd_6572089 := by
    simpa [prefixWord, tailWord_6572089, baseEnd_6572089] using wordTrace_append hprefix tailTrace_6572089
  have hstable : (prefixWord ++ tailWord_6572089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572089).length < 2 ^ (prefixWord ++ tailWord_6572089).sum := by decide
  have hdescent : baseEnd_6572089 < baseStart_6572089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572092 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 3, 5, 2]
def baseStart_6572092 : Nat := 118140960795 + 6572092 * 2 ^ 59
def prefixEnd_6572092 : Nat := 4983230072969 + 3 ^ 40 * 6572092 * 2
def baseEnd_6572092 : Nat := 3374642101568605893525505

theorem tailTrace_6572092 : CollatzResearch.WordTrace tailWord_6572092 prefixEnd_6572092 3374642101568605893525505 := by
  unfold tailWord_6572092
  simp only [CollatzResearch.WordTrace]
  refine ⟨119851943853220291398987265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159802591804293721865316353 119851943853220291398987265)
  ·
    refine ⟨89888957889915218549240449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119851943853220291398987265 89888957889915218549240449)
    ·
      refine ⟨67416718417436413911930337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89888957889915218549240449 67416718417436413911930337)
      ·
        refine ⟨50562538813077310433947753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67416718417436413911930337 50562538813077310433947753)
        ·
          refine ⟨37921904109807982825460815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50562538813077310433947753 37921904109807982825460815)
          ·
            refine ⟨56882856164711974238191223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37921904109807982825460815 56882856164711974238191223)
            ·
              refine ⟨85324284247067961357286835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56882856164711974238191223 85324284247067961357286835)
              ·
                refine ⟨127986426370601942035930253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85324284247067961357286835 127986426370601942035930253)
                ·
                  refine ⟨47994909888975728263473845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127986426370601942035930253 47994909888975728263473845)
                  ·
                    refine ⟨4499522802091474524700673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47994909888975728263473845 4499522802091474524700673)
                    ·
                      refine ⟨3374642101568605893525505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4499522802091474524700673 3374642101568605893525505)
                      ·
                        rfl

theorem cell23_6572092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_6572092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572092 prefixEnd_6572092 := by exact prefixLift 6572092
  have htrace : WordTrace (prefixWord ++ tailWord_6572092) baseStart_6572092 baseEnd_6572092 := by
    simpa [prefixWord, tailWord_6572092, baseEnd_6572092] using wordTrace_append hprefix tailTrace_6572092
  have hstable : (prefixWord ++ tailWord_6572092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572092).length < 2 ^ (prefixWord ++ tailWord_6572092).sum := by decide
  have hdescent : baseEnd_6572092 < baseStart_6572092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572109 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_6572109 : Nat := 118140960795 + 6572109 * 2 ^ 59
def prefixEnd_6572109 : Nat := 4983230072969 + 3 ^ 40 * 6572109 * 2
def baseEnd_6572109 : Nat := 3374650830739732327012927

theorem tailTrace_6572109 : CollatzResearch.WordTrace tailWord_6572109 prefixEnd_6572109 3374650830739732327012927 := by
  unfold tailWord_6572109
  simp only [CollatzResearch.WordTrace]
  refine ⟨239704507747378994701343381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159803005164919329800895587 239704507747378994701343381)
  ·
    refine ⟨11236148800658390376625471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 239704507747378994701343381 11236148800658390376625471)
    ·
      refine ⟨16854223200987585564938207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11236148800658390376625471 16854223200987585564938207)
      ·
        refine ⟨25281334801481378347407311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16854223200987585564938207 25281334801481378347407311)
        ·
          refine ⟨37922002202222067521110967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25281334801481378347407311 37922002202222067521110967)
          ·
            refine ⟨56883003303333101281666451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37922002202222067521110967 56883003303333101281666451)
            ·
              refine ⟨85324504954999651922499677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56883003303333101281666451 85324504954999651922499677)
              ·
                refine ⟨31996689358124869470937379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85324504954999651922499677 31996689358124869470937379)
                ·
                  refine ⟨47995034037187304206406069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31996689358124869470937379 47995034037187304206406069)
                  ·
                    refine ⟨4499534440986309769350569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47995034037187304206406069 4499534440986309769350569)
                    ·
                      refine ⟨3374650830739732327012927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4499534440986309769350569 3374650830739732327012927)
                      ·
                        rfl

theorem cell23_6572109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_6572109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572109 prefixEnd_6572109 := by exact prefixLift 6572109
  have htrace : WordTrace (prefixWord ++ tailWord_6572109) baseStart_6572109 baseEnd_6572109 := by
    simpa [prefixWord, tailWord_6572109, baseEnd_6572109] using wordTrace_append hprefix tailTrace_6572109
  have hstable : (prefixWord ++ tailWord_6572109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572109).length < 2 ^ (prefixWord ++ tailWord_6572109).sum := by decide
  have hdescent : baseEnd_6572109 < baseStart_6572109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572122 : List Nat := [3, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4]
def baseStart_6572122 : Nat := 118140960795 + 6572122 * 2 ^ 59
def prefixEnd_6572122 : Nat := 4983230072969 + 3 ^ 40 * 6572122 * 2
def baseEnd_6572122 : Nat := 3374657505988240776150367

theorem tailTrace_6572122 : CollatzResearch.WordTrace tailWord_6572122 prefixEnd_6572122 3374657505988240776150367 := by
  unfold tailWord_6572122
  simp only [CollatzResearch.WordTrace]
  refine ⟨59926245474082974480391655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159803321264221265281044413 59926245474082974480391655)
  ·
    refine ⟨89889368211124461720587483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59926245474082974480391655 89889368211124461720587483)
    ·
      refine ⟨134834052316686692580881225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89889368211124461720587483 134834052316686692580881225)
      ·
        refine ⟨101125539237515019435660919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134834052316686692580881225 101125539237515019435660919)
        ·
          refine ⟨151688308856272529153491379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101125539237515019435660919 151688308856272529153491379)
          ·
            refine ⟨227532463284408793730237069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151688308856272529153491379 227532463284408793730237069)
            ·
              refine ⟨85324673731653297648838901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227532463284408793730237069 85324673731653297648838901)
              ·
                refine ⟨7999188162342496654578647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85324673731653297648838901 7999188162342496654578647)
                ·
                  refine ⟨11998782243513744981867971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7999188162342496654578647 11998782243513744981867971)
                  ·
                    refine ⟨17998173365270617472801957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11998782243513744981867971 17998173365270617472801957)
                    ·
                      refine ⟨3374657505988240776150367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17998173365270617472801957 3374657505988240776150367)
                      ·
                        rfl

theorem cell23_6572122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_6572122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572122 prefixEnd_6572122 := by exact prefixLift 6572122
  have htrace : WordTrace (prefixWord ++ tailWord_6572122) baseStart_6572122 baseEnd_6572122 := by
    simpa [prefixWord, tailWord_6572122, baseEnd_6572122] using wordTrace_append hprefix tailTrace_6572122
  have hstable : (prefixWord ++ tailWord_6572122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572122).length < 2 ^ (prefixWord ++ tailWord_6572122).sum := by decide
  have hdescent : baseEnd_6572122 < baseStart_6572122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572132 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_6572132 : Nat := 118140960795 + 6572132 * 2 ^ 59
def prefixEnd_6572132 : Nat := 4983230072969 + 3 ^ 40 * 6572132 * 2
def baseEnd_6572132 : Nat := 1124887546931595245675107

theorem tailTrace_6572132 : CollatzResearch.WordTrace tailWord_6572132 prefixEnd_6572132 1124887546931595245675107 := by
  unfold tailWord_6572132
  simp only [CollatzResearch.WordTrace]
  refine ⟨119852673313147834814715325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159803564417530446419620433 119852673313147834814715325)
  ·
    refine ⟨44944752492430438055518247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119852673313147834814715325 44944752492430438055518247)
    ·
      refine ⟨67417128738645657083277371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44944752492430438055518247 67417128738645657083277371)
      ·
        refine ⟨101125693107968485624916057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67417128738645657083277371 101125693107968485624916057)
        ·
          refine ⟨75844269830976364218687043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101125693107968485624916057 75844269830976364218687043)
          ·
            refine ⟨113766404746464546328030565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75844269830976364218687043 113766404746464546328030565)
            ·
              refine ⟨21331200889962102436505731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113766404746464546328030565 21331200889962102436505731)
              ·
                refine ⟨31996801334943153654758597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21331200889962102436505731 31996801334943153654758597)
                ·
                  refine ⟨5999400250301841310267237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31996801334943153654758597 5999400250301841310267237)
                  ·
                    refine ⟨1124887546931595245675107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5999400250301841310267237 1124887546931595245675107)
                    ·
                      rfl

theorem cell23_6572132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_6572132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572132 prefixEnd_6572132 := by exact prefixLift 6572132
  have htrace : WordTrace (prefixWord ++ tailWord_6572132) baseStart_6572132 baseEnd_6572132 := by
    simpa [prefixWord, tailWord_6572132, baseEnd_6572132] using wordTrace_append hprefix tailTrace_6572132
  have hstable : (prefixWord ++ tailWord_6572132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572132).length < 2 ^ (prefixWord ++ tailWord_6572132).sum := by decide
  have hdescent : baseEnd_6572132 < baseStart_6572132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572133 : List Nat := [1, 3, 1, 3, 2, 3, 3, 2, 1, 1, 3]
def baseStart_6572133 : Nat := 118140960795 + 6572133 * 2 ^ 59
def prefixEnd_6572133 : Nat := 4983230072969 + 3 ^ 40 * 6572133 * 2
def baseEnd_6572133 : Nat := 3374663154275440233112817

theorem tailTrace_6572133 : CollatzResearch.WordTrace tailWord_6572133 prefixEnd_6572133 3374663154275440233112817 := by
  unfold tailWord_6572133
  simp only [CollatzResearch.WordTrace]
  refine ⟨239705383099292046800217053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159803588732861364533478035 239705383099292046800217053)
  ·
    refine ⟨89889518662234517550081395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239705383099292046800217053 89889518662234517550081395)
    ·
      refine ⟨134834277993351776325122093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89889518662234517550081395 134834277993351776325122093)
      ·
        refine ⟨50562854247506916121920785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134834277993351776325122093 50562854247506916121920785)
        ·
          refine ⟨37922140685630187091440589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50562854247506916121920785 37922140685630187091440589)
          ·
            refine ⟨14220802757111320159290221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37922140685630187091440589 14220802757111320159290221)
            ·
              refine ⟨5332801033916745059733833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14220802757111320159290221 5332801033916745059733833)
              ·
                refine ⟨3999600775437558794800375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5332801033916745059733833 3999600775437558794800375)
                ·
                  refine ⟨5999401163156338192200563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3999600775437558794800375 5999401163156338192200563)
                  ·
                    refine ⟨8999101744734507288300845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5999401163156338192200563 8999101744734507288300845)
                    ·
                      refine ⟨3374663154275440233112817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8999101744734507288300845 3374663154275440233112817)
                      ·
                        rfl

theorem cell23_6572133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_6572133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572133 prefixEnd_6572133 := by exact prefixLift 6572133
  have htrace : WordTrace (prefixWord ++ tailWord_6572133) baseStart_6572133 baseEnd_6572133 := by
    simpa [prefixWord, tailWord_6572133, baseEnd_6572133] using wordTrace_append hprefix tailTrace_6572133
  have hstable : (prefixWord ++ tailWord_6572133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572133).length < 2 ^ (prefixWord ++ tailWord_6572133).sum := by decide
  have hdescent : baseEnd_6572133 < baseStart_6572133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572135 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_6572135 : Nat := 118140960795 + 6572135 * 2 ^ 59
def prefixEnd_6572135 : Nat := 4983230072969 + 3 ^ 40 * 6572135 * 2
def baseEnd_6572135 : Nat := 3374664181236749225287807

theorem tailTrace_6572135 : CollatzResearch.WordTrace tailWord_6572135 prefixEnd_6572135 3374664181236749225287807 := by
  unfold tailWord_6572135
  simp only [CollatzResearch.WordTrace]
  refine ⟨239705456045284801141789859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159803637363523200761193239 239705456045284801141789859)
  ·
    refine ⟨359558184067927201712684789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239705456045284801141789859 359558184067927201712684789)
    ·
      refine ⟨33708579756368175160564199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 359558184067927201712684789 33708579756368175160564199)
      ·
        refine ⟨50562869634552262740846299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33708579756368175160564199 50562869634552262740846299)
        ·
          refine ⟨75844304451828394111269449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50562869634552262740846299 75844304451828394111269449)
          ·
            refine ⟨56883228338871295583452087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75844304451828394111269449 56883228338871295583452087)
            ·
              refine ⟨85324842508306943375178131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56883228338871295583452087 85324842508306943375178131)
              ·
                refine ⟨127987263762460415062767197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85324842508306943375178131 127987263762460415062767197)
                ·
                  refine ⟨47995223910922655648537699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127987263762460415062767197 47995223910922655648537699)
                  ·
                    refine ⟨71992835866383983472806549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47995223910922655648537699 71992835866383983472806549)
                    ·
                      refine ⟨3374664181236749225287807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71992835866383983472806549 3374664181236749225287807)
                      ·
                        rfl

theorem cell23_6572135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_6572135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572135 prefixEnd_6572135 := by exact prefixLift 6572135
  have htrace : WordTrace (prefixWord ++ tailWord_6572135) baseStart_6572135 baseEnd_6572135 := by
    simpa [prefixWord, tailWord_6572135, baseEnd_6572135] using wordTrace_append hprefix tailTrace_6572135
  have hstable : (prefixWord ++ tailWord_6572135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572135).length < 2 ^ (prefixWord ++ tailWord_6572135).sum := by decide
  have hdescent : baseEnd_6572135 < baseStart_6572135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572142 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_6572142 : Nat := 118140960795 + 6572142 * 2 ^ 59
def prefixEnd_6572142 : Nat := 4983230072969 + 3 ^ 40 * 6572142 * 2
def baseEnd_6572142 : Nat := 3374667775601330697900275

theorem tailTrace_6572142 : CollatzResearch.WordTrace tailWord_6572142 prefixEnd_6572142 3374667775601330697900275 := by
  unfold tailWord_6572142
  simp only [CollatzResearch.WordTrace]
  refine ⟨29963213919532430167161835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159803807570839627558196453 29963213919532430167161835)
  ·
    refine ⟨44944820879298645250742753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29963213919532430167161835 44944820879298645250742753)
    ·
      refine ⟨33708615659473983938057065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44944820879298645250742753 33708615659473983938057065)
      ·
        refine ⟨25281461744605487953542799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33708615659473983938057065 25281461744605487953542799)
        ·
          refine ⟨37922192616908231930314199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25281461744605487953542799 37922192616908231930314199)
          ·
            refine ⟨56883288925362347895471299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37922192616908231930314199 56883288925362347895471299)
            ·
              refine ⟨85324933388043521843206949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56883288925362347895471299 85324933388043521843206949)
              ·
                refine ⟨15998425010258160345601303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85324933388043521843206949 15998425010258160345601303)
                ·
                  refine ⟨23997637515387240518401955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15998425010258160345601303 23997637515387240518401955)
                  ·
                    refine ⟨35996456273080860777602933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23997637515387240518401955 35996456273080860777602933)
                    ·
                      refine ⟨3374667775601330697900275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35996456273080860777602933 3374667775601330697900275)
                      ·
                        rfl

theorem cell23_6572142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_6572142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572142 prefixEnd_6572142 := by exact prefixLift 6572142
  have htrace : WordTrace (prefixWord ++ tailWord_6572142) baseStart_6572142 baseEnd_6572142 := by
    simpa [prefixWord, tailWord_6572142, baseEnd_6572142] using wordTrace_append hprefix tailTrace_6572142
  have hstable : (prefixWord ++ tailWord_6572142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572142).length < 2 ^ (prefixWord ++ tailWord_6572142).sum := by decide
  have hdescent : baseEnd_6572142 < baseStart_6572142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572145 : List Nat := [1, 2, 2, 2, 1, 1, 6, 8]
def baseStart_6572145 : Nat := 118140960795 + 6572145 * 2 ^ 59
def prefixEnd_6572145 : Nat := 4983230072969 + 3 ^ 40 * 6572145 * 2
def baseEnd_6572145 : Nat := 124987752446047932820843

theorem tailTrace_6572145 : CollatzResearch.WordTrace tailWord_6572145 prefixEnd_6572145 124987752446047932820843 := by
  unfold tailWord_6572145
  simp only [CollatzResearch.WordTrace]
  refine ⟨239705820775248572849653889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159803880516832381899769259 239705820775248572849653889)
  ·
    refine ⟨179779365581436429637240417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239705820775248572849653889 179779365581436429637240417)
    ·
      refine ⟨134834524186077322227930313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179779365581436429637240417 134834524186077322227930313)
      ·
        refine ⟨101125893139557991670947735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134834524186077322227930313 101125893139557991670947735)
        ·
          refine ⟨151688839709336987506421603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101125893139557991670947735 151688839709336987506421603)
          ·
            refine ⟨227533259564005481259632405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151688839709336987506421603 227533259564005481259632405)
            ·
              refine ⟨10665621542062756934045269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 227533259564005481259632405 10665621542062756934045269)
              ·
                refine ⟨124987752446047932820843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10665621542062756934045269 124987752446047932820843)
                ·
                  rfl

theorem cell23_6572145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 8].length) (baseStart_6572145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572145 prefixEnd_6572145 := by exact prefixLift 6572145
  have htrace : WordTrace (prefixWord ++ tailWord_6572145) baseStart_6572145 baseEnd_6572145 := by
    simpa [prefixWord, tailWord_6572145, baseEnd_6572145] using wordTrace_append hprefix tailTrace_6572145
  have hstable : (prefixWord ++ tailWord_6572145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572145).length < 2 ^ (prefixWord ++ tailWord_6572145).sum := by decide
  have hdescent : baseEnd_6572145 < baseStart_6572145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572185 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 2, 2, 5]
def baseStart_6572185 : Nat := 118140960795 + 6572185 * 2 ^ 59
def prefixEnd_6572185 : Nat := 4983230072969 + 3 ^ 40 * 6572185 * 2
def baseEnd_6572185 : Nat := 3374689855269474029662577

theorem tailTrace_6572185 : CollatzResearch.WordTrace tailWord_6572185 prefixEnd_6572185 3374689855269474029662577 := by
  unfold tailWord_6572185
  simp only [CollatzResearch.WordTrace]
  refine ⟨239707279695103659681110009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159804853130069106454073339 239707279695103659681110009)
  ·
    refine ⟨179780459771327744760832507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239707279695103659681110009 179780459771327744760832507)
    ·
      refine ⟨269670689656991617141248761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179780459771327744760832507 269670689656991617141248761)
      ·
        refine ⟨202253017242743712855936571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269670689656991617141248761 202253017242743712855936571)
        ·
          refine ⟨303379525864115569283904857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202253017242743712855936571 303379525864115569283904857)
          ·
            refine ⟨227534644398086676962928643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303379525864115569283904857 227534644398086676962928643)
            ·
              refine ⟨341301966597130015444392965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227534644398086676962928643 341301966597130015444392965)
              ·
                refine ⟨63994118736961877895823681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 341301966597130015444392965 63994118736961877895823681)
                ·
                  refine ⟨47995589052721408421867761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63994118736961877895823681 47995589052721408421867761)
                  ·
                    refine ⟨35996691789541056316400821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47995589052721408421867761 35996691789541056316400821)
                    ·
                      refine ⟨3374689855269474029662577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35996691789541056316400821 3374689855269474029662577)
                      ·
                        rfl

theorem cell23_6572185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_6572185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572185 prefixEnd_6572185 := by exact prefixLift 6572185
  have htrace : WordTrace (prefixWord ++ tailWord_6572185) baseStart_6572185 baseEnd_6572185 := by
    simpa [prefixWord, tailWord_6572185, baseEnd_6572185] using wordTrace_append hprefix tailTrace_6572185
  have hstable : (prefixWord ++ tailWord_6572185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572185).length < 2 ^ (prefixWord ++ tailWord_6572185).sum := by decide
  have hdescent : baseEnd_6572185 < baseStart_6572185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572229 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 1, 4, 2]
def baseStart_6572229 : Nat := 118140960795 + 6572229 * 2 ^ 59
def prefixEnd_6572229 : Nat := 4983230072969 + 3 ^ 40 * 6572229 * 2
def baseEnd_6572229 : Nat := 3374712448418271857512375

theorem tailTrace_6572229 : CollatzResearch.WordTrace tailWord_6572229 prefixEnd_6572229 3374712448418271857512375 := by
  unfold tailWord_6572229
  simp only [CollatzResearch.WordTrace]
  refine ⟨239708884506944255195711741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159805923004629503463807827 239708884506944255195711741)
  ·
    refine ⟨89890831690104095698391903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239708884506944255195711741 89890831690104095698391903)
    ·
      refine ⟨134836247535156143547587855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89890831690104095698391903 134836247535156143547587855)
      ·
        refine ⟨202254371302734215321381783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134836247535156143547587855 202254371302734215321381783)
        ·
          refine ⟨303381556954101322982072675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202254371302734215321381783 303381556954101322982072675)
          ·
            refine ⟨455072335431151984473109013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303381556954101322982072675 455072335431151984473109013)
            ·
              refine ⟨21331515723335249272176985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 455072335431151984473109013 21331515723335249272176985)
              ·
                refine ⟨15998636792501436954132739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21331515723335249272176985 15998636792501436954132739)
                ·
                  refine ⟨23997955188752155431199109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15998636792501436954132739 23997955188752155431199109)
                  ·
                    refine ⟨4499616597891029143349833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23997955188752155431199109 4499616597891029143349833)
                    ·
                      refine ⟨3374712448418271857512375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4499616597891029143349833 3374712448418271857512375)
                      ·
                        rfl

theorem cell23_6572229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 4, 2].length) (baseStart_6572229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572229 prefixEnd_6572229 := by exact prefixLift 6572229
  have htrace : WordTrace (prefixWord ++ tailWord_6572229) baseStart_6572229 baseEnd_6572229 := by
    simpa [prefixWord, tailWord_6572229, baseEnd_6572229] using wordTrace_append hprefix tailTrace_6572229
  have hstable : (prefixWord ++ tailWord_6572229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572229).length < 2 ^ (prefixWord ++ tailWord_6572229).sum := by decide
  have hdescent : baseEnd_6572229 < baseStart_6572229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572235 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 9]
def baseStart_6572235 : Nat := 118140960795 + 6572235 * 2 ^ 59
def prefixEnd_6572235 : Nat := 4983230072969 + 3 ^ 40 * 6572235 * 2
def baseEnd_6572235 : Nat := 374968392144688759337483

theorem tailTrace_6572235 : CollatzResearch.WordTrace tailWord_6572235 prefixEnd_6572235 374968392144688759337483 := by
  unfold tailWord_6572235
  simp only [CollatzResearch.WordTrace]
  refine ⟨239709103344922518220430159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159806068896615012146953439 239709103344922518220430159)
  ·
    refine ⟨359563655017383777330645239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239709103344922518220430159 359563655017383777330645239)
    ·
      refine ⟨539345482526075665995967859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359563655017383777330645239 539345482526075665995967859)
      ·
        refine ⟨809018223789113498993951789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539345482526075665995967859 809018223789113498993951789)
        ·
          refine ⟨303381833920917562122731921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 809018223789113498993951789 303381833920917562122731921)
          ·
            refine ⟨227536375440688171592048941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303381833920917562122731921 227536375440688171592048941)
            ·
              refine ⟨85326140790258064347018353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227536375440688171592048941 85326140790258064347018353)
              ·
                refine ⟨63994605592693548260263765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85326140790258064347018353 63994605592693548260263765)
                ·
                  refine ⟨374968392144688759337483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63994605592693548260263765 374968392144688759337483)
                  ·
                    rfl

theorem cell23_6572235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 9].length) (baseStart_6572235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572235 prefixEnd_6572235 := by exact prefixLift 6572235
  have htrace : WordTrace (prefixWord ++ tailWord_6572235) baseStart_6572235 baseEnd_6572235 := by
    simpa [prefixWord, tailWord_6572235, baseEnd_6572235] using wordTrace_append hprefix tailTrace_6572235
  have hstable : (prefixWord ++ tailWord_6572235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572235).length < 2 ^ (prefixWord ++ tailWord_6572235).sum := by decide
  have hdescent : baseEnd_6572235 < baseStart_6572235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572263 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_6572263 : Nat := 118140960795 + 6572263 * 2 ^ 59
def prefixEnd_6572263 : Nat := 4983230072969 + 3 ^ 40 * 6572263 * 2
def baseEnd_6572263 : Nat := 3374729906760524724487219

theorem tailTrace_6572263 : CollatzResearch.WordTrace tailWord_6572263 prefixEnd_6572263 3374729906760524724487219 := by
  unfold tailWord_6572263
  simp only [CollatzResearch.WordTrace]
  refine ⟨239710124588821079002449443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159806749725880719334966295 239710124588821079002449443)
  ·
    refine ⟨359565186883231618503674165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239710124588821079002449443 359565186883231618503674165)
    ·
      refine ⟨33709236270302964234719453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 359565186883231618503674165 33709236270302964234719453)
      ·
        refine ⟨12640963601363611588019795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33709236270302964234719453 12640963601363611588019795)
        ·
          refine ⟨18961445402045417382029693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12640963601363611588019795 18961445402045417382029693)
          ·
            refine ⟨7110542025767031518261135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18961445402045417382029693 7110542025767031518261135)
            ·
              refine ⟨10665813038650547277391703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7110542025767031518261135 10665813038650547277391703)
              ·
                refine ⟨15998719557975820916087555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10665813038650547277391703 15998719557975820916087555)
                ·
                  refine ⟨23998079336963731374131333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15998719557975820916087555 23998079336963731374131333)
                  ·
                    refine ⟨4499639875680699632649625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23998079336963731374131333 4499639875680699632649625)
                    ·
                      refine ⟨3374729906760524724487219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4499639875680699632649625 3374729906760524724487219)
                      ·
                        rfl

theorem cell23_6572263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_6572263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572263 prefixEnd_6572263 := by exact prefixLift 6572263
  have htrace : WordTrace (prefixWord ++ tailWord_6572263) baseStart_6572263 baseEnd_6572263 := by
    simpa [prefixWord, tailWord_6572263, baseEnd_6572263] using wordTrace_append hprefix tailTrace_6572263
  have hstable : (prefixWord ++ tailWord_6572263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572263).length < 2 ^ (prefixWord ++ tailWord_6572263).sum := by decide
  have hdescent : baseEnd_6572263 < baseStart_6572263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572282 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 1, 7]
def baseStart_6572282 : Nat := 118140960795 + 6572282 * 2 ^ 59
def prefixEnd_6572282 : Nat := 4983230072969 + 3 ^ 40 * 6572282 * 2
def baseEnd_6572282 : Nat := 1124913220964320050049877

theorem tailTrace_6572282 : CollatzResearch.WordTrace tailWord_6572282 prefixEnd_6572282 1124913220964320050049877 := by
  unfold tailWord_6572282
  simp only [CollatzResearch.WordTrace]
  refine ⟨59927704393938061311847775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159807211717168163498260733 59927704393938061311847775)
  ·
    refine ⟨89891556590907091967771663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59927704393938061311847775 89891556590907091967771663)
    ·
      refine ⟨134837334886360637951657495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89891556590907091967771663 134837334886360637951657495)
      ·
        refine ⟨202256002329540956927486243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134837334886360637951657495 202256002329540956927486243)
        ·
          refine ⟨303384003494311435391229365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202256002329540956927486243 303384003494311435391229365)
          ·
            refine ⟨28442250327591697067927753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 303384003494311435391229365 28442250327591697067927753)
            ·
              refine ⟨21331687745693772800945815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28442250327591697067927753 21331687745693772800945815)
              ·
                refine ⟨31997531618540659201418723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21331687745693772800945815 31997531618540659201418723)
                ·
                  refine ⟨47996297427810988802128085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31997531618540659201418723 47996297427810988802128085)
                  ·
                    refine ⟨1124913220964320050049877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47996297427810988802128085 1124913220964320050049877)
                    ·
                      rfl

theorem cell23_6572282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_6572282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572282 prefixEnd_6572282 := by exact prefixLift 6572282
  have htrace : WordTrace (prefixWord ++ tailWord_6572282) baseStart_6572282 baseEnd_6572282 := by
    simpa [prefixWord, tailWord_6572282, baseEnd_6572282] using wordTrace_append hprefix tailTrace_6572282
  have hstable : (prefixWord ++ tailWord_6572282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572282).length < 2 ^ (prefixWord ++ tailWord_6572282).sum := by decide
  have hdescent : baseEnd_6572282 < baseStart_6572282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572332 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_6572332 : Nat := 118140960795 + 6572332 * 2 ^ 59
def prefixEnd_6572332 : Nat := 4983230072969 + 3 ^ 40 * 6572332 * 2
def baseEnd_6572332 : Nat := 3374765336925684954524401

theorem tailTrace_6572332 : CollatzResearch.WordTrace tailWord_6572332 prefixEnd_6572332 3374765336925684954524401 := by
  unfold tailWord_6572332
  simp only [CollatzResearch.WordTrace]
  refine ⟨119856320612785551893355625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159808427483714069191140833 119856320612785551893355625)
  ·
    refine ⟨89892240459589163920016719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119856320612785551893355625 89892240459589163920016719)
    ·
      refine ⟨134838360689383745880025079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89892240459589163920016719 134838360689383745880025079)
      ·
        refine ⟨202257541034075618820037619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134838360689383745880025079 202257541034075618820037619)
        ·
          refine ⟨303386311551113428230056429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202257541034075618820037619 303386311551113428230056429)
          ·
            refine ⟨113769866831667535586271161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303386311551113428230056429 113769866831667535586271161)
            ·
              refine ⟨85327400123750651689703371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113769866831667535586271161 85327400123750651689703371)
              ·
                refine ⟨127991100185625977534555057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85327400123750651689703371 127991100185625977534555057)
                ·
                  refine ⟨95993325139219483150916293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127991100185625977534555057 95993325139219483150916293)
                  ·
                    refine ⟨17998748463603653090796805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95993325139219483150916293 17998748463603653090796805)
                    ·
                      refine ⟨3374765336925684954524401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17998748463603653090796805 3374765336925684954524401)
                      ·
                        rfl

theorem cell23_6572332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_6572332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572332 prefixEnd_6572332 := by exact prefixLift 6572332
  have htrace : WordTrace (prefixWord ++ tailWord_6572332) baseStart_6572332 baseEnd_6572332 := by
    simpa [prefixWord, tailWord_6572332, baseEnd_6572332] using wordTrace_append hprefix tailTrace_6572332
  have hstable : (prefixWord ++ tailWord_6572332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572332).length < 2 ^ (prefixWord ++ tailWord_6572332).sum := by decide
  have hdescent : baseEnd_6572332 < baseStart_6572332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572333 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_6572333 : Nat := 118140960795 + 6572333 * 2 ^ 59
def prefixEnd_6572333 : Nat := 4983230072969 + 3 ^ 40 * 6572333 * 2
def baseEnd_6572333 : Nat := 1124921950135446483537299

theorem tailTrace_6572333 : CollatzResearch.WordTrace tailWord_6572333 prefixEnd_6572333 1124921950135446483537299 := by
  unfold tailWord_6572333
  simp only [CollatzResearch.WordTrace]
  refine ⟨239712677698567480957497653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159808451799044987304998435 239712677698567480957497653)
  ·
    refine ⟨22473063534240701339765405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239712677698567480957497653 22473063534240701339765405)
    ·
      refine ⟨8427398825340263002412027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22473063534240701339765405 8427398825340263002412027)
      ·
        refine ⟨12641098238010394503618041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8427398825340263002412027 12641098238010394503618041)
        ·
          refine ⟨9480823678507795877713531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12641098238010394503618041 9480823678507795877713531)
          ·
            refine ⟨14221235517761693816570297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9480823678507795877713531 14221235517761693816570297)
            ·
              refine ⟨10665926638321270362427723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14221235517761693816570297 10665926638321270362427723)
              ·
                refine ⟨15998889957481905543641585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10665926638321270362427723 15998889957481905543641585)
                ·
                  refine ⟨11999167468111429157731189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15998889957481905543641585 11999167468111429157731189)
                  ·
                    refine ⟨1124921950135446483537299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11999167468111429157731189 1124921950135446483537299)
                    ·
                      rfl

theorem cell23_6572333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_6572333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572333 prefixEnd_6572333 := by exact prefixLift 6572333
  have htrace : WordTrace (prefixWord ++ tailWord_6572333) baseStart_6572333 baseEnd_6572333 := by
    simpa [prefixWord, tailWord_6572333, baseEnd_6572333] using wordTrace_append hprefix tailTrace_6572333
  have hstable : (prefixWord ++ tailWord_6572333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572333).length < 2 ^ (prefixWord ++ tailWord_6572333).sum := by decide
  have hdescent : baseEnd_6572333 < baseStart_6572333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572359 : List Nat := [1, 1, 4, 1, 2, 2, 4, 2, 6]
def baseStart_6572359 : Nat := 118140960795 + 6572359 * 2 ^ 59
def prefixEnd_6572359 : Nat := 4983230072969 + 3 ^ 40 * 6572359 * 2
def baseEnd_6572359 : Nat := 374975466767039594320753

theorem tailTrace_6572359 : CollatzResearch.WordTrace tailWord_6572359 prefixEnd_6572359 374975466767039594320753 := by
  unfold tailWord_6572359
  simp only [CollatzResearch.WordTrace]
  refine ⟨239713625996473287397944131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159809083997648858265296087 239713625996473287397944131)
  ·
    refine ⟨359570438994709931096916197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239713625996473287397944131 359570438994709931096916197)
    ·
      refine ⟨67419457311508112080671787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 359570438994709931096916197 67419457311508112080671787)
      ·
        refine ⟨101129185967262168121007681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67419457311508112080671787 101129185967262168121007681)
        ·
          refine ⟨75846889475446626090755761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101129185967262168121007681 75846889475446626090755761)
          ·
            refine ⟨56885167106584969568066821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75846889475446626090755761 56885167106584969568066821)
            ·
              refine ⟨10665968832484681794012529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56885167106584969568066821 10665968832484681794012529)
              ·
                refine ⟨7999476624363511345509397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10665968832484681794012529 7999476624363511345509397)
                ·
                  refine ⟨374975466767039594320753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7999476624363511345509397 374975466767039594320753)
                  ·
                    rfl

theorem cell23_6572359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 6].length) (baseStart_6572359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572359 prefixEnd_6572359 := by exact prefixLift 6572359
  have htrace : WordTrace (prefixWord ++ tailWord_6572359) baseStart_6572359 baseEnd_6572359 := by
    simpa [prefixWord, tailWord_6572359, baseEnd_6572359] using wordTrace_append hprefix tailTrace_6572359
  have hstable : (prefixWord ++ tailWord_6572359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572359).length < 2 ^ (prefixWord ++ tailWord_6572359).sum := by decide
  have hdescent : baseEnd_6572359 < baseStart_6572359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572389 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 3, 5]
def baseStart_6572389 : Nat := 118140960795 + 6572389 * 2 ^ 59
def prefixEnd_6572389 : Nat := 4983230072969 + 3 ^ 40 * 6572389 * 2
def baseEnd_6572389 : Nat := 1124931535107663743837213

theorem tailTrace_6572389 : CollatzResearch.WordTrace tailWord_6572389 prefixEnd_6572389 1124931535107663743837213 := by
  unfold tailWord_6572389
  simp only [CollatzResearch.WordTrace]
  refine ⟨239714720186364602521536221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159809813457576401681024147 239714720186364602521536221)
  ·
    refine ⟨89893020069886725945576083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239714720186364602521536221 89893020069886725945576083)
    ·
      refine ⟨134839530104830088918364125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89893020069886725945576083 134839530104830088918364125)
      ·
        refine ⟨50564823789311283344386547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134839530104830088918364125 50564823789311283344386547)
        ·
          refine ⟨75847235683966925016579821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50564823789311283344386547 75847235683966925016579821)
          ·
            refine ⟨28442713381487596881217433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75847235683966925016579821 28442713381487596881217433)
            ·
              refine ⟨21332035036115697660913075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28442713381487596881217433 21332035036115697660913075)
              ·
                refine ⟨31998052554173546491369613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21332035036115697660913075 31998052554173546491369613)
                ·
                  refine ⟨11999269707815079934263605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31998052554173546491369613 11999269707815079934263605)
                  ·
                    refine ⟨1124931535107663743837213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11999269707815079934263605 1124931535107663743837213)
                    ·
                      rfl

theorem cell23_6572389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_6572389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572389 prefixEnd_6572389 := by exact prefixLift 6572389
  have htrace : WordTrace (prefixWord ++ tailWord_6572389) baseStart_6572389 baseEnd_6572389 := by
    simpa [prefixWord, tailWord_6572389, baseEnd_6572389] using wordTrace_append hprefix tailTrace_6572389
  have hstable : (prefixWord ++ tailWord_6572389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572389).length < 2 ^ (prefixWord ++ tailWord_6572389).sum := by decide
  have hdescent : baseEnd_6572389 < baseStart_6572389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572514 : List Nat := [3, 3, 3, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_6572514 : Nat := 118140960795 + 6572514 * 2 ^ 59
def prefixEnd_6572514 : Nat := 4983230072969 + 3 ^ 40 * 6572514 * 2
def baseEnd_6572514 : Nat := 3374858790404803242448565

theorem tailTrace_6572514 : CollatzResearch.WordTrace tailWord_6572514 prefixEnd_6572514 3374858790404803242448565 := by
  unfold tailWord_6572514
  simp only [CollatzResearch.WordTrace]
  refine ⟨59929819827727937217459149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159812852873941165913224397 59929819827727937217459149)
  ·
    refine ⟨22473682435397976456547181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59929819827727937217459149 22473682435397976456547181)
    ·
      refine ⟨8427630913274241171205193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22473682435397976456547181 8427630913274241171205193)
      ·
        refine ⟨6320723184955680878403895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8427630913274241171205193 6320723184955680878403895)
        ·
          refine ⟨9481084777433521317605843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6320723184955680878403895 9481084777433521317605843)
          ·
            refine ⟨14221627166150281976408765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9481084777433521317605843 14221627166150281976408765)
            ·
              refine ⟨5333110187306355741153287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14221627166150281976408765 5333110187306355741153287)
              ·
                refine ⟨7999665280959533611729931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5333110187306355741153287 7999665280959533611729931)
                ·
                  refine ⟨11999497921439300417594897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7999665280959533611729931 11999497921439300417594897)
                  ·
                    refine ⟨8999623441079475313196173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11999497921439300417594897 8999623441079475313196173)
                    ·
                      refine ⟨3374858790404803242448565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8999623441079475313196173 3374858790404803242448565)
                      ·
                        rfl

theorem cell23_6572514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_6572514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572514 prefixEnd_6572514 := by exact prefixLift 6572514
  have htrace : WordTrace (prefixWord ++ tailWord_6572514) baseStart_6572514 baseEnd_6572514 := by
    simpa [prefixWord, tailWord_6572514, baseEnd_6572514] using wordTrace_append hprefix tailTrace_6572514
  have hstable : (prefixWord ++ tailWord_6572514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572514).length < 2 ^ (prefixWord ++ tailWord_6572514).sum := by decide
  have hdescent : baseEnd_6572514 < baseStart_6572514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572556 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 7]
def baseStart_6572556 : Nat := 118140960795 + 6572556 * 2 ^ 59
def prefixEnd_6572556 : Nat := 4983230072969 + 3 ^ 40 * 6572556 * 2
def baseEnd_6572556 : Nat := 374986706288032453124819

theorem tailTrace_6572556 : CollatzResearch.WordTrace tailWord_6572556 prefixEnd_6572556 374986706288032453124819 := by
  unfold tailWord_6572556
  simp only [CollatzResearch.WordTrace]
  refine ⟨119860405588379795021432761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159813874117839726695243681 119860405588379795021432761)
  ·
    refine ⟨89895304191284846266074571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119860405588379795021432761 89895304191284846266074571)
    ·
      refine ⟨134842956286927269399111857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89895304191284846266074571 134842956286927269399111857)
      ·
        refine ⟨101132217215195452049333893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134842956286927269399111857 101132217215195452049333893)
        ·
          refine ⟨18962290727849147259250105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101132217215195452049333893 18962290727849147259250105)
          ·
            refine ⟨14221718045886860444437579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18962290727849147259250105 14221718045886860444437579)
            ·
              refine ⟨21332577068830290666656369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14221718045886860444437579 21332577068830290666656369)
              ·
                refine ⟨15999432801622717999992277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21332577068830290666656369 15999432801622717999992277)
                ·
                  refine ⟨374986706288032453124819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15999432801622717999992277 374986706288032453124819)
                  ·
                    rfl

theorem cell23_6572556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_6572556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572556 prefixEnd_6572556 := by exact prefixLift 6572556
  have htrace : WordTrace (prefixWord ++ tailWord_6572556) baseStart_6572556 baseEnd_6572556 := by
    simpa [prefixWord, tailWord_6572556, baseEnd_6572556] using wordTrace_append hprefix tailTrace_6572556
  have hstable : (prefixWord ++ tailWord_6572556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572556).length < 2 ^ (prefixWord ++ tailWord_6572556).sum := by decide
  have hdescent : baseEnd_6572556 < baseStart_6572556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572569 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 1, 7]
def baseStart_6572569 : Nat := 118140960795 + 6572569 * 2 ^ 59
def prefixEnd_6572569 : Nat := 4983230072969 + 3 ^ 40 * 6572569 * 2
def baseEnd_6572569 : Nat := 1124962343946933509086937

theorem tailTrace_6572569 : CollatzResearch.WordTrace tailWord_6572569 prefixEnd_6572569 1124962343946933509086937 := by
  unfold tailWord_6572569
  simp only [CollatzResearch.WordTrace]
  refine ⟨239721285325712493263088761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159814190217141662175392507 239721285325712493263088761)
  ·
    refine ⟨179790963994284369947316571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239721285325712493263088761 179790963994284369947316571)
    ·
      refine ⟨269686445991426554920974857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179790963994284369947316571 269686445991426554920974857)
      ·
        refine ⟨202264834493569916190731143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269686445991426554920974857 202264834493569916190731143)
        ·
          refine ⟨303397251740354874286096715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202264834493569916190731143 303397251740354874286096715)
          ·
            refine ⟨455095877610532311429145073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303397251740354874286096715 455095877610532311429145073)
            ·
              refine ⟨341321908207899233571858805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455095877610532311429145073 341321908207899233571858805)
              ·
                refine ⟨31998928894490553147361763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 341321908207899233571858805 31998928894490553147361763)
                ·
                  refine ⟨47998393341735829721042645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31998928894490553147361763 47998393341735829721042645)
                  ·
                    refine ⟨1124962343946933509086937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47998393341735829721042645 1124962343946933509086937)
                    ·
                      rfl

theorem cell23_6572569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 7].length) (baseStart_6572569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572569 prefixEnd_6572569 := by exact prefixLift 6572569
  have htrace : WordTrace (prefixWord ++ tailWord_6572569) baseStart_6572569 baseEnd_6572569 := by
    simpa [prefixWord, tailWord_6572569, baseEnd_6572569] using wordTrace_append hprefix tailTrace_6572569
  have hstable : (prefixWord ++ tailWord_6572569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572569).length < 2 ^ (prefixWord ++ tailWord_6572569).sum := by decide
  have hdescent : baseEnd_6572569 < baseStart_6572569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572573 : List Nat := [1, 4, 2, 2, 1, 2, 1, 5, 5]
def baseStart_6572573 : Nat := 118140960795 + 6572573 * 2 ^ 59
def prefixEnd_6572573 : Nat := 4983230072969 + 3 ^ 40 * 6572573 * 2
def baseEnd_6572573 : Nat := 374987676195935390178977

theorem tailTrace_6572573 : CollatzResearch.WordTrace tailWord_6572573 prefixEnd_6572573 374987676195935390178977 := by
  unfold tailWord_6572573
  simp only [CollatzResearch.WordTrace]
  refine ⟨239721431217698001946234373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159814287478465334630822915 239721431217698001946234373)
  ·
    refine ⟨44947768353318375364918945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239721431217698001946234373 44947768353318375364918945)
    ·
      refine ⟨33710826264988781523689209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44947768353318375364918945 33710826264988781523689209)
      ·
        refine ⟨25283119698741586142766907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33710826264988781523689209 25283119698741586142766907)
        ·
          refine ⟨37924679548112379214150361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25283119698741586142766907 37924679548112379214150361)
          ·
            refine ⟨28443509661084284410612771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37924679548112379214150361 28443509661084284410612771)
            ·
              refine ⟨42665264491626426615919157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28443509661084284410612771 42665264491626426615919157)
              ·
                refine ⟨3999868546089977495242421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42665264491626426615919157 3999868546089977495242421)
                ·
                  refine ⟨374987676195935390178977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3999868546089977495242421 374987676195935390178977)
                  ·
                    rfl

theorem cell23_6572573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_6572573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572573 prefixEnd_6572573 := by exact prefixLift 6572573
  have htrace : WordTrace (prefixWord ++ tailWord_6572573) baseStart_6572573 baseEnd_6572573 := by
    simpa [prefixWord, tailWord_6572573, baseEnd_6572573] using wordTrace_append hprefix tailTrace_6572573
  have hstable : (prefixWord ++ tailWord_6572573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572573).length < 2 ^ (prefixWord ++ tailWord_6572573).sum := by decide
  have hdescent : baseEnd_6572573 < baseStart_6572573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572584 : List Nat := [2, 1, 5, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_6572584 : Nat := 118140960795 + 6572584 * 2 ^ 59
def prefixEnd_6572584 : Nat := 4983230072969 + 3 ^ 40 * 6572584 * 2
def baseEnd_6572584 : Nat := 3374894734050617968573243

theorem tailTrace_6572584 : CollatzResearch.WordTrace tailWord_6572584 prefixEnd_6572584 3374894734050617968573243 := by
  unfold tailWord_6572584
  simp only [CollatzResearch.WordTrace]
  refine ⟨119860916210329075412442403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159814554947105433883256537 119860916210329075412442403)
  ·
    refine ⟨179791374315493613118663605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119860916210329075412442403 179791374315493613118663605)
    ·
      refine ⟨16855441342077526229874713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179791374315493613118663605 16855441342077526229874713)
      ·
        refine ⟨12641581006558144672406035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16855441342077526229874713 12641581006558144672406035)
        ·
          refine ⟨18962371509837217008609053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12641581006558144672406035 18962371509837217008609053)
          ·
            refine ⟨7110889316188956378228395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18962371509837217008609053 7110889316188956378228395)
            ·
              refine ⟨10666333974283434567342593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7110889316188956378228395 10666333974283434567342593)
              ·
                refine ⟨7999750480712575925506945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10666333974283434567342593 7999750480712575925506945)
                ·
                  refine ⟨5999812860534431944130209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7999750480712575925506945 5999812860534431944130209)
                  ·
                    refine ⟨4499859645400823958097657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5999812860534431944130209 4499859645400823958097657)
                    ·
                      refine ⟨3374894734050617968573243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4499859645400823958097657 3374894734050617968573243)
                      ·
                        rfl

theorem cell23_6572584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_6572584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572584 prefixEnd_6572584 := by exact prefixLift 6572584
  have htrace : WordTrace (prefixWord ++ tailWord_6572584) baseStart_6572584 baseEnd_6572584 := by
    simpa [prefixWord, tailWord_6572584, baseEnd_6572584] using wordTrace_append hprefix tailTrace_6572584
  have hstable : (prefixWord ++ tailWord_6572584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572584).length < 2 ^ (prefixWord ++ tailWord_6572584).sum := by decide
  have hdescent : baseEnd_6572584 < baseStart_6572584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572643 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 3]
def baseStart_6572643 : Nat := 118140960795 + 6572643 * 2 ^ 59
def prefixEnd_6572643 : Nat := 4983230072969 + 3 ^ 40 * 6572643 * 2
def baseEnd_6572643 : Nat := 3374925029409233237735471

theorem tailTrace_6572643 : CollatzResearch.WordTrace tailWord_6572643 prefixEnd_6572643 3374925029409233237735471 := by
  unfold tailWord_6572643
  simp only [CollatzResearch.WordTrace]
  refine ⟨239723984327444403901282583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159815989551629602600855055 239723984327444403901282583)
  ·
    refine ⟨359585976491166605851923875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239723984327444403901282583 359585976491166605851923875)
    ·
      refine ⟨539378964736749908777885813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359585976491166605851923875 539378964736749908777885813)
      ·
        refine ⟨50566777944070303947926795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 539378964736749908777885813 50566777944070303947926795)
        ·
          refine ⟨75850166916105455921890193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50566777944070303947926795 75850166916105455921890193)
          ·
            refine ⟨56887625187079091941417645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75850166916105455921890193 56887625187079091941417645)
            ·
              refine ⟨21332859445154659478031617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56887625187079091941417645 21332859445154659478031617)
              ·
                refine ⟨15999644583865994608523713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21332859445154659478031617 15999644583865994608523713)
                ·
                  refine ⟨11999733437899495956392785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15999644583865994608523713 11999733437899495956392785)
                  ·
                    refine ⟨8999800078424621967294589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11999733437899495956392785 8999800078424621967294589)
                    ·
                      refine ⟨3374925029409233237735471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8999800078424621967294589 3374925029409233237735471)
                      ·
                        rfl

theorem cell23_6572643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_6572643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572643 prefixEnd_6572643 := by exact prefixLift 6572643
  have htrace : WordTrace (prefixWord ++ tailWord_6572643) baseStart_6572643 baseEnd_6572643 := by
    simpa [prefixWord, tailWord_6572643, baseEnd_6572643] using wordTrace_append hprefix tailTrace_6572643
  have hstable : (prefixWord ++ tailWord_6572643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572643).length < 2 ^ (prefixWord ++ tailWord_6572643).sum := by decide
  have hdescent : baseEnd_6572643 < baseStart_6572643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572663 : List Nat := [1, 1, 3, 1, 1, 3, 6, 1, 6]
def baseStart_6572663 : Nat := 118140960795 + 6572663 * 2 ^ 59
def prefixEnd_6572663 : Nat := 4983230072969 + 3 ^ 40 * 6572663 * 2
def baseEnd_6572663 : Nat := 374992811002480351053931

theorem tailTrace_6572663 : CollatzResearch.WordTrace tailWord_6572663 prefixEnd_6572663 374992811002480351053931 := by
  unfold tailWord_6572663
  simp only [CollatzResearch.WordTrace]
  refine ⟨239724713787371947317010643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159816475858247964878007095 239724713787371947317010643)
  ·
    refine ⟨359587070681057920975515965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239724713787371947317010643 359587070681057920975515965)
    ·
      refine ⟨134845151505396720365818487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359587070681057920975515965 134845151505396720365818487)
      ·
        refine ⟨202267727258095080548727731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134845151505396720365818487 202267727258095080548727731)
        ·
          refine ⟨303401590887142620823091597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202267727258095080548727731 303401590887142620823091597)
          ·
            refine ⟨113775596582678482808659349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303401590887142620823091597 113775596582678482808659349)
            ·
              refine ⟨5333231089813053881655907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113775596582678482808659349 5333231089813053881655907)
              ·
                refine ⟨7999846634719580822483861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5333231089813053881655907 7999846634719580822483861)
                ·
                  refine ⟨374992811002480351053931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7999846634719580822483861 374992811002480351053931)
                  ·
                    rfl

theorem cell23_6572663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 6].length) (baseStart_6572663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572663 prefixEnd_6572663 := by exact prefixLift 6572663
  have htrace : WordTrace (prefixWord ++ tailWord_6572663) baseStart_6572663 baseEnd_6572663 := by
    simpa [prefixWord, tailWord_6572663, baseEnd_6572663] using wordTrace_append hprefix tailTrace_6572663
  have hstable : (prefixWord ++ tailWord_6572663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572663).length < 2 ^ (prefixWord ++ tailWord_6572663).sum := by decide
  have hdescent : baseEnd_6572663 < baseStart_6572663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572723 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 1, 6]
def baseStart_6572723 : Nat := 118140960795 + 6572723 * 2 ^ 59
def prefixEnd_6572723 : Nat := 4983230072969 + 3 ^ 40 * 6572723 * 2
def baseEnd_6572723 : Nat := 1124988702620530974911701

theorem tailTrace_6572723 : CollatzResearch.WordTrace tailWord_6572723 prefixEnd_6572723 1124988702620530974911701 := by
  unfold tailWord_6572723
  simp only [CollatzResearch.WordTrace]
  refine ⟨239726902167154577564194823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159817934778103051709463215 239726902167154577564194823)
  ·
    refine ⟨359590353250731866346292235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239726902167154577564194823 359590353250731866346292235)
    ·
      refine ⟨539385529876097799519438353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359590353250731866346292235 539385529876097799519438353)
      ·
        refine ⟨404539147407073349639578765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539385529876097799519438353 404539147407073349639578765)
        ·
          refine ⟨151702180277652506114842037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404539147407073349639578765 151702180277652506114842037)
          ·
            refine ⟨14222079401029922448266441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151702180277652506114842037 14222079401029922448266441)
            ·
              refine ⟨10666559550772441836199831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14222079401029922448266441 10666559550772441836199831)
              ·
                refine ⟨15999839326158662754299747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10666559550772441836199831 15999839326158662754299747)
                ·
                  refine ⟨23999758989237994131449621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15999839326158662754299747 23999758989237994131449621)
                  ·
                    refine ⟨1124988702620530974911701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23999758989237994131449621 1124988702620530974911701)
                    ·
                      rfl

theorem cell23_6572723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 6].length) (baseStart_6572723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572723 prefixEnd_6572723 := by exact prefixLift 6572723
  have htrace : WordTrace (prefixWord ++ tailWord_6572723) baseStart_6572723 baseEnd_6572723 := by
    simpa [prefixWord, tailWord_6572723, baseEnd_6572723] using wordTrace_append hprefix tailTrace_6572723
  have hstable : (prefixWord ++ tailWord_6572723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572723).length < 2 ^ (prefixWord ++ tailWord_6572723).sum := by decide
  have hdescent : baseEnd_6572723 < baseStart_6572723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572757 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 4, 4]
def baseStart_6572757 : Nat := 118140960795 + 6572757 * 2 ^ 59
def prefixEnd_6572757 : Nat := 4983230072969 + 3 ^ 40 * 6572757 * 2
def baseEnd_6572757 : Nat := 1124994522067948597236649

theorem tailTrace_6572757 : CollatzResearch.WordTrace tailWord_6572757 prefixEnd_6572757 1124994522067948597236649 := by
  unfold tailWord_6572757
  simp only [CollatzResearch.WordTrace]
  refine ⟨239728142249031401370932525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159818761499354267580621683 239728142249031401370932525)
  ·
    refine ⟨89898053343386775514099697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239728142249031401370932525 89898053343386775514099697)
    ·
      refine ⟨67423540007540081635574773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89898053343386775514099697 67423540007540081635574773)
      ·
        refine ⟨6320956875706882653335135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67423540007540081635574773 6320956875706882653335135)
        ·
          refine ⟨9481435313560323980002703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6320956875706882653335135 9481435313560323980002703)
          ·
            refine ⟨14222152970340485970004055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9481435313560323980002703 14222152970340485970004055)
            ·
              refine ⟨21333229455510728955006083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14222152970340485970004055 21333229455510728955006083)
              ·
                refine ⟨31999844183266093432509125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21333229455510728955006083 31999844183266093432509125)
                ·
                  refine ⟨5999970784362392518595461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31999844183266093432509125 5999970784362392518595461)
                  ·
                    refine ⟨1124994522067948597236649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5999970784362392518595461 1124994522067948597236649)
                    ·
                      rfl

theorem cell23_6572757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_6572757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572757 prefixEnd_6572757 := by exact prefixLift 6572757
  have htrace : WordTrace (prefixWord ++ tailWord_6572757) baseStart_6572757 baseEnd_6572757 := by
    simpa [prefixWord, tailWord_6572757, baseEnd_6572757] using wordTrace_append hprefix tailTrace_6572757
  have hstable : (prefixWord ++ tailWord_6572757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572757).length < 2 ^ (prefixWord ++ tailWord_6572757).sum := by decide
  have hdescent : baseEnd_6572757 < baseStart_6572757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572764 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_6572764 : Nat := 118140960795 + 6572764 * 2 ^ 59
def prefixEnd_6572764 : Nat := 4983230072969 + 3 ^ 40 * 6572764 * 2
def baseEnd_6572764 : Nat := 3374987160568427264322415

theorem tailTrace_6572764 : CollatzResearch.WordTrace tailWord_6572764 prefixEnd_6572764 3374987160568427264322415 := by
  unfold tailWord_6572764
  simp only [CollatzResearch.WordTrace]
  refine ⟨119864198780003020783218673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159818931706670694377624897 119864198780003020783218673)
  ·
    refine ⟨89898149085002265587414005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119864198780003020783218673 89898149085002265587414005)
    ·
      refine ⟨8427951476718962398820063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89898149085002265587414005 8427951476718962398820063)
      ·
        refine ⟨12641927215078443598230095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8427951476718962398820063 12641927215078443598230095)
        ·
          refine ⟨18962890822617665397345143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12641927215078443598230095 18962890822617665397345143)
          ·
            refine ⟨28444336233926498096017715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18962890822617665397345143 28444336233926498096017715)
            ·
              refine ⟨42666504350889747144026573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28444336233926498096017715 42666504350889747144026573)
              ·
                refine ⟨15999939131583655179009965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42666504350889747144026573 15999939131583655179009965)
                ·
                  refine ⟨5999977174343870692128737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15999939131583655179009965 5999977174343870692128737)
                  ·
                    refine ⟨4499982880757903019096553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5999977174343870692128737 4499982880757903019096553)
                    ·
                      refine ⟨3374987160568427264322415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4499982880757903019096553 3374987160568427264322415)
                      ·
                        rfl

theorem cell23_6572764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_6572764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572764 prefixEnd_6572764 := by exact prefixLift 6572764
  have htrace : WordTrace (prefixWord ++ tailWord_6572764) baseStart_6572764 baseEnd_6572764 := by
    simpa [prefixWord, tailWord_6572764, baseEnd_6572764] using wordTrace_append hprefix tailTrace_6572764
  have hstable : (prefixWord ++ tailWord_6572764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572764).length < 2 ^ (prefixWord ++ tailWord_6572764).sum := by decide
  have hdescent : baseEnd_6572764 < baseStart_6572764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572798 : List Nat := [4, 2, 2, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_6572798 : Nat := 118140960795 + 6572798 * 2 ^ 59
def prefixEnd_6572798 : Nat := 4983230072969 + 3 ^ 40 * 6572798 * 2
def baseEnd_6572798 : Nat := 3375004618910680131297259

theorem tailTrace_6572798 : CollatzResearch.WordTrace tailWord_6572798 prefixEnd_6572798 3375004618910680131297259 := by
  unfold tailWord_6572798
  simp only [CollatzResearch.WordTrace]
  refine ⟨29966204705235358171646881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159819758427921910248783365 29966204705235358171646881)
  ·
    refine ⟨22474653528926518628735161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29966204705235358171646881 22474653528926518628735161)
    ·
      refine ⟨16855990146694888971551371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22474653528926518628735161 16855990146694888971551371)
      ·
        refine ⟨25283985220042333457327057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16855990146694888971551371 25283985220042333457327057)
        ·
          refine ⟨18962988915031750092995293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25283985220042333457327057 18962988915031750092995293)
          ·
            refine ⟨7111120843136906284873235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18962988915031750092995293 7111120843136906284873235)
            ·
              refine ⟨10666681264705359427309853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7111120843136906284873235 10666681264705359427309853)
              ·
                refine ⟨4000005474264509785241195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10666681264705359427309853 4000005474264509785241195)
                ·
                  refine ⟨6000008211396764677861793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000005474264509785241195 6000008211396764677861793)
                  ·
                    refine ⟨4500006158547573508396345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6000008211396764677861793 4500006158547573508396345)
                    ·
                      refine ⟨3375004618910680131297259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4500006158547573508396345 3375004618910680131297259)
                      ·
                        rfl

theorem cell23_6572798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_6572798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572798 prefixEnd_6572798 := by exact prefixLift 6572798
  have htrace : WordTrace (prefixWord ++ tailWord_6572798) baseStart_6572798 baseEnd_6572798 := by
    simpa [prefixWord, tailWord_6572798, baseEnd_6572798] using wordTrace_append hprefix tailTrace_6572798
  have hstable : (prefixWord ++ tailWord_6572798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572798).length < 2 ^ (prefixWord ++ tailWord_6572798).sum := by decide
  have hdescent : baseEnd_6572798 < baseStart_6572798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572833 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_6572833 : Nat := 118140960795 + 6572833 * 2 ^ 59
def prefixEnd_6572833 : Nat := 4983230072969 + 3 ^ 40 * 6572833 * 2
def baseEnd_6572833 : Nat := 3375022590733587494359597

theorem tailTrace_6572833 : CollatzResearch.WordTrace tailWord_6572833 prefixEnd_6572833 3375022590733587494359597 := by
  unfold tailWord_6572833
  simp only [CollatzResearch.WordTrace]
  refine ⟨239730914196756066350699153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159820609464504044233799435 239730914196756066350699153)
  ·
    refine ⟨179798185647567049763024365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239730914196756066350699153 179798185647567049763024365)
    ·
      refine ⟨67424319617837643661134137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179798185647567049763024365 67424319617837643661134137)
      ·
        refine ⟨50568239713378232745850603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67424319617837643661134137 50568239713378232745850603)
        ·
          refine ⟨75852359570067349118775905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50568239713378232745850603 75852359570067349118775905)
          ·
            refine ⟨56889269677550511839081929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75852359570067349118775905 56889269677550511839081929)
            ·
              refine ⟨42666952258162883879311447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56889269677550511839081929 42666952258162883879311447)
              ·
                refine ⟨64000428387244325818967171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42666952258162883879311447 64000428387244325818967171)
                ·
                  refine ⟨96000642580866488728450757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64000428387244325818967171 96000642580866488728450757)
                  ·
                    refine ⟨18000120483912466636584517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96000642580866488728450757 18000120483912466636584517)
                    ·
                      refine ⟨3375022590733587494359597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18000120483912466636584517 3375022590733587494359597)
                      ·
                        rfl

theorem cell23_6572833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_6572833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572833 prefixEnd_6572833 := by exact prefixLift 6572833
  have htrace : WordTrace (prefixWord ++ tailWord_6572833) baseStart_6572833 baseEnd_6572833 := by
    simpa [prefixWord, tailWord_6572833, baseEnd_6572833] using wordTrace_append hprefix tailTrace_6572833
  have hstable : (prefixWord ++ tailWord_6572833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572833).length < 2 ^ (prefixWord ++ tailWord_6572833).sum := by decide
  have hdescent : baseEnd_6572833 < baseStart_6572833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572860 : List Nat := [2, 2, 2, 2, 1, 1, 1, 7, 5]
def baseStart_6572860 : Nat := 118140960795 + 6572860 * 2 ^ 59
def prefixEnd_6572860 : Nat := 4983230072969 + 3 ^ 40 * 6572860 * 2
def baseEnd_6572860 : Nat := 375004050523473209857997

theorem tailTrace_6572860 : CollatzResearch.WordTrace tailWord_6572860 prefixEnd_6572860 375004050523473209857997 := by
  unfold tailWord_6572860
  simp only [CollatzResearch.WordTrace]
  refine ⟨119865949483829124980966017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159821265978438833307954689 119865949483829124980966017)
  ·
    refine ⟨89899462112871843735724513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119865949483829124980966017 89899462112871843735724513)
    ·
      refine ⟨67424596584653882801793385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89899462112871843735724513 67424596584653882801793385)
      ·
        refine ⟨50568447438490412101345039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67424596584653882801793385 50568447438490412101345039)
        ·
          refine ⟨75852671157735618152017559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50568447438490412101345039 75852671157735618152017559)
          ·
            refine ⟨113779006736603427228026339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75852671157735618152017559 113779006736603427228026339)
            ·
              refine ⟨170668510104905140842039509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113779006736603427228026339 170668510104905140842039509)
              ·
                refine ⟨4000043205583714238485301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 170668510104905140842039509 4000043205583714238485301)
                ·
                  refine ⟨375004050523473209857997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4000043205583714238485301 375004050523473209857997)
                  ·
                    rfl

theorem cell23_6572860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 5].length) (baseStart_6572860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572860 prefixEnd_6572860 := by exact prefixLift 6572860
  have htrace : WordTrace (prefixWord ++ tailWord_6572860) baseStart_6572860 baseEnd_6572860 := by
    simpa [prefixWord, tailWord_6572860, baseEnd_6572860] using wordTrace_append hprefix tailTrace_6572860
  have hstable : (prefixWord ++ tailWord_6572860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572860).length < 2 ^ (prefixWord ++ tailWord_6572860).sum := by decide
  have hdescent : baseEnd_6572860 < baseStart_6572860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572880 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 2, 5, 2]
def baseStart_6572880 : Nat := 118140960795 + 6572880 * 2 ^ 59
def prefixEnd_6572880 : Nat := 4983230072969 + 3 ^ 40 * 6572880 * 2
def baseEnd_6572880 : Nat := 3375046724324348810471881

theorem tailTrace_6572880 : CollatzResearch.WordTrace tailWord_6572880 prefixEnd_6572880 3375046724324348810471881 := by
  unfold tailWord_6572880
  simp only [CollatzResearch.WordTrace]
  refine ⟨119866314213792896688830047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159821752285057195585106729 119866314213792896688830047)
  ·
    refine ⟨179799471320689345033245071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119866314213792896688830047 179799471320689345033245071)
    ·
      refine ⟨269699206981034017549867607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179799471320689345033245071 269699206981034017549867607)
      ·
        refine ⟨404548810471551026324801411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269699206981034017549867607 404548810471551026324801411)
        ·
          refine ⟨606823215707326539487202117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404548810471551026324801411 606823215707326539487202117)
          ·
            refine ⟨113779352945123726153850397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 606823215707326539487202117 113779352945123726153850397)
            ·
              refine ⟨42667257354421397307693899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113779352945123726153850397 42667257354421397307693899)
              ·
                refine ⟨64000886031632095961540849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42667257354421397307693899 64000886031632095961540849)
                ·
                  refine ⟨48000664523724071971155637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64000886031632095961540849 48000664523724071971155637)
                  ·
                    refine ⟨4500062299099131747295841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48000664523724071971155637 4500062299099131747295841)
                    ·
                      refine ⟨3375046724324348810471881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4500062299099131747295841 3375046724324348810471881)
                      ·
                        rfl

theorem cell23_6572880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 5, 2].length) (baseStart_6572880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572880 prefixEnd_6572880 := by exact prefixLift 6572880
  have htrace : WordTrace (prefixWord ++ tailWord_6572880) baseStart_6572880 baseEnd_6572880 := by
    simpa [prefixWord, tailWord_6572880, baseEnd_6572880] using wordTrace_append hprefix tailTrace_6572880
  have hstable : (prefixWord ++ tailWord_6572880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572880).length < 2 ^ (prefixWord ++ tailWord_6572880).sum := by decide
  have hdescent : baseEnd_6572880 < baseStart_6572880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572923 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 6]
def baseStart_6572923 : Nat := 118140960795 + 6572923 * 2 ^ 59
def prefixEnd_6572923 : Nat := 4983230072969 + 3 ^ 40 * 6572923 * 2
def baseEnd_6572923 : Nat := 3375068803992492142234183

theorem tailTrace_6572923 : CollatzResearch.WordTrace tailWord_6572923 prefixEnd_6572923 3375068803992492142234183 := by
  unfold tailWord_6572923
  simp only [CollatzResearch.WordTrace]
  refine ⟨239734196766430011721475423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159822797844286674480983615 239734196766430011721475423)
  ·
    refine ⟨359601295149645017582213135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239734196766430011721475423 359601295149645017582213135)
    ·
      refine ⟨539401942724467526373319703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359601295149645017582213135 539401942724467526373319703)
      ·
        refine ⟨809102914086701289559979555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539401942724467526373319703 809102914086701289559979555)
        ·
          refine ⟨1213654371130051934339969333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 809102914086701289559979555 1213654371130051934339969333)
          ·
            refine ⟨113780097293442368844372125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1213654371130051934339969333 113780097293442368844372125)
            ·
              refine ⟨42667536485040888316639547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113780097293442368844372125 42667536485040888316639547)
              ·
                refine ⟨64001304727561332474959321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42667536485040888316639547 64001304727561332474959321)
                ·
                  refine ⟨48000978545670999356219491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64001304727561332474959321 48000978545670999356219491)
                  ·
                    refine ⟨72001467818506499034329237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48000978545670999356219491 72001467818506499034329237)
                    ·
                      refine ⟨3375068803992492142234183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72001467818506499034329237 3375068803992492142234183)
                      ·
                        rfl

theorem cell23_6572923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 6].length) (baseStart_6572923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572923 prefixEnd_6572923 := by exact prefixLift 6572923
  have htrace : WordTrace (prefixWord ++ tailWord_6572923) baseStart_6572923 baseEnd_6572923 := by
    simpa [prefixWord, tailWord_6572923, baseEnd_6572923] using wordTrace_append hprefix tailTrace_6572923
  have hstable : (prefixWord ++ tailWord_6572923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572923).length < 2 ^ (prefixWord ++ tailWord_6572923).sum := by decide
  have hdescent : baseEnd_6572923 < baseStart_6572923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572937 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 3, 4]
def baseStart_6572937 : Nat := 118140960795 + 6572937 * 2 ^ 59
def prefixEnd_6572937 : Nat := 4983230072969 + 3 ^ 40 * 6572937 * 2
def baseEnd_6572937 : Nat := 1125025330907218362486373

theorem tailTrace_6572937 : CollatzResearch.WordTrace tailWord_6572937 prefixEnd_6572937 1125025330907218362486373 := by
  unfold tailWord_6572937
  simp only [CollatzResearch.WordTrace]
  refine ⟨239734707388379292112485065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159823138258919528074990043 239734707388379292112485065)
  ·
    refine ⟨179801030541284469084363799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239734707388379292112485065 179801030541284469084363799)
    ·
      refine ⟨269701545811926703626545699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179801030541284469084363799 269701545811926703626545699)
      ·
        refine ⟨404552318717890055439818549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269701545811926703626545699 404552318717890055439818549)
        ·
          refine ⟨37926779879802192697482989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 404552318717890055439818549 37926779879802192697482989)
          ·
            refine ⟨14222542454925822261556121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37926779879802192697482989 14222542454925822261556121)
            ·
              refine ⟨10666906841194366696167091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14222542454925822261556121 10666906841194366696167091)
              ·
                refine ⟨16000360261791550044250637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10666906841194366696167091 16000360261791550044250637)
                ·
                  refine ⟨6000135098171831266593989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16000360261791550044250637 6000135098171831266593989)
                  ·
                    refine ⟨1125025330907218362486373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6000135098171831266593989 1125025330907218362486373)
                    ·
                      rfl

theorem cell23_6572937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 4].length) (baseStart_6572937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572937 prefixEnd_6572937 := by exact prefixLift 6572937
  have htrace : WordTrace (prefixWord ++ tailWord_6572937) baseStart_6572937 baseEnd_6572937 := by
    simpa [prefixWord, tailWord_6572937, baseEnd_6572937] using wordTrace_append hprefix tailTrace_6572937
  have hstable : (prefixWord ++ tailWord_6572937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572937).length < 2 ^ (prefixWord ++ tailWord_6572937).sum := by decide
  have hdescent : baseEnd_6572937 < baseStart_6572937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6572953 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 6]
def baseStart_6572953 : Nat := 118140960795 + 6572953 * 2 ^ 59
def prefixEnd_6572953 : Nat := 4983230072969 + 3 ^ 40 * 6572953 * 2
def baseEnd_6572953 : Nat := 3375084208412127024859045

theorem tailTrace_6572953 : CollatzResearch.WordTrace tailWord_6572953 prefixEnd_6572953 3375084208412127024859045 := by
  unfold tailWord_6572953
  simp only [CollatzResearch.WordTrace]
  refine ⟨239735290956321326845067513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159823527304214217896711675 239735290956321326845067513)
  ·
    refine ⟨179801468217240995133800635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239735290956321326845067513 179801468217240995133800635)
    ·
      refine ⟨269702202325861492700700953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179801468217240995133800635 269702202325861492700700953)
      ·
        refine ⟨202276651744396119525525715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269702202325861492700700953 202276651744396119525525715)
        ·
          refine ⟨303414977616594179288288573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202276651744396119525525715 303414977616594179288288573)
          ·
            refine ⟨113780616606222817233108215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303414977616594179288288573 113780616606222817233108215)
            ·
              refine ⟨170670924909334225849662323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113780616606222817233108215 170670924909334225849662323)
              ·
                refine ⟨256006387364001338774493485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170670924909334225849662323 256006387364001338774493485)
                ·
                  refine ⟨96002395261500502040435057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256006387364001338774493485 96002395261500502040435057)
                  ·
                    refine ⟨72001796446125376530326293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96002395261500502040435057 72001796446125376530326293)
                    ·
                      refine ⟨3375084208412127024859045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72001796446125376530326293 3375084208412127024859045)
                      ·
                        rfl

theorem cell23_6572953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_6572953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6572953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6572953 prefixEnd_6572953 := by exact prefixLift 6572953
  have htrace : WordTrace (prefixWord ++ tailWord_6572953) baseStart_6572953 baseEnd_6572953 := by
    simpa [prefixWord, tailWord_6572953, baseEnd_6572953] using wordTrace_append hprefix tailTrace_6572953
  have hstable : (prefixWord ++ tailWord_6572953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6572953).length < 2 ^ (prefixWord ++ tailWord_6572953).sum := by decide
  have hdescent : baseEnd_6572953 < baseStart_6572953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6572953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573014 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_6573014 : Nat := 118140960795 + 6573014 * 2 ^ 59
def prefixEnd_6573014 : Nat := 4983230072969 + 3 ^ 40 * 6573014 * 2
def baseEnd_6573014 : Nat := 1125038510244017095398755

theorem tailTrace_6573014 : CollatzResearch.WordTrace tailWord_6573014 prefixEnd_6573014 1125038510244017095398755 := by
  unfold tailWord_6573014
  simp only [CollatzResearch.WordTrace]
  refine ⟨14983594738068770891439881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159825010539400222842025397 14983594738068770891439881)
  ·
    refine ⟨11237696053551578168579911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14983594738068770891439881 11237696053551578168579911)
    ·
      refine ⟨16856544080327367252869867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11237696053551578168579911 16856544080327367252869867)
      ·
        refine ⟨25284816120491050879304801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16856544080327367252869867 25284816120491050879304801)
        ·
          refine ⟨18963612090368288159478601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25284816120491050879304801 18963612090368288159478601)
          ·
            refine ⟨14222709067776216119608951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18963612090368288159478601 14222709067776216119608951)
            ·
              refine ⟨21334063601664324179413427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14222709067776216119608951 21334063601664324179413427)
              ·
                refine ⟨32001095402496486269120141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21334063601664324179413427 32001095402496486269120141)
                ·
                  refine ⟨12000410775936182350920053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32001095402496486269120141 12000410775936182350920053)
                  ·
                    refine ⟨1125038510244017095398755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12000410775936182350920053 1125038510244017095398755)
                    ·
                      rfl

theorem cell23_6573014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_6573014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573014 prefixEnd_6573014 := by exact prefixLift 6573014
  have htrace : WordTrace (prefixWord ++ tailWord_6573014) baseStart_6573014 baseEnd_6573014 := by
    simpa [prefixWord, tailWord_6573014, baseEnd_6573014] using wordTrace_append hprefix tailTrace_6573014
  have hstable : (prefixWord ++ tailWord_6573014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573014).length < 2 ^ (prefixWord ++ tailWord_6573014).sum := by decide
  have hdescent : baseEnd_6573014 < baseStart_6573014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573017 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 3, 1, 4]
def baseStart_6573017 : Nat := 118140960795 + 6573017 * 2 ^ 59
def prefixEnd_6573017 : Nat := 4983230072969 + 3 ^ 40 * 6573017 * 2
def baseEnd_6573017 : Nat := 3375117071174014774458751

theorem tailTrace_6573017 : CollatzResearch.WordTrace tailWord_6573017 prefixEnd_6573017 3375117071174014774458751 := by
  unfold tailWord_6573017
  simp only [CollatzResearch.WordTrace]
  refine ⟨239737625228089465775397305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159825083485392977183598203 239737625228089465775397305)
  ·
    refine ⟨179803218921067099331547979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239737625228089465775397305 179803218921067099331547979)
    ·
      refine ⟨269704828381600648997321969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179803218921067099331547979 269704828381600648997321969)
      ·
        refine ⟨202278621286200486747991477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269704828381600648997321969 202278621286200486747991477)
        ·
          refine ⟨18963620745581295632624201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202278621286200486747991477 18963620745581295632624201)
          ·
            refine ⟨14222715559185971724468151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18963620745581295632624201 14222715559185971724468151)
            ·
              refine ⟨21334073338778957586702227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14222715559185971724468151 21334073338778957586702227)
              ·
                refine ⟨32001110008168436380053341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21334073338778957586702227 32001110008168436380053341)
                ·
                  refine ⟨12000416253063163642520003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32001110008168436380053341 12000416253063163642520003)
                  ·
                    refine ⟨18000624379594745463780005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12000416253063163642520003 18000624379594745463780005)
                    ·
                      refine ⟨3375117071174014774458751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18000624379594745463780005 3375117071174014774458751)
                      ·
                        rfl

theorem cell23_6573017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_6573017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573017 prefixEnd_6573017 := by exact prefixLift 6573017
  have htrace : WordTrace (prefixWord ++ tailWord_6573017) baseStart_6573017 baseEnd_6573017 := by
    simpa [prefixWord, tailWord_6573017, baseEnd_6573017] using wordTrace_append hprefix tailTrace_6573017
  have hstable : (prefixWord ++ tailWord_6573017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573017).length < 2 ^ (prefixWord ++ tailWord_6573017).sum := by decide
  have hdescent : baseEnd_6573017 < baseStart_6573017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573021 : List Nat := [1, 4, 3, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_6573021 : Nat := 118140960795 + 6573021 * 2 ^ 59
def prefixEnd_6573021 : Nat := 4983230072969 + 3 ^ 40 * 6573021 * 2
def baseEnd_6573021 : Nat := 3375119125096632758808733

theorem tailTrace_6573021 : CollatzResearch.WordTrace tailWord_6573021 prefixEnd_6573021 3375119125096632758808733 := by
  unfold tailWord_6573021
  simp only [CollatzResearch.WordTrace]
  refine ⟨239737771120074974458542917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159825180746716649639028611 239737771120074974458542917)
  ·
    refine ⟨44950832085014057710976797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239737771120074974458542917 44950832085014057710976797)
    ·
      refine ⟨16856562031880271641616299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44950832085014057710976797 16856562031880271641616299)
      ·
        refine ⟨25284843047820407462424449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16856562031880271641616299 25284843047820407462424449)
        ·
          refine ⟨18963632285865305596818337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25284843047820407462424449 18963632285865305596818337)
          ·
            refine ⟨14222724214398979197613753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18963632285865305596818337 14222724214398979197613753)
            ·
              refine ⟨10667043160799234398210315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14222724214398979197613753 10667043160799234398210315)
              ·
                refine ⟨16000564741198851597315473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10667043160799234398210315 16000564741198851597315473)
                ·
                  refine ⟨12000423555899138697986605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16000564741198851597315473 12000423555899138697986605)
                  ·
                    refine ⟨4500158833462177011744977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12000423555899138697986605 4500158833462177011744977)
                    ·
                      refine ⟨3375119125096632758808733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4500158833462177011744977 3375119125096632758808733)
                      ·
                        rfl

theorem cell23_6573021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_6573021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573021 prefixEnd_6573021 := by exact prefixLift 6573021
  have htrace : WordTrace (prefixWord ++ tailWord_6573021) baseStart_6573021 baseEnd_6573021 := by
    simpa [prefixWord, tailWord_6573021, baseEnd_6573021] using wordTrace_append hprefix tailTrace_6573021
  have hstable : (prefixWord ++ tailWord_6573021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573021).length < 2 ^ (prefixWord ++ tailWord_6573021).sum := by decide
  have hdescent : baseEnd_6573021 < baseStart_6573021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573045 : List Nat := [1, 3, 5, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6573045 : Nat := 118140960795 + 6573045 * 2 ^ 59
def prefixEnd_6573045 : Nat := 4983230072969 + 3 ^ 40 * 6573045 * 2
def baseEnd_6573045 : Nat := 3375131448632340664908623

theorem tailTrace_6573045 : CollatzResearch.WordTrace tailWord_6573045 prefixEnd_6573045 3375131448632340664908623 := by
  unfold tailWord_6573045
  simp only [CollatzResearch.WordTrace]
  refine ⟨239738646471988026557416589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159825764314658684371611059 239738646471988026557416589)
  ·
    refine ⟨89901992426995509959031221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239738646471988026557416589 89901992426995509959031221)
    ·
      refine ⟨8428311790030829058659177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89901992426995509959031221 8428311790030829058659177)
      ·
        refine ⟨6321233842523121793994383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8428311790030829058659177 6321233842523121793994383)
        ·
          refine ⟨9481850763784682690991575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6321233842523121793994383 9481850763784682690991575)
          ·
            refine ⟨14222776145677024036487363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9481850763784682690991575 14222776145677024036487363)
            ·
              refine ⟨21334164218515536054731045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14222776145677024036487363 21334164218515536054731045)
              ·
                refine ⟨4000155790971663010262071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21334164218515536054731045 4000155790971663010262071)
                ·
                  refine ⟨6000233686457494515393107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000155790971663010262071 6000233686457494515393107)
                  ·
                    refine ⟨9000350529686241773089661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6000233686457494515393107 9000350529686241773089661)
                    ·
                      refine ⟨3375131448632340664908623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9000350529686241773089661 3375131448632340664908623)
                      ·
                        rfl

theorem cell23_6573045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6573045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573045 prefixEnd_6573045 := by exact prefixLift 6573045
  have htrace : WordTrace (prefixWord ++ tailWord_6573045) baseStart_6573045 baseEnd_6573045 := by
    simpa [prefixWord, tailWord_6573045, baseEnd_6573045] using wordTrace_append hprefix tailTrace_6573045
  have hstable : (prefixWord ++ tailWord_6573045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573045).length < 2 ^ (prefixWord ++ tailWord_6573045).sum := by decide
  have hdescent : baseEnd_6573045 < baseStart_6573045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573057 : List Nat := [1, 2, 4, 1, 2, 4, 1, 8]
def baseStart_6573057 : Nat := 118140960795 + 6573057 * 2 ^ 59
def prefixEnd_6573057 : Nat := 4983230072969 + 3 ^ 40 * 6573057 * 2
def baseEnd_6573057 : Nat := 125005096681488689554021

theorem tailTrace_6573057 : CollatzResearch.WordTrace tailWord_6573057 prefixEnd_6573057 125005096681488689554021 := by
  unfold tailWord_6573057
  simp only [CollatzResearch.WordTrace]
  refine ⟨239739084147944552606853425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159826056098629701737902283 239739084147944552606853425)
  ·
    refine ⟨179804313110958414455140069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239739084147944552606853425 179804313110958414455140069)
    ·
      refine ⟨33713308708304702710338763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179804313110958414455140069 33713308708304702710338763)
      ·
        refine ⟨50569963062457054065508145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33713308708304702710338763 50569963062457054065508145)
        ·
          refine ⟨37927472296842790549131109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50569963062457054065508145 37927472296842790549131109)
          ·
            refine ⟨7111401055658023227962083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37927472296842790549131109 7111401055658023227962083)
            ·
              refine ⟨10667101583487034841943125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7111401055658023227962083 10667101583487034841943125)
              ·
                refine ⟨125005096681488689554021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10667101583487034841943125 125005096681488689554021)
                ·
                  rfl

theorem cell23_6573057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 8].length) (baseStart_6573057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573057 prefixEnd_6573057 := by exact prefixLift 6573057
  have htrace : WordTrace (prefixWord ++ tailWord_6573057) baseStart_6573057 baseEnd_6573057 := by
    simpa [prefixWord, tailWord_6573057, baseEnd_6573057] using wordTrace_append hprefix tailTrace_6573057
  have hstable : (prefixWord ++ tailWord_6573057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573057).length < 2 ^ (prefixWord ++ tailWord_6573057).sum := by decide
  have hdescent : baseEnd_6573057 < baseStart_6573057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573067 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 3]
def baseStart_6573067 : Nat := 118140960795 + 6573067 * 2 ^ 59
def prefixEnd_6573067 : Nat := 4983230072969 + 3 ^ 40 * 6573067 * 2
def baseEnd_6573067 : Nat := 3375142745206739578833521

theorem tailTrace_6573067 : CollatzResearch.WordTrace tailWord_6573067 prefixEnd_6573067 3375142745206739578833521 := by
  unfold tailWord_6573067
  simp only [CollatzResearch.WordTrace]
  refine ⟨239739448877908324314717455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159826299251938882876478303 239739448877908324314717455)
  ·
    refine ⟨359609173316862486472076183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239739448877908324314717455 359609173316862486472076183)
    ·
      refine ⟨539413759975293729708114275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359609173316862486472076183 539413759975293729708114275)
      ·
        refine ⟨809120639962940594562171413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539413759975293729708114275 809120639962940594562171413)
        ·
          refine ⟨37927529998262840370101785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 809120639962940594562171413 37927529998262840370101785)
          ·
            refine ⟨28445647498697130277576339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37927529998262840370101785 28445647498697130277576339)
            ·
              refine ⟨42668471248045695416364509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28445647498697130277576339 42668471248045695416364509)
              ·
                refine ⟨16000676718017135781136691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42668471248045695416364509 16000676718017135781136691)
                ·
                  refine ⟨24001015077025703671705037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16000676718017135781136691 24001015077025703671705037)
                  ·
                    refine ⟨9000380653884638876889389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24001015077025703671705037 9000380653884638876889389)
                    ·
                      refine ⟨3375142745206739578833521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9000380653884638876889389 3375142745206739578833521)
                      ·
                        rfl

theorem cell23_6573067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 3].length) (baseStart_6573067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573067 prefixEnd_6573067 := by exact prefixLift 6573067
  have htrace : WordTrace (prefixWord ++ tailWord_6573067) baseStart_6573067 baseEnd_6573067 := by
    simpa [prefixWord, tailWord_6573067, baseEnd_6573067] using wordTrace_append hprefix tailTrace_6573067
  have hstable : (prefixWord ++ tailWord_6573067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573067).length < 2 ^ (prefixWord ++ tailWord_6573067).sum := by decide
  have hdescent : baseEnd_6573067 < baseStart_6573067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573085 : List Nat := [1, 4, 2, 2, 3, 1, 2, 3, 1, 2, 2]
def baseStart_6573085 : Nat := 118140960795 + 6573085 * 2 ^ 59
def prefixEnd_6573085 : Nat := 4983230072969 + 3 ^ 40 * 6573085 * 2
def baseEnd_6573085 : Nat := 3375151987858520508408439

theorem tailTrace_6573085 : CollatzResearch.WordTrace tailWord_6573085 prefixEnd_6573085 3375151987858520508408439 := by
  unfold tailWord_6573085
  simp only [CollatzResearch.WordTrace]
  refine ⟨239740105391843113388872709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159826736927895408925915139 239740105391843113388872709)
  ·
    refine ⟨44951269760970583760413633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239740105391843113388872709 44951269760970583760413633)
    ·
      refine ⟨33713452320727937820310225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44951269760970583760413633 33713452320727937820310225)
      ·
        refine ⟨25285089240545953365232669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33713452320727937820310225 25285089240545953365232669)
        ·
          refine ⟨9481908465204732511962251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25285089240545953365232669 9481908465204732511962251)
          ·
            refine ⟨14222862697807098767943377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9481908465204732511962251 14222862697807098767943377)
            ·
              refine ⟨10667147023355324075957533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14222862697807098767943377 10667147023355324075957533)
              ·
                refine ⟨4000180133758246528484075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10667147023355324075957533 4000180133758246528484075)
                ·
                  refine ⟨6000270200637369792726113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000180133758246528484075 6000270200637369792726113)
                  ·
                    refine ⟨4500202650478027344544585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6000270200637369792726113 4500202650478027344544585)
                    ·
                      refine ⟨3375151987858520508408439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4500202650478027344544585 3375151987858520508408439)
                      ·
                        rfl

theorem cell23_6573085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_6573085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573085 prefixEnd_6573085 := by exact prefixLift 6573085
  have htrace : WordTrace (prefixWord ++ tailWord_6573085) baseStart_6573085 baseEnd_6573085 := by
    simpa [prefixWord, tailWord_6573085, baseEnd_6573085] using wordTrace_append hprefix tailTrace_6573085
  have hstable : (prefixWord ++ tailWord_6573085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573085).length < 2 ^ (prefixWord ++ tailWord_6573085).sum := by decide
  have hdescent : baseEnd_6573085 < baseStart_6573085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573100 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 4, 6]
def baseStart_6573100 : Nat := 118140960795 + 6573100 * 2 ^ 59
def prefixEnd_6573100 : Nat := 4983230072969 + 3 ^ 40 * 6573100 * 2
def baseEnd_6573100 : Nat := 1125053230022779316573623

theorem tailTrace_6573100 : CollatzResearch.WordTrace tailWord_6573100 prefixEnd_6573100 1125053230022779316573623 := by
  unfold tailWord_6573100
  simp only [CollatzResearch.WordTrace]
  refine ⟨119870326243394385475334377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159827101657859180633779169 119870326243394385475334377)
  ·
    refine ⟨89902744682545789106500783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119870326243394385475334377 89902744682545789106500783)
    ·
      refine ⟨134854117023818683659751175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89902744682545789106500783 134854117023818683659751175)
      ·
        refine ⟨202281175535728025489626763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134854117023818683659751175 202281175535728025489626763)
        ·
          refine ⟨303421763303592038234440145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202281175535728025489626763 303421763303592038234440145)
          ·
            refine ⟨227566322477694028675830109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303421763303592038234440145 227566322477694028675830109)
            ·
              refine ⟨85337370929135260753436291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227566322477694028675830109 85337370929135260753436291)
              ·
                refine ⟨128006056393702891130154437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85337370929135260753436291 128006056393702891130154437)
                ·
                  refine ⟨24001135573819292086903957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128006056393702891130154437 24001135573819292086903957)
                  ·
                    refine ⟨1125053230022779316573623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24001135573819292086903957 1125053230022779316573623)
                    ·
                      rfl

theorem cell23_6573100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_6573100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573100 prefixEnd_6573100 := by exact prefixLift 6573100
  have htrace : WordTrace (prefixWord ++ tailWord_6573100) baseStart_6573100 baseEnd_6573100 := by
    simpa [prefixWord, tailWord_6573100, baseEnd_6573100] using wordTrace_append hprefix tailTrace_6573100
  have hstable : (prefixWord ++ tailWord_6573100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573100).length < 2 ^ (prefixWord ++ tailWord_6573100).sum := by decide
  have hdescent : baseEnd_6573100 < baseStart_6573100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573117 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_6573117 : Nat := 118140960795 + 6573117 * 2 ^ 59
def prefixEnd_6573117 : Nat := 4983230072969 + 3 ^ 40 * 6573117 * 2
def baseEnd_6573117 : Nat := 1125056139746488127736097

theorem tailTrace_6573117 : CollatzResearch.WordTrace tailWord_6573117 prefixEnd_6573117 1125056139746488127736097 := by
  unfold tailWord_6573117
  simp only [CollatzResearch.WordTrace]
  refine ⟨239741272527727182854037605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159827515018484788569358403 239741272527727182854037605)
  ·
    refine ⟨44951488598948846785132051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239741272527727182854037605 44951488598948846785132051)
    ·
      refine ⟨67427232898423270177698077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44951488598948846785132051 67427232898423270177698077)
      ·
        refine ⟨25285212336908726316636779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67427232898423270177698077 25285212336908726316636779)
        ·
          refine ⟨37927818505363089474955169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25285212336908726316636779 37927818505363089474955169)
          ·
            refine ⟨28445863879022317106216377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37927818505363089474955169 28445863879022317106216377)
            ·
              refine ⟨21334397909266737829662283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28445863879022317106216377 21334397909266737829662283)
              ·
                refine ⟨32001596863900106744493425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21334397909266737829662283 32001596863900106744493425)
                ·
                  refine ⟨24001197647925080058370069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32001596863900106744493425 24001197647925080058370069)
                  ·
                    refine ⟨1125056139746488127736097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24001197647925080058370069 1125056139746488127736097)
                    ·
                      rfl

theorem cell23_6573117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_6573117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573117 prefixEnd_6573117 := by exact prefixLift 6573117
  have htrace : WordTrace (prefixWord ++ tailWord_6573117) baseStart_6573117 baseEnd_6573117 := by
    simpa [prefixWord, tailWord_6573117, baseEnd_6573117] using wordTrace_append hprefix tailTrace_6573117
  have hstable : (prefixWord ++ tailWord_6573117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573117).length < 2 ^ (prefixWord ++ tailWord_6573117).sum := by decide
  have hdescent : baseEnd_6573117 < baseStart_6573117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573174 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_6573174 : Nat := 118140960795 + 6573174 * 2 ^ 59
def prefixEnd_6573174 : Nat := 4983230072969 + 3 ^ 40 * 6573174 * 2
def baseEnd_6573174 : Nat := 3375197687636770660195529

theorem tailTrace_6573174 : CollatzResearch.WordTrace tailWord_6573174 prefixEnd_6573174 3375197687636770660195529 := by
  unfold tailWord_6573174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14983959468032542599303911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159828900992347121059241717 14983959468032542599303911)
  ·
    refine ⟨22475939202048813898955867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14983959468032542599303911 22475939202048813898955867)
    ·
      refine ⟨33713908803073220848433801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22475939202048813898955867 33713908803073220848433801)
      ·
        refine ⟨25285431602304915636325351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33713908803073220848433801 25285431602304915636325351)
        ·
          refine ⟨37928147403457373454488027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25285431602304915636325351 37928147403457373454488027)
          ·
            refine ⟨56892221105186060181732041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37928147403457373454488027 56892221105186060181732041)
            ·
              refine ⟨42669165828889545136299031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56892221105186060181732041 42669165828889545136299031)
              ·
                refine ⟨64003748743334317704448547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42669165828889545136299031 64003748743334317704448547)
                ·
                  refine ⟨96005623115001476556672821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64003748743334317704448547 96005623115001476556672821)
                  ·
                    refine ⟨9000527167031388427188077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96005623115001476556672821 9000527167031388427188077)
                    ·
                      refine ⟨3375197687636770660195529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9000527167031388427188077 3375197687636770660195529)
                      ·
                        rfl

theorem cell23_6573174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_6573174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573174 prefixEnd_6573174 := by exact prefixLift 6573174
  have htrace : WordTrace (prefixWord ++ tailWord_6573174) baseStart_6573174 baseEnd_6573174 := by
    simpa [prefixWord, tailWord_6573174, baseEnd_6573174] using wordTrace_append hprefix tailTrace_6573174
  have hstable : (prefixWord ++ tailWord_6573174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573174).length < 2 ^ (prefixWord ++ tailWord_6573174).sum := by decide
  have hdescent : baseEnd_6573174 < baseStart_6573174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573194 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 2, 5]
def baseStart_6573194 : Nat := 118140960795 + 6573194 * 2 ^ 59
def prefixEnd_6573194 : Nat := 4983230072969 + 3 ^ 40 * 6573194 * 2
def baseEnd_6573194 : Nat := 1125069319083286860648479

theorem tailTrace_6573194 : CollatzResearch.WordTrace tailWord_6573194 prefixEnd_6573194 1125069319083286860648479 := by
  unfold tailWord_6573194
  simp only [CollatzResearch.WordTrace]
  refine ⟨59936020237112056251147659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159829387298965483336393757 59936020237112056251147659)
  ·
    refine ⟨89904030355668084376721489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59936020237112056251147659 89904030355668084376721489)
    ·
      refine ⟨67428022766751063282541117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89904030355668084376721489 67428022766751063282541117)
      ·
        refine ⟨25285508537531648730952919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67428022766751063282541117 25285508537531648730952919)
        ·
          refine ⟨37928262806297473096429379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25285508537531648730952919 37928262806297473096429379)
          ·
            refine ⟨56892394209446209644644069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37928262806297473096429379 56892394209446209644644069)
            ·
              refine ⟨10667323914271164308370763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56892394209446209644644069 10667323914271164308370763)
              ·
                refine ⟨16000985871406746462556145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10667323914271164308370763 16000985871406746462556145)
                ·
                  refine ⟨12000739403555059846917109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16000985871406746462556145 12000739403555059846917109)
                  ·
                    refine ⟨1125069319083286860648479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12000739403555059846917109 1125069319083286860648479)
                    ·
                      rfl

theorem cell23_6573194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_6573194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573194 prefixEnd_6573194 := by exact prefixLift 6573194
  have htrace : WordTrace (prefixWord ++ tailWord_6573194) baseStart_6573194 baseEnd_6573194 := by
    simpa [prefixWord, tailWord_6573194, baseEnd_6573194] using wordTrace_append hprefix tailTrace_6573194
  have hstable : (prefixWord ++ tailWord_6573194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573194).length < 2 ^ (prefixWord ++ tailWord_6573194).sum := by decide
  have hdescent : baseEnd_6573194 < baseStart_6573194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573215 : List Nat := [1, 1, 2, 6, 3, 1, 2, 2, 5]
def baseStart_6573215 : Nat := 118140960795 + 6573215 * 2 ^ 59
def prefixEnd_6573215 : Nat := 4983230072969 + 3 ^ 40 * 6573215 * 2
def baseEnd_6573215 : Nat := 375024304482622777753649

theorem tailTrace_6573215 : CollatzResearch.WordTrace tailWord_6573215 prefixEnd_6573215 375024304482622777753649 := by
  unfold tailWord_6573215
  simp only [CollatzResearch.WordTrace]
  refine ⟨239744846881372145591105099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159829897920914763727403399 239744846881372145591105099)
  ·
    refine ⟨359617270322058218386657649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239744846881372145591105099 359617270322058218386657649)
    ·
      refine ⟨269712952741543663789993237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359617270322058218386657649 269712952741543663789993237)
      ·
        refine ⟨12642794659759859240155933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 269712952741543663789993237 12642794659759859240155933)
        ·
          refine ⟨4741047997409947215058475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12642794659759859240155933 4741047997409947215058475)
          ·
            refine ⟨7111571996114920822587713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4741047997409947215058475 7111571996114920822587713)
            ·
              refine ⟨5333678997086190616940785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7111571996114920822587713 5333678997086190616940785)
              ·
                refine ⟨4000259247814642962705589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5333678997086190616940785 4000259247814642962705589)
                ·
                  refine ⟨375024304482622777753649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4000259247814642962705589 375024304482622777753649)
                  ·
                    rfl

theorem cell23_6573215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 5].length) (baseStart_6573215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573215 prefixEnd_6573215 := by exact prefixLift 6573215
  have htrace : WordTrace (prefixWord ++ tailWord_6573215) baseStart_6573215 baseEnd_6573215 := by
    simpa [prefixWord, tailWord_6573215, baseEnd_6573215] using wordTrace_append hprefix tailTrace_6573215
  have hstable : (prefixWord ++ tailWord_6573215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573215).length < 2 ^ (prefixWord ++ tailWord_6573215).sum := by decide
  have hdescent : baseEnd_6573215 < baseStart_6573215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573217 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_6573217 : Nat := 118140960795 + 6573217 * 2 ^ 59
def prefixEnd_6573217 : Nat := 4983230072969 + 3 ^ 40 * 6573217 * 2
def baseEnd_6573217 : Nat := 3375219767304913991957831

theorem tailTrace_6573217 : CollatzResearch.WordTrace tailWord_6573217 prefixEnd_6573217 3375219767304913991957831 := by
  unfold tailWord_6573217
  simp only [CollatzResearch.WordTrace]
  refine ⟨239744919827364899932677905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159829946551576599955118603 239744919827364899932677905)
  ·
    refine ⟨179808689870523674949508429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239744919827364899932677905 179808689870523674949508429)
    ·
      refine ⟨67428258701446378106065661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179808689870523674949508429 67428258701446378106065661)
      ·
        refine ⟨25285597013042391789774623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67428258701446378106065661 25285597013042391789774623)
        ·
          refine ⟨37928395519563587684661935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25285597013042391789774623 37928395519563587684661935)
          ·
            refine ⟨56892593279345381526992903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37928395519563587684661935 56892593279345381526992903)
            ·
              refine ⟨85338889919018072290489355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56892593279345381526992903 85338889919018072290489355)
              ·
                refine ⟨128008334878527108435734033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85338889919018072290489355 128008334878527108435734033)
                ·
                  refine ⟨96006251158895331326800525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128008334878527108435734033 96006251158895331326800525)
                  ·
                    refine ⟨36002344184585749247550197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96006251158895331326800525 36002344184585749247550197)
                    ·
                      refine ⟨3375219767304913991957831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36002344184585749247550197 3375219767304913991957831)
                      ·
                        rfl

theorem cell23_6573217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_6573217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573217 prefixEnd_6573217 := by exact prefixLift 6573217
  have htrace : WordTrace (prefixWord ++ tailWord_6573217) baseStart_6573217 baseEnd_6573217 := by
    simpa [prefixWord, tailWord_6573217, baseEnd_6573217] using wordTrace_append hprefix tailTrace_6573217
  have hstable : (prefixWord ++ tailWord_6573217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573217).length < 2 ^ (prefixWord ++ tailWord_6573217).sum := by decide
  have hdescent : baseEnd_6573217 < baseStart_6573217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573248 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 2, 1, 4]
def baseStart_6573248 : Nat := 118140960795 + 6573248 * 2 ^ 59
def prefixEnd_6573248 : Nat := 4983230072969 + 3 ^ 40 * 6573248 * 2
def baseEnd_6573248 : Nat := 3375235685205203370670189

theorem tailTrace_6573248 : CollatzResearch.WordTrace tailWord_6573248 prefixEnd_6573248 3375235685205203370670189 := by
  unfold tailWord_6573248
  simp only [CollatzResearch.WordTrace]
  refine ⟨119873025245126296113528199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159830700326835061484704265 119873025245126296113528199)
  ·
    refine ⟨179809537867689444170292299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119873025245126296113528199 179809537867689444170292299)
    ·
      refine ⟨269714306801534166255438449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179809537867689444170292299 269714306801534166255438449)
      ·
        refine ⟨202285730101150624691578837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269714306801534166255438449 202285730101150624691578837)
        ·
          refine ⟨4741071799245717766208879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 202285730101150624691578837 4741071799245717766208879)
          ·
            refine ⟨7111607698868576649313319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4741071799245717766208879 7111607698868576649313319)
            ·
              refine ⟨10667411548302864973969979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7111607698868576649313319 10667411548302864973969979)
              ·
                refine ⟨16001117322454297460954969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10667411548302864973969979 16001117322454297460954969)
                ·
                  refine ⟨12000837991840723095716227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16001117322454297460954969 12000837991840723095716227)
                  ·
                    refine ⟨18001256987761084643574341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12000837991840723095716227 18001256987761084643574341)
                    ·
                      refine ⟨3375235685205203370670189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18001256987761084643574341 3375235685205203370670189)
                      ·
                        rfl

theorem cell23_6573248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 2, 1, 4].length) (baseStart_6573248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573248 prefixEnd_6573248 := by exact prefixLift 6573248
  have htrace : WordTrace (prefixWord ++ tailWord_6573248) baseStart_6573248 baseEnd_6573248 := by
    simpa [prefixWord, tailWord_6573248, baseEnd_6573248] using wordTrace_append hprefix tailTrace_6573248
  have hstable : (prefixWord ++ tailWord_6573248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573248).length < 2 ^ (prefixWord ++ tailWord_6573248).sum := by decide
  have hdescent : baseEnd_6573248 < baseStart_6573248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573258 : List Nat := [3, 1, 2, 1, 3, 3, 2, 3, 1, 4]
def baseStart_6573258 : Nat := 118140960795 + 6573258 * 2 ^ 59
def prefixEnd_6573258 : Nat := 4983230072969 + 3 ^ 40 * 6573258 * 2
def baseEnd_6573258 : Nat := 1125080273337249443848381

theorem tailTrace_6573258 : CollatzResearch.WordTrace tailWord_6573258 prefixEnd_6573258 1125080273337249443848381 := by
  unfold tailWord_6573258
  simp only [CollatzResearch.WordTrace]
  refine ⟨59936603805054090983730107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159830943480144242623280285 59936603805054090983730107)
  ·
    refine ⟨89904905707581136475595161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59936603805054090983730107 89904905707581136475595161)
    ·
      refine ⟨67428679280685852356696371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89904905707581136475595161 67428679280685852356696371)
      ·
        refine ⟨101143018921028778535044557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67428679280685852356696371 101143018921028778535044557)
        ·
          refine ⟨37928632095385791950641709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101143018921028778535044557 37928632095385791950641709)
          ·
            refine ⟨14223237035769671981490641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37928632095385791950641709 14223237035769671981490641)
            ·
              refine ⟨10667427776827253986117981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14223237035769671981490641 10667427776827253986117981)
              ·
                refine ⟨4000285416310220244794243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10667427776827253986117981 4000285416310220244794243)
                ·
                  refine ⟨6000428124465330367191365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000285416310220244794243 6000428124465330367191365)
                  ·
                    refine ⟨1125080273337249443848381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6000428124465330367191365 1125080273337249443848381)
                    ·
                      rfl

theorem cell23_6573258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_6573258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573258 prefixEnd_6573258 := by exact prefixLift 6573258
  have htrace : WordTrace (prefixWord ++ tailWord_6573258) baseStart_6573258 baseEnd_6573258 := by
    simpa [prefixWord, tailWord_6573258, baseEnd_6573258] using wordTrace_append hprefix tailTrace_6573258
  have hstable : (prefixWord ++ tailWord_6573258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573258).length < 2 ^ (prefixWord ++ tailWord_6573258).sum := by decide
  have hdescent : baseEnd_6573258 < baseStart_6573258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573281 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 3, 1, 3]
def baseStart_6573281 : Nat := 118140960795 + 6573281 * 2 ^ 59
def prefixEnd_6573281 : Nat := 4983230072969 + 3 ^ 40 * 6573281 * 2
def baseEnd_6573281 : Nat := 3375252630066801741557537

theorem tailTrace_6573281 : CollatzResearch.WordTrace tailWord_6573281 prefixEnd_6573281 3375252630066801741557537 := by
  unfold tailWord_6573281
  simp only [CollatzResearch.WordTrace]
  refine ⟨239747254099133038863007697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159831502732755359242005131 239747254099133038863007697)
  ·
    refine ⟨179810440574349779147255773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239747254099133038863007697 179810440574349779147255773)
    ·
      refine ⟨67428915215381167180220915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179810440574349779147255773 67428915215381167180220915)
      ·
        refine ⟨101143372823071750770331373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67428915215381167180220915 101143372823071750770331373)
        ·
          refine ⟨37928764808651906538874265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101143372823071750770331373 37928764808651906538874265)
          ·
            refine ⟨28446573606488929904155699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37928764808651906538874265 28446573606488929904155699)
            ·
              refine ⟨42669860409733394856233549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28446573606488929904155699 42669860409733394856233549)
              ·
                refine ⟨16001197653650023071087581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42669860409733394856233549 16001197653650023071087581)
                ·
                  refine ⟨6000449120118758651657843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16001197653650023071087581 6000449120118758651657843)
                  ·
                    refine ⟨9000673680178137977486765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6000449120118758651657843 9000673680178137977486765)
                    ·
                      refine ⟨3375252630066801741557537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9000673680178137977486765 3375252630066801741557537)
                      ·
                        rfl

theorem cell23_6573281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_6573281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573281 prefixEnd_6573281 := by exact prefixLift 6573281
  have htrace : WordTrace (prefixWord ++ tailWord_6573281) baseStart_6573281 baseEnd_6573281 := by
    simpa [prefixWord, tailWord_6573281, baseEnd_6573281] using wordTrace_append hprefix tailTrace_6573281
  have hstable : (prefixWord ++ tailWord_6573281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573281).length < 2 ^ (prefixWord ++ tailWord_6573281).sum := by decide
  have hdescent : baseEnd_6573281 < baseStart_6573281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573315 : List Nat := [1, 1, 1, 3, 2, 6, 1, 3, 1, 1, 3]
def baseStart_6573315 : Nat := 118140960795 + 6573315 * 2 ^ 59
def prefixEnd_6573315 : Nat := 4983230072969 + 3 ^ 40 * 6573315 * 2
def baseEnd_6573315 : Nat := 3375270088409054608532381

theorem tailTrace_6573315 : CollatzResearch.WordTrace tailWord_6573315 prefixEnd_6573315 3375270088409054608532381 := by
  unfold tailWord_6573315
  simp only [CollatzResearch.WordTrace]
  refine ⟨239748494181009862669745399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159832329454006575113163599 239748494181009862669745399)
  ·
    refine ⟨359622741271514794004618099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239748494181009862669745399 359622741271514794004618099)
    ·
      refine ⟨539434111907272191006927149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359622741271514794004618099 539434111907272191006927149)
      ·
        refine ⟨202287791965227071627597681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 539434111907272191006927149 202287791965227071627597681)
        ·
          refine ⟨151715843973920303720698261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202287791965227071627597681 151715843973920303720698261)
          ·
            refine ⟨7111680186277514236907731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 151715843973920303720698261 7111680186277514236907731)
            ·
              refine ⟨10667520279416271355361597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7111680186277514236907731 10667520279416271355361597)
              ·
                refine ⟨4000320104781101758260599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10667520279416271355361597 4000320104781101758260599)
                ·
                  refine ⟨6000480157171652637390899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000320104781101758260599 6000480157171652637390899)
                  ·
                    refine ⟨9000720235757478956086349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6000480157171652637390899 9000720235757478956086349)
                    ·
                      refine ⟨3375270088409054608532381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9000720235757478956086349 3375270088409054608532381)
                      ·
                        rfl

theorem cell23_6573315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 1, 1, 3].length) (baseStart_6573315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573315 prefixEnd_6573315 := by exact prefixLift 6573315
  have htrace : WordTrace (prefixWord ++ tailWord_6573315) baseStart_6573315 baseEnd_6573315 := by
    simpa [prefixWord, tailWord_6573315, baseEnd_6573315] using wordTrace_append hprefix tailTrace_6573315
  have hstable : (prefixWord ++ tailWord_6573315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573315).length < 2 ^ (prefixWord ++ tailWord_6573315).sum := by decide
  have hdescent : baseEnd_6573315 < baseStart_6573315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573324 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 1, 1, 5]
def baseStart_6573324 : Nat := 118140960795 + 6573324 * 2 ^ 59
def prefixEnd_6573324 : Nat := 4983230072969 + 3 ^ 40 * 6573324 * 2
def baseEnd_6573324 : Nat := 3375274709734945073319839

theorem tailTrace_6573324 : CollatzResearch.WordTrace tailWord_6573324 prefixEnd_6573324 3375274709734945073319839 := by
  unfold tailWord_6573324
  simp only [CollatzResearch.WordTrace]
  refine ⟨119874411218988628603411513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159832548291984838137882017 119874411218988628603411513)
  ·
    refine ⟨89905808414241471452558635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119874411218988628603411513 89905808414241471452558635)
    ·
      refine ⟨134858712621362207178837953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89905808414241471452558635 134858712621362207178837953)
      ·
        refine ⟨101144034466021655384128465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134858712621362207178837953 101144034466021655384128465)
        ·
          refine ⟨75858025849516241538096349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101144034466021655384128465 75858025849516241538096349)
          ·
            refine ⟨28446759693568590576786131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75858025849516241538096349 28446759693568590576786131)
            ·
              refine ⟨42670139540352885865179197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28446759693568590576786131 42670139540352885865179197)
              ·
                refine ⟨16001302327632332199442199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42670139540352885865179197 16001302327632332199442199)
                ·
                  refine ⟨24001953491448498299163299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16001302327632332199442199 24001953491448498299163299)
                  ·
                    refine ⟨36002930237172747448744949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24001953491448498299163299 36002930237172747448744949)
                    ·
                      refine ⟨3375274709734945073319839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36002930237172747448744949 3375274709734945073319839)
                      ·
                        rfl

theorem cell23_6573324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_6573324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573324 prefixEnd_6573324 := by exact prefixLift 6573324
  have htrace : WordTrace (prefixWord ++ tailWord_6573324) baseStart_6573324 baseEnd_6573324 := by
    simpa [prefixWord, tailWord_6573324, baseEnd_6573324] using wordTrace_append hprefix tailTrace_6573324
  have hstable : (prefixWord ++ tailWord_6573324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573324).length < 2 ^ (prefixWord ++ tailWord_6573324).sum := by decide
  have hdescent : baseEnd_6573324 < baseStart_6573324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573341 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_6573341 : Nat := 118140960795 + 6573341 * 2 ^ 59
def prefixEnd_6573341 : Nat := 4983230072969 + 3 ^ 40 * 6573341 * 2
def baseEnd_6573341 : Nat := 3375283438906071506807261

theorem tailTrace_6573341 : CollatzResearch.WordTrace tailWord_6573341 prefixEnd_6573341 3375283438906071506807261 := by
  unfold tailWord_6573341
  simp only [CollatzResearch.WordTrace]
  refine ⟨239749442478915669110191877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159832961652610446073461251 239749442478915669110191877)
  ·
    refine ⟨44953020464796687958160977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239749442478915669110191877 44953020464796687958160977)
    ·
      refine ⟨33714765348597515968620733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44953020464796687958160977 33714765348597515968620733)
      ·
        refine ⟨12643037005724068488232775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33714765348597515968620733 12643037005724068488232775)
        ·
          refine ⟨18964555508586102732349163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12643037005724068488232775 18964555508586102732349163)
          ·
            refine ⟨28446833262879154098523745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18964555508586102732349163 28446833262879154098523745)
            ·
              refine ⟨21335124947159365573892809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28446833262879154098523745 21335124947159365573892809)
              ·
                refine ⟨16001343710369524180419607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21335124947159365573892809 16001343710369524180419607)
                ·
                  refine ⟨24002015565554286270629411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16001343710369524180419607 24002015565554286270629411)
                  ·
                    refine ⟨36003023348331429405944117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24002015565554286270629411 36003023348331429405944117)
                    ·
                      refine ⟨3375283438906071506807261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36003023348331429405944117 3375283438906071506807261)
                      ·
                        rfl

theorem cell23_6573341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_6573341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573341 prefixEnd_6573341 := by exact prefixLift 6573341
  have htrace : WordTrace (prefixWord ++ tailWord_6573341) baseStart_6573341 baseEnd_6573341 := by
    simpa [prefixWord, tailWord_6573341, baseEnd_6573341] using wordTrace_append hprefix tailTrace_6573341
  have hstable : (prefixWord ++ tailWord_6573341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573341).length < 2 ^ (prefixWord ++ tailWord_6573341).sum := by decide
  have hdescent : baseEnd_6573341 < baseStart_6573341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573388 : List Nat := [2, 2, 1, 3, 2, 2, 1, 4, 2, 1, 3]
def baseStart_6573388 : Nat := 118140960795 + 6573388 * 2 ^ 59
def prefixEnd_6573388 : Nat := 4983230072969 + 3 ^ 40 * 6573388 * 2
def baseEnd_6573388 : Nat := 3375307572496832822919545

theorem tailTrace_6573388 : CollatzResearch.WordTrace tailWord_6573388 prefixEnd_6573388 3375307572496832822919545 := by
  unfold tailWord_6573388
  simp only [CollatzResearch.WordTrace]
  refine ⟨119875578354872698068576409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159834104473163597424768545 119875578354872698068576409)
  ·
    refine ⟨89906683766154523551432307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119875578354872698068576409 89906683766154523551432307)
    ·
      refine ⟨134860025649231785327148461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89906683766154523551432307 134860025649231785327148461)
      ·
        refine ⟨50572509618461919497680673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134860025649231785327148461 50572509618461919497680673)
        ·
          refine ⟨37929382213846439623260505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50572509618461919497680673 37929382213846439623260505)
          ·
            refine ⟨28447036660384829717445379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37929382213846439623260505 28447036660384829717445379)
            ·
              refine ⟨42670554990577244576168069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28447036660384829717445379 42670554990577244576168069)
              ·
                refine ⟨8000729060733233358031513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42670554990577244576168069 8000729060733233358031513)
                ·
                  refine ⟨6000546795549925018523635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8000729060733233358031513 6000546795549925018523635)
                  ·
                    refine ⟨9000820193324887527785453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6000546795549925018523635 9000820193324887527785453)
                    ·
                      refine ⟨3375307572496832822919545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9000820193324887527785453 3375307572496832822919545)
                      ·
                        rfl

theorem cell23_6573388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_6573388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573388 prefixEnd_6573388 := by exact prefixLift 6573388
  have htrace : WordTrace (prefixWord ++ tailWord_6573388) baseStart_6573388 baseEnd_6573388 := by
    simpa [prefixWord, tailWord_6573388, baseEnd_6573388] using wordTrace_append hprefix tailTrace_6573388
  have hstable : (prefixWord ++ tailWord_6573388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573388).length < 2 ^ (prefixWord ++ tailWord_6573388).sum := by decide
  have hdescent : baseEnd_6573388 < baseStart_6573388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573424 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 4]
def baseStart_6573424 : Nat := 118140960795 + 6573424 * 2 ^ 59
def prefixEnd_6573424 : Nat := 4983230072969 + 3 ^ 40 * 6573424 * 2
def baseEnd_6573424 : Nat := 3375326057800394682069379

theorem tailTrace_6573424 : CollatzResearch.WordTrace tailWord_6573424 prefixEnd_6573424 3375326057800394682069379 := by
  unfold tailWord_6573424
  simp only [CollatzResearch.WordTrace]
  refine ⟨119876234868807487142731663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159834979825076649523642217 119876234868807487142731663)
  ·
    refine ⟨179814352303211230714097495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119876234868807487142731663 179814352303211230714097495)
    ·
      refine ⟨269721528454816846071146243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179814352303211230714097495 269721528454816846071146243)
      ·
        refine ⟨404582292682225269106719365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269721528454816846071146243 404582292682225269106719365)
        ·
          refine ⟨75859179877917237957509881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 404582292682225269106719365 75859179877917237957509881)
          ·
            refine ⟨56894384908437928468132411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75859179877917237957509881 56894384908437928468132411)
            ·
              refine ⟨85341577362656892702198617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56894384908437928468132411 85341577362656892702198617)
              ·
                refine ⟨64006183021992669526648963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85341577362656892702198617 64006183021992669526648963)
                ·
                  refine ⟨96009274532989004289973445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64006183021992669526648963 96009274532989004289973445)
                  ·
                    refine ⟨18001738974935438304370021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96009274532989004289973445 18001738974935438304370021)
                    ·
                      refine ⟨3375326057800394682069379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18001738974935438304370021 3375326057800394682069379)
                      ·
                        rfl

theorem cell23_6573424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_6573424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573424 prefixEnd_6573424 := by exact prefixLift 6573424
  have htrace : WordTrace (prefixWord ++ tailWord_6573424) baseStart_6573424 baseEnd_6573424 := by
    simpa [prefixWord, tailWord_6573424, baseEnd_6573424] using wordTrace_append hprefix tailTrace_6573424
  have hstable : (prefixWord ++ tailWord_6573424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573424).length < 2 ^ (prefixWord ++ tailWord_6573424).sum := by decide
  have hdescent : baseEnd_6573424 < baseStart_6573424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573445 : List Nat := [1, 3, 1, 1, 3, 1, 5, 2, 2, 2, 2]
def baseStart_6573445 : Nat := 118140960795 + 6573445 * 2 ^ 59
def prefixEnd_6573445 : Nat := 4983230072969 + 3 ^ 40 * 6573445 * 2
def baseEnd_6573445 : Nat := 3375336840894139099906783

theorem tailTrace_6573445 : CollatzResearch.WordTrace tailWord_6573445 prefixEnd_6573445 3375336840894139099906783 := by
  unfold tailWord_6573445
  simp only [CollatzResearch.WordTrace]
  refine ⟨239753235670538894871977789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159835490447025929914651859 239753235670538894871977789)
  ·
    refine ⟨89907463376452085576991671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239753235670538894871977789 89907463376452085576991671)
    ·
      refine ⟨134861195064678128365487507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89907463376452085576991671 134861195064678128365487507)
      ·
        refine ⟨202291792597017192548231261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134861195064678128365487507 202291792597017192548231261)
        ·
          refine ⟨75859422223881447205586723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202291792597017192548231261 75859422223881447205586723)
          ·
            refine ⟨113789133335822170808380085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75859422223881447205586723 113789133335822170808380085)
            ·
              refine ⟨10667731250233328513285633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113789133335822170808380085 10667731250233328513285633)
              ·
                refine ⟨8000798437674996384964225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10667731250233328513285633 8000798437674996384964225)
                ·
                  refine ⟨6000598828256247288723169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8000798437674996384964225 6000598828256247288723169)
                  ·
                    refine ⟨4500449121192185466542377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6000598828256247288723169 4500449121192185466542377)
                    ·
                      refine ⟨3375336840894139099906783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4500449121192185466542377 3375336840894139099906783)
                      ·
                        rfl

theorem cell23_6573445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 2, 2].length) (baseStart_6573445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573445 prefixEnd_6573445 := by exact prefixLift 6573445
  have htrace : WordTrace (prefixWord ++ tailWord_6573445) baseStart_6573445 baseEnd_6573445 := by
    simpa [prefixWord, tailWord_6573445, baseEnd_6573445] using wordTrace_append hprefix tailTrace_6573445
  have hstable : (prefixWord ++ tailWord_6573445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573445).length < 2 ^ (prefixWord ++ tailWord_6573445).sum := by decide
  have hdescent : baseEnd_6573445 < baseStart_6573445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573451 : List Nat := [1, 1, 1, 1, 4, 3, 1, 6, 5]
def baseStart_6573451 : Nat := 118140960795 + 6573451 * 2 ^ 59
def prefixEnd_6573451 : Nat := 4983230072969 + 3 ^ 40 * 6573451 * 2
def baseEnd_6573451 : Nat := 375037769086451786270195

theorem tailTrace_6573451 : CollatzResearch.WordTrace tailWord_6573451 prefixEnd_6573451 375037769086451786270195 := by
  unfold tailWord_6573451
  simp only [CollatzResearch.WordTrace]
  refine ⟨239753454508517157896696207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159835636339011438597797471 239753454508517157896696207)
  ·
    refine ⟨359630181762775736845044311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239753454508517157896696207 359630181762775736845044311)
    ·
      refine ⟨539445272644163605267566467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359630181762775736845044311 539445272644163605267566467)
      ·
        refine ⟨809167908966245407901349701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539445272644163605267566467 809167908966245407901349701)
        ·
          refine ⟨151718982931171013981503069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 809167908966245407901349701 151718982931171013981503069)
          ·
            refine ⟨56894618599189130243063651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151718982931171013981503069 56894618599189130243063651)
            ·
              refine ⟨85341927898783695364595477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56894618599189130243063651 85341927898783695364595477)
              ·
                refine ⟨4000402870255485720215413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85341927898783695364595477 4000402870255485720215413)
                ·
                  refine ⟨375037769086451786270195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4000402870255485720215413 375037769086451786270195)
                  ·
                    rfl

theorem cell23_6573451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 5].length) (baseStart_6573451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573451 prefixEnd_6573451 := by exact prefixLift 6573451
  have htrace : WordTrace (prefixWord ++ tailWord_6573451) baseStart_6573451 baseEnd_6573451 := by
    simpa [prefixWord, tailWord_6573451, baseEnd_6573451] using wordTrace_append hprefix tailTrace_6573451
  have hstable : (prefixWord ++ tailWord_6573451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573451).length < 2 ^ (prefixWord ++ tailWord_6573451).sum := by decide
  have hdescent : baseEnd_6573451 < baseStart_6573451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573461 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_6573461 : Nat := 118140960795 + 6573461 * 2 ^ 59
def prefixEnd_6573461 : Nat := 4983230072969 + 3 ^ 40 * 6573461 * 2
def baseEnd_6573461 : Nat := 3375345056584611037306709

theorem tailTrace_6573461 : CollatzResearch.WordTrace tailWord_6573461 prefixEnd_6573461 3375345056584611037306709 := by
  unfold tailWord_6573461
  simp only [CollatzResearch.WordTrace]
  refine ⟨239753819238480929604560237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159835879492320619736373491 239753819238480929604560237)
  ·
    refine ⟨89907682214430348601710089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239753819238480929604560237 89907682214430348601710089)
    ·
      refine ⟨67430761660822761451282567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89907682214430348601710089 67430761660822761451282567)
      ·
        refine ⟨101146142491234142176923851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67430761660822761451282567 101146142491234142176923851)
        ·
          refine ⟨151719213736851213265385777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101146142491234142176923851 151719213736851213265385777)
          ·
            refine ⟨113789410302638409949039333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151719213736851213265385777 113789410302638409949039333)
            ·
              refine ⟨21335514431744701865444875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113789410302638409949039333 21335514431744701865444875)
              ·
                refine ⟨32003271647617052798167313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21335514431744701865444875 32003271647617052798167313)
                ·
                  refine ⟨24002453735712789598625485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32003271647617052798167313 24002453735712789598625485)
                  ·
                    refine ⟨9000920150892296099484557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24002453735712789598625485 9000920150892296099484557)
                    ·
                      refine ⟨3375345056584611037306709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9000920150892296099484557 3375345056584611037306709)
                      ·
                        rfl

theorem cell23_6573461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_6573461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573461 prefixEnd_6573461 := by exact prefixLift 6573461
  have htrace : WordTrace (prefixWord ++ tailWord_6573461) baseStart_6573461 baseEnd_6573461 := by
    simpa [prefixWord, tailWord_6573461, baseEnd_6573461] using wordTrace_append hprefix tailTrace_6573461
  have hstable : (prefixWord ++ tailWord_6573461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573461).length < 2 ^ (prefixWord ++ tailWord_6573461).sum := by decide
  have hdescent : baseEnd_6573461 < baseStart_6573461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573485 : List Nat := [1, 5, 2, 2, 1, 1, 3, 3, 5]
def baseStart_6573485 : Nat := 118140960795 + 6573485 * 2 ^ 59
def prefixEnd_6573485 : Nat := 4983230072969 + 3 ^ 40 * 6573485 * 2
def baseEnd_6573485 : Nat := 375039708902257660378511

theorem tailTrace_6573485 : CollatzResearch.WordTrace tailWord_6573485 prefixEnd_6573485 375039708902257660378511 := by
  unfold tailWord_6573485
  simp only [CollatzResearch.WordTrace]
  refine ⟨239754694590393981703433909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159836463060262654468955939 239754694590393981703433909)
  ·
    refine ⟨22477002617849435784696929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239754694590393981703433909 22477002617849435784696929)
    ·
      refine ⟨16857751963387076838522697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22477002617849435784696929 16857751963387076838522697)
      ·
        refine ⟨12643313972540307628892023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16857751963387076838522697 12643313972540307628892023)
        ·
          refine ⟨18964970958810461443338035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12643313972540307628892023 18964970958810461443338035)
          ·
            refine ⟨28447456438215692165007053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18964970958810461443338035 28447456438215692165007053)
            ·
              refine ⟨10667796164330884561877645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28447456438215692165007053 10667796164330884561877645)
              ·
                refine ⟨4000423561624081710704117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10667796164330884561877645 4000423561624081710704117)
                ·
                  refine ⟨375039708902257660378511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4000423561624081710704117 375039708902257660378511)
                  ·
                    rfl

theorem cell23_6573485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_6573485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573485 prefixEnd_6573485 := by exact prefixLift 6573485
  have htrace : WordTrace (prefixWord ++ tailWord_6573485) baseStart_6573485 baseEnd_6573485 := by
    simpa [prefixWord, tailWord_6573485, baseEnd_6573485] using wordTrace_append hprefix tailTrace_6573485
  have hstable : (prefixWord ++ tailWord_6573485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573485).length < 2 ^ (prefixWord ++ tailWord_6573485).sum := by decide
  have hdescent : baseEnd_6573485 < baseStart_6573485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573508 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_6573508 : Nat := 118140960795 + 6573508 * 2 ^ 59
def prefixEnd_6573508 : Nat := 4983230072969 + 3 ^ 40 * 6573508 * 2
def baseEnd_6573508 : Nat := 3375369190175372353418993

theorem tailTrace_6573508 : CollatzResearch.WordTrace tailWord_6573508 prefixEnd_6573508 3375369190175372353418993 := by
  unfold tailWord_6573508
  simp only [CollatzResearch.WordTrace]
  refine ⟨119877766734655328315760589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159837022312873771087680785 119877766734655328315760589)
  ·
    refine ⟨44954162525495748118410221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119877766734655328315760589 44954162525495748118410221)
    ·
      refine ⟨16857810947060905544403833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44954162525495748118410221 16857810947060905544403833)
      ·
        refine ⟨12643358210295679158302875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16857810947060905544403833 12643358210295679158302875)
        ·
          refine ⟨18965037315443518737454313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12643358210295679158302875 18965037315443518737454313)
          ·
            refine ⟨14223777986582639053090735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18965037315443518737454313 14223777986582639053090735)
            ·
              refine ⟨21335666979873958579636103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14223777986582639053090735 21335666979873958579636103)
              ·
                refine ⟨32003500469810937869454155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21335666979873958579636103 32003500469810937869454155)
                ·
                  refine ⟨48005250704716406804181233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32003500469810937869454155 48005250704716406804181233)
                  ·
                    refine ⟨36003938028537305103135925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48005250704716406804181233 36003938028537305103135925)
                    ·
                      refine ⟨3375369190175372353418993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36003938028537305103135925 3375369190175372353418993)
                      ·
                        rfl

theorem cell23_6573508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_6573508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573508 prefixEnd_6573508 := by exact prefixLift 6573508
  have htrace : WordTrace (prefixWord ++ tailWord_6573508) baseStart_6573508 baseEnd_6573508 := by
    simpa [prefixWord, tailWord_6573508, baseEnd_6573508] using wordTrace_append hprefix tailTrace_6573508
  have hstable : (prefixWord ++ tailWord_6573508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573508).length < 2 ^ (prefixWord ++ tailWord_6573508).sum := by decide
  have hdescent : baseEnd_6573508 < baseStart_6573508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573518 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2]
def baseStart_6573518 : Nat := 118140960795 + 6573518 * 2 ^ 59
def prefixEnd_6573518 : Nat := 4983230072969 + 3 ^ 40 * 6573518 * 2
def baseEnd_6573518 : Nat := 3375374324981917314293947

theorem tailTrace_6573518 : CollatzResearch.WordTrace tailWord_6573518 prefixEnd_6573518 3375374324981917314293947 := by
  unfold tailWord_6573518
  simp only [CollatzResearch.WordTrace]
  refine ⟨29969487274909303542423151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159837265466182952226256805 29969487274909303542423151)
  ·
    refine ⟨44954230912363955313634727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29969487274909303542423151 44954230912363955313634727)
    ·
      refine ⟨67431346368545932970452091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44954230912363955313634727 67431346368545932970452091)
      ·
        refine ⟨101147019552818899455678137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67431346368545932970452091 101147019552818899455678137)
        ·
          refine ⟨75860264664614174591758603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101147019552818899455678137 75860264664614174591758603)
          ·
            refine ⟨113790396996921261887637905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75860264664614174591758603 113790396996921261887637905)
            ·
              refine ⟨85342797747690946415728429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113790396996921261887637905 85342797747690946415728429)
              ·
                refine ⟨32003549155384104905898161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85342797747690946415728429 32003549155384104905898161)
                ·
                  refine ⟨24002661866538078679423621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32003549155384104905898161 24002661866538078679423621)
                  ·
                    refine ⟨4500499099975889752391929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24002661866538078679423621 4500499099975889752391929)
                    ·
                      refine ⟨3375374324981917314293947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4500499099975889752391929 3375374324981917314293947)
                      ·
                        rfl

theorem cell23_6573518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_6573518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573518 prefixEnd_6573518 := by exact prefixLift 6573518
  have htrace : WordTrace (prefixWord ++ tailWord_6573518) baseStart_6573518 baseEnd_6573518 := by
    simpa [prefixWord, tailWord_6573518, baseEnd_6573518] using wordTrace_append hprefix tailTrace_6573518
  have hstable : (prefixWord ++ tailWord_6573518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573518).length < 2 ^ (prefixWord ++ tailWord_6573518).sum := by decide
  have hdescent : baseEnd_6573518 < baseStart_6573518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573558 : List Nat := [5, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_6573558 : Nat := 118140960795 + 6573558 * 2 ^ 59
def prefixEnd_6573558 : Nat := 4983230072969 + 3 ^ 40 * 6573558 * 2
def baseEnd_6573558 : Nat := 375043873800899684199307

theorem tailTrace_6573558 : CollatzResearch.WordTrace tailWord_6573558 prefixEnd_6573558 375043873800899684199307 := by
  unfold tailWord_6573558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14984834819945594698177583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159838238079419676780560885 14984834819945594698177583)
  ·
    refine ⟨22477252229918392047266375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14984834819945594698177583 22477252229918392047266375)
    ·
      refine ⟨33715878344877588070899563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22477252229918392047266375 33715878344877588070899563)
      ·
        refine ⟨50573817517316382106349345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33715878344877588070899563 50573817517316382106349345)
        ·
          refine ⟨37930363137987286579762009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50573817517316382106349345 37930363137987286579762009)
          ·
            refine ⟨28447772353490464934821507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37930363137987286579762009 28447772353490464934821507)
            ·
              refine ⟨42671658530235697402232261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28447772353490464934821507 42671658530235697402232261)
              ·
                refine ⟨8000935974419193262918549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42671658530235697402232261 8000935974419193262918549)
                ·
                  refine ⟨375043873800899684199307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8000935974419193262918549 375043873800899684199307)
                  ·
                    rfl

theorem cell23_6573558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_6573558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573558 prefixEnd_6573558 := by exact prefixLift 6573558
  have htrace : WordTrace (prefixWord ++ tailWord_6573558) baseStart_6573558 baseEnd_6573558 := by
    simpa [prefixWord, tailWord_6573558, baseEnd_6573558] using wordTrace_append hprefix tailTrace_6573558
  have hstable : (prefixWord ++ tailWord_6573558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573558).length < 2 ^ (prefixWord ++ tailWord_6573558).sum := by decide
  have hdescent : baseEnd_6573558 < baseStart_6573558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573602 : List Nat := [3, 3, 1, 1, 1, 1, 3, 5, 1, 1, 3]
def baseStart_6573602 : Nat := 118140960795 + 6573602 * 2 ^ 59
def prefixEnd_6573602 : Nat := 4983230072969 + 3 ^ 40 * 6573602 * 2
def baseEnd_6573602 : Nat := 3375417457356894985643561

theorem tailTrace_6573602 : CollatzResearch.WordTrace tailWord_6573602 prefixEnd_6573602 3375417457356894985643561 := by
  unfold tailWord_6573602
  simp only [CollatzResearch.WordTrace]
  refine ⟨59939740482742527671360765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159839307953980073790295373 59939740482742527671360765)
  ·
    refine ⟨22477402681028447876760287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59939740482742527671360765 22477402681028447876760287)
    ·
      refine ⟨33716104021542671815140431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22477402681028447876760287 33716104021542671815140431)
      ·
        refine ⟨50574156032314007722710647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33716104021542671815140431 50574156032314007722710647)
        ·
          refine ⟨75861234048471011584065971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50574156032314007722710647 75861234048471011584065971)
          ·
            refine ⟨113791851072706517376098957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75861234048471011584065971 113791851072706517376098957)
            ·
              refine ⟨42671944152264944016037109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113791851072706517376098957 42671944152264944016037109)
              ·
                refine ⟨4000494764274838501503479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42671944152264944016037109 4000494764274838501503479)
                ·
                  refine ⟨6000742146412257752255219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4000494764274838501503479 6000742146412257752255219)
                  ·
                    refine ⟨9001113219618386628382829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6000742146412257752255219 9001113219618386628382829)
                    ·
                      refine ⟨3375417457356894985643561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9001113219618386628382829 3375417457356894985643561)
                      ·
                        rfl

theorem cell23_6573602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_6573602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573602 prefixEnd_6573602 := by exact prefixLift 6573602
  have htrace : WordTrace (prefixWord ++ tailWord_6573602) baseStart_6573602 baseEnd_6573602 := by
    simpa [prefixWord, tailWord_6573602, baseEnd_6573602] using wordTrace_append hprefix tailTrace_6573602
  have hstable : (prefixWord ++ tailWord_6573602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573602).length < 2 ^ (prefixWord ++ tailWord_6573602).sum := by decide
  have hdescent : baseEnd_6573602 < baseStart_6573602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573658 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3]
def baseStart_6573658 : Nat := 118140960795 + 6573658 * 2 ^ 59
def prefixEnd_6573658 : Nat := 4983230072969 + 3 ^ 40 * 6573658 * 2
def baseEnd_6573658 : Nat := 3375446212273546766543303

theorem tailTrace_6573658 : CollatzResearch.WordTrace tailWord_6573658 prefixEnd_6573658 3375446212273546766543303 := by
  unfold tailWord_6573658
  simp only [CollatzResearch.WordTrace]
  refine ⟨59940251104691808062370407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159840669612511488166321085 59940251104691808062370407)
  ·
    refine ⟨89910376657037712093555611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59940251104691808062370407 89910376657037712093555611)
    ·
      refine ⟨134865564985556568140333417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89910376657037712093555611 134865564985556568140333417)
      ·
        refine ⟨101149173739167426105250063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134865564985556568140333417 101149173739167426105250063)
        ·
          refine ⟨151723760608751139157875095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101149173739167426105250063 151723760608751139157875095)
          ·
            refine ⟨227585640913126708736812643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151723760608751139157875095 227585640913126708736812643)
            ·
              refine ⟨341378461369690063105218965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227585640913126708736812643 341378461369690063105218965)
              ·
                refine ⟨16002115376704221708057139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 341378461369690063105218965 16002115376704221708057139)
                ·
                  refine ⟨24003173065056332562085709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16002115376704221708057139 24003173065056332562085709)
                  ·
                    refine ⟨9001189899396124710782141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24003173065056332562085709 9001189899396124710782141)
                    ·
                      refine ⟨3375446212273546766543303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9001189899396124710782141 3375446212273546766543303)
                      ·
                        rfl

theorem cell23_6573658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_6573658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573658 prefixEnd_6573658 := by exact prefixLift 6573658
  have htrace : WordTrace (prefixWord ++ tailWord_6573658) baseStart_6573658 baseEnd_6573658 := by
    simpa [prefixWord, tailWord_6573658, baseEnd_6573658] using wordTrace_append hprefix tailTrace_6573658
  have hstable : (prefixWord ++ tailWord_6573658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573658).length < 2 ^ (prefixWord ++ tailWord_6573658).sum := by decide
  have hdescent : baseEnd_6573658 < baseStart_6573658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573691 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 1, 8]
def baseStart_6573691 : Nat := 118140960795 + 6573691 * 2 ^ 59
def prefixEnd_6573691 : Nat := 4983230072969 + 3 ^ 40 * 6573691 * 2
def baseEnd_6573691 : Nat := 1125154385711715045810217

theorem tailTrace_6573691 : CollatzResearch.WordTrace tailWord_6573691 prefixEnd_6573691 1125154385711715045810217 := by
  unfold tailWord_6573691
  simp only [CollatzResearch.WordTrace]
  refine ⟨239762208027647678885432927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159841472018431785923621951 239762208027647678885432927)
  ·
    refine ⟨359643312041471518328149391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239762208027647678885432927 359643312041471518328149391)
    ·
      refine ⟨539464968062207277492224087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359643312041471518328149391 539464968062207277492224087)
      ·
        refine ⟨809197452093310916238336131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539464968062207277492224087 809197452093310916238336131)
        ·
          refine ⟨1213796178139966374357504197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 809197452093310916238336131 1213796178139966374357504197)
          ·
            refine ⟨227586783401243695192032037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1213796178139966374357504197 227586783401243695192032037)
            ·
              refine ⟨42672521887733192848506007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227586783401243695192032037 42672521887733192848506007)
              ·
                refine ⟨64008782831599789272759011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42672521887733192848506007 64008782831599789272759011)
                ·
                  refine ⟨96013174247399683909138517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64008782831599789272759011 96013174247399683909138517)
                  ·
                    refine ⟨1125154385711715045810217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96013174247399683909138517 1125154385711715045810217)
                    ·
                      rfl

theorem cell23_6573691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 8].length) (baseStart_6573691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573691 prefixEnd_6573691 := by exact prefixLift 6573691
  have htrace : WordTrace (prefixWord ++ tailWord_6573691) baseStart_6573691 baseEnd_6573691 := by
    simpa [prefixWord, tailWord_6573691, baseEnd_6573691] using wordTrace_append hprefix tailTrace_6573691
  have hstable : (prefixWord ++ tailWord_6573691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573691).length < 2 ^ (prefixWord ++ tailWord_6573691).sum := by decide
  have hdescent : baseEnd_6573691 < baseStart_6573691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573719 : List Nat := [1, 1, 3, 3, 2, 3, 3, 1, 1, 3, 2]
def baseStart_6573719 : Nat := 118140960795 + 6573719 * 2 ^ 59
def prefixEnd_6573719 : Nat := 4983230072969 + 3 ^ 40 * 6573719 * 2
def baseEnd_6573719 : Nat := 3375477534593471027880523

theorem tailTrace_6573719 : CollatzResearch.WordTrace tailWord_6573719 prefixEnd_6573719 3375477534593471027880523 := by
  unfold tailWord_6573719
  simp only [CollatzResearch.WordTrace]
  refine ⟨239763229271546239667452211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159842152847697493111634807 239763229271546239667452211)
  ·
    refine ⟨359644843907319359501178317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239763229271546239667452211 359644843907319359501178317)
    ·
      refine ⟨134866816465244759812941869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359644843907319359501178317 134866816465244759812941869)
      ·
        refine ⟨50575056174466784929853201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134866816465244759812941869 50575056174466784929853201)
        ·
          refine ⟨37931292130850088697389901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50575056174466784929853201 37931292130850088697389901)
          ·
            refine ⟨14224234549068783261521213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37931292130850088697389901 14224234549068783261521213)
            ·
              refine ⟨5334087955900793723070455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14224234549068783261521213 5334087955900793723070455)
              ·
                refine ⟨8001131933851190584605683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5334087955900793723070455 8001131933851190584605683)
                ·
                  refine ⟨12001697900776785876908525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8001131933851190584605683 12001697900776785876908525)
                  ·
                    refine ⟨4500636712791294703840697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12001697900776785876908525 4500636712791294703840697)
                    ·
                      refine ⟨3375477534593471027880523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4500636712791294703840697 3375477534593471027880523)
                      ·
                        rfl

theorem cell23_6573719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_6573719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573719 prefixEnd_6573719 := by exact prefixLift 6573719
  have htrace : WordTrace (prefixWord ++ tailWord_6573719) baseStart_6573719 baseEnd_6573719 := by
    simpa [prefixWord, tailWord_6573719, baseEnd_6573719] using wordTrace_append hprefix tailTrace_6573719
  have hstable : (prefixWord ++ tailWord_6573719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573719).length < 2 ^ (prefixWord ++ tailWord_6573719).sum := by decide
  have hdescent : baseEnd_6573719 < baseStart_6573719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573721 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 11]
def baseStart_6573721 : Nat := 118140960795 + 6573721 * 2 ^ 59
def prefixEnd_6573721 : Nat := 4983230072969 + 3 ^ 40 * 6573721 * 2
def baseEnd_6573721 : Nat := 375053173506086668895057

theorem tailTrace_6573721 : CollatzResearch.WordTrace tailWord_6573721 prefixEnd_6573721 375053173506086668895057 := by
  unfold tailWord_6573721
  simp only [CollatzResearch.WordTrace]
  refine ⟨239763302217538994009025017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159842201478359329339350011 239763302217538994009025017)
  ·
    refine ⟨179822476663154245506768763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239763302217538994009025017 179822476663154245506768763)
    ·
      refine ⟨269733714994731368260153145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179822476663154245506768763 269733714994731368260153145)
      ·
        refine ⟨202300286246048526195114859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269733714994731368260153145 202300286246048526195114859)
        ·
          refine ⟨303450429369072789292672289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202300286246048526195114859 303450429369072789292672289)
          ·
            refine ⟨227587822026804591969504217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303450429369072789292672289 227587822026804591969504217)
            ·
              refine ⟨170690866520103443977128163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227587822026804591969504217 170690866520103443977128163)
              ·
                refine ⟨256036299780155165965692245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170690866520103443977128163 256036299780155165965692245)
                ·
                  refine ⟨375053173506086668895057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 256036299780155165965692245 375053173506086668895057)
                  ·
                    rfl

theorem cell23_6573721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 11].length) (baseStart_6573721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573721 prefixEnd_6573721 := by exact prefixLift 6573721
  have htrace : WordTrace (prefixWord ++ tailWord_6573721) baseStart_6573721 baseEnd_6573721 := by
    simpa [prefixWord, tailWord_6573721, baseEnd_6573721] using wordTrace_append hprefix tailTrace_6573721
  have hstable : (prefixWord ++ tailWord_6573721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573721).length < 2 ^ (prefixWord ++ tailWord_6573721).sum := by decide
  have hdescent : baseEnd_6573721 < baseStart_6573721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573742 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_6573742 : Nat := 118140960795 + 6573742 * 2 ^ 59
def prefixEnd_6573742 : Nat := 4983230072969 + 3 ^ 40 * 6573742 * 2
def baseEnd_6573742 : Nat := 1125163114882841479297639

theorem tailTrace_6573742 : CollatzResearch.WordTrace tailWord_6573742 prefixEnd_6573742 1125163114882841479297639 := by
  unfold tailWord_6573742
  simp only [CollatzResearch.WordTrace]
  refine ⟨29970508518807864324442435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159842712100308609730359653 29970508518807864324442435)
  ·
    refine ⟨44955762778211796486663653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29970508518807864324442435 44955762778211796486663653)
    ·
      refine ⟨8429205520914711841249435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44955762778211796486663653 8429205520914711841249435)
      ·
        refine ⟨12643808281372067761874153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8429205520914711841249435 12643808281372067761874153)
        ·
          refine ⟨9482856211029050821405615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12643808281372067761874153 9482856211029050821405615)
          ·
            refine ⟨14224284316543576232108423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9482856211029050821405615 14224284316543576232108423)
            ·
              refine ⟨21336426474815364348162635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14224284316543576232108423 21336426474815364348162635)
              ·
                refine ⟨32004639712223046522243953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21336426474815364348162635 32004639712223046522243953)
                ·
                  refine ⟨24003479784167284891682965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32004639712223046522243953 24003479784167284891682965)
                  ·
                    refine ⟨1125163114882841479297639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24003479784167284891682965 1125163114882841479297639)
                    ·
                      rfl

theorem cell23_6573742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_6573742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573742 prefixEnd_6573742 := by exact prefixLift 6573742
  have htrace : WordTrace (prefixWord ++ tailWord_6573742) baseStart_6573742 baseEnd_6573742 := by
    simpa [prefixWord, tailWord_6573742, baseEnd_6573742] using wordTrace_append hprefix tailTrace_6573742
  have hstable : (prefixWord ++ tailWord_6573742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573742).length < 2 ^ (prefixWord ++ tailWord_6573742).sum := by decide
  have hdescent : baseEnd_6573742 < baseStart_6573742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573749 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_6573749 : Nat := 118140960795 + 6573749 * 2 ^ 59
def prefixEnd_6573749 : Nat := 4983230072969 + 3 ^ 40 * 6573749 * 2
def baseEnd_6573749 : Nat := 3375492939013105910505385

theorem tailTrace_6573749 : CollatzResearch.WordTrace tailWord_6573749 prefixEnd_6573749 3375492939013105910505385 := by
  unfold tailWord_6573749
  simp only [CollatzResearch.WordTrace]
  refine ⟨239764323461437554791044301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159842882307625036527362867 239764323461437554791044301)
  ·
    refine ⟨89911621298039083046641613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239764323461437554791044301 89911621298039083046641613)
    ·
      refine ⟨33716857986764656142490605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89911621298039083046641613 33716857986764656142490605)
      ·
        refine ⟨12643821745036746053433977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33716857986764656142490605 12643821745036746053433977)
        ·
          refine ⟨9482866308777559540075483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12643821745036746053433977 9482866308777559540075483)
          ·
            refine ⟨14224299463166339310113225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9482866308777559540075483 14224299463166339310113225)
            ·
              refine ⟨10668224597374754482584919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14224299463166339310113225 10668224597374754482584919)
              ·
                refine ⟨16002336896062131723877379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10668224597374754482584919 16002336896062131723877379)
                ·
                  refine ⟨24003505344093197585816069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16002336896062131723877379 24003505344093197585816069)
                  ·
                    refine ⟨4500657252017474547340513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24003505344093197585816069 4500657252017474547340513)
                    ·
                      refine ⟨3375492939013105910505385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4500657252017474547340513 3375492939013105910505385)
                      ·
                        rfl

theorem cell23_6573749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_6573749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573749 prefixEnd_6573749 := by exact prefixLift 6573749
  have htrace : WordTrace (prefixWord ++ tailWord_6573749) baseStart_6573749 baseEnd_6573749 := by
    simpa [prefixWord, tailWord_6573749, baseEnd_6573749] using wordTrace_append hprefix tailTrace_6573749
  have hstable : (prefixWord ++ tailWord_6573749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573749).length < 2 ^ (prefixWord ++ tailWord_6573749).sum := by decide
  have hdescent : baseEnd_6573749 < baseStart_6573749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573766 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_6573766 : Nat := 118140960795 + 6573766 * 2 ^ 59
def prefixEnd_6573766 : Nat := 4983230072969 + 3 ^ 40 * 6573766 * 2
def baseEnd_6573766 : Nat := 3375501668184232343992807

theorem tailTrace_6573766 : CollatzResearch.WordTrace tailWord_6573766 prefixEnd_6573766 3375501668184232343992807 := by
  unfold tailWord_6573766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7492654484449248959200411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 159843295668250644462942101 7492654484449248959200411)
  ·
    refine ⟨11238981726673873438800617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7492654484449248959200411 11238981726673873438800617)
    ·
      refine ⟨8429236295005405079100463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11238981726673873438800617 8429236295005405079100463)
      ·
        refine ⟨12643854442508107618650695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8429236295005405079100463 12643854442508107618650695)
        ·
          refine ⟨18965781663762161427976043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12643854442508107618650695 18965781663762161427976043)
          ·
            refine ⟨28448672495643242141964065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18965781663762161427976043 28448672495643242141964065)
            ·
              refine ⟨21336504371732431606473049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28448672495643242141964065 21336504371732431606473049)
              ·
                refine ⟨16002378278799323704854787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21336504371732431606473049 16002378278799323704854787)
                ·
                  refine ⟨24003567418198985557282181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16002378278799323704854787 24003567418198985557282181)
                  ·
                    refine ⟨4500668890912309791990409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24003567418198985557282181 4500668890912309791990409)
                    ·
                      refine ⟨3375501668184232343992807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4500668890912309791990409 3375501668184232343992807)
                      ·
                        rfl

theorem cell23_6573766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_6573766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573766 prefixEnd_6573766 := by exact prefixLift 6573766
  have htrace : WordTrace (prefixWord ++ tailWord_6573766) baseStart_6573766 baseEnd_6573766 := by
    simpa [prefixWord, tailWord_6573766, baseEnd_6573766] using wordTrace_append hprefix tailTrace_6573766
  have hstable : (prefixWord ++ tailWord_6573766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573766).length < 2 ^ (prefixWord ++ tailWord_6573766).sum := by decide
  have hdescent : baseEnd_6573766 < baseStart_6573766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573768 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 1, 7]
def baseStart_6573768 : Nat := 118140960795 + 6573768 * 2 ^ 59
def prefixEnd_6573768 : Nat := 4983230072969 + 3 ^ 40 * 6573768 * 2
def baseEnd_6573768 : Nat := 1125167565048513778722599

theorem tailTrace_6573768 : CollatzResearch.WordTrace tailWord_6573768 prefixEnd_6573768 1125167565048513778722599 := by
  unfold tailWord_6573768
  simp only [CollatzResearch.WordTrace]
  refine ⟨119882508224184360517992979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159843344298912480690657305 119882508224184360517992979)
  ·
    refine ⟨179823762336276540776989469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119882508224184360517992979 179823762336276540776989469)
    ·
      refine ⟨67433910876103702791371051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179823762336276540776989469 67433910876103702791371051)
      ·
        refine ⟨101150866314155554187056577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67433910876103702791371051 101150866314155554187056577)
        ·
          refine ⟨75863149735616665640292433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101150866314155554187056577 75863149735616665640292433)
          ·
            refine ⟨56897362301712499230219325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75863149735616665640292433 56897362301712499230219325)
            ·
              refine ⟨21336510863142187211332247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56897362301712499230219325 21336510863142187211332247)
              ·
                refine ⟨32004766294713280816998371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21336510863142187211332247 32004766294713280816998371)
                ·
                  refine ⟨48007149442069921225497557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32004766294713280816998371 48007149442069921225497557)
                  ·
                    refine ⟨1125167565048513778722599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48007149442069921225497557 1125167565048513778722599)
                    ·
                      rfl

theorem cell23_6573768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_6573768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573768 prefixEnd_6573768 := by exact prefixLift 6573768
  have htrace : WordTrace (prefixWord ++ tailWord_6573768) baseStart_6573768 baseEnd_6573768 := by
    simpa [prefixWord, tailWord_6573768, baseEnd_6573768] using wordTrace_append hprefix tailTrace_6573768
  have hstable : (prefixWord ++ tailWord_6573768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573768).length < 2 ^ (prefixWord ++ tailWord_6573768).sum := by decide
  have hdescent : baseEnd_6573768 < baseStart_6573768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6573805 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_6573805 : Nat := 118140960795 + 6573805 * 2 ^ 59
def prefixEnd_6573805 : Nat := 4983230072969 + 3 ^ 40 * 6573805 * 2
def baseEnd_6573805 : Nat := 3375521693929757691405127

theorem tailTrace_6573805 : CollatzResearch.WordTrace tailWord_6573805 prefixEnd_6573805 3375521693929757691405127 := by
  unfold tailWord_6573805
  simp only [CollatzResearch.WordTrace]
  refine ⟨239766365949234676355082869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159844243966156450903388579 239766365949234676355082869)
  ·
    refine ⟨22478096807740750908289019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239766365949234676355082869 22478096807740750908289019)
    ·
      refine ⟨33717145211611126362433529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22478096807740750908289019 33717145211611126362433529)
      ·
        refine ⟨25287858908708344771825147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33717145211611126362433529 25287858908708344771825147)
        ·
          refine ⟨37931788363062517157737721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25287858908708344771825147 37931788363062517157737721)
          ·
            refine ⟨28448841272296887868303291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37931788363062517157737721 28448841272296887868303291)
            ·
              refine ⟨42673261908445331802454937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28448841272296887868303291 42673261908445331802454937)
              ·
                refine ⟨32004946431333998851841203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42673261908445331802454937 32004946431333998851841203)
                ·
                  refine ⟨48007419647000998277761805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32004946431333998851841203 48007419647000998277761805)
                  ·
                    refine ⟨18002782367625374354160677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48007419647000998277761805 18002782367625374354160677)
                    ·
                      refine ⟨3375521693929757691405127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18002782367625374354160677 3375521693929757691405127)
                      ·
                        rfl

theorem cell23_6573805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_6573805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6573805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6573805 prefixEnd_6573805 := by exact prefixLift 6573805
  have htrace : WordTrace (prefixWord ++ tailWord_6573805) baseStart_6573805 baseEnd_6573805 := by
    simpa [prefixWord, tailWord_6573805, baseEnd_6573805] using wordTrace_append hprefix tailTrace_6573805
  have hstable : (prefixWord ++ tailWord_6573805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6573805).length < 2 ^ (prefixWord ++ tailWord_6573805).sum := by decide
  have hdescent : baseEnd_6573805 < baseStart_6573805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6573805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
