import V185TrunkScan22Chunk000

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_8647 : List Nat := [1, 1, 4, 1, 1, 4, 4, 2, 1, 3]
def baseStart_8647 : Nat := 118140960795 + 8647 * 2 ^ 59
def prefixEnd_8647 : Nat := 4983230072969 + 3 ^ 40 * 8647 * 2
def baseEnd_8647 : Nat := 2960044813021934848493

theorem tailTrace_8647 : CollatzResearch.WordTrace tailWord_8647 prefixEnd_8647 2960044813021934848493 := by
  unfold tailWord_8647
  simp only [CollatzResearch.WordTrace]
  refine ⟨315381999680870635136195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 210254666453913756757463 315381999680870635136195)
  ·
    refine ⟨473072999521305952704293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 315381999680870635136195 473072999521305952704293)
    ·
      refine ⟨88701187410244866132055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 473072999521305952704293 88701187410244866132055)
      ·
        refine ⟨133051781115367299198083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88701187410244866132055 133051781115367299198083)
        ·
          refine ⟨199577671673050948797125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133051781115367299198083 199577671673050948797125)
          ·
            refine ⟨37420813438697052899461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199577671673050948797125 37420813438697052899461)
            ·
              refine ⟨7016402519755697418649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37420813438697052899461 7016402519755697418649)
              ·
                refine ⟨5262301889816773063987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7016402519755697418649 5262301889816773063987)
                ·
                  refine ⟨7893452834725159595981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5262301889816773063987 7893452834725159595981)
                  ·
                    refine ⟨2960044813021934848493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7893452834725159595981 2960044813021934848493)
                    ·
                      rfl

theorem cell22_8647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_8647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8647 prefixEnd_8647 := by exact prefixLift 8647
  have htrace : WordTrace (prefixWord ++ tailWord_8647) baseStart_8647 baseEnd_8647 := by
    simpa [prefixWord, tailWord_8647, baseEnd_8647] using wordTrace_append hprefix tailTrace_8647
  have hstable : (prefixWord ++ tailWord_8647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8647).length < 2 ^ (prefixWord ++ tailWord_8647).sum := by decide
  have hdescent : baseEnd_8647 < baseStart_8647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8671 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 8]
def baseStart_8671 : Nat := 118140960795 + 8671 * 2 ^ 59
def prefixEnd_8671 : Nat := 4983230072969 + 3 ^ 40 * 8671 * 2
def baseEnd_8671 : Nat := 989420167831290749473

theorem tailTrace_8671 : CollatzResearch.WordTrace tailWord_8671 prefixEnd_8671 989420167831290749473 := by
  unfold tailWord_8671
  simp only [CollatzResearch.WordTrace]
  refine ⟨316257351593922734009867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 210838234395948489339911 316257351593922734009867)
  ·
    refine ⟨474386027390884101014801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 316257351593922734009867 474386027390884101014801)
    ·
      refine ⟨355789520543163075761101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 474386027390884101014801 355789520543163075761101)
      ·
        refine ⟨133421070203686153410413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 355789520543163075761101 133421070203686153410413)
        ·
          refine ⟨50032901326382307528905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133421070203686153410413 50032901326382307528905)
          ·
            refine ⟨37524675994786730646679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50032901326382307528905 37524675994786730646679)
            ·
              refine ⟨56287013992180095970019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37524675994786730646679 56287013992180095970019)
              ·
                refine ⟨84430520988270143955029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56287013992180095970019 84430520988270143955029)
                ·
                  refine ⟨989420167831290749473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 84430520988270143955029 989420167831290749473)
                  ·
                    rfl

theorem cell22_8671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 8].length) (baseStart_8671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8671 prefixEnd_8671 := by exact prefixLift 8671
  have htrace : WordTrace (prefixWord ++ tailWord_8671) baseStart_8671 baseEnd_8671 := by
    simpa [prefixWord, tailWord_8671, baseEnd_8671] using wordTrace_append hprefix tailTrace_8671
  have hstable : (prefixWord ++ tailWord_8671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8671).length < 2 ^ (prefixWord ++ tailWord_8671).sum := by decide
  have hdescent : baseEnd_8671 < baseStart_8671 := by decide
  rcases family_descends (prefixWord ++ tailWord_8671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8673 : List Nat := [1, 2, 3, 1, 2, 2, 2, 4, 1, 4]
def baseStart_8673 : Nat := 118140960795 + 8673 * 2 ^ 59
def prefixEnd_8673 : Nat := 4983230072969 + 3 ^ 40 * 8673 * 2
def baseEnd_8673 : Nat := 2968945144366533698413

theorem tailTrace_8673 : CollatzResearch.WordTrace tailWord_8673 prefixEnd_8673 2968945144366533698413 := by
  unfold tailWord_8673
  simp only [CollatzResearch.WordTrace]
  refine ⟨316330297586677075582673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 210886865057784717055115 316330297586677075582673)
  ·
    refine ⟨237247723190007806687005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 316330297586677075582673 237247723190007806687005)
    ·
      refine ⟨88967896196252927507627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237247723190007806687005 88967896196252927507627)
      ·
        refine ⟨133451844294379391261441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88967896196252927507627 133451844294379391261441)
        ·
          refine ⟨100088883220784543446081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133451844294379391261441 100088883220784543446081)
          ·
            refine ⟨75066662415588407584561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100088883220784543446081 75066662415588407584561)
            ·
              refine ⟨56299996811691305688421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75066662415588407584561 56299996811691305688421)
              ·
                refine ⟨10556249402192119816579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56299996811691305688421 10556249402192119816579)
                ·
                  refine ⟨15834374103288179724869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10556249402192119816579 15834374103288179724869)
                  ·
                    refine ⟨2968945144366533698413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15834374103288179724869 2968945144366533698413)
                    ·
                      rfl

theorem cell22_8673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_8673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8673 prefixEnd_8673 := by exact prefixLift 8673
  have htrace : WordTrace (prefixWord ++ tailWord_8673) baseStart_8673 baseEnd_8673 := by
    simpa [prefixWord, tailWord_8673, baseEnd_8673] using wordTrace_append hprefix tailTrace_8673
  have hstable : (prefixWord ++ tailWord_8673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8673).length < 2 ^ (prefixWord ++ tailWord_8673).sum := by decide
  have hdescent : baseEnd_8673 < baseStart_8673 := by decide
  rcases family_descends (prefixWord ++ tailWord_8673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8703 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 4, 3]
def baseStart_8703 : Nat := 118140960795 + 8703 * 2 ^ 59
def prefixEnd_8703 : Nat := 4983230072969 + 3 ^ 40 * 8703 * 2
def baseEnd_8703 : Nat := 2979214757456455448321

theorem tailTrace_8703 : CollatzResearch.WordTrace tailWord_8703 prefixEnd_8703 2979214757456455448321 := by
  unfold tailWord_8703
  simp only [CollatzResearch.WordTrace]
  refine ⟨317424487477992199174763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 211616324985328132783175 317424487477992199174763)
  ·
    refine ⟨476136731216988298762145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 317424487477992199174763 476136731216988298762145)
    ·
      refine ⟨357102548412741224071609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 476136731216988298762145 357102548412741224071609)
      ·
        refine ⟨267826911309555918053707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357102548412741224071609 267826911309555918053707)
        ·
          refine ⟨401740366964333877080561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267826911309555918053707 401740366964333877080561)
          ·
            refine ⟨301305275223250407810421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 401740366964333877080561 301305275223250407810421)
            ·
              refine ⟨28247369552179725732227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 301305275223250407810421 28247369552179725732227)
              ·
                refine ⟨42371054328269588598341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28247369552179725732227 42371054328269588598341)
                ·
                  refine ⟨7944572686550547862189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42371054328269588598341 7944572686550547862189)
                  ·
                    refine ⟨2979214757456455448321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7944572686550547862189 2979214757456455448321)
                    ·
                      rfl

theorem cell22_8703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 3].length) (baseStart_8703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8703 prefixEnd_8703 := by exact prefixLift 8703
  have htrace : WordTrace (prefixWord ++ tailWord_8703) baseStart_8703 baseEnd_8703 := by
    simpa [prefixWord, tailWord_8703, baseEnd_8703] using wordTrace_append hprefix tailTrace_8703
  have hstable : (prefixWord ++ tailWord_8703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8703).length < 2 ^ (prefixWord ++ tailWord_8703).sum := by decide
  have hdescent : baseEnd_8703 < baseStart_8703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8705 : List Nat := [1, 2, 4, 1, 3, 1, 2, 4, 4]
def baseStart_8705 : Nat := 118140960795 + 8705 * 2 ^ 59
def prefixEnd_8705 : Nat := 4983230072969 + 3 ^ 40 * 8705 * 2
def baseEnd_8705 : Nat := 993299799443038966105

theorem tailTrace_8705 : CollatzResearch.WordTrace tailWord_8705 prefixEnd_8705 993299799443038966105 := by
  unfold tailWord_8705
  simp only [CollatzResearch.WordTrace]
  refine ⟨317497433470746540747569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 211664955647164360498379 317497433470746540747569)
  ·
    refine ⟨238123075103059905560677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 317497433470746540747569 238123075103059905560677)
    ·
      refine ⟨44648076581823732292627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 238123075103059905560677 44648076581823732292627)
      ·
        refine ⟨66972114872735598438941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44648076581823732292627 66972114872735598438941)
        ·
          refine ⟨25114543077275849414603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66972114872735598438941 25114543077275849414603)
          ·
            refine ⟨37671814615913774121905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25114543077275849414603 37671814615913774121905)
            ·
              refine ⟨28253860961935330591429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37671814615913774121905 28253860961935330591429)
              ·
                refine ⟨5297598930362874485893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28253860961935330591429 5297598930362874485893)
                ·
                  refine ⟨993299799443038966105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5297598930362874485893 993299799443038966105)
                  ·
                    rfl

theorem cell22_8705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 4].length) (baseStart_8705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8705 prefixEnd_8705 := by exact prefixLift 8705
  have htrace : WordTrace (prefixWord ++ tailWord_8705) baseStart_8705 baseEnd_8705 := by
    simpa [prefixWord, tailWord_8705, baseEnd_8705] using wordTrace_append hprefix tailTrace_8705
  have hstable : (prefixWord ++ tailWord_8705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8705).length < 2 ^ (prefixWord ++ tailWord_8705).sum := by decide
  have hdescent : baseEnd_8705 < baseStart_8705 := by decide
  rcases family_descends (prefixWord ++ tailWord_8705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8718 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_8718 : Nat := 118140960795 + 8718 * 2 ^ 59
def prefixEnd_8718 : Nat := 4983230072969 + 3 ^ 40 * 8718 * 2
def baseEnd_8718 : Nat := 2984349564001416323275

theorem tailTrace_8718 : CollatzResearch.WordTrace tailWord_8718 prefixEnd_8718 2984349564001416323275 := by
  unfold tailWord_8718
  simp only [CollatzResearch.WordTrace]
  refine ⟨39746447802956220121351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 211981054949099840647205 39746447802956220121351)
  ·
    refine ⟨59619671704434330182027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39746447802956220121351 59619671704434330182027)
    ·
      refine ⟨89429507556651495273041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59619671704434330182027 89429507556651495273041)
      ·
        refine ⟨67072130667488621454781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89429507556651495273041 67072130667488621454781)
        ·
          refine ⟨25152049000308233045543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67072130667488621454781 25152049000308233045543)
          ·
            refine ⟨37728073500462349568315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25152049000308233045543 37728073500462349568315)
            ·
              refine ⟨56592110250693524352473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37728073500462349568315 56592110250693524352473)
              ·
                refine ⟨42444082688020143264355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56592110250693524352473 42444082688020143264355)
                ·
                  refine ⟨63666124032030214896533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42444082688020143264355 63666124032030214896533)
                  ·
                    refine ⟨2984349564001416323275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63666124032030214896533 2984349564001416323275)
                    ·
                      rfl

theorem cell22_8718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_8718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8718 prefixEnd_8718 := by exact prefixLift 8718
  have htrace : WordTrace (prefixWord ++ tailWord_8718) baseStart_8718 baseEnd_8718 := by
    simpa [prefixWord, tailWord_8718, baseEnd_8718] using wordTrace_append hprefix tailTrace_8718
  have hstable : (prefixWord ++ tailWord_8718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8718).length < 2 ^ (prefixWord ++ tailWord_8718).sum := by decide
  have hdescent : baseEnd_8718 < baseStart_8718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8733 : List Nat := [1, 4, 2, 2, 1, 3, 1, 8]
def baseStart_8733 : Nat := 118140960795 + 8733 * 2 ^ 59
def prefixEnd_8733 : Nat := 4983230072969 + 3 ^ 40 * 8733 * 2
def baseEnd_8733 : Nat := 332164930060708577581

theorem tailTrace_8733 : CollatzResearch.WordTrace tailWord_8733 prefixEnd_8733 332164930060708577581 := by
  unfold tailWord_8733
  simp only [CollatzResearch.WordTrace]
  refine ⟨318518677369307322766853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 212345784912871548511235 318518677369307322766853)
  ·
    refine ⟨59722252006745123018785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 318518677369307322766853 59722252006745123018785)
    ·
      refine ⟨44791689005058842264089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59722252006745123018785 44791689005058842264089)
      ·
        refine ⟨33593766753794131698067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44791689005058842264089 33593766753794131698067)
        ·
          refine ⟨50390650130691197547101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33593766753794131698067 50390650130691197547101)
          ·
            refine ⟨18896493799009199080163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50390650130691197547101 18896493799009199080163)
            ·
              refine ⟨28344740698513798620245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18896493799009199080163 28344740698513798620245)
              ·
                refine ⟨332164930060708577581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 28344740698513798620245 332164930060708577581)
                ·
                  rfl

theorem cell22_8733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 8].length) (baseStart_8733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8733 prefixEnd_8733 := by exact prefixLift 8733
  have htrace : WordTrace (prefixWord ++ tailWord_8733) baseStart_8733 baseEnd_8733 := by
    simpa [prefixWord, tailWord_8733, baseEnd_8733] using wordTrace_append hprefix tailTrace_8733
  have hstable : (prefixWord ++ tailWord_8733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8733).length < 2 ^ (prefixWord ++ tailWord_8733).sum := by decide
  have hdescent : baseEnd_8733 < baseStart_8733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8748 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 5, 3]
def baseStart_8748 : Nat := 118140960795 + 8748 * 2 ^ 59
def prefixEnd_8748 : Nat := 4983230072969 + 3 ^ 40 * 8748 * 2
def baseEnd_8748 : Nat := 2994619177091338073183

theorem tailTrace_8748 : CollatzResearch.WordTrace tailWord_8748 prefixEnd_8748 2994619177091338073183 := by
  unfold tailWord_8748
  simp only [CollatzResearch.WordTrace]
  refine ⟨159532886157482442281449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 212710514876643256375265 159532886157482442281449)
  ·
    refine ⟨119649664618111831711087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159532886157482442281449 119649664618111831711087)
    ·
      refine ⟨179474496927167747566631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119649664618111831711087 179474496927167747566631)
      ·
        refine ⟨269211745390751621349947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179474496927167747566631 269211745390751621349947)
        ·
          refine ⟨403817618086127432024921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269211745390751621349947 403817618086127432024921)
          ·
            refine ⟨302863213564595574018691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403817618086127432024921 302863213564595574018691)
            ·
              refine ⟨454294820346893361028037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302863213564595574018691 454294820346893361028037)
              ·
                refine ⟨85180278815042505192757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 454294820346893361028037 85180278815042505192757)
                ·
                  refine ⟨7985651138910234861821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85180278815042505192757 7985651138910234861821)
                  ·
                    refine ⟨2994619177091338073183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7985651138910234861821 2994619177091338073183)
                    ·
                      rfl

theorem cell22_8748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_8748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8748 prefixEnd_8748 := by exact prefixLift 8748
  have htrace : WordTrace (prefixWord ++ tailWord_8748) baseStart_8748 baseEnd_8748 := by
    simpa [prefixWord, tailWord_8748, baseEnd_8748] using wordTrace_append hprefix tailTrace_8748
  have hstable : (prefixWord ++ tailWord_8748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8748).length < 2 ^ (prefixWord ++ tailWord_8748).sum := by decide
  have hdescent : baseEnd_8748 < baseStart_8748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8750 : List Nat := [4, 1, 3, 1, 3, 2, 8]
def baseStart_8750 : Nat := 118140960795 + 8750 * 2 ^ 59
def prefixEnd_8750 : Nat := 4983230072969 + 3 ^ 40 * 8750 * 2
def baseEnd_8750 : Nat := 110937178443111093451

theorem tailTrace_8750 : CollatzResearch.WordTrace tailWord_8750 prefixEnd_8750 110937178443111093451 := by
  unfold tailWord_8750
  simp only [CollatzResearch.WordTrace]
  refine ⟨39892339788464903266963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 212759145538479484090469 39892339788464903266963)
  ·
    refine ⟨59838509682697354900445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39892339788464903266963 59838509682697354900445)
    ·
      refine ⟨22439441131011508087667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59838509682697354900445 22439441131011508087667)
      ·
        refine ⟨33659161696517262131501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22439441131011508087667 33659161696517262131501)
        ·
          refine ⟨12622185636193973299313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33659161696517262131501 12622185636193973299313)
          ·
            refine ⟨9466639227145479974485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12622185636193973299313 9466639227145479974485)
            ·
              refine ⟨110937178443111093451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 9466639227145479974485 110937178443111093451)
              ·
                rfl

theorem cell22_8750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 8].length) (baseStart_8750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8750 prefixEnd_8750 := by exact prefixLift 8750
  have htrace : WordTrace (prefixWord ++ tailWord_8750) baseStart_8750 baseEnd_8750 := by
    simpa [prefixWord, tailWord_8750, baseEnd_8750] using wordTrace_append hprefix tailTrace_8750
  have hstable : (prefixWord ++ tailWord_8750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8750).length < 2 ^ (prefixWord ++ tailWord_8750).sum := by decide
  have hdescent : baseEnd_8750 < baseStart_8750 := by decide
  rcases family_descends (prefixWord ++ tailWord_8750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8756 : List Nat := [2, 5, 1, 3, 1, 1, 3, 2, 4]
def baseStart_8756 : Nat := 118140960795 + 8756 * 2 ^ 59
def prefixEnd_8756 : Nat := 4983230072969 + 3 ^ 40 * 8756 * 2
def baseEnd_8756 : Nat := 999119246860661291053

theorem tailTrace_8756 : CollatzResearch.WordTrace tailWord_8756 prefixEnd_8756 999119246860661291053 := by
  unfold tailWord_8756
  simp only [CollatzResearch.WordTrace]
  refine ⟨159678778142991125427061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 212905037523988167236081 159678778142991125427061)
  ·
    refine ⟨14969885450905418008787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159678778142991125427061 14969885450905418008787)
    ·
      refine ⟨22454828176358127013181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14969885450905418008787 22454828176358127013181)
      ·
        refine ⟨8420560566134297629943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22454828176358127013181 8420560566134297629943)
        ·
          refine ⟨12630840849201446444915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8420560566134297629943 12630840849201446444915)
          ·
            refine ⟨18946261273802169667373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12630840849201446444915 18946261273802169667373)
            ·
              refine ⟨7104847977675813625265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18946261273802169667373 7104847977675813625265)
              ·
                refine ⟨5328635983256860218949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7104847977675813625265 5328635983256860218949)
                ·
                  refine ⟨999119246860661291053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5328635983256860218949 999119246860661291053)
                  ·
                    rfl

theorem cell22_8756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_8756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8756 prefixEnd_8756 := by exact prefixLift 8756
  have htrace : WordTrace (prefixWord ++ tailWord_8756) baseStart_8756 baseEnd_8756 := by
    simpa [prefixWord, tailWord_8756, baseEnd_8756] using wordTrace_append hprefix tailTrace_8756
  have hstable : (prefixWord ++ tailWord_8756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8756).length < 2 ^ (prefixWord ++ tailWord_8756).sum := by decide
  have hdescent : baseEnd_8756 < baseStart_8756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8816 : List Nat := [2, 1, 1, 1, 7, 2, 2, 2, 1, 3]
def baseStart_8816 : Nat := 118140960795 + 8816 * 2 ^ 59
def prefixEnd_8816 : Nat := 4983230072969 + 3 ^ 40 * 8816 * 2
def baseEnd_8816 : Nat := 3017896966761827372975

theorem tailTrace_8816 : CollatzResearch.WordTrace tailWord_8816 prefixEnd_8816 3017896966761827372975 := by
  unfold tailWord_8816
  simp only [CollatzResearch.WordTrace]
  refine ⟨160772968034306249019151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 214363957379074998692201 160772968034306249019151)
  ·
    refine ⟨241159452051459373528727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160772968034306249019151 241159452051459373528727)
    ·
      refine ⟨361739178077189060293091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241159452051459373528727 361739178077189060293091)
      ·
        refine ⟨542608767115783590439637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361739178077189060293091 542608767115783590439637)
        ·
          refine ⟨12717392979276177900929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 542608767115783590439637 12717392979276177900929)
          ·
            refine ⟨9538044734457133425697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12717392979276177900929 9538044734457133425697)
            ·
              refine ⟨7153533550842850069273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9538044734457133425697 7153533550842850069273)
              ·
                refine ⟨5365150163132137551955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7153533550842850069273 5365150163132137551955)
                ·
                  refine ⟨8047725244698206327933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5365150163132137551955 8047725244698206327933)
                  ·
                    refine ⟨3017896966761827372975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8047725244698206327933 3017896966761827372975)
                    ·
                      rfl

theorem cell22_8816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 1, 3].length) (baseStart_8816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8816 prefixEnd_8816 := by exact prefixLift 8816
  have htrace : WordTrace (prefixWord ++ tailWord_8816) baseStart_8816 baseEnd_8816 := by
    simpa [prefixWord, tailWord_8816, baseEnd_8816] using wordTrace_append hprefix tailTrace_8816
  have hstable : (prefixWord ++ tailWord_8816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8816).length < 2 ^ (prefixWord ++ tailWord_8816).sum := by decide
  have hdescent : baseEnd_8816 < baseStart_8816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8855 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 4, 3]
def baseStart_8855 : Nat := 118140960795 + 8855 * 2 ^ 59
def prefixEnd_8855 : Nat := 4983230072969 + 3 ^ 40 * 8855 * 2
def baseEnd_8855 : Nat := 3031247463778725647855

theorem tailTrace_8855 : CollatzResearch.WordTrace tailWord_8855 prefixEnd_8855 3031247463778725647855 := by
  unfold tailWord_8855
  simp only [CollatzResearch.WordTrace]
  refine ⟨322968382927322158708019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 215312255284881439138679 322968382927322158708019)
  ·
    refine ⟨484452574390983238062029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 322968382927322158708019 484452574390983238062029)
    ·
      refine ⟨181669715396618714273261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 484452574390983238062029 181669715396618714273261)
      ·
        refine ⟨68126143273732017852473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181669715396618714273261 68126143273732017852473)
        ·
          refine ⟨51094607455299013389355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68126143273732017852473 51094607455299013389355)
          ·
            refine ⟨76641911182948520084033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51094607455299013389355 76641911182948520084033)
            ·
              refine ⟨57481433387211390063025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76641911182948520084033 57481433387211390063025)
              ·
                refine ⟨43111075040408542547269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57481433387211390063025 43111075040408542547269)
                ·
                  refine ⟨8083326570076601727613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43111075040408542547269 8083326570076601727613)
                  ·
                    refine ⟨3031247463778725647855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8083326570076601727613 3031247463778725647855)
                    ·
                      rfl

theorem cell22_8855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_8855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8855 prefixEnd_8855 := by exact prefixLift 8855
  have htrace : WordTrace (prefixWord ++ tailWord_8855) baseStart_8855 baseEnd_8855 := by
    simpa [prefixWord, tailWord_8855, baseEnd_8855] using wordTrace_append hprefix tailTrace_8855
  have hstable : (prefixWord ++ tailWord_8855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8855).length < 2 ^ (prefixWord ++ tailWord_8855).sum := by decide
  have hdescent : baseEnd_8855 < baseStart_8855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8868 : List Nat := [2, 3, 1, 2, 2, 1, 11]
def baseStart_8868 : Nat := 118140960795 + 8868 * 2 ^ 59
def prefixEnd_8868 : Nat := 4983230072969 + 3 ^ 40 * 8868 * 2
def baseEnd_8868 : Nat := 112433245535223150845

theorem tailTrace_8868 : CollatzResearch.WordTrace tailWord_8868 prefixEnd_8868 112433245535223150845 := by
  unfold tailWord_8868
  simp only [CollatzResearch.WordTrace]
  refine ⟨161721265940112689465629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 215628354586816919287505 161721265940112689465629)
  ·
    refine ⟨60645474727542258549611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161721265940112689465629 60645474727542258549611)
    ·
      refine ⟨90968212091313387824417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60645474727542258549611 90968212091313387824417)
      ·
        refine ⟨68226159068485040868313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90968212091313387824417 68226159068485040868313)
        ·
          refine ⟨51169619301363780651235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68226159068485040868313 51169619301363780651235)
          ·
            refine ⟨76754428952045670976853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51169619301363780651235 76754428952045670976853)
            ·
              refine ⟨112433245535223150845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 76754428952045670976853 112433245535223150845)
              ·
                rfl

theorem cell22_8868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 11].length) (baseStart_8868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8868 prefixEnd_8868 := by exact prefixLift 8868
  have htrace : WordTrace (prefixWord ++ tailWord_8868) baseStart_8868 baseEnd_8868 := by
    simpa [prefixWord, tailWord_8868, baseEnd_8868] using wordTrace_append hprefix tailTrace_8868
  have hstable : (prefixWord ++ tailWord_8868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8868).length < 2 ^ (prefixWord ++ tailWord_8868).sum := by decide
  have hdescent : baseEnd_8868 < baseStart_8868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8874 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 6]
def baseStart_8874 : Nat := 118140960795 + 8874 * 2 ^ 59
def prefixEnd_8874 : Nat := 4983230072969 + 3 ^ 40 * 8874 * 2
def baseEnd_8874 : Nat := 1012583850689669807599

theorem tailTrace_8874 : CollatzResearch.WordTrace tailWord_8874 prefixEnd_8874 1012583850689669807599 := by
  unfold tailWord_8874
  simp only [CollatzResearch.WordTrace]
  refine ⟨80915342464622100912419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 215774246572325602433117 80915342464622100912419)
  ·
    refine ⟨121373013696933151368629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80915342464622100912419 121373013696933151368629)
    ·
      refine ⟨11378720034087482940809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121373013696933151368629 11378720034087482940809)
      ·
        refine ⟨8534040025565612205607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11378720034087482940809 8534040025565612205607)
        ·
          refine ⟨12801060038348418308411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8534040025565612205607 12801060038348418308411)
          ·
            refine ⟨19201590057522627462617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12801060038348418308411 19201590057522627462617)
            ·
              refine ⟨14401192543141970596963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19201590057522627462617 14401192543141970596963)
              ·
                refine ⟨21601788814712955895445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14401192543141970596963 21601788814712955895445)
                ·
                  refine ⟨1012583850689669807599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21601788814712955895445 1012583850689669807599)
                  ·
                    rfl

theorem cell22_8874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_8874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8874 prefixEnd_8874 := by exact prefixLift 8874
  have htrace : WordTrace (prefixWord ++ tailWord_8874) baseStart_8874 baseEnd_8874 := by
    simpa [prefixWord, tailWord_8874, baseEnd_8874] using wordTrace_append hprefix tailTrace_8874
  have hstable : (prefixWord ++ tailWord_8874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8874).length < 2 ^ (prefixWord ++ tailWord_8874).sum := by decide
  have hdescent : baseEnd_8874 < baseStart_8874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8913 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 9]
def baseStart_8913 : Nat := 118140960795 + 8913 * 2 ^ 59
def prefixEnd_8913 : Nat := 4983230072969 + 3 ^ 40 * 8913 * 2
def baseEnd_8913 : Nat := 1017034016361969232559

theorem tailTrace_8913 : CollatzResearch.WordTrace tailWord_8913 prefixEnd_8913 1017034016361969232559 := by
  unfold tailWord_8913
  simp only [CollatzResearch.WordTrace]
  refine ⟨325083816717198064319393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 216722544478132042879595 325083816717198064319393)
  ·
    refine ⟨243812862537898548239545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 325083816717198064319393 243812862537898548239545)
    ·
      refine ⟨182859646903423911179659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243812862537898548239545 182859646903423911179659)
      ·
        refine ⟨274289470355135866769489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182859646903423911179659 274289470355135866769489)
        ·
          refine ⟨205717102766351900077117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274289470355135866769489 205717102766351900077117)
          ·
            refine ⟨77143913537381962528919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205717102766351900077117 77143913537381962528919)
            ·
              refine ⟨115715870306072943793379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77143913537381962528919 115715870306072943793379)
              ·
                refine ⟨173573805459109415690069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115715870306072943793379 173573805459109415690069)
                ·
                  refine ⟨1017034016361969232559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 173573805459109415690069 1017034016361969232559)
                  ·
                    rfl

theorem cell22_8913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_8913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_8913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_8913 prefixEnd_8913 := by exact prefixLift 8913
  have htrace : WordTrace (prefixWord ++ tailWord_8913) baseStart_8913 baseEnd_8913 := by
    simpa [prefixWord, tailWord_8913, baseEnd_8913] using wordTrace_append hprefix tailTrace_8913
  have hstable : (prefixWord ++ tailWord_8913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8913).length < 2 ^ (prefixWord ++ tailWord_8913).sum := by decide
  have hdescent : baseEnd_8913 < baseStart_8913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9041 : List Nat := [1, 2, 2, 1, 6, 2, 1, 2, 2, 3]
def baseStart_9041 : Nat := 118140960795 + 9041 * 2 ^ 59
def prefixEnd_9041 : Nat := 4983230072969 + 3 ^ 40 * 9041 * 2
def baseEnd_9041 : Nat := 3094919064936240497285

theorem tailTrace_9041 : CollatzResearch.WordTrace tailWord_9041 prefixEnd_9041 3094919064936240497285 := by
  unfold tailWord_9041
  simp only [CollatzResearch.WordTrace]
  refine ⟨329752360253475924978977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 219834906835650616652651 329752360253475924978977)
  ·
    refine ⟨247314270190106943734233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 329752360253475924978977 247314270190106943734233)
    ·
      refine ⟨185485702642580207800675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247314270190106943734233 185485702642580207800675)
      ·
        refine ⟨278228553963870311701013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185485702642580207800675 278228553963870311701013)
        ·
          refine ⟨13041963467056420860985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 278228553963870311701013 13041963467056420860985)
          ·
            refine ⟨9781472600292315645739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13041963467056420860985 9781472600292315645739)
            ·
              refine ⟨14672208900438473468609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9781472600292315645739 14672208900438473468609)
              ·
                refine ⟨11004156675328855101457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14672208900438473468609 11004156675328855101457)
                ·
                  refine ⟨8253117506496641326093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11004156675328855101457 8253117506496641326093)
                  ·
                    refine ⟨3094919064936240497285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8253117506496641326093 3094919064936240497285)
                    ·
                      rfl

theorem cell22_9041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_9041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9041 prefixEnd_9041 := by exact prefixLift 9041
  have htrace : WordTrace (prefixWord ++ tailWord_9041) baseStart_9041 baseEnd_9041 := by
    simpa [prefixWord, tailWord_9041, baseEnd_9041] using wordTrace_append hprefix tailTrace_9041
  have hstable : (prefixWord ++ tailWord_9041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9041).length < 2 ^ (prefixWord ++ tailWord_9041).sum := by decide
  have hdescent : baseEnd_9041 < baseStart_9041 := by decide
  rcases family_descends (prefixWord ++ tailWord_9041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9058 : List Nat := [3, 3, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_9058 : Nat := 118140960795 + 9058 * 2 ^ 59
def prefixEnd_9058 : Nat := 4983230072969 + 3 ^ 40 * 9058 * 2
def baseEnd_9058 : Nat := 3100738512353862822233

theorem tailTrace_9058 : CollatzResearch.WordTrace tailWord_9058 prefixEnd_9058 3100738512353862822233 := by
  unfold tailWord_9058
  simp only [CollatzResearch.WordTrace]
  refine ⟨82593100297971957086957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 220248267461258552231885 82593100297971957086957)
  ·
    refine ⟨30972412611739483907609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82593100297971957086957 30972412611739483907609)
    ·
      refine ⟨23229309458804612930707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30972412611739483907609 23229309458804612930707)
      ·
        refine ⟨34843964188206919396061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23229309458804612930707 34843964188206919396061)
        ·
          refine ⟨13066486570577594773523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34843964188206919396061 13066486570577594773523)
          ·
            refine ⟨19599729855866392160285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13066486570577594773523 19599729855866392160285)
            ·
              refine ⟨7349898695949897060107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19599729855866392160285 7349898695949897060107)
              ·
                refine ⟨11024848043924845590161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7349898695949897060107 11024848043924845590161)
                ·
                  refine ⟨8268636032943634192621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11024848043924845590161 8268636032943634192621)
                  ·
                    refine ⟨3100738512353862822233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8268636032943634192621 3100738512353862822233)
                    ·
                      rfl

theorem cell22_9058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_9058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9058 prefixEnd_9058 := by exact prefixLift 9058
  have htrace : WordTrace (prefixWord ++ tailWord_9058) baseStart_9058 baseEnd_9058 := by
    simpa [prefixWord, tailWord_9058, baseEnd_9058] using wordTrace_append hprefix tailTrace_9058
  have hstable : (prefixWord ++ tailWord_9058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9058).length < 2 ^ (prefixWord ++ tailWord_9058).sum := by decide
  have hdescent : baseEnd_9058 < baseStart_9058 := by decide
  rcases family_descends (prefixWord ++ tailWord_9058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9080 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 4, 5]
def baseStart_9080 : Nat := 118140960795 + 9080 * 2 ^ 59
def prefixEnd_9080 : Nat := 4983230072969 + 3 ^ 40 * 9080 * 2
def baseEnd_9080 : Nat := 3108269561953138772165

theorem tailTrace_9080 : CollatzResearch.WordTrace tailWord_9080 prefixEnd_9080 3108269561953138772165 := by
  unfold tailWord_9080
  simp only [CollatzResearch.WordTrace]
  refine ⟨165587403556092792824347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 220783204741457057099129 165587403556092792824347)
  ·
    refine ⟨248381105334139189236521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165587403556092792824347 248381105334139189236521)
    ·
      refine ⟨186285829000604391927391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248381105334139189236521 186285829000604391927391)
      ·
        refine ⟨279428743500906587891087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186285829000604391927391 279428743500906587891087)
        ·
          refine ⟨419143115251359881836631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279428743500906587891087 419143115251359881836631)
          ·
            refine ⟨628714672877039822754947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419143115251359881836631 628714672877039822754947)
            ·
              refine ⟨943072009315559734132421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628714672877039822754947 943072009315559734132421)
              ·
                refine ⟨176826001746667450149829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 943072009315559734132421 176826001746667450149829)
                ·
                  refine ⟨33154875327500146903093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 176826001746667450149829 33154875327500146903093)
                  ·
                    refine ⟨3108269561953138772165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33154875327500146903093 3108269561953138772165)
                    ·
                      rfl

theorem cell22_9080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_9080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9080 prefixEnd_9080 := by exact prefixLift 9080
  have htrace : WordTrace (prefixWord ++ tailWord_9080) baseStart_9080 baseEnd_9080 := by
    simpa [prefixWord, tailWord_9080, baseEnd_9080] using wordTrace_append hprefix tailTrace_9080
  have hstable : (prefixWord ++ tailWord_9080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9080).length < 2 ^ (prefixWord ++ tailWord_9080).sum := by decide
  have hdescent : baseEnd_9080 < baseStart_9080 := by decide
  rcases family_descends (prefixWord ++ tailWord_9080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9159 : List Nat := [1, 1, 4, 1, 1, 2, 3, 4, 2, 3]
def baseStart_9159 : Nat := 118140960795 + 9159 * 2 ^ 59
def prefixEnd_9159 : Nat := 4983230072969 + 3 ^ 40 * 9159 * 2
def baseEnd_9159 : Nat := 3135312876423266046923

theorem tailTrace_9159 : CollatzResearch.WordTrace tailWord_9159 prefixEnd_9159 3135312876423266046923 := by
  unfold tailWord_9159
  simp only [CollatzResearch.WordTrace]
  refine ⟨334056173825982077774531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 222704115883988051849687 334056173825982077774531)
  ·
    refine ⟨501084260738973116661797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 334056173825982077774531 501084260738973116661797)
    ·
      refine ⟨93953298888557459374087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 501084260738973116661797 93953298888557459374087)
      ·
        refine ⟨140929948332836189061131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93953298888557459374087 140929948332836189061131)
        ·
          refine ⟨211394922499254283591697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140929948332836189061131 211394922499254283591697)
          ·
            refine ⟨158546191874440712693773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211394922499254283591697 158546191874440712693773)
            ·
              refine ⟨59454821952915267260165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158546191874440712693773 59454821952915267260165)
              ·
                refine ⟨11147779116171612611281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59454821952915267260165 11147779116171612611281)
                ·
                  refine ⟨8360834337128709458461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11147779116171612611281 8360834337128709458461)
                  ·
                    refine ⟨3135312876423266046923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8360834337128709458461 3135312876423266046923)
                    ·
                      rfl

theorem cell22_9159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_9159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9159 prefixEnd_9159 := by exact prefixLift 9159
  have htrace : WordTrace (prefixWord ++ tailWord_9159) baseStart_9159 baseEnd_9159 := by
    simpa [prefixWord, tailWord_9159, baseEnd_9159] using wordTrace_append hprefix tailTrace_9159
  have hstable : (prefixWord ++ tailWord_9159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9159).length < 2 ^ (prefixWord ++ tailWord_9159).sum := by decide
  have hdescent : baseEnd_9159 < baseStart_9159 := by decide
  rcases family_descends (prefixWord ++ tailWord_9159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9191 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 2, 4]
def baseStart_9191 : Nat := 118140960795 + 9191 * 2 ^ 59
def prefixEnd_9191 : Nat := 4983230072969 + 3 ^ 40 * 9191 * 2
def baseEnd_9191 : Nat := 3146267130385849246825

theorem tailTrace_9191 : CollatzResearch.WordTrace tailWord_9191 prefixEnd_9191 3146267130385849246825 := by
  unfold tailWord_9191
  simp only [CollatzResearch.WordTrace]
  refine ⟨335223309710051542939427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 223482206473367695292951 335223309710051542939427)
  ·
    refine ⟨502834964565077314409141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 335223309710051542939427 502834964565077314409141)
    ·
      refine ⟨47140777927975998225857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 502834964565077314409141 47140777927975998225857)
      ·
        refine ⟨35355583445981998669393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47140777927975998225857 35355583445981998669393)
        ·
          refine ⟨26516687584486499002045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35355583445981998669393 26516687584486499002045)
          ·
            refine ⟨9943757844182437125767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26516687584486499002045 9943757844182437125767)
            ·
              refine ⟨14915636766273655688651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9943757844182437125767 14915636766273655688651)
              ·
                refine ⟨22373455149410483532977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14915636766273655688651 22373455149410483532977)
                ·
                  refine ⟨16780091362057862649733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22373455149410483532977 16780091362057862649733)
                  ·
                    refine ⟨3146267130385849246825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16780091362057862649733 3146267130385849246825)
                    ·
                      rfl

theorem cell22_9191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_9191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9191 prefixEnd_9191 := by exact prefixLift 9191
  have htrace : WordTrace (prefixWord ++ tailWord_9191) baseStart_9191 baseEnd_9191 := by
    simpa [prefixWord, tailWord_9191, baseEnd_9191] using wordTrace_append hprefix tailTrace_9191
  have hstable : (prefixWord ++ tailWord_9191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9191).length < 2 ^ (prefixWord ++ tailWord_9191).sum := by decide
  have hdescent : baseEnd_9191 < baseStart_9191 := by decide
  rcases family_descends (prefixWord ++ tailWord_9191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9221 : List Nat := [1, 3, 1, 1, 2, 3, 1, 6, 1, 3]
def baseStart_9221 : Nat := 118140960795 + 9221 * 2 ^ 59
def prefixEnd_9221 : Nat := 4983230072969 + 3 ^ 40 * 9221 * 2
def baseEnd_9221 : Nat := 3156536743475770996733

theorem tailTrace_9221 : CollatzResearch.WordTrace tailWord_9221 prefixEnd_9221 3156536743475770996733 := by
  unfold tailWord_9221
  simp only [CollatzResearch.WordTrace]
  refine ⟨336317499601366666531517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 224211666400911111021011 336317499601366666531517)
  ·
    refine ⟨126119062350512499949319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 336317499601366666531517 126119062350512499949319)
    ·
      refine ⟨189178593525768749923979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126119062350512499949319 189178593525768749923979)
      ·
        refine ⟨283767890288653124885969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189178593525768749923979 283767890288653124885969)
        ·
          refine ⟨212825917716489843664477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283767890288653124885969 212825917716489843664477)
          ·
            refine ⟨79809719143683691374179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212825917716489843664477 79809719143683691374179)
            ·
              refine ⟨119714578715525537061269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79809719143683691374179 119714578715525537061269)
              ·
                refine ⟨5611620877290259549747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 119714578715525537061269 5611620877290259549747)
                ·
                  refine ⟨8417431315935389324621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5611620877290259549747 8417431315935389324621)
                  ·
                    refine ⟨3156536743475770996733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8417431315935389324621 3156536743475770996733)
                    ·
                      rfl

theorem cell22_9221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_9221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9221 prefixEnd_9221 := by exact prefixLift 9221
  have htrace : WordTrace (prefixWord ++ tailWord_9221) baseStart_9221 baseEnd_9221 := by
    simpa [prefixWord, tailWord_9221, baseEnd_9221] using wordTrace_append hprefix tailTrace_9221
  have hstable : (prefixWord ++ tailWord_9221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9221).length < 2 ^ (prefixWord ++ tailWord_9221).sum := by decide
  have hdescent : baseEnd_9221 < baseStart_9221 := by decide
  rcases family_descends (prefixWord ++ tailWord_9221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9255 : List Nat := [1, 1, 7, 1, 1, 1, 3, 3, 1, 3]
def baseStart_9255 : Nat := 118140960795 + 9255 * 2 ^ 59
def prefixEnd_9255 : Nat := 4983230072969 + 3 ^ 40 * 9255 * 2
def baseEnd_9255 : Nat := 3168175638311015646629

theorem tailTrace_9255 : CollatzResearch.WordTrace tailWord_9255 prefixEnd_9255 3168175638311015646629 := by
  unfold tailWord_9255
  simp only [CollatzResearch.WordTrace]
  refine ⟨337557581478190473269219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 225038387652126982179479 337557581478190473269219)
  ·
    refine ⟨506336372217285709903829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 337557581478190473269219 506336372217285709903829)
    ·
      refine ⟨11867258723842633825871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 506336372217285709903829 11867258723842633825871)
      ·
        refine ⟨17800888085763950738807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11867258723842633825871 17800888085763950738807)
        ·
          refine ⟨26701332128645926108211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17800888085763950738807 26701332128645926108211)
          ·
            refine ⟨40051998192968889162317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26701332128645926108211 40051998192968889162317)
            ·
              refine ⟨15019499322363333435869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40051998192968889162317 15019499322363333435869)
              ·
                refine ⟨5632312245886250038451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15019499322363333435869 5632312245886250038451)
                ·
                  refine ⟨8448468368829375057677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5632312245886250038451 8448468368829375057677)
                  ·
                    refine ⟨3168175638311015646629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8448468368829375057677 3168175638311015646629)
                    ·
                      rfl

theorem cell22_9255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_9255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9255 prefixEnd_9255 := by exact prefixLift 9255
  have htrace : WordTrace (prefixWord ++ tailWord_9255) baseStart_9255 baseEnd_9255 := by
    simpa [prefixWord, tailWord_9255, baseEnd_9255] using wordTrace_append hprefix tailTrace_9255
  have hstable : (prefixWord ++ tailWord_9255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9255).length < 2 ^ (prefixWord ++ tailWord_9255).sum := by decide
  have hdescent : baseEnd_9255 < baseStart_9255 := by decide
  rcases family_descends (prefixWord ++ tailWord_9255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9264 : List Nat := [2, 1, 1, 1, 2, 4, 1, 5, 1, 4]
def baseStart_9264 : Nat := 118140960795 + 9264 * 2 ^ 59
def prefixEnd_9264 : Nat := 4983230072969 + 3 ^ 40 * 9264 * 2
def baseEnd_9264 : Nat := 3171256522237992171601

theorem tailTrace_9264 : CollatzResearch.WordTrace tailWord_9264 prefixEnd_9264 3171256522237992171601 := by
  unfold tailWord_9264
  simp only [CollatzResearch.WordTrace]
  refine ⟨168942919222792505173423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 225257225630390006897897 168942919222792505173423)
  ·
    refine ⟨253414378834188757760135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168942919222792505173423 253414378834188757760135)
    ·
      refine ⟨380121568251283136640203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253414378834188757760135 380121568251283136640203)
      ·
        refine ⟨570182352376924704960305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380121568251283136640203 570182352376924704960305)
        ·
          refine ⟨427636764282693528720229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570182352376924704960305 427636764282693528720229)
          ·
            refine ⟨80181893303005036635043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 427636764282693528720229 80181893303005036635043)
            ·
              refine ⟨120272839954507554952565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80181893303005036635043 120272839954507554952565)
              ·
                refine ⟨11275578745735083276803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120272839954507554952565 11275578745735083276803)
                ·
                  refine ⟨16913368118602624915205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11275578745735083276803 16913368118602624915205)
                  ·
                    refine ⟨3171256522237992171601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16913368118602624915205 3171256522237992171601)
                    ·
                      rfl

theorem cell22_9264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_9264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9264 prefixEnd_9264 := by exact prefixLift 9264
  have htrace : WordTrace (prefixWord ++ tailWord_9264) baseStart_9264 baseEnd_9264 := by
    simpa [prefixWord, tailWord_9264, baseEnd_9264] using wordTrace_append hprefix tailTrace_9264
  have hstable : (prefixWord ++ tailWord_9264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9264).length < 2 ^ (prefixWord ++ tailWord_9264).sum := by decide
  have hdescent : baseEnd_9264 < baseStart_9264 := by decide
  rcases family_descends (prefixWord ++ tailWord_9264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9294 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_9294 : Nat := 118140960795 + 9294 * 2 ^ 59
def prefixEnd_9294 : Nat := 4983230072969 + 3 ^ 40 * 9294 * 2
def baseEnd_9294 : Nat := 3181526135327913921509

theorem tailTrace_9294 : CollatzResearch.WordTrace tailWord_9294 prefixEnd_9294 3181526135327913921509 := by
  unfold tailWord_9294
  simp only [CollatzResearch.WordTrace]
  refine ⟨42372503542112516742367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 225986685557933422625957 42372503542112516742367)
  ·
    refine ⟨63558755313168775113551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42372503542112516742367 63558755313168775113551)
    ·
      refine ⟨95338132969753162670327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63558755313168775113551 95338132969753162670327)
      ·
        refine ⟨143007199454629744005491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95338132969753162670327 143007199454629744005491)
        ·
          refine ⟨214510799181944616008237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143007199454629744005491 214510799181944616008237)
          ·
            refine ⟨80441549693229231003089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214510799181944616008237 80441549693229231003089)
            ·
              refine ⟨60331162269921923252317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80441549693229231003089 60331162269921923252317)
              ·
                refine ⟨22624185851220721219619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60331162269921923252317 22624185851220721219619)
                ·
                  refine ⟨33936278776831081829429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22624185851220721219619 33936278776831081829429)
                  ·
                    refine ⟨3181526135327913921509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33936278776831081829429 3181526135327913921509)
                    ·
                      rfl

theorem cell22_9294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_9294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9294 prefixEnd_9294 := by exact prefixLift 9294
  have htrace : WordTrace (prefixWord ++ tailWord_9294) baseStart_9294 baseEnd_9294 := by
    simpa [prefixWord, tailWord_9294, baseEnd_9294] using wordTrace_append hprefix tailTrace_9294
  have hstable : (prefixWord ++ tailWord_9294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9294).length < 2 ^ (prefixWord ++ tailWord_9294).sum := by decide
  have hdescent : baseEnd_9294 < baseStart_9294 := by decide
  rcases family_descends (prefixWord ++ tailWord_9294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9298 : List Nat := [3, 2, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_9298 : Nat := 118140960795 + 9298 * 2 ^ 59
def prefixEnd_9298 : Nat := 4983230072969 + 3 ^ 40 * 9298 * 2
def baseEnd_9298 : Nat := 3182895417073236821497

theorem tailTrace_9298 : CollatzResearch.WordTrace tailWord_9298 prefixEnd_9298 3182895417073236821497 := by
  unfold tailWord_9298
  simp only [CollatzResearch.WordTrace]
  refine ⟨84781480080602204271137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 226083946881605878056365 84781480080602204271137)
  ·
    refine ⟨63586110060451653203353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84781480080602204271137 63586110060451653203353)
    ·
      refine ⟨47689582545338739902515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63586110060451653203353 47689582545338739902515)
      ·
        refine ⟨71534373818008109853773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47689582545338739902515 71534373818008109853773)
        ·
          refine ⟨26825390181753041195165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71534373818008109853773 26825390181753041195165)
          ·
            refine ⟨10059521318157390448187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26825390181753041195165 10059521318157390448187)
            ·
              refine ⟨15089281977236085672281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10059521318157390448187 15089281977236085672281)
              ·
                refine ⟨11316961482927064254211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15089281977236085672281 11316961482927064254211)
                ·
                  refine ⟨16975442224390596381317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11316961482927064254211 16975442224390596381317)
                  ·
                    refine ⟨3182895417073236821497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16975442224390596381317 3182895417073236821497)
                    ·
                      rfl

theorem cell22_9298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_9298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9298 prefixEnd_9298 := by exact prefixLift 9298
  have htrace : WordTrace (prefixWord ++ tailWord_9298) baseStart_9298 baseEnd_9298 := by
    simpa [prefixWord, tailWord_9298, baseEnd_9298] using wordTrace_append hprefix tailTrace_9298
  have hstable : (prefixWord ++ tailWord_9298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9298).length < 2 ^ (prefixWord ++ tailWord_9298).sum := by decide
  have hdescent : baseEnd_9298 < baseStart_9298 := by decide
  rcases family_descends (prefixWord ++ tailWord_9298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9326 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_9326 : Nat := 118140960795 + 9326 * 2 ^ 59
def prefixEnd_9326 : Nat := 4983230072969 + 3 ^ 40 * 9326 * 2
def baseEnd_9326 : Nat := 3192480389290497121411

theorem tailTrace_9326 : CollatzResearch.WordTrace tailWord_9326 prefixEnd_9326 3192480389290497121411 := by
  unfold tailWord_9326
  simp only [CollatzResearch.WordTrace]
  refine ⟨42518395527621199887979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 226764776147313066069221 42518395527621199887979)
  ·
    refine ⟨63777593291431799831969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42518395527621199887979 63777593291431799831969)
    ·
      refine ⟨47833194968573849873977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63777593291431799831969 47833194968573849873977)
      ·
        refine ⟨35874896226430387405483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47833194968573849873977 35874896226430387405483)
        ·
          refine ⟨53812344339645581108225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35874896226430387405483 53812344339645581108225)
          ·
            refine ⟨40359258254734185831169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53812344339645581108225 40359258254734185831169)
            ·
              refine ⟨30269443691050639373377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40359258254734185831169 30269443691050639373377)
              ·
                refine ⟨22702082768287979530033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30269443691050639373377 22702082768287979530033)
                ·
                  refine ⟨17026562076215984647525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22702082768287979530033 17026562076215984647525)
                  ·
                    refine ⟨3192480389290497121411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17026562076215984647525 3192480389290497121411)
                    ·
                      rfl

theorem cell22_9326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_9326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9326 prefixEnd_9326 := by exact prefixLift 9326
  have htrace : WordTrace (prefixWord ++ tailWord_9326) baseStart_9326 baseEnd_9326 := by
    simpa [prefixWord, tailWord_9326, baseEnd_9326] using wordTrace_append hprefix tailTrace_9326
  have hstable : (prefixWord ++ tailWord_9326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9326).length < 2 ^ (prefixWord ++ tailWord_9326).sum := by decide
  have hdescent : baseEnd_9326 < baseStart_9326 := by decide
  rcases family_descends (prefixWord ++ tailWord_9326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9339 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 7, 3]
def baseStart_9339 : Nat := 118140960795 + 9339 * 2 ^ 59
def prefixEnd_9339 : Nat := 4983230072969 + 3 ^ 40 * 9339 * 2
def baseEnd_9339 : Nat := 3196930554962796546371

theorem tailTrace_9339 : CollatzResearch.WordTrace tailWord_9339 prefixEnd_9339 3196930554962796546371 := by
  unfold tailWord_9339
  simp only [CollatzResearch.WordTrace]
  refine ⟨340621313173872819327071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 227080875449248546218047 340621313173872819327071)
  ·
    refine ⟨510931969760809228990607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 340621313173872819327071 510931969760809228990607)
    ·
      refine ⟨766397954641213843485911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 510931969760809228990607 766397954641213843485911)
      ·
        refine ⟨1149596931961820765228867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 766397954641213843485911 1149596931961820765228867)
        ·
          refine ⟨1724395397942731147843301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1149596931961820765228867 1724395397942731147843301)
          ·
            refine ⟨323324137114262090220619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1724395397942731147843301 323324137114262090220619)
            ·
              refine ⟨484986205671393135330929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323324137114262090220619 484986205671393135330929)
              ·
                refine ⟨363739654253544851498197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484986205671393135330929 363739654253544851498197)
                ·
                  refine ⟨8525148146567457456989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 363739654253544851498197 8525148146567457456989)
                  ·
                    refine ⟨3196930554962796546371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8525148146567457456989 3196930554962796546371)
                    ·
                      rfl

theorem cell22_9339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 3].length) (baseStart_9339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9339 prefixEnd_9339 := by exact prefixLift 9339
  have htrace : WordTrace (prefixWord ++ tailWord_9339) baseStart_9339 baseEnd_9339 := by
    simpa [prefixWord, tailWord_9339, baseEnd_9339] using wordTrace_append hprefix tailTrace_9339
  have hstable : (prefixWord ++ tailWord_9339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9339).length < 2 ^ (prefixWord ++ tailWord_9339).sum := by decide
  have hdescent : baseEnd_9339 < baseStart_9339 := by decide
  rcases family_descends (prefixWord ++ tailWord_9339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9354 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_9354 : Nat := 118140960795 + 9354 * 2 ^ 59
def prefixEnd_9354 : Nat := 4983230072969 + 3 ^ 40 * 9354 * 2
def baseEnd_9354 : Nat := 3202065361507757421325

theorem tailTrace_9354 : CollatzResearch.WordTrace tailWord_9354 prefixEnd_9354 3202065361507757421325 := by
  unfold tailWord_9354
  simp only [CollatzResearch.WordTrace]
  refine ⟨85292102029882595280779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 227445605413020254082077 85292102029882595280779)
  ·
    refine ⟨127938153044823892921169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85292102029882595280779 127938153044823892921169)
    ·
      refine ⟨95953614783617919690877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127938153044823892921169 95953614783617919690877)
      ·
        refine ⟨35982605543856719884079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95953614783617919690877 35982605543856719884079)
        ·
          refine ⟨53973908315785079826119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35982605543856719884079 53973908315785079826119)
          ·
            refine ⟨80960862473677619739179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53973908315785079826119 80960862473677619739179)
            ·
              refine ⟨121441293710516429608769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80960862473677619739179 121441293710516429608769)
              ·
                refine ⟨91080970282887322206577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121441293710516429608769 91080970282887322206577)
                ·
                  refine ⟨68310727712165491654933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91080970282887322206577 68310727712165491654933)
                  ·
                    refine ⟨3202065361507757421325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68310727712165491654933 3202065361507757421325)
                    ·
                      rfl

theorem cell22_9354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_9354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9354 prefixEnd_9354 := by exact prefixLift 9354
  have htrace : WordTrace (prefixWord ++ tailWord_9354) baseStart_9354 baseEnd_9354 := by
    simpa [prefixWord, tailWord_9354, baseEnd_9354] using wordTrace_append hprefix tailTrace_9354
  have hstable : (prefixWord ++ tailWord_9354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9354).length < 2 ^ (prefixWord ++ tailWord_9354).sum := by decide
  have hdescent : baseEnd_9354 < baseStart_9354 := by decide
  rcases family_descends (prefixWord ++ tailWord_9354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9416 : List Nat := [2, 1, 3, 1, 2, 1, 3, 4, 1, 4]
def baseStart_9416 : Nat := 118140960795 + 9416 * 2 ^ 59
def prefixEnd_9416 : Nat := 4983230072969 + 3 ^ 40 * 9416 * 2
def baseEnd_9416 : Nat := 3223289228560262371135

theorem tailTrace_9416 : CollatzResearch.WordTrace tailWord_9416 prefixEnd_9416 3223289228560262371135 := by
  unfold tailWord_9416
  simp only [CollatzResearch.WordTrace]
  refine ⟨171714866947457484940051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 228953155929943313253401 171714866947457484940051)
  ·
    refine ⟨257572300421186227410077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171714866947457484940051 257572300421186227410077)
    ·
      refine ⟨96589612657944835278779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257572300421186227410077 96589612657944835278779)
      ·
        refine ⟨144884418986917252918169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96589612657944835278779 144884418986917252918169)
        ·
          refine ⟨108663314240187939688627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144884418986917252918169 108663314240187939688627)
          ·
            refine ⟨162994971360281909532941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108663314240187939688627 162994971360281909532941)
            ·
              refine ⟨61123114260105716074853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162994971360281909532941 61123114260105716074853)
              ·
                refine ⟨11460583923769821764035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61123114260105716074853 11460583923769821764035)
                ·
                  refine ⟨17190875885654732646053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11460583923769821764035 17190875885654732646053)
                  ·
                    refine ⟨3223289228560262371135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17190875885654732646053 3223289228560262371135)
                    ·
                      rfl

theorem cell22_9416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_9416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9416 prefixEnd_9416 := by exact prefixLift 9416
  have htrace : WordTrace (prefixWord ++ tailWord_9416) baseStart_9416 baseEnd_9416 := by
    simpa [prefixWord, tailWord_9416, baseEnd_9416] using wordTrace_append hprefix tailTrace_9416
  have hstable : (prefixWord ++ tailWord_9416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9416).length < 2 ^ (prefixWord ++ tailWord_9416).sum := by decide
  have hdescent : baseEnd_9416 < baseStart_9416 := by decide
  rcases family_descends (prefixWord ++ tailWord_9416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9459 : List Nat := [1, 1, 1, 2, 2, 5, 1, 9]
def baseStart_9459 : Nat := 118140960795 + 9459 * 2 ^ 59
def prefixEnd_9459 : Nat := 4983230072969 + 3 ^ 40 * 9459 * 2
def baseEnd_9459 : Nat := 359778778591387060667

theorem tailTrace_9459 : CollatzResearch.WordTrace tailWord_9459 prefixEnd_9459 359778778591387060667 := by
  unfold tailWord_9459
  simp only [CollatzResearch.WordTrace]
  refine ⟨344998072739133313695431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 229998715159422209130287 344998072739133313695431)
  ·
    refine ⟨517497109108699970543147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 344998072739133313695431 517497109108699970543147)
    ·
      refine ⟨776245663663049955814721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 517497109108699970543147 776245663663049955814721)
      ·
        refine ⟨582184247747287466861041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 776245663663049955814721 582184247747287466861041)
        ·
          refine ⟨436638185810465600145781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582184247747287466861041 436638185810465600145781)
          ·
            refine ⟨40934829919731150013667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 436638185810465600145781 40934829919731150013667)
            ·
              refine ⟨61402244879596725020501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40934829919731150013667 61402244879596725020501)
              ·
                refine ⟨359778778591387060667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 61402244879596725020501 359778778591387060667)
                ·
                  rfl

theorem cell22_9459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 9].length) (baseStart_9459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9459 prefixEnd_9459 := by exact prefixLift 9459
  have htrace : WordTrace (prefixWord ++ tailWord_9459) baseStart_9459 baseEnd_9459 := by
    simpa [prefixWord, tailWord_9459, baseEnd_9459] using wordTrace_append hprefix tailTrace_9459
  have hstable : (prefixWord ++ tailWord_9459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9459).length < 2 ^ (prefixWord ++ tailWord_9459).sum := by decide
  have hdescent : baseEnd_9459 < baseStart_9459 := by decide
  rcases family_descends (prefixWord ++ tailWord_9459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9476 : List Nat := [2, 3, 2, 2, 2, 1, 2, 8]
def baseStart_9476 : Nat := 118140960795 + 9476 * 2 ^ 59
def prefixEnd_9476 : Nat := 4983230072969 + 3 ^ 40 * 9476 * 2
def baseEnd_9476 : Nat := 360425383860011763439

theorem tailTrace_9476 : CollatzResearch.WordTrace tailWord_9476 prefixEnd_9476 360425383860011763439 := by
  unfold tailWord_9476
  simp only [CollatzResearch.WordTrace]
  refine ⟨172809056838772608532141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 230412075785030144709521 172809056838772608532141)
  ·
    refine ⟨64803396314539728199553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172809056838772608532141 64803396314539728199553)
    ·
      refine ⟨48602547235904796149665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64803396314539728199553 48602547235904796149665)
      ·
        refine ⟨36451910426928597112249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48602547235904796149665 36451910426928597112249)
        ·
          refine ⟨27338932820196447834187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36451910426928597112249 27338932820196447834187)
          ·
            refine ⟨41008399230294671751281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27338932820196447834187 41008399230294671751281)
            ·
              refine ⟨30756299422721003813461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41008399230294671751281 30756299422721003813461)
              ·
                refine ⟨360425383860011763439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 30756299422721003813461 360425383860011763439)
                ·
                  rfl

theorem cell22_9476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 8].length) (baseStart_9476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9476 prefixEnd_9476 := by exact prefixLift 9476
  have htrace : WordTrace (prefixWord ++ tailWord_9476) baseStart_9476 baseEnd_9476 := by
    simpa [prefixWord, tailWord_9476, baseEnd_9476] using wordTrace_append hprefix tailTrace_9476
  have hstable : (prefixWord ++ tailWord_9476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9476).length < 2 ^ (prefixWord ++ tailWord_9476).sum := by decide
  have hdescent : baseEnd_9476 < baseStart_9476 := by decide
  rcases family_descends (prefixWord ++ tailWord_9476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9508 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_9508 : Nat := 118140960795 + 9508 * 2 ^ 59
def prefixEnd_9508 : Nat := 4983230072969 + 3 ^ 40 * 9508 * 2
def baseEnd_9508 : Nat := 3254782708702689070853

theorem tailTrace_9508 : CollatzResearch.WordTrace tailWord_9508 prefixEnd_9508 3254782708702689070853 := by
  unfold tailWord_9508
  simp only [CollatzResearch.WordTrace]
  refine ⟨173392624780807341114589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 231190166374409788152785 173392624780807341114589)
  ·
    refine ⟨65022234292802752917971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173392624780807341114589 65022234292802752917971)
    ·
      refine ⟨97533351439204129376957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65022234292802752917971 97533351439204129376957)
      ·
        refine ⟨36575006789701548516359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97533351439204129376957 36575006789701548516359)
        ·
          refine ⟨54862510184552322774539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36575006789701548516359 54862510184552322774539)
          ·
            refine ⟨82293765276828484161809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54862510184552322774539 82293765276828484161809)
            ·
              refine ⟨61720323957621363121357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82293765276828484161809 61720323957621363121357)
              ·
                refine ⟨23145121484108011170509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61720323957621363121357 23145121484108011170509)
                ·
                  refine ⟨8679420556540504188941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23145121484108011170509 8679420556540504188941)
                  ·
                    refine ⟨3254782708702689070853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8679420556540504188941 3254782708702689070853)
                    ·
                      rfl

theorem cell22_9508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_9508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9508 prefixEnd_9508 := by exact prefixLift 9508
  have htrace : WordTrace (prefixWord ++ tailWord_9508) baseStart_9508 baseEnd_9508 := by
    simpa [prefixWord, tailWord_9508, baseEnd_9508] using wordTrace_append hprefix tailTrace_9508
  have hstable : (prefixWord ++ tailWord_9508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9508).length < 2 ^ (prefixWord ++ tailWord_9508).sum := by decide
  have hdescent : baseEnd_9508 < baseStart_9508 := by decide
  rcases family_descends (prefixWord ++ tailWord_9508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9596 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_9596 : Nat := 118140960795 + 9596 * 2 ^ 59
def prefixEnd_9596 : Nat := 4983230072969 + 3 ^ 40 * 9596 * 2
def baseEnd_9596 : Nat := 3284906907099792870583

theorem tailTrace_9596 : CollatzResearch.WordTrace tailWord_9596 prefixEnd_9596 3284906907099792870583 := by
  unfold tailWord_9596
  simp only [CollatzResearch.WordTrace]
  refine ⟨174997436621402855716321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 233329915495203807621761 174997436621402855716321)
  ·
    refine ⟨131248077466052141787241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174997436621402855716321 131248077466052141787241)
    ·
      refine ⟨98436058099539106340431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131248077466052141787241 98436058099539106340431)
      ·
        refine ⟨147654087149308659510647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98436058099539106340431 147654087149308659510647)
        ·
          refine ⟨221481130723962989265971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147654087149308659510647 221481130723962989265971)
          ·
            refine ⟨332221696085944483898957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221481130723962989265971 332221696085944483898957)
            ·
              refine ⟨124583136032229181462109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 332221696085944483898957 124583136032229181462109)
              ·
                refine ⟨46718676012085943048291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124583136032229181462109 46718676012085943048291)
                ·
                  refine ⟨70078014018128914572437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46718676012085943048291 70078014018128914572437)
                  ·
                    refine ⟨3284906907099792870583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70078014018128914572437 3284906907099792870583)
                    ·
                      rfl

theorem cell22_9596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_9596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9596 prefixEnd_9596 := by exact prefixLift 9596
  have htrace : WordTrace (prefixWord ++ tailWord_9596) baseStart_9596 baseEnd_9596 := by
    simpa [prefixWord, tailWord_9596, baseEnd_9596] using wordTrace_append hprefix tailTrace_9596
  have hstable : (prefixWord ++ tailWord_9596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9596).length < 2 ^ (prefixWord ++ tailWord_9596).sum := by decide
  have hdescent : baseEnd_9596 < baseStart_9596 := by decide
  rcases family_descends (prefixWord ++ tailWord_9596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9602 : List Nat := [3, 4, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_9602 : Nat := 118140960795 + 9602 * 2 ^ 59
def prefixEnd_9602 : Nat := 4983230072969 + 3 ^ 40 * 9602 * 2
def baseEnd_9602 : Nat := 3286960829717777220565

theorem tailTrace_9602 : CollatzResearch.WordTrace tailWord_9602 prefixEnd_9602 3286960829717777220565 := by
  unfold tailWord_9602
  simp only [CollatzResearch.WordTrace]
  refine ⟨87553427805267184037765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 233475807480712490767373 87553427805267184037765)
  ·
    refine ⟨16416267713487597007081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87553427805267184037765 16416267713487597007081)
    ·
      refine ⟨12312200785115697755311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16416267713487597007081 12312200785115697755311)
      ·
        refine ⟨18468301177673546632967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12312200785115697755311 18468301177673546632967)
        ·
          refine ⟨27702451766510319949451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18468301177673546632967 27702451766510319949451)
          ·
            refine ⟨41553677649765479924177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27702451766510319949451 41553677649765479924177)
            ·
              refine ⟨31165258237324109943133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41553677649765479924177 31165258237324109943133)
              ·
                refine ⟨11686971838996541228675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31165258237324109943133 11686971838996541228675)
                ·
                  refine ⟨17530457758494811843013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11686971838996541228675 17530457758494811843013)
                  ·
                    refine ⟨3286960829717777220565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17530457758494811843013 3286960829717777220565)
                    ·
                      rfl

theorem cell22_9602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_9602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9602 prefixEnd_9602 := by exact prefixLift 9602
  have htrace : WordTrace (prefixWord ++ tailWord_9602) baseStart_9602 baseEnd_9602 := by
    simpa [prefixWord, tailWord_9602, baseEnd_9602] using wordTrace_append hprefix tailTrace_9602
  have hstable : (prefixWord ++ tailWord_9602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9602).length < 2 ^ (prefixWord ++ tailWord_9602).sum := by decide
  have hdescent : baseEnd_9602 < baseStart_9602 := by decide
  rcases family_descends (prefixWord ++ tailWord_9602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9656 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 9]
def baseStart_9656 : Nat := 118140960795 + 9656 * 2 ^ 59
def prefixEnd_9656 : Nat := 4983230072969 + 3 ^ 40 * 9656 * 2
def baseEnd_9656 : Nat := 1101815377759878790133

theorem tailTrace_9656 : CollatzResearch.WordTrace tailWord_9656 prefixEnd_9656 1101815377759878790133 := by
  unfold tailWord_9656
  simp only [CollatzResearch.WordTrace]
  refine ⟨176091626512717979308411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 234788835350290639077881 176091626512717979308411)
  ·
    refine ⟨264137439769076968962617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176091626512717979308411 264137439769076968962617)
    ·
      refine ⟨198103079826807726721963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264137439769076968962617 198103079826807726721963)
      ·
        refine ⟨297154619740211590082945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198103079826807726721963 297154619740211590082945)
        ·
          refine ⟨222865964805158692562209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297154619740211590082945 222865964805158692562209)
          ·
            refine ⟨167149473603869019421657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222865964805158692562209 167149473603869019421657)
            ·
              refine ⟨125362105202901764566243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167149473603869019421657 125362105202901764566243)
              ·
                refine ⟨188043157804352646849365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125362105202901764566243 188043157804352646849365)
                ·
                  refine ⟨1101815377759878790133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 188043157804352646849365 1101815377759878790133)
                  ·
                    rfl

theorem cell22_9656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_9656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9656 prefixEnd_9656 := by exact prefixLift 9656
  have htrace : WordTrace (prefixWord ++ tailWord_9656) baseStart_9656 baseEnd_9656 := by
    simpa [prefixWord, tailWord_9656, baseEnd_9656] using wordTrace_append hprefix tailTrace_9656
  have hstable : (prefixWord ++ tailWord_9656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9656).length < 2 ^ (prefixWord ++ tailWord_9656).sum := by decide
  have hdescent : baseEnd_9656 < baseStart_9656 := by decide
  rcases family_descends (prefixWord ++ tailWord_9656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9720 : List Nat := [2, 1, 2, 1, 1, 6, 1, 3, 1, 4]
def baseStart_9720 : Nat := 118140960795 + 9720 * 2 ^ 59
def prefixEnd_9720 : Nat := 4983230072969 + 3 ^ 40 * 9720 * 2
def baseEnd_9720 : Nat := 3327354641204802770203

theorem tailTrace_9720 : CollatzResearch.WordTrace tailWord_9720 prefixEnd_9720 3327354641204802770203 := by
  unfold tailWord_9720
  simp only [CollatzResearch.WordTrace]
  refine ⟨177258762396787444473307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 236345016529049925964409 177258762396787444473307)
  ·
    refine ⟨265888143595181166709961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177258762396787444473307 265888143595181166709961)
    ·
      refine ⟨199416107696385875032471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265888143595181166709961 199416107696385875032471)
      ·
        refine ⟨299124161544578812548707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199416107696385875032471 299124161544578812548707)
        ·
          refine ⟨448686242316868218823061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299124161544578812548707 448686242316868218823061)
          ·
            refine ⟨21032167608603197757331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 448686242316868218823061 21032167608603197757331)
            ·
              refine ⟨31548251412904796635997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21032167608603197757331 31548251412904796635997)
              ·
                refine ⟨11830594279839298738499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31548251412904796635997 11830594279839298738499)
                ·
                  refine ⟨17745891419758948107749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11830594279839298738499 17745891419758948107749)
                  ·
                    refine ⟨3327354641204802770203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17745891419758948107749 3327354641204802770203)
                    ·
                      rfl

theorem cell22_9720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_9720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9720 prefixEnd_9720 := by exact prefixLift 9720
  have htrace : WordTrace (prefixWord ++ tailWord_9720) baseStart_9720 baseEnd_9720 := by
    simpa [prefixWord, tailWord_9720, baseEnd_9720] using wordTrace_append hprefix tailTrace_9720
  have hstable : (prefixWord ++ tailWord_9720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9720).length < 2 ^ (prefixWord ++ tailWord_9720).sum := by decide
  have hdescent : baseEnd_9720 < baseStart_9720 := by decide
  rcases family_descends (prefixWord ++ tailWord_9720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9735 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 6]
def baseStart_9735 : Nat := 118140960795 + 9735 * 2 ^ 59
def prefixEnd_9735 : Nat := 4983230072969 + 3 ^ 40 * 9735 * 2
def baseEnd_9735 : Nat := 1110829815916587881719

theorem tailTrace_9735 : CollatzResearch.WordTrace tailWord_9735 prefixEnd_9735 1110829815916587881719 := by
  unfold tailWord_9735
  simp only [CollatzResearch.WordTrace]
  refine ⟨355064619739232450742659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 236709746492821633828439 355064619739232450742659)
  ·
    refine ⟨532596929608848676113989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 355064619739232450742659 532596929608848676113989)
    ·
      refine ⟨99861924301659126771373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 532596929608848676113989 99861924301659126771373)
      ·
        refine ⟨37448221613122172539265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99861924301659126771373 37448221613122172539265)
        ·
          refine ⟨28086166209841629404449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37448221613122172539265 28086166209841629404449)
          ·
            refine ⟨21064624657381222053337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28086166209841629404449 21064624657381222053337)
            ·
              refine ⟨15798468493035916540003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21064624657381222053337 15798468493035916540003)
              ·
                refine ⟨23697702739553874810005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15798468493035916540003 23697702739553874810005)
                ·
                  refine ⟨1110829815916587881719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23697702739553874810005 1110829815916587881719)
                  ·
                    rfl

theorem cell22_9735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 6].length) (baseStart_9735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9735 prefixEnd_9735 := by exact prefixLift 9735
  have htrace : WordTrace (prefixWord ++ tailWord_9735) baseStart_9735 baseEnd_9735 := by
    simpa [prefixWord, tailWord_9735, baseEnd_9735] using wordTrace_append hprefix tailTrace_9735
  have hstable : (prefixWord ++ tailWord_9735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9735).length < 2 ^ (prefixWord ++ tailWord_9735).sum := by decide
  have hdescent : baseEnd_9735 < baseStart_9735 := by decide
  rcases family_descends (prefixWord ++ tailWord_9735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9741 : List Nat := [1, 7, 1, 1, 2, 1, 3, 1, 5]
def baseStart_9741 : Nat := 118140960795 + 9741 * 2 ^ 59
def prefixEnd_9741 : Nat := 4983230072969 + 3 ^ 40 * 9741 * 2
def baseEnd_9741 : Nat := 1111514456789249331713

theorem tailTrace_9741 : CollatzResearch.WordTrace tailWord_9741 prefixEnd_9741 1111514456789249331713 := by
  unfold tailWord_9741
  simp only [CollatzResearch.WordTrace]
  refine ⟨355283457717495475461077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 236855638478330316974051 355283457717495475461077)
  ·
    refine ⟨8326956040253800206119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 355283457717495475461077 8326956040253800206119)
    ·
      refine ⟨12490434060380700309179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8326956040253800206119 12490434060380700309179)
      ·
        refine ⟨18735651090571050463769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12490434060380700309179 18735651090571050463769)
        ·
          refine ⟨14051738317928287847827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18735651090571050463769 14051738317928287847827)
          ·
            refine ⟨21077607476892431771741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14051738317928287847827 21077607476892431771741)
            ·
              refine ⟨7904102803834661914403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21077607476892431771741 7904102803834661914403)
              ·
                refine ⟨11856154205751992871605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7904102803834661914403 11856154205751992871605)
                ·
                  refine ⟨1111514456789249331713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11856154205751992871605 1111514456789249331713)
                  ·
                    rfl

theorem cell22_9741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_9741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9741 prefixEnd_9741 := by exact prefixLift 9741
  have htrace : WordTrace (prefixWord ++ tailWord_9741) baseStart_9741 baseEnd_9741 := by
    simpa [prefixWord, tailWord_9741, baseEnd_9741] using wordTrace_append hprefix tailTrace_9741
  have hstable : (prefixWord ++ tailWord_9741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9741).length < 2 ^ (prefixWord ++ tailWord_9741).sum := by decide
  have hdescent : baseEnd_9741 < baseStart_9741 := by decide
  rcases family_descends (prefixWord ++ tailWord_9741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9823 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 6, 5]
def baseStart_9823 : Nat := 118140960795 + 9823 * 2 ^ 59
def prefixEnd_9823 : Nat := 4983230072969 + 3 ^ 40 * 9823 * 2
def baseEnd_9823 : Nat := 3362613646146867444887

theorem tailTrace_9823 : CollatzResearch.WordTrace tailWord_9823 prefixEnd_9823 3362613646146867444887 := by
  unfold tailWord_9823
  simp only [CollatzResearch.WordTrace]
  refine ⟨358274243420423479946123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 238849495613615653297415 358274243420423479946123)
  ·
    refine ⟨537411365130635219919185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 358274243420423479946123 537411365130635219919185)
    ·
      refine ⟨403058523847976414939389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 537411365130635219919185 403058523847976414939389)
      ·
        refine ⟨151146946442991155602271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 403058523847976414939389 151146946442991155602271)
        ·
          refine ⟨226720419664486733403407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151146946442991155602271 226720419664486733403407)
          ·
            refine ⟨340080629496730100105111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226720419664486733403407 340080629496730100105111)
            ·
              refine ⟨510120944245095150157667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340080629496730100105111 510120944245095150157667)
              ·
                refine ⟨765181416367642725236501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510120944245095150157667 765181416367642725236501)
                ·
                  refine ⟨35867878892233252745461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 765181416367642725236501 35867878892233252745461)
                  ·
                    refine ⟨3362613646146867444887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35867878892233252745461 3362613646146867444887)
                    ·
                      rfl

theorem cell22_9823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_9823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9823 prefixEnd_9823 := by exact prefixLift 9823
  have htrace : WordTrace (prefixWord ++ tailWord_9823) baseStart_9823 baseEnd_9823 := by
    simpa [prefixWord, tailWord_9823, baseEnd_9823] using wordTrace_append hprefix tailTrace_9823
  have hstable : (prefixWord ++ tailWord_9823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9823).length < 2 ^ (prefixWord ++ tailWord_9823).sum := by decide
  have hdescent : baseEnd_9823 < baseStart_9823 := by decide
  rcases family_descends (prefixWord ++ tailWord_9823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9842 : List Nat := [3, 2, 1, 2, 3, 2, 2, 2, 5]
def baseStart_9842 : Nat := 118140960795 + 9842 * 2 ^ 59
def prefixEnd_9842 : Nat := 4983230072969 + 3 ^ 40 * 9842 * 2
def baseEnd_9842 : Nat := 1123039244812383739943

theorem tailTrace_9842 : CollatzResearch.WordTrace tailWord_9842 prefixEnd_9842 1123039244812383739943 := by
  unfold tailWord_9842
  simp only [CollatzResearch.WordTrace]
  refine ⟨89741807587897431221945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 239311486901059816591853 89741807587897431221945)
  ·
    refine ⟨67306355690923073416459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89741807587897431221945 67306355690923073416459)
    ·
      refine ⟨100959533536384610124689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67306355690923073416459 100959533536384610124689)
      ·
        refine ⟨75719650152288457593517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100959533536384610124689 75719650152288457593517)
        ·
          refine ⟨28394868807108171597569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75719650152288457593517 28394868807108171597569)
          ·
            refine ⟨21296151605331128698177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28394868807108171597569 21296151605331128698177)
            ·
              refine ⟨15972113703998346523633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21296151605331128698177 15972113703998346523633)
              ·
                refine ⟨11979085277998759892725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15972113703998346523633 11979085277998759892725)
                ·
                  refine ⟨1123039244812383739943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11979085277998759892725 1123039244812383739943)
                  ·
                    rfl

theorem cell22_9842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_9842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9842 prefixEnd_9842 := by exact prefixLift 9842
  have htrace : WordTrace (prefixWord ++ tailWord_9842) baseStart_9842 baseEnd_9842 := by
    simpa [prefixWord, tailWord_9842, baseEnd_9842] using wordTrace_append hprefix tailTrace_9842
  have hstable : (prefixWord ++ tailWord_9842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9842).length < 2 ^ (prefixWord ++ tailWord_9842).sum := by decide
  have hdescent : baseEnd_9842 < baseStart_9842 := by decide
  rcases family_descends (prefixWord ++ tailWord_9842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9846 : List Nat := [5, 1, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_9846 : Nat := 118140960795 + 9846 * 2 ^ 59
def prefixEnd_9846 : Nat := 4983230072969 + 3 ^ 40 * 9846 * 2
def baseEnd_9846 : Nat := 3370487016182474119817

theorem tailTrace_9846 : CollatzResearch.WordTrace tailWord_9846 prefixEnd_9846 3370487016182474119817 := by
  unfold tailWord_9846
  simp only [CollatzResearch.WordTrace]
  refine ⟨22444570146068650502087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 239408748224732272022261 22444570146068650502087)
  ·
    refine ⟨33666855219102975753131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22444570146068650502087 33666855219102975753131)
    ·
      refine ⟨50500282828654463629697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33666855219102975753131 50500282828654463629697)
      ·
        refine ⟨37875212121490847722273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50500282828654463629697 37875212121490847722273)
        ·
          refine ⟨28406409091118135791705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37875212121490847722273 28406409091118135791705)
          ·
            refine ⟨21304806818338601843779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28406409091118135791705 21304806818338601843779)
            ·
              refine ⟨31957210227507902765669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21304806818338601843779 31957210227507902765669)
              ·
                refine ⟨5991976917657731768563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31957210227507902765669 5991976917657731768563)
                ·
                  refine ⟨8987965376486597652845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5991976917657731768563 8987965376486597652845)
                  ·
                    refine ⟨3370487016182474119817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8987965376486597652845 3370487016182474119817)
                    ·
                      rfl

theorem cell22_9846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_9846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9846 prefixEnd_9846 := by exact prefixLift 9846
  have htrace : WordTrace (prefixWord ++ tailWord_9846) baseStart_9846 baseEnd_9846 := by
    simpa [prefixWord, tailWord_9846, baseEnd_9846] using wordTrace_append hprefix tailTrace_9846
  have hstable : (prefixWord ++ tailWord_9846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9846).length < 2 ^ (prefixWord ++ tailWord_9846).sum := by decide
  have hdescent : baseEnd_9846 < baseStart_9846 := by decide
  rcases family_descends (prefixWord ++ tailWord_9846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9870 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_9870 : Nat := 118140960795 + 9870 * 2 ^ 59
def prefixEnd_9870 : Nat := 4983230072969 + 3 ^ 40 * 9870 * 2
def baseEnd_9870 : Nat := 1126234235551470506581

theorem tailTrace_9870 : CollatzResearch.WordTrace tailWord_9870 prefixEnd_9870 1126234235551470506581 := by
  unfold tailWord_9870
  simp only [CollatzResearch.WordTrace]
  refine ⟨44998559281268813363383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 239992316166767004604709 44998559281268813363383)
  ·
    refine ⟨67497838921903220045075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44998559281268813363383 67497838921903220045075)
    ·
      refine ⟨101246758382854830067613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67497838921903220045075 101246758382854830067613)
      ·
        refine ⟨37967534393570561275355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101246758382854830067613 37967534393570561275355)
        ·
          refine ⟨56951301590355841913033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37967534393570561275355 56951301590355841913033)
          ·
            refine ⟨42713476192766881434775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56951301590355841913033 42713476192766881434775)
            ·
              refine ⟨64070214289150322152163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42713476192766881434775 64070214289150322152163)
              ·
                refine ⟨96105321433725483228245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64070214289150322152163 96105321433725483228245)
                ·
                  refine ⟨1126234235551470506581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 96105321433725483228245 1126234235551470506581)
                  ·
                    rfl

theorem cell22_9870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_9870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9870 prefixEnd_9870 := by exact prefixLift 9870
  have htrace : WordTrace (prefixWord ++ tailWord_9870) baseStart_9870 baseEnd_9870 := by
    simpa [prefixWord, tailWord_9870, baseEnd_9870] using wordTrace_append hprefix tailTrace_9870
  have hstable : (prefixWord ++ tailWord_9870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9870).length < 2 ^ (prefixWord ++ tailWord_9870).sum := by decide
  have hdescent : baseEnd_9870 < baseStart_9870 := by decide
  rcases family_descends (prefixWord ++ tailWord_9870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9889 : List Nat := [1, 2, 3, 3, 2, 1, 4, 1, 1, 4]
def baseStart_9889 : Nat := 118140960795 + 9889 * 2 ^ 59
def prefixEnd_9889 : Nat := 4983230072969 + 3 ^ 40 * 9889 * 2
def baseEnd_9889 : Nat := 3385206794944695294685

theorem tailTrace_9889 : CollatzResearch.WordTrace tailWord_9889 prefixEnd_9889 3385206794944695294685 := by
  unfold tailWord_9889
  simp only [CollatzResearch.WordTrace]
  refine ⟨360681461181316751848721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 240454307454211167899147 360681461181316751848721)
  ·
    refine ⟨270511095885987563886541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 360681461181316751848721 270511095885987563886541)
    ·
      refine ⟨101441660957245336457453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270511095885987563886541 101441660957245336457453)
      ·
        refine ⟨38040622858967001171545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101441660957245336457453 38040622858967001171545)
        ·
          refine ⟨28530467144225250878659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38040622858967001171545 28530467144225250878659)
          ·
            refine ⟨42795700716337876317989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28530467144225250878659 42795700716337876317989)
            ·
              refine ⟨8024193884313351809623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42795700716337876317989 8024193884313351809623)
              ·
                refine ⟨12036290826470027714435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8024193884313351809623 12036290826470027714435)
                ·
                  refine ⟨18054436239705041571653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12036290826470027714435 18054436239705041571653)
                  ·
                    refine ⟨3385206794944695294685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18054436239705041571653 3385206794944695294685)
                    ·
                      rfl

theorem cell22_9889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_9889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9889 prefixEnd_9889 := by exact prefixLift 9889
  have htrace : WordTrace (prefixWord ++ tailWord_9889) baseStart_9889 baseEnd_9889 := by
    simpa [prefixWord, tailWord_9889, baseEnd_9889] using wordTrace_append hprefix tailTrace_9889
  have hstable : (prefixWord ++ tailWord_9889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9889).length < 2 ^ (prefixWord ++ tailWord_9889).sum := by decide
  have hdescent : baseEnd_9889 < baseStart_9889 := by decide
  rcases family_descends (prefixWord ++ tailWord_9889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9919 : List Nat := [1, 1, 2, 2, 2, 3, 5, 1, 2, 3]
def baseStart_9919 : Nat := 118140960795 + 9919 * 2 ^ 59
def prefixEnd_9919 : Nat := 4983230072969 + 3 ^ 40 * 9919 * 2
def baseEnd_9919 : Nat := 3395476408034617044593

theorem tailTrace_9919 : CollatzResearch.WordTrace tailWord_9919 prefixEnd_9919 3395476408034617044593 := by
  unfold tailWord_9919
  simp only [CollatzResearch.WordTrace]
  refine ⟨361775651072631875440811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 241183767381754583627207 361775651072631875440811)
  ·
    refine ⟨542663476608947813161217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 361775651072631875440811 542663476608947813161217)
    ·
      refine ⟨406997607456710859870913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 542663476608947813161217 406997607456710859870913)
      ·
        refine ⟨305248205592533144903185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406997607456710859870913 305248205592533144903185)
        ·
          refine ⟨228936154194399858677389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305248205592533144903185 228936154194399858677389)
          ·
            refine ⟨85851057822899947004021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228936154194399858677389 85851057822899947004021)
            ·
              refine ⟨8048536670896870031627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85851057822899947004021 8048536670896870031627)
              ·
                refine ⟨12072805006345305047441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8048536670896870031627 12072805006345305047441)
                ·
                  refine ⟨9054603754758978785581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12072805006345305047441 9054603754758978785581)
                  ·
                    refine ⟨3395476408034617044593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9054603754758978785581 3395476408034617044593)
                    ·
                      rfl

theorem cell22_9919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 2, 3].length) (baseStart_9919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9919 prefixEnd_9919 := by exact prefixLift 9919
  have htrace : WordTrace (prefixWord ++ tailWord_9919) baseStart_9919 baseEnd_9919 := by
    simpa [prefixWord, tailWord_9919, baseEnd_9919] using wordTrace_append hprefix tailTrace_9919
  have hstable : (prefixWord ++ tailWord_9919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9919).length < 2 ^ (prefixWord ++ tailWord_9919).sum := by decide
  have hdescent : baseEnd_9919 < baseStart_9919 := by decide
  rcases family_descends (prefixWord ++ tailWord_9919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9932 : List Nat := [2, 2, 1, 5, 2, 1, 1, 8]
def baseStart_9932 : Nat := 118140960795 + 9932 * 2 ^ 59
def prefixEnd_9932 : Nat := 4983230072969 + 3 ^ 40 * 9932 * 2
def baseEnd_9932 : Nat := 377769619300768496617

theorem tailTrace_9932 : CollatzResearch.WordTrace tailWord_9932 prefixEnd_9932 377769619300768496617 := by
  unfold tailWord_9932
  simp only [CollatzResearch.WordTrace]
  refine ⟨181124900012767547832025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 241499866683690063776033 181124900012767547832025)
  ·
    refine ⟨135843675009575660874019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181124900012767547832025 135843675009575660874019)
    ·
      refine ⟨203765512514363491311029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135843675009575660874019 203765512514363491311029)
      ·
        refine ⟨19103016798221577310409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203765512514363491311029 19103016798221577310409)
        ·
          refine ⟨14327262598666182982807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19103016798221577310409 14327262598666182982807)
          ·
            refine ⟨21490893897999274474211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14327262598666182982807 21490893897999274474211)
            ·
              refine ⟨32236340846998911711317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21490893897999274474211 32236340846998911711317)
              ·
                refine ⟨377769619300768496617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 32236340846998911711317 377769619300768496617)
                ·
                  rfl

theorem cell22_9932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 8].length) (baseStart_9932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9932 prefixEnd_9932 := by exact prefixLift 9932
  have htrace : WordTrace (prefixWord ++ tailWord_9932) baseStart_9932 baseEnd_9932 := by
    simpa [prefixWord, tailWord_9932, baseEnd_9932] using wordTrace_append hprefix tailTrace_9932
  have hstable : (prefixWord ++ tailWord_9932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9932).length < 2 ^ (prefixWord ++ tailWord_9932).sum := by decide
  have hdescent : baseEnd_9932 < baseStart_9932 := by decide
  rcases family_descends (prefixWord ++ tailWord_9932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9949 : List Nat := [1, 4, 3, 3, 1, 2, 8]
def baseStart_9949 : Nat := 118140960795 + 9949 * 2 ^ 59
def prefixEnd_9949 : Nat := 4983230072969 + 3 ^ 40 * 9949 * 2
def baseEnd_9949 : Nat := 126138741523131066463

theorem tailTrace_9949 : CollatzResearch.WordTrace tailWord_9949 prefixEnd_9949 126138741523131066463 := by
  unfold tailWord_9949
  simp only [CollatzResearch.WordTrace]
  refine ⟨362869840963946999032901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 241913227309297999355267 362869840963946999032901)
  ·
    refine ⟨68038095180740062318669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 362869840963946999032901 68038095180740062318669)
    ·
      refine ⟨25514285692777523369501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68038095180740062318669 25514285692777523369501)
      ·
        refine ⟨9567857134791571263563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25514285692777523369501 9567857134791571263563)
        ·
          refine ⟨14351785702187356895345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9567857134791571263563 14351785702187356895345)
          ·
            refine ⟨10763839276640517671509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14351785702187356895345 10763839276640517671509)
            ·
              refine ⟨126138741523131066463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 10763839276640517671509 126138741523131066463)
              ·
                rfl

theorem cell22_9949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 8].length) (baseStart_9949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9949 prefixEnd_9949 := by exact prefixLift 9949
  have htrace : WordTrace (prefixWord ++ tailWord_9949) baseStart_9949 baseEnd_9949 := by
    simpa [prefixWord, tailWord_9949, baseEnd_9949] using wordTrace_append hprefix tailTrace_9949
  have hstable : (prefixWord ++ tailWord_9949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9949).length < 2 ^ (prefixWord ++ tailWord_9949).sum := by decide
  have hdescent : baseEnd_9949 < baseStart_9949 := by decide
  rcases family_descends (prefixWord ++ tailWord_9949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9964 : List Nat := [2, 2, 1, 1, 2, 2, 2, 6, 1, 3]
def baseStart_9964 : Nat := 118140960795 + 9964 * 2 ^ 59
def prefixEnd_9964 : Nat := 4983230072969 + 3 ^ 40 * 9964 * 2
def baseEnd_9964 : Nat := 3410880827669499669455

theorem tailTrace_9964 : CollatzResearch.WordTrace tailWord_9964 prefixEnd_9964 3410880827669499669455 := by
  unfold tailWord_9964
  simp only [CollatzResearch.WordTrace]
  refine ⟨181708467954802280414473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 242277957273069707219297 181708467954802280414473)
  ·
    refine ⟨136281350966101710310855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181708467954802280414473 136281350966101710310855)
    ·
      refine ⟨204422026449152565466283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136281350966101710310855 204422026449152565466283)
      ·
        refine ⟨306633039673728848199425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204422026449152565466283 306633039673728848199425)
        ·
          refine ⟨229974779755296636149569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306633039673728848199425 229974779755296636149569)
          ·
            refine ⟨172481084816472477112177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229974779755296636149569 172481084816472477112177)
            ·
              refine ⟨129360813612354357834133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172481084816472477112177 129360813612354357834133)
              ·
                refine ⟨6063788138079110523475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129360813612354357834133 6063788138079110523475)
                ·
                  refine ⟨9095682207118665785213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6063788138079110523475 9095682207118665785213)
                  ·
                    refine ⟨3410880827669499669455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9095682207118665785213 3410880827669499669455)
                    ·
                      rfl

theorem cell22_9964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_9964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9964 prefixEnd_9964 := by exact prefixLift 9964
  have htrace : WordTrace (prefixWord ++ tailWord_9964) baseStart_9964 baseEnd_9964 := by
    simpa [prefixWord, tailWord_9964, baseEnd_9964] using wordTrace_append hprefix tailTrace_9964
  have hstable : (prefixWord ++ tailWord_9964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9964).length < 2 ^ (prefixWord ++ tailWord_9964).sum := by decide
  have hdescent : baseEnd_9964 < baseStart_9964 := by decide
  rcases family_descends (prefixWord ++ tailWord_9964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9975 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 2, 5]
def baseStart_9975 : Nat := 118140960795 + 9975 * 2 ^ 59
def prefixEnd_9975 : Nat := 4983230072969 + 3 ^ 40 * 9975 * 2
def baseEnd_9975 : Nat := 3414646352469137644421

theorem tailTrace_9975 : CollatzResearch.WordTrace tailWord_9975 prefixEnd_9975 3414646352469137644421 := by
  unfold tailWord_9975
  simp only [CollatzResearch.WordTrace]
  refine ⟨363818138869753439479379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 242545425913168959652919 363818138869753439479379)
  ·
    refine ⟨545727208304630159219069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 363818138869753439479379 545727208304630159219069)
    ·
      refine ⟨204647703114236309707151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 545727208304630159219069 204647703114236309707151)
      ·
        refine ⟨306971554671354464560727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204647703114236309707151 306971554671354464560727)
        ·
          refine ⟨460457332007031696841091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306971554671354464560727 460457332007031696841091)
          ·
            refine ⟨690685998010547545261637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460457332007031696841091 690685998010547545261637)
            ·
              refine ⟨129503624626977664736557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 690685998010547545261637 129503624626977664736557)
              ·
                refine ⟨48563859235116624276209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129503624626977664736557 48563859235116624276209)
                ·
                  refine ⟨36422894426337468207157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48563859235116624276209 36422894426337468207157)
                  ·
                    refine ⟨3414646352469137644421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36422894426337468207157 3414646352469137644421)
                    ·
                      rfl

theorem cell22_9975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_9975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_9975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_9975 prefixEnd_9975 := by exact prefixLift 9975
  have htrace : WordTrace (prefixWord ++ tailWord_9975) baseStart_9975 baseEnd_9975 := by
    simpa [prefixWord, tailWord_9975, baseEnd_9975] using wordTrace_append hprefix tailTrace_9975
  have hstable : (prefixWord ++ tailWord_9975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9975).length < 2 ^ (prefixWord ++ tailWord_9975).sum := by decide
  have hdescent : baseEnd_9975 < baseStart_9975 := by decide
  rcases family_descends (prefixWord ++ tailWord_9975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10133 : List Nat := [1, 3, 2, 1, 1, 3, 5, 2, 1, 3]
def baseStart_10133 : Nat := 118140960795 + 10133 * 2 ^ 59
def prefixEnd_10133 : Nat := 4983230072969 + 3 ^ 40 * 10133 * 2
def baseEnd_10133 : Nat := 3468732981409392193937

theorem tailTrace_10133 : CollatzResearch.WordTrace tailWord_10133 prefixEnd_10133 3468732981409392193937 := by
  unfold tailWord_10133
  simp only [CollatzResearch.WordTrace]
  refine ⟨369580872297346423731053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 246387248198230949154035 369580872297346423731053)
  ·
    refine ⟨138592827111504908899145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 369580872297346423731053 138592827111504908899145)
    ·
      refine ⟨103944620333628681674359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138592827111504908899145 103944620333628681674359)
      ·
        refine ⟨155916930500443022511539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103944620333628681674359 155916930500443022511539)
        ·
          refine ⟨233875395750664533767309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155916930500443022511539 233875395750664533767309)
          ·
            refine ⟨87703273406499200162741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233875395750664533767309 87703273406499200162741)
            ·
              refine ⟨8222181881859300015257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87703273406499200162741 8222181881859300015257)
              ·
                refine ⟨6166636411394475011443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8222181881859300015257 6166636411394475011443)
                ·
                  refine ⟨9249954617091712517165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6166636411394475011443 9249954617091712517165)
                  ·
                    refine ⟨3468732981409392193937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9249954617091712517165 3468732981409392193937)
                    ·
                      rfl

theorem cell22_10133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_10133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10133 prefixEnd_10133 := by exact prefixLift 10133
  have htrace : WordTrace (prefixWord ++ tailWord_10133) baseStart_10133 baseEnd_10133 := by
    simpa [prefixWord, tailWord_10133, baseEnd_10133] using wordTrace_append hprefix tailTrace_10133
  have hstable : (prefixWord ++ tailWord_10133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10133).length < 2 ^ (prefixWord ++ tailWord_10133).sum := by decide
  have hdescent : baseEnd_10133 < baseStart_10133 := by decide
  rcases family_descends (prefixWord ++ tailWord_10133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10146 : List Nat := [3, 3, 1, 2, 3, 1, 1, 3, 5]
def baseStart_10146 : Nat := 118140960795 + 10146 * 2 ^ 59
def prefixEnd_10146 : Nat := 4983230072969 + 3 ^ 40 * 10146 * 2
def baseEnd_10146 : Nat := 1157727715693897206299

theorem tailTrace_10146 : CollatzResearch.WordTrace tailWord_10146 prefixEnd_10146 1157727715693897206299 := by
  unfold tailWord_10146
  simp only [CollatzResearch.WordTrace]
  refine ⟨92513755312562410988573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 246703347500166429302861 92513755312562410988573)
  ·
    refine ⟨34692658242210904120715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92513755312562410988573 34692658242210904120715)
    ·
      refine ⟨52038987363316356181073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34692658242210904120715 52038987363316356181073)
      ·
        refine ⟨39029240522487267135805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52038987363316356181073 39029240522487267135805)
        ·
          refine ⟨14635965195932725175927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39029240522487267135805 14635965195932725175927)
          ·
            refine ⟨21953947793899087763891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14635965195932725175927 21953947793899087763891)
            ·
              refine ⟨32930921690848631645837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21953947793899087763891 32930921690848631645837)
              ·
                refine ⟨12349095634068236867189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32930921690848631645837 12349095634068236867189)
                ·
                  refine ⟨1157727715693897206299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12349095634068236867189 1157727715693897206299)
                  ·
                    rfl

theorem cell22_10146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_10146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10146 prefixEnd_10146 := by exact prefixLift 10146
  have htrace : WordTrace (prefixWord ++ tailWord_10146) baseStart_10146 baseEnd_10146 := by
    simpa [prefixWord, tailWord_10146, baseEnd_10146] using wordTrace_append hprefix tailTrace_10146
  have hstable : (prefixWord ++ tailWord_10146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10146).length < 2 ^ (prefixWord ++ tailWord_10146).sum := by decide
  have hdescent : baseEnd_10146 < baseStart_10146 := by decide
  rcases family_descends (prefixWord ++ tailWord_10146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10176 : List Nat := [2, 1, 1, 2, 3, 2, 5, 1, 1, 4]
def baseStart_10176 : Nat := 118140960795 + 10176 * 2 ^ 59
def prefixEnd_10176 : Nat := 4983230072969 + 3 ^ 40 * 10176 * 2
def baseEnd_10176 : Nat := 3483452760171613368805

theorem tailTrace_10176 : CollatzResearch.WordTrace tailWord_10176 prefixEnd_10176 3483452760171613368805 := by
  unfold tailWord_10176
  simp only [CollatzResearch.WordTrace]
  refine ⟨185574605570782383773191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 247432807427709845030921 185574605570782383773191)
  ·
    refine ⟨278361908356173575659787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185574605570782383773191 278361908356173575659787)
    ·
      refine ⟨417542862534260363489681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278361908356173575659787 417542862534260363489681)
      ·
        refine ⟨313157146900695272617261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417542862534260363489681 313157146900695272617261)
        ·
          refine ⟨117433930087760727231473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313157146900695272617261 117433930087760727231473)
          ·
            refine ⟨88075447565820545423605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117433930087760727231473 88075447565820545423605)
            ·
              refine ⟨8257073209295676133463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88075447565820545423605 8257073209295676133463)
              ·
                refine ⟨12385609813943514200195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8257073209295676133463 12385609813943514200195)
                ·
                  refine ⟨18578414720915271300293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12385609813943514200195 18578414720915271300293)
                  ·
                    refine ⟨3483452760171613368805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18578414720915271300293 3483452760171613368805)
                    ·
                      rfl

theorem cell22_10176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 1, 4].length) (baseStart_10176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10176 prefixEnd_10176 := by exact prefixLift 10176
  have htrace : WordTrace (prefixWord ++ tailWord_10176) baseStart_10176 baseEnd_10176 := by
    simpa [prefixWord, tailWord_10176, baseEnd_10176] using wordTrace_append hprefix tailTrace_10176
  have hstable : (prefixWord ++ tailWord_10176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10176).length < 2 ^ (prefixWord ++ tailWord_10176).sum := by decide
  have hdescent : baseEnd_10176 < baseStart_10176 := by decide
  rcases family_descends (prefixWord ++ tailWord_10176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10251 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 3, 3]
def baseStart_10251 : Nat := 118140960795 + 10251 * 2 ^ 59
def prefixEnd_10251 : Nat := 4983230072969 + 3 ^ 40 * 10251 * 2
def baseEnd_10251 : Nat := 3509126792896417743575

theorem tailTrace_10251 : CollatzResearch.WordTrace tailWord_10251 prefixEnd_10251 3509126792896417743575 := by
  unfold tailWord_10251
  simp only [CollatzResearch.WordTrace]
  refine ⟨373884685869852576526607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 249256457246568384351071 373884685869852576526607)
  ·
    refine ⟨560827028804778864789911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 373884685869852576526607 560827028804778864789911)
    ·
      refine ⟨841240543207168297184867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 560827028804778864789911 841240543207168297184867)
      ·
        refine ⟨1261860814810752445777301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 841240543207168297184867 1261860814810752445777301)
        ·
          refine ⟨59149725694254020895811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1261860814810752445777301 59149725694254020895811)
          ·
            refine ⟨88724588541381031343717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59149725694254020895811 88724588541381031343717)
            ·
              refine ⟨16635860351508943376947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88724588541381031343717 16635860351508943376947)
              ·
                refine ⟨24953790527263415065421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16635860351508943376947 24953790527263415065421)
                ·
                  refine ⟨9357671447723780649533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24953790527263415065421 9357671447723780649533)
                  ·
                    refine ⟨3509126792896417743575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9357671447723780649533 3509126792896417743575)
                    ·
                      rfl

theorem cell22_10251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 3].length) (baseStart_10251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10251 prefixEnd_10251 := by exact prefixLift 10251
  have htrace : WordTrace (prefixWord ++ tailWord_10251) baseStart_10251 baseEnd_10251 := by
    simpa [prefixWord, tailWord_10251, baseEnd_10251] using wordTrace_append hprefix tailTrace_10251
  have hstable : (prefixWord ++ tailWord_10251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10251).length < 2 ^ (prefixWord ++ tailWord_10251).sum := by decide
  have hdescent : baseEnd_10251 < baseStart_10251 := by decide
  rcases family_descends (prefixWord ++ tailWord_10251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10302 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_10302 : Nat := 118140960795 + 10302 * 2 ^ 59
def prefixEnd_10302 : Nat := 4983230072969 + 3 ^ 40 * 10302 * 2
def baseEnd_10302 : Nat := 3526585135149284718419

theorem tailTrace_10302 : CollatzResearch.WordTrace tailWord_10302 prefixEnd_10302 3526585135149284718419 := by
  unfold tailWord_10302
  simp only [CollatzResearch.WordTrace]
  refine ⟨46968101085636035829145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 250496539123392191088773 46968101085636035829145)
  ·
    refine ⟨35226075814227026871859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46968101085636035829145 35226075814227026871859)
    ·
      refine ⟨52839113721340540307789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35226075814227026871859 52839113721340540307789)
      ·
        refine ⟨19814667645502702615421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52839113721340540307789 19814667645502702615421)
        ·
          refine ⟨7430500367063513480783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19814667645502702615421 7430500367063513480783)
          ·
            refine ⟨11145750550595270221175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7430500367063513480783 11145750550595270221175)
            ·
              refine ⟨16718625825892905331763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11145750550595270221175 16718625825892905331763)
              ·
                refine ⟨25077938738839357997645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16718625825892905331763 25077938738839357997645)
                ·
                  refine ⟨9404227027064759249117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25077938738839357997645 9404227027064759249117)
                  ·
                    refine ⟨3526585135149284718419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9404227027064759249117 3526585135149284718419)
                    ·
                      rfl

theorem cell22_10302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_10302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10302 prefixEnd_10302 := by exact prefixLift 10302
  have htrace : WordTrace (prefixWord ++ tailWord_10302) baseStart_10302 baseEnd_10302 := by
    simpa [prefixWord, tailWord_10302, baseEnd_10302] using wordTrace_append hprefix tailTrace_10302
  have hstable : (prefixWord ++ tailWord_10302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10302).length < 2 ^ (prefixWord ++ tailWord_10302).sum := by decide
  have hdescent : baseEnd_10302 < baseStart_10302 := by decide
  rcases family_descends (prefixWord ++ tailWord_10302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10328 : List Nat := [2, 1, 2, 2, 1, 6, 1, 2, 1, 4]
def baseStart_10328 : Nat := 118140960795 + 10328 * 2 ^ 59
def prefixEnd_10328 : Nat := 4983230072969 + 3 ^ 40 * 10328 * 2
def baseEnd_10328 : Nat := 3535485466493883568339

theorem tailTrace_10328 : CollatzResearch.WordTrace tailWord_10328 prefixEnd_10328 3535485466493883568339 := by
  unfold tailWord_10328
  simp only [CollatzResearch.WordTrace]
  refine ⟨188346553295447363539819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 251128737727263151386425 188346553295447363539819)
  ·
    refine ⟨282519829943171045309729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188346553295447363539819 282519829943171045309729)
    ·
      refine ⟨211889872457378283982297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 282519829943171045309729 211889872457378283982297)
      ·
        refine ⟨158917404343033712986723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211889872457378283982297 158917404343033712986723)
        ·
          refine ⟨238376106514550569480085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158917404343033712986723 238376106514550569480085)
          ·
            refine ⟨11173879992869557944379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 238376106514550569480085 11173879992869557944379)
            ·
              refine ⟨16760819989304336916569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11173879992869557944379 16760819989304336916569)
              ·
                refine ⟨12570614991978252687427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16760819989304336916569 12570614991978252687427)
                ·
                  refine ⟨18855922487967379031141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12570614991978252687427 18855922487967379031141)
                  ·
                    refine ⟨3535485466493883568339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18855922487967379031141 3535485466493883568339)
                    ·
                      rfl

theorem cell22_10328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_10328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10328 prefixEnd_10328 := by exact prefixLift 10328
  have htrace : WordTrace (prefixWord ++ tailWord_10328) baseStart_10328 baseEnd_10328 := by
    simpa [prefixWord, tailWord_10328, baseEnd_10328] using wordTrace_append hprefix tailTrace_10328
  have hstable : (prefixWord ++ tailWord_10328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10328).length < 2 ^ (prefixWord ++ tailWord_10328).sum := by decide
  have hdescent : baseEnd_10328 < baseStart_10328 := by decide
  rcases family_descends (prefixWord ++ tailWord_10328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10339 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 1, 6]
def baseStart_10339 : Nat := 118140960795 + 10339 * 2 ^ 59
def prefixEnd_10339 : Nat := 4983230072969 + 3 ^ 40 * 10339 * 2
def baseEnd_10339 : Nat := 3539250991293521543305

theorem tailTrace_10339 : CollatzResearch.WordTrace tailWord_10339 prefixEnd_10339 3539250991293521543305 := by
  unfold tailWord_10339
  simp only [CollatzResearch.WordTrace]
  refine ⟨377094309551043605730071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 251396206367362403820047 377094309551043605730071)
  ·
    refine ⟨565641464326565408595107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 377094309551043605730071 565641464326565408595107)
    ·
      refine ⟨848462196489848112892661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565641464326565408595107 848462196489848112892661)
      ·
        refine ⟨79543330920923260583687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 848462196489848112892661 79543330920923260583687)
        ·
          refine ⟨119314996381384890875531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79543330920923260583687 119314996381384890875531)
          ·
            refine ⟨178972494572077336313297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119314996381384890875531 178972494572077336313297)
            ·
              refine ⟨134229370929058002234973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178972494572077336313297 134229370929058002234973)
              ·
                refine ⟨50336014098396750838115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134229370929058002234973 50336014098396750838115)
                ·
                  refine ⟨75504021147595126257173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50336014098396750838115 75504021147595126257173)
                  ·
                    refine ⟨3539250991293521543305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75504021147595126257173 3539250991293521543305)
                    ·
                      rfl

theorem cell22_10339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 6].length) (baseStart_10339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10339 prefixEnd_10339 := by exact prefixLift 10339
  have htrace : WordTrace (prefixWord ++ tailWord_10339) baseStart_10339 baseEnd_10339 := by
    simpa [prefixWord, tailWord_10339, baseEnd_10339] using wordTrace_append hprefix tailTrace_10339
  have hstable : (prefixWord ++ tailWord_10339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10339).length < 2 ^ (prefixWord ++ tailWord_10339).sum := by decide
  have hdescent : baseEnd_10339 < baseStart_10339 := by decide
  rcases family_descends (prefixWord ++ tailWord_10339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10341 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_10341 : Nat := 118140960795 + 10341 * 2 ^ 59
def prefixEnd_10341 : Nat := 4983230072969 + 3 ^ 40 * 10341 * 2
def baseEnd_10341 : Nat := 3539935632166182993299

theorem tailTrace_10341 : CollatzResearch.WordTrace tailWord_10341 prefixEnd_10341 3539935632166182993299 := by
  unfold tailWord_10341
  simp only [CollatzResearch.WordTrace]
  refine ⟨377167255543797947302877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 251444837029198631535251 377167255543797947302877)
  ·
    refine ⟨141437720828924230238579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 377167255543797947302877 141437720828924230238579)
    ·
      refine ⟨212156581243386345357869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141437720828924230238579 212156581243386345357869)
      ·
        refine ⟨79558717966269879509201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212156581243386345357869 79558717966269879509201)
        ·
          refine ⟨59669038474702409631901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79558717966269879509201 59669038474702409631901)
          ·
            refine ⟨22375889428013403611963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59669038474702409631901 22375889428013403611963)
            ·
              refine ⟨33563834142020105417945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22375889428013403611963 33563834142020105417945)
              ·
                refine ⟨25172875606515079063459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33563834142020105417945 25172875606515079063459)
                ·
                  refine ⟨37759313409772618595189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25172875606515079063459 37759313409772618595189)
                  ·
                    refine ⟨3539935632166182993299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37759313409772618595189 3539935632166182993299)
                    ·
                      rfl

theorem cell22_10341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_10341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10341 prefixEnd_10341 := by exact prefixLift 10341
  have htrace : WordTrace (prefixWord ++ tailWord_10341) baseStart_10341 baseEnd_10341 := by
    simpa [prefixWord, tailWord_10341, baseEnd_10341] using wordTrace_append hprefix tailTrace_10341
  have hstable : (prefixWord ++ tailWord_10341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10341).length < 2 ^ (prefixWord ++ tailWord_10341).sum := by decide
  have hdescent : baseEnd_10341 < baseStart_10341 := by decide
  rcases family_descends (prefixWord ++ tailWord_10341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10354 : List Nat := [3, 2, 1, 2, 2, 12]
def baseStart_10354 : Nat := 118140960795 + 10354 * 2 ^ 59
def prefixEnd_10354 : Nat := 4983230072969 + 3 ^ 40 * 10354 * 2
def baseEnd_10354 : Nat := 43757849356030647139

theorem tailTrace_10354 : CollatzResearch.WordTrace tailWord_10354 prefixEnd_10354 43757849356030647139 := by
  unfold tailWord_10354
  simp only [CollatzResearch.WordTrace]
  refine ⟨94410351124175291881529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 251760936331134111684077 94410351124175291881529)
  ·
    refine ⟨70807763343131468911147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94410351124175291881529 70807763343131468911147)
    ·
      refine ⟨106211645014697203366721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70807763343131468911147 106211645014697203366721)
      ·
        refine ⟨79658733761022902525041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106211645014697203366721 79658733761022902525041)
        ·
          refine ⟨59744050320767176893781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79658733761022902525041 59744050320767176893781)
          ·
            refine ⟨43757849356030647139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 59744050320767176893781 43757849356030647139)
            ·
              rfl

theorem cell22_10354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 12].length) (baseStart_10354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10354 prefixEnd_10354 := by exact prefixLift 10354
  have htrace : WordTrace (prefixWord ++ tailWord_10354) baseStart_10354 baseEnd_10354 := by
    simpa [prefixWord, tailWord_10354, baseEnd_10354] using wordTrace_append hprefix tailTrace_10354
  have hstable : (prefixWord ++ tailWord_10354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10354).length < 2 ^ (prefixWord ++ tailWord_10354).sum := by decide
  have hdescent : baseEnd_10354 < baseStart_10354 := by decide
  rcases family_descends (prefixWord ++ tailWord_10354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10371 : List Nat := [1, 1, 1, 3, 3, 5, 1, 7]
def baseStart_10371 : Nat := 118140960795 + 10371 * 2 ^ 59
def prefixEnd_10371 : Nat := 4983230072969 + 3 ^ 40 * 10371 * 2
def baseEnd_10371 : Nat := 394467249472900527023

theorem tailTrace_10371 : CollatzResearch.WordTrace tailWord_10371 prefixEnd_10371 394467249472900527023 := by
  unfold tailWord_10371
  simp only [CollatzResearch.WordTrace]
  refine ⟨378261445435113070894967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 252174296956742047263311 378261445435113070894967)
  ·
    refine ⟨567392168152669606342451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 378261445435113070894967 567392168152669606342451)
    ·
      refine ⟨851088252229004409513677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 567392168152669606342451 851088252229004409513677)
      ·
        refine ⟨319158094585876653567629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 851088252229004409513677 319158094585876653567629)
        ·
          refine ⟨119684285469703745087861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319158094585876653567629 119684285469703745087861)
          ·
            refine ⟨11220401762784726101987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119684285469703745087861 11220401762784726101987)
            ·
              refine ⟨16830602644177089152981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11220401762784726101987 16830602644177089152981)
              ·
                refine ⟨394467249472900527023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16830602644177089152981 394467249472900527023)
                ·
                  rfl

theorem cell22_10371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 7].length) (baseStart_10371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10371 prefixEnd_10371 := by exact prefixLift 10371
  have htrace : WordTrace (prefixWord ++ tailWord_10371) baseStart_10371 baseEnd_10371 := by
    simpa [prefixWord, tailWord_10371, baseEnd_10371] using wordTrace_append hprefix tailTrace_10371
  have hstable : (prefixWord ++ tailWord_10371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10371).length < 2 ^ (prefixWord ++ tailWord_10371).sum := by decide
  have hdescent : baseEnd_10371 < baseStart_10371 := by decide
  rcases family_descends (prefixWord ++ tailWord_10371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10384 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 2, 6]
def baseStart_10384 : Nat := 118140960795 + 10384 * 2 ^ 59
def prefixEnd_10384 : Nat := 4983230072969 + 3 ^ 40 * 10384 * 2
def baseEnd_10384 : Nat := 3554655410928404168167

theorem tailTrace_10384 : CollatzResearch.WordTrace tailWord_10384 prefixEnd_10384 3554655410928404168167 := by
  unfold tailWord_10384
  simp only [CollatzResearch.WordTrace]
  refine ⟨189367797194008145559103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 252490396258677527412137 189367797194008145559103)
  ·
    refine ⟨284051695791012218338655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189367797194008145559103 284051695791012218338655)
    ·
      refine ⟨426077543686518327507983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284051695791012218338655 426077543686518327507983)
      ·
        refine ⟨639116315529777491261975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426077543686518327507983 639116315529777491261975)
        ·
          refine ⟨958674473294666236892963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639116315529777491261975 958674473294666236892963)
          ·
            refine ⟨1438011709941999355339445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958674473294666236892963 1438011709941999355339445)
            ·
              refine ⟨134813597807062439563073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1438011709941999355339445 134813597807062439563073)
              ·
                refine ⟨101110198355296829672305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134813597807062439563073 101110198355296829672305)
                ·
                  refine ⟨75832648766472622254229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101110198355296829672305 75832648766472622254229)
                  ·
                    refine ⟨3554655410928404168167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75832648766472622254229 3554655410928404168167)
                    ·
                      rfl

theorem cell22_10384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_10384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10384 prefixEnd_10384 := by exact prefixLift 10384
  have htrace : WordTrace (prefixWord ++ tailWord_10384) baseStart_10384 baseEnd_10384 := by
    simpa [prefixWord, tailWord_10384, baseEnd_10384] using wordTrace_append hprefix tailTrace_10384
  have hstable : (prefixWord ++ tailWord_10384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10384).length < 2 ^ (prefixWord ++ tailWord_10384).sum := by decide
  have hdescent : baseEnd_10384 < baseStart_10384 := by decide
  rcases family_descends (prefixWord ++ tailWord_10384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10454 : List Nat := [5, 2, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_10454 : Nat := 118140960795 + 10454 * 2 ^ 59
def prefixEnd_10454 : Nat := 4983230072969 + 3 ^ 40 * 10454 * 2
def baseEnd_10454 : Nat := 3578617841471554917953

theorem tailTrace_10454 : CollatzResearch.WordTrace tailWord_10454 prefixEnd_10454 3578617841471554917953 := by
  unfold tailWord_10454
  simp only [CollatzResearch.WordTrace]
  refine ⟨23830544008401140385401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 254192469422945497444277 23830544008401140385401)
  ·
    refine ⟨17872908006300855289051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23830544008401140385401 17872908006300855289051)
    ·
      refine ⟨26809362009451282933577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17872908006300855289051 26809362009451282933577)
      ·
        refine ⟨20107021507088462200183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26809362009451282933577 20107021507088462200183)
        ·
          refine ⟨30160532260632693300275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20107021507088462200183 30160532260632693300275)
          ·
            refine ⟨45240798390949039950413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30160532260632693300275 45240798390949039950413)
            ·
              refine ⟨16965299396605889981405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45240798390949039950413 16965299396605889981405)
              ·
                refine ⟨6361987273727208743027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16965299396605889981405 6361987273727208743027)
                ·
                  refine ⟨9542980910590813114541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6361987273727208743027 9542980910590813114541)
                  ·
                    refine ⟨3578617841471554917953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9542980910590813114541 3578617841471554917953)
                    ·
                      rfl

theorem cell22_10454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_10454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10454 prefixEnd_10454 := by exact prefixLift 10454
  have htrace : WordTrace (prefixWord ++ tailWord_10454) baseStart_10454 baseEnd_10454 := by
    simpa [prefixWord, tailWord_10454, baseEnd_10454] using wordTrace_append hprefix tailTrace_10454
  have hstable : (prefixWord ++ tailWord_10454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10454).length < 2 ^ (prefixWord ++ tailWord_10454).sum := by decide
  have hdescent : baseEnd_10454 < baseStart_10454 := by decide
  rcases family_descends (prefixWord ++ tailWord_10454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10506 : List Nat := [3, 1, 2, 2, 1, 1, 4, 8]
def baseStart_10506 : Nat := 118140960795 + 10506 * 2 ^ 59
def prefixEnd_10506 : Nat := 4983230072969 + 3 ^ 40 * 10506 * 2
def baseEnd_10506 : Nat := 399602056017861401977

theorem tailTrace_10506 : CollatzResearch.WordTrace tailWord_10506 prefixEnd_10506 399602056017861401977 := by
  unfold tailWord_10506
  simp only [CollatzResearch.WordTrace]
  refine ⟨95796324986507781764843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 255456866630687418039581 95796324986507781764843)
  ·
    refine ⟨143694487479761672647265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95796324986507781764843 143694487479761672647265)
    ·
      refine ⟨107770865609821254485449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143694487479761672647265 107770865609821254485449)
      ·
        refine ⟨80828149207365940864087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107770865609821254485449 80828149207365940864087)
        ·
          refine ⟨121242223811048911296131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80828149207365940864087 121242223811048911296131)
          ·
            refine ⟨181863335716573366944197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121242223811048911296131 181863335716573366944197)
            ·
              refine ⟨34099375446857506302037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181863335716573366944197 34099375446857506302037)
              ·
                refine ⟨399602056017861401977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 34099375446857506302037 399602056017861401977)
                ·
                  rfl

theorem cell22_10506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_10506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10506 prefixEnd_10506 := by exact prefixLift 10506
  have htrace : WordTrace (prefixWord ++ tailWord_10506) baseStart_10506 baseEnd_10506 := by
    simpa [prefixWord, tailWord_10506, baseEnd_10506] using wordTrace_append hprefix tailTrace_10506
  have hstable : (prefixWord ++ tailWord_10506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10506).length < 2 ^ (prefixWord ++ tailWord_10506).sum := by decide
  have hdescent : baseEnd_10506 < baseStart_10506 := by decide
  rcases family_descends (prefixWord ++ tailWord_10506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10508 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 2, 4]
def baseStart_10508 : Nat := 118140960795 + 10508 * 2 ^ 59
def prefixEnd_10508 : Nat := 4983230072969 + 3 ^ 40 * 10508 * 2
def baseEnd_10508 : Nat := 3597103145033414067787

theorem tailTrace_10508 : CollatzResearch.WordTrace tailWord_10508 prefixEnd_10508 3597103145033414067787 := by
  unfold tailWord_10508
  simp only [CollatzResearch.WordTrace]
  refine ⟨191629122969392734316089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 255505497292523645754785 191629122969392734316089)
  ·
    refine ⟨143721842227044550737067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191629122969392734316089 143721842227044550737067)
    ·
      refine ⟨215582763340566826105601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143721842227044550737067 215582763340566826105601)
      ·
        refine ⟨161687072505425119579201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215582763340566826105601 161687072505425119579201)
        ·
          refine ⟨121265304379068839684401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161687072505425119579201 121265304379068839684401)
          ·
            refine ⟨90948978284301629763301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121265304379068839684401 90948978284301629763301)
            ·
              refine ⟨17052933428306555580619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90948978284301629763301 17052933428306555580619)
              ·
                refine ⟨25579400142459833370929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17052933428306555580619 25579400142459833370929)
                ·
                  refine ⟨19184550106844875028197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25579400142459833370929 19184550106844875028197)
                  ·
                    refine ⟨3597103145033414067787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19184550106844875028197 3597103145033414067787)
                    ·
                      rfl

theorem cell22_10508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_10508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10508 prefixEnd_10508 := by exact prefixLift 10508
  have htrace : WordTrace (prefixWord ++ tailWord_10508) baseStart_10508 baseEnd_10508 := by
    simpa [prefixWord, tailWord_10508, baseEnd_10508] using wordTrace_append hprefix tailTrace_10508
  have hstable : (prefixWord ++ tailWord_10508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10508).length < 2 ^ (prefixWord ++ tailWord_10508).sum := by decide
  have hdescent : baseEnd_10508 < baseStart_10508 := by decide
  rcases family_descends (prefixWord ++ tailWord_10508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10572 : List Nat := [2, 2, 1, 3, 2, 1, 4, 3, 1, 3]
def baseStart_10572 : Nat := 118140960795 + 10572 * 2 ^ 59
def prefixEnd_10572 : Nat := 4983230072969 + 3 ^ 40 * 10572 * 2
def baseEnd_10572 : Nat := 3619011652958580467591

theorem tailTrace_10572 : CollatzResearch.WordTrace tailWord_10572 prefixEnd_10572 3619011652958580467591 := by
  unfold tailWord_10572
  simp only [CollatzResearch.WordTrace]
  refine ⟨192796258853462199480985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 257061678471282932641313 192796258853462199480985)
  ·
    refine ⟨144597194140096649610739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192796258853462199480985 144597194140096649610739)
    ·
      refine ⟨216895791210144974416109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144597194140096649610739 216895791210144974416109)
      ·
        refine ⟨81335921703804365406041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216895791210144974416109 81335921703804365406041)
        ·
          refine ⟨61001941277853274054531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81335921703804365406041 61001941277853274054531)
          ·
            refine ⟨91502911916779911081797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61001941277853274054531 91502911916779911081797)
            ·
              refine ⟨17156795984396233327837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91502911916779911081797 17156795984396233327837)
              ·
                refine ⟨6433798494148587497939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17156795984396233327837 6433798494148587497939)
                ·
                  refine ⟨9650697741222881246909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6433798494148587497939 9650697741222881246909)
                  ·
                    refine ⟨3619011652958580467591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9650697741222881246909 3619011652958580467591)
                    ·
                      rfl

theorem cell22_10572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_10572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10572 prefixEnd_10572 := by exact prefixLift 10572
  have htrace : WordTrace (prefixWord ++ tailWord_10572) baseStart_10572 baseEnd_10572 := by
    simpa [prefixWord, tailWord_10572, baseEnd_10572] using wordTrace_append hprefix tailTrace_10572
  have hstable : (prefixWord ++ tailWord_10572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10572).length < 2 ^ (prefixWord ++ tailWord_10572).sum := by decide
  have hdescent : baseEnd_10572 < baseStart_10572 := by decide
  rcases family_descends (prefixWord ++ tailWord_10572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10602 : List Nat := [3, 1, 3, 3, 1, 2, 3, 1, 5]
def baseStart_10602 : Nat := 118140960795 + 10602 * 2 ^ 59
def prefixEnd_10602 : Nat := 4983230072969 + 3 ^ 40 * 10602 * 2
def baseEnd_10602 : Nat := 1209760422016167405833

theorem tailTrace_10602 : CollatzResearch.WordTrace tailWord_10602 prefixEnd_10602 1209760422016167405833 := by
  unfold tailWord_10602
  simp only [CollatzResearch.WordTrace]
  refine ⟨96671676899559880638515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 257791138398826348369373 96671676899559880638515)
  ·
    refine ⟨145007515349339820957773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96671676899559880638515 145007515349339820957773)
    ·
      refine ⟨54377818256002432859165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145007515349339820957773 54377818256002432859165)
      ·
        refine ⟨20391681846000912322187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54377818256002432859165 20391681846000912322187)
        ·
          refine ⟨30587522769001368483281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20391681846000912322187 30587522769001368483281)
          ·
            refine ⟨22940642076751026362461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30587522769001368483281 22940642076751026362461)
            ·
              refine ⟨8602740778781634885923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22940642076751026362461 8602740778781634885923)
              ·
                refine ⟨12904111168172452328885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8602740778781634885923 12904111168172452328885)
                ·
                  refine ⟨1209760422016167405833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12904111168172452328885 1209760422016167405833)
                  ·
                    rfl

theorem cell22_10602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_10602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10602 prefixEnd_10602 := by exact prefixLift 10602
  have htrace : WordTrace (prefixWord ++ tailWord_10602) baseStart_10602 baseEnd_10602 := by
    simpa [prefixWord, tailWord_10602, baseEnd_10602] using wordTrace_append hprefix tailTrace_10602
  have hstable : (prefixWord ++ tailWord_10602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10602).length < 2 ^ (prefixWord ++ tailWord_10602).sum := by decide
  have hdescent : baseEnd_10602 < baseStart_10602 := by decide
  rcases family_descends (prefixWord ++ tailWord_10602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10628 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_10628 : Nat := 118140960795 + 10628 * 2 ^ 59
def prefixEnd_10628 : Nat := 4983230072969 + 3 ^ 40 * 10628 * 2
def baseEnd_10628 : Nat := 3638181597393101067419

theorem tailTrace_10628 : CollatzResearch.WordTrace tailWord_10628 prefixEnd_10628 3638181597393101067419 := by
  unfold tailWord_10628
  simp only [CollatzResearch.WordTrace]
  refine ⟨193817502752022981500269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 258423337002697308667025 193817502752022981500269)
  ·
    refine ⟨72681563532008618062601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193817502752022981500269 72681563532008618062601)
    ·
      refine ⟨54511172649006463546951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72681563532008618062601 54511172649006463546951)
      ·
        refine ⟨81766758973509695320427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54511172649006463546951 81766758973509695320427)
        ·
          refine ⟨122650138460264542980641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81766758973509695320427 122650138460264542980641)
          ·
            refine ⟨91987603845198407235481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122650138460264542980641 91987603845198407235481)
            ·
              refine ⟨68990702883898805426611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91987603845198407235481 68990702883898805426611)
              ·
                refine ⟨103486054325848208139917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68990702883898805426611 103486054325848208139917)
                ·
                  refine ⟨38807270372193078052469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103486054325848208139917 38807270372193078052469)
                  ·
                    refine ⟨3638181597393101067419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38807270372193078052469 3638181597393101067419)
                    ·
                      rfl

theorem cell22_10628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_10628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10628 prefixEnd_10628 := by exact prefixLift 10628
  have htrace : WordTrace (prefixWord ++ tailWord_10628) baseStart_10628 baseEnd_10628 := by
    simpa [prefixWord, tailWord_10628, baseEnd_10628] using wordTrace_append hprefix tailTrace_10628
  have hstable : (prefixWord ++ tailWord_10628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10628).length < 2 ^ (prefixWord ++ tailWord_10628).sum := by decide
  have hdescent : baseEnd_10628 < baseStart_10628 := by decide
  rcases family_descends (prefixWord ++ tailWord_10628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10645 : List Nat := [1, 3, 2, 1, 1, 2, 1, 6, 2, 3]
def baseStart_10645 : Nat := 118140960795 + 10645 * 2 ^ 59
def prefixEnd_10645 : Nat := 4983230072969 + 3 ^ 40 * 10645 * 2
def baseEnd_10645 : Nat := 3644001044810723392367

theorem tailTrace_10645 : CollatzResearch.WordTrace tailWord_10645 prefixEnd_10645 3644001044810723392367 := by
  unfold tailWord_10645
  simp only [CollatzResearch.WordTrace]
  refine ⟨388255046442457866369389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 258836697628305244246259 388255046442457866369389)
  ·
    refine ⟨145595642415921699888521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 388255046442457866369389 145595642415921699888521)
    ·
      refine ⟨109196731811941274916391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145595642415921699888521 109196731811941274916391)
      ·
        refine ⟨163795097717911912374587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109196731811941274916391 163795097717911912374587)
        ·
          refine ⟨245692646576867868561881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163795097717911912374587 245692646576867868561881)
          ·
            refine ⟨184269484932650901421411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245692646576867868561881 184269484932650901421411)
            ·
              refine ⟨276404227398976352132117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184269484932650901421411 276404227398976352132117)
              ·
                refine ⟨12956448159327016506193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 276404227398976352132117 12956448159327016506193)
                ·
                  refine ⟨9717336119495262379645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12956448159327016506193 9717336119495262379645)
                  ·
                    refine ⟨3644001044810723392367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9717336119495262379645 3644001044810723392367)
                    ·
                      rfl

theorem cell22_10645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_10645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10645 prefixEnd_10645 := by exact prefixLift 10645
  have htrace : WordTrace (prefixWord ++ tailWord_10645) baseStart_10645 baseEnd_10645 := by
    simpa [prefixWord, tailWord_10645, baseEnd_10645] using wordTrace_append hprefix tailTrace_10645
  have hstable : (prefixWord ++ tailWord_10645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10645).length < 2 ^ (prefixWord ++ tailWord_10645).sum := by decide
  have hdescent : baseEnd_10645 < baseStart_10645 := by decide
  rcases family_descends (prefixWord ++ tailWord_10645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10677 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 2, 4]
def baseStart_10677 : Nat := 118140960795 + 10677 * 2 ^ 59
def prefixEnd_10677 : Nat := 4983230072969 + 3 ^ 40 * 10677 * 2
def baseEnd_10677 : Nat := 3654955298773306592269

theorem tailTrace_10677 : CollatzResearch.WordTrace tailWord_10677 prefixEnd_10677 3654955298773306592269 := by
  unfold tailWord_10677
  simp only [CollatzResearch.WordTrace]
  refine ⟨389422182326527331534285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 259614788217684887689523 389422182326527331534285)
  ·
    refine ⟨146033318372447749325357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 389422182326527331534285 146033318372447749325357)
    ·
      refine ⟨54762494389667905997009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146033318372447749325357 54762494389667905997009)
      ·
        refine ⟨41071870792250929497757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54762494389667905997009 41071870792250929497757)
        ·
          refine ⟨15401951547094098561659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41071870792250929497757 15401951547094098561659)
          ·
            refine ⟨23102927320641147842489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15401951547094098561659 23102927320641147842489)
            ·
              refine ⟨17327195490480860881867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23102927320641147842489 17327195490480860881867)
              ·
                refine ⟨25990793235721291322801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17327195490480860881867 25990793235721291322801)
                ·
                  refine ⟨19493094926790968492101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25990793235721291322801 19493094926790968492101)
                  ·
                    refine ⟨3654955298773306592269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19493094926790968492101 3654955298773306592269)
                    ·
                      rfl

theorem cell22_10677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_10677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10677 prefixEnd_10677 := by exact prefixLift 10677
  have htrace : WordTrace (prefixWord ++ tailWord_10677) baseStart_10677 baseEnd_10677 := by
    simpa [prefixWord, tailWord_10677, baseEnd_10677] using wordTrace_append hprefix tailTrace_10677
  have hstable : (prefixWord ++ tailWord_10677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10677).length < 2 ^ (prefixWord ++ tailWord_10677).sum := by decide
  have hdescent : baseEnd_10677 < baseStart_10677 := by decide
  rcases family_descends (prefixWord ++ tailWord_10677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10748 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 10]
def baseStart_10748 : Nat := 118140960795 + 10748 * 2 ^ 59
def prefixEnd_10748 : Nat := 4983230072969 + 3 ^ 40 * 10748 * 2
def baseEnd_10748 : Nat := 1226420016584262689017

theorem tailTrace_10748 : CollatzResearch.WordTrace tailWord_10748 prefixEnd_10748 1226420016584262689017 := by
  unfold tailWord_10748
  simp only [CollatzResearch.WordTrace]
  refine ⟨196005882534653228684449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 261341176712870971579265 196005882534653228684449)
  ·
    refine ⟨147004411900989921513337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196005882534653228684449 147004411900989921513337)
    ·
      refine ⟨110253308925742441135003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147004411900989921513337 110253308925742441135003)
      ·
        refine ⟨165379963388613661702505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110253308925742441135003 165379963388613661702505)
        ·
          refine ⟨124034972541460246276879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165379963388613661702505 124034972541460246276879)
          ·
            refine ⟨186052458812190369415319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124034972541460246276879 186052458812190369415319)
            ·
              refine ⟨279078688218285554122979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186052458812190369415319 279078688218285554122979)
              ·
                refine ⟨418618032327428331184469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279078688218285554122979 418618032327428331184469)
                ·
                  refine ⟨1226420016584262689017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 418618032327428331184469 1226420016584262689017)
                  ·
                    rfl

theorem cell22_10748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_10748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10748 prefixEnd_10748 := by exact prefixLift 10748
  have htrace : WordTrace (prefixWord ++ tailWord_10748) baseStart_10748 baseEnd_10748 := by
    simpa [prefixWord, tailWord_10748, baseEnd_10748] using wordTrace_append hprefix tailTrace_10748
  have hstable : (prefixWord ++ tailWord_10748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10748).length < 2 ^ (prefixWord ++ tailWord_10748).sum := by decide
  have hdescent : baseEnd_10748 < baseStart_10748 := by decide
  rcases family_descends (prefixWord ++ tailWord_10748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10758 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_10758 : Nat := 118140960795 + 10758 * 2 ^ 59
def prefixEnd_10758 : Nat := 4983230072969 + 3 ^ 40 * 10758 * 2
def baseEnd_10758 : Nat := 3682683254116095317021

theorem tailTrace_10758 : CollatzResearch.WordTrace tailWord_10758 prefixEnd_10758 3682683254116095317021 := by
  unfold tailWord_10758
  simp only [CollatzResearch.WordTrace]
  refine ⟨12261765469783692663529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 261584330022052110155285 12261765469783692663529)
  ·
    refine ⟨9196324102337769497647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12261765469783692663529 9196324102337769497647)
    ·
      refine ⟨13794486153506654246471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9196324102337769497647 13794486153506654246471)
      ·
        refine ⟨20691729230259981369707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13794486153506654246471 20691729230259981369707)
        ·
          refine ⟨31037593845389972054561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20691729230259981369707 31037593845389972054561)
          ·
            refine ⟨23278195384042479040921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31037593845389972054561 23278195384042479040921)
            ·
              refine ⟨17458646538031859280691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23278195384042479040921 17458646538031859280691)
              ·
                refine ⟨26187969807047788921037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17458646538031859280691 26187969807047788921037)
                ·
                  refine ⟨9820488677642920845389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26187969807047788921037 9820488677642920845389)
                  ·
                    refine ⟨3682683254116095317021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9820488677642920845389 3682683254116095317021)
                    ·
                      rfl

theorem cell22_10758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_10758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10758 prefixEnd_10758 := by exact prefixLift 10758
  have htrace : WordTrace (prefixWord ++ tailWord_10758) baseStart_10758 baseEnd_10758 := by
    simpa [prefixWord, tailWord_10758, baseEnd_10758] using wordTrace_append hprefix tailTrace_10758
  have hstable : (prefixWord ++ tailWord_10758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10758).length < 2 ^ (prefixWord ++ tailWord_10758).sum := by decide
  have hdescent : baseEnd_10758 < baseStart_10758 := by decide
  rcases family_descends (prefixWord ++ tailWord_10758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10784 : List Nat := [2, 1, 1, 6, 2, 1, 2, 2, 1, 4]
def baseStart_10784 : Nat := 118140960795 + 10784 * 2 ^ 59
def prefixEnd_10784 : Nat := 4983230072969 + 3 ^ 40 * 10784 * 2
def baseEnd_10784 : Nat := 3691583585460694166941

theorem tailTrace_10784 : CollatzResearch.WordTrace tailWord_10784 prefixEnd_10784 3691583585460694166941 := by
  unfold tailWord_10784
  simp only [CollatzResearch.WordTrace]
  refine ⟨196662396469442302839703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 262216528625923070452937 196662396469442302839703)
  ·
    refine ⟨294993594704163454259555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196662396469442302839703 294993594704163454259555)
    ·
      refine ⟨442490392056245181389333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294993594704163454259555 442490392056245181389333)
      ·
        refine ⟨20741737127636492877625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 442490392056245181389333 20741737127636492877625)
        ·
          refine ⟨15556302845727369658219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20741737127636492877625 15556302845727369658219)
          ·
            refine ⟨23334454268591054487329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15556302845727369658219 23334454268591054487329)
            ·
              refine ⟨17500840701443290865497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23334454268591054487329 17500840701443290865497)
              ·
                refine ⟨13125630526082468149123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17500840701443290865497 13125630526082468149123)
                ·
                  refine ⟨19688445789123702223685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13125630526082468149123 19688445789123702223685)
                  ·
                    refine ⟨3691583585460694166941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19688445789123702223685 3691583585460694166941)
                    ·
                      rfl

theorem cell22_10784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_10784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10784 prefixEnd_10784 := by exact prefixLift 10784
  have htrace : WordTrace (prefixWord ++ tailWord_10784) baseStart_10784 baseEnd_10784 := by
    simpa [prefixWord, tailWord_10784, baseEnd_10784] using wordTrace_append hprefix tailTrace_10784
  have hstable : (prefixWord ++ tailWord_10784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10784).length < 2 ^ (prefixWord ++ tailWord_10784).sum := by decide
  have hdescent : baseEnd_10784 < baseStart_10784 := by decide
  rcases family_descends (prefixWord ++ tailWord_10784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10810 : List Nat := [3, 1, 1, 1, 3, 5, 8]
def baseStart_10810 : Nat := 118140960795 + 10810 * 2 ^ 59
def prefixEnd_10810 : Nat := 4983230072969 + 3 ^ 40 * 10810 * 2
def baseEnd_10810 : Nat := 137054959881677519143

theorem tailTrace_10810 : CollatzResearch.WordTrace tailWord_10810 prefixEnd_10810 137054959881677519143 := by
  unfold tailWord_10810
  simp only [CollatzResearch.WordTrace]
  refine ⟨98568272711172761531471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 262848727229794030750589 98568272711172761531471)
  ·
    refine ⟨147852409066759142297207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98568272711172761531471 147852409066759142297207)
    ·
      refine ⟨221778613600138713445811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147852409066759142297207 221778613600138713445811)
      ·
        refine ⟨332667920400208070168717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221778613600138713445811 332667920400208070168717)
        ·
          refine ⟨124750470150078026313269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332667920400208070168717 124750470150078026313269)
          ·
            refine ⟨11695356576569814966869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124750470150078026313269 11695356576569814966869)
            ·
              refine ⟨137054959881677519143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 11695356576569814966869 137054959881677519143)
              ·
                rfl

theorem cell22_10810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 8].length) (baseStart_10810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10810 prefixEnd_10810 := by exact prefixLift 10810
  have htrace : WordTrace (prefixWord ++ tailWord_10810) baseStart_10810 baseEnd_10810 := by
    simpa [prefixWord, tailWord_10810, baseEnd_10810] using wordTrace_append hprefix tailTrace_10810
  have hstable : (prefixWord ++ tailWord_10810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10810).length < 2 ^ (prefixWord ++ tailWord_10810).sum := by decide
  have hdescent : baseEnd_10810 < baseStart_10810 := by decide
  rcases family_descends (prefixWord ++ tailWord_10810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10812 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_10812 : Nat := 118140960795 + 10812 * 2 ^ 59
def prefixEnd_10812 : Nat := 4983230072969 + 3 ^ 40 * 10812 * 2
def baseEnd_10812 : Nat := 3701168557677954466855

theorem tailTrace_10812 : CollatzResearch.WordTrace tailWord_10812 prefixEnd_10812 3701168557677954466855 := by
  unfold tailWord_10812
  simp only [CollatzResearch.WordTrace]
  refine ⟨197173018418722693849345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 262897357891630258465793 197173018418722693849345)
  ·
    refine ⟨147879763814042020387009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197173018418722693849345 147879763814042020387009)
    ·
      refine ⟨110909822860531515290257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147879763814042020387009 110909822860531515290257)
      ·
        refine ⟨83182367145398636467693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110909822860531515290257 83182367145398636467693)
        ·
          refine ⟨31193387679524488675385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83182367145398636467693 31193387679524488675385)
          ·
            refine ⟨23395040759643366506539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31193387679524488675385 23395040759643366506539)
            ·
              refine ⟨35092561139465049759809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23395040759643366506539 35092561139465049759809)
              ·
                refine ⟨26319420854598787319857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35092561139465049759809 26319420854598787319857)
                ·
                  refine ⟨19739565640949090489893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26319420854598787319857 19739565640949090489893)
                  ·
                    refine ⟨3701168557677954466855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19739565640949090489893 3701168557677954466855)
                    ·
                      rfl

theorem cell22_10812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_10812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10812 prefixEnd_10812 := by exact prefixLift 10812
  have htrace : WordTrace (prefixWord ++ tailWord_10812) baseStart_10812 baseEnd_10812 := by
    simpa [prefixWord, tailWord_10812, baseEnd_10812] using wordTrace_append hprefix tailTrace_10812
  have hstable : (prefixWord ++ tailWord_10812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10812).length < 2 ^ (prefixWord ++ tailWord_10812).sum := by decide
  have hdescent : baseEnd_10812 < baseStart_10812 := by decide
  rcases family_descends (prefixWord ++ tailWord_10812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10876 : List Nat := [2, 2, 2, 1, 1, 2, 6, 2, 1, 3]
def baseStart_10876 : Nat := 118140960795 + 10876 * 2 ^ 59
def prefixEnd_10876 : Nat := 4983230072969 + 3 ^ 40 * 10876 * 2
def baseEnd_10876 : Nat := 3723077065603120866659

theorem tailTrace_10876 : CollatzResearch.WordTrace tailWord_10876 prefixEnd_10876 3723077065603120866659 := by
  unfold tailWord_10876
  simp only [CollatzResearch.WordTrace]
  refine ⟨198340154302792159014241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 264453539070389545352321 198340154302792159014241)
  ·
    refine ⟨148755115727094119260681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198340154302792159014241 148755115727094119260681)
    ·
      refine ⟨111566336795320589445511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148755115727094119260681 111566336795320589445511)
      ·
        refine ⟨167349505192980884168267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111566336795320589445511 167349505192980884168267)
        ·
          refine ⟨251024257789471326252401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167349505192980884168267 251024257789471326252401)
          ·
            refine ⟨188268193342103494689301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251024257789471326252401 188268193342103494689301)
            ·
              refine ⟨8825071562911101313561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 188268193342103494689301 8825071562911101313561)
              ·
                refine ⟨6618803672183325985171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8825071562911101313561 6618803672183325985171)
                ·
                  refine ⟨9928205508274988977757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6618803672183325985171 9928205508274988977757)
                  ·
                    refine ⟨3723077065603120866659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9928205508274988977757 3723077065603120866659)
                    ·
                      rfl

theorem cell22_10876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_10876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10876 prefixEnd_10876 := by exact prefixLift 10876
  have htrace : WordTrace (prefixWord ++ tailWord_10876) baseStart_10876 baseEnd_10876 := by
    simpa [prefixWord, tailWord_10876, baseEnd_10876] using wordTrace_append hprefix tailTrace_10876
  have hstable : (prefixWord ++ tailWord_10876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10876).length < 2 ^ (prefixWord ++ tailWord_10876).sum := by decide
  have hdescent : baseEnd_10876 < baseStart_10876 := by decide
  rcases family_descends (prefixWord ++ tailWord_10876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10915 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 3, 5]
def baseStart_10915 : Nat := 118140960795 + 10915 * 2 ^ 59
def prefixEnd_10915 : Nat := 4983230072969 + 3 ^ 40 * 10915 * 2
def baseEnd_10915 : Nat := 3736427562620019141539

theorem tailTrace_10915 : CollatzResearch.WordTrace tailWord_10915 prefixEnd_10915 3736427562620019141539 := by
  unfold tailWord_10915
  simp only [CollatzResearch.WordTrace]
  refine ⟨398102755464293978698199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 265401836976195985798799 398102755464293978698199)
  ·
    refine ⟨597154133196440968047299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 398102755464293978698199 597154133196440968047299)
    ·
      refine ⟨895731199794661452070949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 597154133196440968047299 895731199794661452070949)
      ·
        refine ⟨167949599961499022263303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 895731199794661452070949 167949599961499022263303)
        ·
          refine ⟨251924399942248533394955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167949599961499022263303 251924399942248533394955)
          ·
            refine ⟨377886599913372800092433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251924399942248533394955 377886599913372800092433)
            ·
              refine ⟨283414949935029600069325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377886599913372800092433 283414949935029600069325)
              ·
                refine ⟨106280606225636100025997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283414949935029600069325 106280606225636100025997)
                ·
                  refine ⟨39855227334613537509749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106280606225636100025997 39855227334613537509749)
                  ·
                    refine ⟨3736427562620019141539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39855227334613537509749 3736427562620019141539)
                    ·
                      rfl

theorem cell22_10915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 5].length) (baseStart_10915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_10915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_10915 prefixEnd_10915 := by exact prefixLift 10915
  have htrace : WordTrace (prefixWord ++ tailWord_10915) baseStart_10915 baseEnd_10915 := by
    simpa [prefixWord, tailWord_10915, baseEnd_10915] using wordTrace_append hprefix tailTrace_10915
  have hstable : (prefixWord ++ tailWord_10915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10915).length < 2 ^ (prefixWord ++ tailWord_10915).sum := by decide
  have hdescent : baseEnd_10915 < baseStart_10915 := by decide
  rcases family_descends (prefixWord ++ tailWord_10915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11022 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_11022 : Nat := 118140960795 + 11022 * 2 ^ 59
def prefixEnd_11022 : Nat := 4983230072969 + 3 ^ 40 * 11022 * 2
def baseEnd_11022 : Nat := 3773055849307406716211

theorem tailTrace_11022 : CollatzResearch.WordTrace tailWord_11022 prefixEnd_11022 3773055849307406716211 := by
  unfold tailWord_11022
  simp only [CollatzResearch.WordTrace]
  refine ⟨50250670759581406605415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 268003577384434168562213 50250670759581406605415)
  ·
    refine ⟨75376006139372109908123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50250670759581406605415 75376006139372109908123)
    ·
      refine ⟨113064009209058164862185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75376006139372109908123 113064009209058164862185)
      ·
        refine ⟨84798006906793623646639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113064009209058164862185 84798006906793623646639)
        ·
          refine ⟨127197010360190435469959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84798006906793623646639 127197010360190435469959)
          ·
            refine ⟨190795515540285653204939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127197010360190435469959 190795515540285653204939)
            ·
              refine ⟨286193273310428479807409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190795515540285653204939 286193273310428479807409)
              ·
                refine ⟨214644954982821359855557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286193273310428479807409 214644954982821359855557)
                ·
                  refine ⟨40245929059279004972917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 214644954982821359855557 40245929059279004972917)
                  ·
                    refine ⟨3773055849307406716211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40245929059279004972917 3773055849307406716211)
                    ·
                      rfl

theorem cell22_11022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_11022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11022 prefixEnd_11022 := by exact prefixLift 11022
  have htrace : WordTrace (prefixWord ++ tailWord_11022) baseStart_11022 baseEnd_11022 := by
    simpa [prefixWord, tailWord_11022, baseEnd_11022] using wordTrace_append hprefix tailTrace_11022
  have hstable : (prefixWord ++ tailWord_11022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11022).length < 2 ^ (prefixWord ++ tailWord_11022).sum := by decide
  have hdescent : baseEnd_11022 < baseStart_11022 := by decide
  rcases family_descends (prefixWord ++ tailWord_11022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11052 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 6]
def baseStart_11052 : Nat := 118140960795 + 11052 * 2 ^ 59
def prefixEnd_11052 : Nat := 4983230072969 + 3 ^ 40 * 11052 * 2
def baseEnd_11052 : Nat := 1261108487465776155373

theorem tailTrace_11052 : CollatzResearch.WordTrace tailWord_11052 prefixEnd_11052 1261108487465776155373 := by
  unfold tailWord_11052
  simp only [CollatzResearch.WordTrace]
  refine ⟨201549777983983188217705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 268733037311977584290273 201549777983983188217705)
  ·
    refine ⟨151162333487987391163279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201549777983983188217705 151162333487987391163279)
    ·
      refine ⟨226743500231981086744919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151162333487987391163279 226743500231981086744919)
      ·
        refine ⟨340115250347971630117379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226743500231981086744919 340115250347971630117379)
        ·
          refine ⟨510172875521957445176069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340115250347971630117379 510172875521957445176069)
          ·
            refine ⟨95657414160367020970513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 510172875521957445176069 95657414160367020970513)
            ·
              refine ⟨71743060620275265727885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95657414160367020970513 71743060620275265727885)
              ·
                refine ⟨26903647732603224647957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71743060620275265727885 26903647732603224647957)
                ·
                  refine ⟨1261108487465776155373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26903647732603224647957 1261108487465776155373)
                  ·
                    rfl

theorem cell22_11052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_11052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11052 prefixEnd_11052 := by exact prefixLift 11052
  have htrace : WordTrace (prefixWord ++ tailWord_11052) baseStart_11052 baseEnd_11052 := by
    simpa [prefixWord, tailWord_11052, baseEnd_11052] using wordTrace_append hprefix tailTrace_11052
  have hstable : (prefixWord ++ tailWord_11052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11052).length < 2 ^ (prefixWord ++ tailWord_11052).sum := by decide
  have hdescent : baseEnd_11052 < baseStart_11052 := by decide
  rcases family_descends (prefixWord ++ tailWord_11052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11084 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_11084 : Nat := 118140960795 + 11084 * 2 ^ 59
def prefixEnd_11084 : Nat := 4983230072969 + 3 ^ 40 * 11084 * 2
def baseEnd_11084 : Nat := 3794279716359911666021

theorem tailTrace_11084 : CollatzResearch.WordTrace tailWord_11084 prefixEnd_11084 3794279716359911666021 := by
  unfold tailWord_11084
  simp only [CollatzResearch.WordTrace]
  refine ⟨202133345926017920800153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 269511127901357227733537 202133345926017920800153)
  ·
    refine ⟨151600009444513440600115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202133345926017920800153 151600009444513440600115)
    ·
      refine ⟨227400014166770160900173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151600009444513440600115 227400014166770160900173)
      ·
        refine ⟨85275005312538810337565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227400014166770160900173 85275005312538810337565)
        ·
          refine ⟨31978126992202053876587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85275005312538810337565 31978126992202053876587)
          ·
            refine ⟨47967190488303080814881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31978126992202053876587 47967190488303080814881)
            ·
              refine ⟨35975392866227310611161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47967190488303080814881 35975392866227310611161)
              ·
                refine ⟨26981544649670482958371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35975392866227310611161 26981544649670482958371)
                ·
                  refine ⟨40472316974505724437557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26981544649670482958371 40472316974505724437557)
                  ·
                    refine ⟨3794279716359911666021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40472316974505724437557 3794279716359911666021)
                    ·
                      rfl

theorem cell22_11084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_11084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11084 prefixEnd_11084 := by exact prefixLift 11084
  have htrace : WordTrace (prefixWord ++ tailWord_11084) baseStart_11084 baseEnd_11084 := by
    simpa [prefixWord, tailWord_11084, baseEnd_11084] using wordTrace_append hprefix tailTrace_11084
  have hstable : (prefixWord ++ tailWord_11084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11084).length < 2 ^ (prefixWord ++ tailWord_11084).sum := by decide
  have hdescent : baseEnd_11084 < baseStart_11084 := by decide
  rcases family_descends (prefixWord ++ tailWord_11084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11097 : List Nat := [1, 2, 1, 2, 2, 5, 9]
def baseStart_11097 : Nat := 118140960795 + 11097 * 2 ^ 59
def prefixEnd_11097 : Nat := 4983230072969 + 3 ^ 40 * 11097 * 2
def baseEnd_11097 : Nat := 140693699334526336703

theorem tailTrace_11097 : CollatzResearch.WordTrace tailWord_11097 prefixEnd_11097 140693699334526336703 := by
  unfold tailWord_11097
  simp only [CollatzResearch.WordTrace]
  refine ⟨404740840804939061823545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 269827227203292707882363 404740840804939061823545)
  ·
    refine ⟨303555630603704296367659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 404740840804939061823545 303555630603704296367659)
    ·
      refine ⟨455333445905556444551489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303555630603704296367659 455333445905556444551489)
      ·
        refine ⟨341500084429167333413617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 455333445905556444551489 341500084429167333413617)
        ·
          refine ⟨256125063321875500060213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341500084429167333413617 256125063321875500060213)
          ·
            refine ⟨24011724686425828130645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 256125063321875500060213 24011724686425828130645)
            ·
              refine ⟨140693699334526336703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 24011724686425828130645 140693699334526336703)
              ·
                rfl

theorem cell22_11097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 9].length) (baseStart_11097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11097 prefixEnd_11097 := by exact prefixLift 11097
  have htrace : WordTrace (prefixWord ++ tailWord_11097) baseStart_11097 baseEnd_11097 := by
    simpa [prefixWord, tailWord_11097, baseEnd_11097] using wordTrace_append hprefix tailTrace_11097
  have hstable : (prefixWord ++ tailWord_11097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11097).length < 2 ^ (prefixWord ++ tailWord_11097).sum := by decide
  have hdescent : baseEnd_11097 < baseStart_11097 := by decide
  rcases family_descends (prefixWord ++ tailWord_11097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11118 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_11118 : Nat := 118140960795 + 11118 * 2 ^ 59
def prefixEnd_11118 : Nat := 4983230072969 + 3 ^ 40 * 11118 * 2
def baseEnd_11118 : Nat := 3805918611195156315917

theorem tailTrace_11118 : CollatzResearch.WordTrace tailWord_11118 prefixEnd_11118 3805918611195156315917 := by
  unfold tailWord_11118
  simp only [CollatzResearch.WordTrace]
  refine ⟨50688346716107456042251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 270337849152573098892005 50688346716107456042251)
  ·
    refine ⟨76032520074161184063377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50688346716107456042251 76032520074161184063377)
    ·
      refine ⟨57024390055620888047533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76032520074161184063377 57024390055620888047533)
      ·
        refine ⟨21384146270857833017825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57024390055620888047533 21384146270857833017825)
        ·
          refine ⟨16038109703143374763369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21384146270857833017825 16038109703143374763369)
          ·
            refine ⟨12028582277357531072527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16038109703143374763369 12028582277357531072527)
            ·
              refine ⟨18042873416036296608791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12028582277357531072527 18042873416036296608791)
              ·
                refine ⟨27064310124054444913187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18042873416036296608791 27064310124054444913187)
                ·
                  refine ⟨40596465186081667369781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27064310124054444913187 40596465186081667369781)
                  ·
                    refine ⟨3805918611195156315917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40596465186081667369781 3805918611195156315917)
                    ·
                      rfl

theorem cell22_11118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_11118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11118 prefixEnd_11118 := by exact prefixLift 11118
  have htrace : WordTrace (prefixWord ++ tailWord_11118) baseStart_11118 baseEnd_11118 := by
    simpa [prefixWord, tailWord_11118, baseEnd_11118] using wordTrace_append hprefix tailTrace_11118
  have hstable : (prefixWord ++ tailWord_11118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11118).length < 2 ^ (prefixWord ++ tailWord_11118).sum := by decide
  have hdescent : baseEnd_11118 < baseStart_11118 := by decide
  rcases family_descends (prefixWord ++ tailWord_11118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11127 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 2, 6]
def baseStart_11127 : Nat := 118140960795 + 11127 * 2 ^ 59
def prefixEnd_11127 : Nat := 4983230072969 + 3 ^ 40 * 11127 * 2
def baseEnd_11127 : Nat := 3808999495122132840889

theorem tailTrace_11127 : CollatzResearch.WordTrace tailWord_11127 prefixEnd_11127 3808999495122132840889 := by
  unfold tailWord_11127
  simp only [CollatzResearch.WordTrace]
  refine ⟨405835030696254185415635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 270556687130836123610423 405835030696254185415635)
  ·
    refine ⟨608752546044381278123453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 405835030696254185415635 608752546044381278123453)
    ·
      refine ⟨228282204766642979296295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 608752546044381278123453 228282204766642979296295)
      ·
        refine ⟨342423307149964468944443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228282204766642979296295 342423307149964468944443)
        ·
          refine ⟨513634960724946703416665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342423307149964468944443 513634960724946703416665)
          ·
            refine ⟨385226220543710027562499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 513634960724946703416665 385226220543710027562499)
            ·
              refine ⟨577839330815565041343749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385226220543710027562499 577839330815565041343749)
              ·
                refine ⟨108344874527918445251953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 577839330815565041343749 108344874527918445251953)
                ·
                  refine ⟨81258655895938833938965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108344874527918445251953 81258655895938833938965)
                  ·
                    refine ⟨3808999495122132840889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81258655895938833938965 3808999495122132840889)
                    ·
                      rfl

theorem cell22_11127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_11127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11127 prefixEnd_11127 := by exact prefixLift 11127
  have htrace : WordTrace (prefixWord ++ tailWord_11127) baseStart_11127 baseEnd_11127 := by
    simpa [prefixWord, tailWord_11127, baseEnd_11127] using wordTrace_append hprefix tailTrace_11127
  have hstable : (prefixWord ++ tailWord_11127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11127).length < 2 ^ (prefixWord ++ tailWord_11127).sum := by decide
  have hdescent : baseEnd_11127 < baseStart_11127 := by decide
  rcases family_descends (prefixWord ++ tailWord_11127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11159 : List Nat := [1, 1, 3, 3, 1, 2, 2, 4, 5]
def baseStart_11159 : Nat := 118140960795 + 11159 * 2 ^ 59
def prefixEnd_11159 : Nat := 4983230072969 + 3 ^ 40 * 11159 * 2
def baseEnd_11159 : Nat := 1273317916361572013597

theorem tailTrace_11159 : CollatzResearch.WordTrace tailWord_11159 prefixEnd_11159 1273317916361572013597 := by
  unfold tailWord_11159
  simp only [CollatzResearch.WordTrace]
  refine ⟨407002166580323650580531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 271334777720215767053687 407002166580323650580531)
  ·
    refine ⟨610503249870485475870797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 407002166580323650580531 610503249870485475870797)
    ·
      refine ⟨228938718701432053451549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 610503249870485475870797 228938718701432053451549)
      ·
        refine ⟨85852019513037020044331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228938718701432053451549 85852019513037020044331)
        ·
          refine ⟨128778029269555530066497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85852019513037020044331 128778029269555530066497)
          ·
            refine ⟨96583521952166647549873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128778029269555530066497 96583521952166647549873)
            ·
              refine ⟨72437641464124985662405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96583521952166647549873 72437641464124985662405)
              ·
                refine ⟨13582057774523434811701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72437641464124985662405 13582057774523434811701)
                ·
                  refine ⟨1273317916361572013597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13582057774523434811701 1273317916361572013597)
                  ·
                    rfl

theorem cell22_11159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 5].length) (baseStart_11159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11159 prefixEnd_11159 := by exact prefixLift 11159
  have htrace : WordTrace (prefixWord ++ tailWord_11159) baseStart_11159 baseEnd_11159 := by
    simpa [prefixWord, tailWord_11159, baseEnd_11159] using wordTrace_append hprefix tailTrace_11159
  have hstable : (prefixWord ++ tailWord_11159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11159).length < 2 ^ (prefixWord ++ tailWord_11159).sum := by decide
  have hdescent : baseEnd_11159 < baseStart_11159 := by decide
  rcases family_descends (prefixWord ++ tailWord_11159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11298 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_11298 : Nat := 118140960795 + 11298 * 2 ^ 59
def prefixEnd_11298 : Nat := 4983230072969 + 3 ^ 40 * 11298 * 2
def baseEnd_11298 : Nat := 3867536289734686815365

theorem tailTrace_11298 : CollatzResearch.WordTrace tailWord_11298 prefixEnd_11298 3867536289734686815365 := by
  unfold tailWord_11298
  simp only [CollatzResearch.WordTrace]
  refine ⟨103017978269187597472637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 274714608717833593260365 103017978269187597472637)
  ·
    refine ⟨38631741850945349052239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103017978269187597472637 38631741850945349052239)
    ·
      refine ⟨57947612776418023578359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38631741850945349052239 57947612776418023578359)
      ·
        refine ⟨86921419164627035367539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57947612776418023578359 86921419164627035367539)
        ·
          refine ⟨130382128746940553051309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86921419164627035367539 130382128746940553051309)
          ·
            refine ⟨48893298280102707394241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130382128746940553051309 48893298280102707394241)
            ·
              refine ⟨36669973710077030545681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48893298280102707394241 36669973710077030545681)
              ·
                refine ⟨27502480282557772909261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36669973710077030545681 27502480282557772909261)
                ·
                  refine ⟨10313430105959164840973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27502480282557772909261 10313430105959164840973)
                  ·
                    refine ⟨3867536289734686815365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10313430105959164840973 3867536289734686815365)
                    ·
                      rfl

theorem cell22_11298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_11298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11298 prefixEnd_11298 := by exact prefixLift 11298
  have htrace : WordTrace (prefixWord ++ tailWord_11298) baseStart_11298 baseEnd_11298 := by
    simpa [prefixWord, tailWord_11298, baseEnd_11298] using wordTrace_append hprefix tailTrace_11298
  have hstable : (prefixWord ++ tailWord_11298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11298).length < 2 ^ (prefixWord ++ tailWord_11298).sum := by decide
  have hdescent : baseEnd_11298 < baseStart_11298 := by decide
  rcases family_descends (prefixWord ++ tailWord_11298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11356 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 8]
def baseStart_11356 : Nat := 118140960795 + 11356 * 2 ^ 59
def prefixEnd_11356 : Nat := 4983230072969 + 3 ^ 40 * 11356 * 2
def baseEnd_11356 : Nat := 1295796958347289621729

theorem tailTrace_11356 : CollatzResearch.WordTrace tailWord_11356 prefixEnd_11356 1295796958347289621729 := by
  unfold tailWord_11356
  simp only [CollatzResearch.WordTrace]
  refine ⟨207093673433313147750961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 276124897911084197001281 207093673433313147750961)
  ·
    refine ⟨155320255074984860813221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207093673433313147750961 155320255074984860813221)
    ·
      refine ⟨29122547826559661402479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155320255074984860813221 29122547826559661402479)
      ·
        refine ⟨43683821739839492103719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29122547826559661402479 43683821739839492103719)
        ·
          refine ⟨65525732609759238155579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43683821739839492103719 65525732609759238155579)
          ·
            refine ⟨98288598914638857233369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65525732609759238155579 98288598914638857233369)
            ·
              refine ⟨73716449185979142925027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98288598914638857233369 73716449185979142925027)
              ·
                refine ⟨110574673778968714387541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73716449185979142925027 110574673778968714387541)
                ·
                  refine ⟨1295796958347289621729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 110574673778968714387541 1295796958347289621729)
                  ·
                    rfl

theorem cell22_11356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_11356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11356 prefixEnd_11356 := by exact prefixLift 11356
  have htrace : WordTrace (prefixWord ++ tailWord_11356) baseStart_11356 baseEnd_11356 := by
    simpa [prefixWord, tailWord_11356, baseEnd_11356] using wordTrace_append hprefix tailTrace_11356
  have hstable : (prefixWord ++ tailWord_11356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11356).length < 2 ^ (prefixWord ++ tailWord_11356).sum := by decide
  have hdescent : baseEnd_11356 < baseStart_11356 := by decide
  rcases family_descends (prefixWord ++ tailWord_11356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11401 : List Nat := [1, 2, 1, 1, 4, 3, 3, 7]
def baseStart_11401 : Nat := 118140960795 + 11401 * 2 ^ 59
def prefixEnd_11401 : Nat := 4983230072969 + 3 ^ 40 * 11401 * 2
def baseEnd_11401 : Nat := 433643921630750165561

theorem tailTrace_11401 : CollatzResearch.WordTrace tailWord_11401 prefixEnd_11401 433643921630750165561 := by
  unfold tailWord_11401
  simp only [CollatzResearch.WordTrace]
  refine ⟨415828631703598980890057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 277219087802399320593371 415828631703598980890057)
  ·
    refine ⟨311871473777699235667543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 415828631703598980890057 311871473777699235667543)
    ·
      refine ⟨467807210666548853501315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311871473777699235667543 467807210666548853501315)
      ·
        refine ⟨701710815999823280251973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467807210666548853501315 701710815999823280251973)
        ·
          refine ⟨131570777999966865047245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 701710815999823280251973 131570777999966865047245)
          ·
            refine ⟨49339041749987574392717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131570777999966865047245 49339041749987574392717)
            ·
              refine ⟨18502140656245340397269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49339041749987574392717 18502140656245340397269)
              ·
                refine ⟨433643921630750165561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18502140656245340397269 433643921630750165561)
                ·
                  rfl

theorem cell22_11401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 7].length) (baseStart_11401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11401 prefixEnd_11401 := by exact prefixLift 11401
  have htrace : WordTrace (prefixWord ++ tailWord_11401) baseStart_11401 baseEnd_11401 := by
    simpa [prefixWord, tailWord_11401, baseEnd_11401] using wordTrace_append hprefix tailTrace_11401
  have hstable : (prefixWord ++ tailWord_11401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11401).length < 2 ^ (prefixWord ++ tailWord_11401).sum := by decide
  have hdescent : baseEnd_11401 < baseStart_11401 := by decide
  rcases family_descends (prefixWord ++ tailWord_11401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11420 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 2, 4]
def baseStart_11420 : Nat := 118140960795 + 11420 * 2 ^ 59
def prefixEnd_11420 : Nat := 4983230072969 + 3 ^ 40 * 11420 * 2
def baseEnd_11420 : Nat := 3909299382967035264991

theorem tailTrace_11420 : CollatzResearch.WordTrace tailWord_11420 prefixEnd_11420 3909299382967035264991 := by
  unfold tailWord_11420
  simp only [CollatzResearch.WordTrace]
  refine ⟨208260809317382612915857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 277681079089843483887809 208260809317382612915857)
  ·
    refine ⟨156195606988036959686893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208260809317382612915857 156195606988036959686893)
    ·
      refine ⟨58573352620513859882585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156195606988036959686893 58573352620513859882585)
      ·
        refine ⟨43930014465385394911939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58573352620513859882585 43930014465385394911939)
        ·
          refine ⟨65895021698078092367909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43930014465385394911939 65895021698078092367909)
          ·
            refine ⟨12355316568389642318983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65895021698078092367909 12355316568389642318983)
            ·
              refine ⟨18532974852584463478475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12355316568389642318983 18532974852584463478475)
              ·
                refine ⟨27799462278876695217713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18532974852584463478475 27799462278876695217713)
                ·
                  refine ⟨20849596709157521413285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27799462278876695217713 20849596709157521413285)
                  ·
                    refine ⟨3909299382967035264991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20849596709157521413285 3909299382967035264991)
                    ·
                      rfl

theorem cell22_11420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_11420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11420 prefixEnd_11420 := by exact prefixLift 11420
  have htrace : WordTrace (prefixWord ++ tailWord_11420) baseStart_11420 baseEnd_11420 := by
    simpa [prefixWord, tailWord_11420, baseEnd_11420] using wordTrace_append hprefix tailTrace_11420
  have hstable : (prefixWord ++ tailWord_11420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11420).length < 2 ^ (prefixWord ++ tailWord_11420).sum := by decide
  have hdescent : baseEnd_11420 < baseStart_11420 := by decide
  rcases family_descends (prefixWord ++ tailWord_11420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11469 : List Nat := [1, 6, 2, 2, 1, 2, 2, 6]
def baseStart_11469 : Nat := 118140960795 + 11469 * 2 ^ 59
def prefixEnd_11469 : Nat := 4983230072969 + 3 ^ 40 * 11469 * 2
def baseEnd_11469 : Nat := 436230342705248976649

theorem tailTrace_11469 : CollatzResearch.WordTrace tailWord_11469 prefixEnd_11469 436230342705248976649 := by
  unfold tailWord_11469
  simp only [CollatzResearch.WordTrace]
  refine ⟨418308795457246594365461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 278872530304831062910307 418308795457246594365461)
  ·
    refine ⟨19608224787058434110881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 418308795457246594365461 19608224787058434110881)
    ·
      refine ⟨14706168590293825583161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19608224787058434110881 14706168590293825583161)
      ·
        refine ⟨11029626442720369187371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14706168590293825583161 11029626442720369187371)
        ·
          refine ⟨16544439664080553781057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11029626442720369187371 16544439664080553781057)
          ·
            refine ⟨12408329748060415335793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16544439664080553781057 12408329748060415335793)
            ·
              refine ⟨9306247311045311501845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12408329748060415335793 9306247311045311501845)
              ·
                refine ⟨436230342705248976649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9306247311045311501845 436230342705248976649)
                ·
                  rfl

theorem cell22_11469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 6].length) (baseStart_11469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11469 prefixEnd_11469 := by exact prefixLift 11469
  have htrace : WordTrace (prefixWord ++ tailWord_11469) baseStart_11469 baseEnd_11469 := by
    simpa [prefixWord, tailWord_11469, baseEnd_11469] using wordTrace_append hprefix tailTrace_11469
  have hstable : (prefixWord ++ tailWord_11469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11469).length < 2 ^ (prefixWord ++ tailWord_11469).sum := by decide
  have hdescent : baseEnd_11469 < baseStart_11469 := by decide
  rcases family_descends (prefixWord ++ tailWord_11469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11557 : List Nat := [1, 3, 1, 2, 4, 2, 2, 2, 2, 3]
def baseStart_11557 : Nat := 118140960795 + 11557 * 2 ^ 59
def prefixEnd_11557 : Nat := 4983230072969 + 3 ^ 40 * 11557 * 2
def baseEnd_11557 : Nat := 3956197282744344589571

theorem tailTrace_11557 : CollatzResearch.WordTrace tailWord_11557 prefixEnd_11557 3956197282744344589571 := by
  unfold tailWord_11557
  simp only [CollatzResearch.WordTrace]
  refine ⟨421518419138437623568925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 281012279425625082379283 421518419138437623568925)
  ·
    refine ⟨158069407176914108838347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 421518419138437623568925 158069407176914108838347)
    ·
      refine ⟨237104110765371163257521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158069407176914108838347 237104110765371163257521)
      ·
        refine ⟨177828083074028372443141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237104110765371163257521 177828083074028372443141)
        ·
          refine ⟨33342765576380319833089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177828083074028372443141 33342765576380319833089)
          ·
            refine ⟨25007074182285239874817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33342765576380319833089 25007074182285239874817)
            ·
              refine ⟨18755305636713929906113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25007074182285239874817 18755305636713929906113)
              ·
                refine ⟨14066479227535447429585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18755305636713929906113 14066479227535447429585)
                ·
                  refine ⟨10549859420651585572189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14066479227535447429585 10549859420651585572189)
                  ·
                    refine ⟨3956197282744344589571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10549859420651585572189 3956197282744344589571)
                    ·
                      rfl

theorem cell22_11557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_11557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11557 prefixEnd_11557 := by exact prefixLift 11557
  have htrace : WordTrace (prefixWord ++ tailWord_11557) baseStart_11557 baseEnd_11557 := by
    simpa [prefixWord, tailWord_11557, baseEnd_11557] using wordTrace_append hprefix tailTrace_11557
  have hstable : (prefixWord ++ tailWord_11557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11557).length < 2 ^ (prefixWord ++ tailWord_11557).sum := by decide
  have hdescent : baseEnd_11557 < baseStart_11557 := by decide
  rcases family_descends (prefixWord ++ tailWord_11557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11570 : List Nat := [3, 2, 1, 1, 4, 3, 1, 7]
def baseStart_11570 : Nat := 118140960795 + 11570 * 2 ^ 59
def prefixEnd_11570 : Nat := 4983230072969 + 3 ^ 40 * 11570 * 2
def baseEnd_11570 : Nat := 440071938712960446059

theorem tailTrace_11570 : CollatzResearch.WordTrace tailWord_11570 prefixEnd_11570 440071938712960446059 := by
  unfold tailWord_11570
  simp only [CollatzResearch.WordTrace]
  refine ⟨105498142022835210948041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 281328378727560562528109 105498142022835210948041)
  ·
    refine ⟨79123606517126408211031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105498142022835210948041 79123606517126408211031)
    ·
      refine ⟨118685409775689612316547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79123606517126408211031 118685409775689612316547)
      ·
        refine ⟨178028114663534418474821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118685409775689612316547 178028114663534418474821)
        ·
          refine ⟨33380271499412703464029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178028114663534418474821 33380271499412703464029)
          ·
            refine ⟨12517601812279763799011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33380271499412703464029 12517601812279763799011)
            ·
              refine ⟨18776402718419645698517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12517601812279763799011 18776402718419645698517)
              ·
                refine ⟨440071938712960446059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18776402718419645698517 440071938712960446059)
                ·
                  rfl

theorem cell22_11570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 7].length) (baseStart_11570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11570 prefixEnd_11570 := by exact prefixLift 11570
  have htrace : WordTrace (prefixWord ++ tailWord_11570) baseStart_11570 baseEnd_11570 := by
    simpa [prefixWord, tailWord_11570, baseEnd_11570] using wordTrace_append hprefix tailTrace_11570
  have hstable : (prefixWord ++ tailWord_11570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11570).length < 2 ^ (prefixWord ++ tailWord_11570).sum := by decide
  have hdescent : baseEnd_11570 < baseStart_11570 := by decide
  rcases family_descends (prefixWord ++ tailWord_11570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11574 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_11574 : Nat := 118140960795 + 11574 * 2 ^ 59
def prefixEnd_11574 : Nat := 4983230072969 + 3 ^ 40 * 11574 * 2
def baseEnd_11574 : Nat := 3962016730161966914519

theorem tailTrace_11574 : CollatzResearch.WordTrace tailWord_11574 prefixEnd_11574 3962016730161966914519 := by
  unfold tailWord_11574
  simp only [CollatzResearch.WordTrace]
  refine ⟨26383653754803095433611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 281425640051233017958517 26383653754803095433611)
  ·
    refine ⟨39575480632204643150417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26383653754803095433611 39575480632204643150417)
    ·
      refine ⟨29681610474153482362813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39575480632204643150417 29681610474153482362813)
      ·
        refine ⟨11130603927807555886055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29681610474153482362813 11130603927807555886055)
        ·
          refine ⟨16695905891711333829083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11130603927807555886055 16695905891711333829083)
          ·
            refine ⟨25043858837567000743625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16695905891711333829083 25043858837567000743625)
            ·
              refine ⟨18782894128175250557719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25043858837567000743625 18782894128175250557719)
              ·
                refine ⟨28174341192262875836579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18782894128175250557719 28174341192262875836579)
                ·
                  refine ⟨42261511788394313754869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28174341192262875836579 42261511788394313754869)
                  ·
                    refine ⟨3962016730161966914519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42261511788394313754869 3962016730161966914519)
                    ·
                      rfl

theorem cell22_11574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_11574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11574 prefixEnd_11574 := by exact prefixLift 11574
  have htrace : WordTrace (prefixWord ++ tailWord_11574) baseStart_11574 baseEnd_11574 := by
    simpa [prefixWord, tailWord_11574, baseEnd_11574] using wordTrace_append hprefix tailTrace_11574
  have hstable : (prefixWord ++ tailWord_11574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11574).length < 2 ^ (prefixWord ++ tailWord_11574).sum := by decide
  have hdescent : baseEnd_11574 < baseStart_11574 := by decide
  rcases family_descends (prefixWord ++ tailWord_11574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11598 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_11598 : Nat := 118140960795 + 11598 * 2 ^ 59
def prefixEnd_11598 : Nat := 4983230072969 + 3 ^ 40 * 11598 * 2
def baseEnd_11598 : Nat := 1323410806877968104815

theorem tailTrace_11598 : CollatzResearch.WordTrace tailWord_11598 prefixEnd_11598 1323410806877968104815 := by
  unfold tailWord_11598
  simp only [CollatzResearch.WordTrace]
  refine ⟨52876726498737703226431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 282009207993267750540965 52876726498737703226431)
  ·
    refine ⟨79315089748106554839647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52876726498737703226431 79315089748106554839647)
    ·
      refine ⟨118972634622159832259471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79315089748106554839647 118972634622159832259471)
      ·
        refine ⟨178458951933239748389207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118972634622159832259471 178458951933239748389207)
        ·
          refine ⟨267688427899859622583811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178458951933239748389207 267688427899859622583811)
          ·
            refine ⟨401532641849789433875717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267688427899859622583811 401532641849789433875717)
            ·
              refine ⟨75287370346835518851697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 401532641849789433875717 75287370346835518851697)
              ·
                refine ⟨56465527760126639138773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75287370346835518851697 56465527760126639138773)
                ·
                  refine ⟨1323410806877968104815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 56465527760126639138773 1323410806877968104815)
                  ·
                    rfl

theorem cell22_11598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_11598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11598 prefixEnd_11598 := by exact prefixLift 11598
  have htrace : WordTrace (prefixWord ++ tailWord_11598) baseStart_11598 baseEnd_11598 := by
    simpa [prefixWord, tailWord_11598, baseEnd_11598] using wordTrace_append hprefix tailTrace_11598
  have hstable : (prefixWord ++ tailWord_11598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11598).length < 2 ^ (prefixWord ++ tailWord_11598).sum := by decide
  have hdescent : baseEnd_11598 < baseStart_11598 := by decide
  rcases family_descends (prefixWord ++ tailWord_11598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11643 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 6]
def baseStart_11643 : Nat := 118140960795 + 11643 * 2 ^ 59
def prefixEnd_11643 : Nat := 4983230072969 + 3 ^ 40 * 11643 * 2
def baseEnd_11643 : Nat := 1328545613422928979769

theorem tailTrace_11643 : CollatzResearch.WordTrace tailWord_11643 prefixEnd_11643 1328545613422928979769 := by
  unfold tailWord_11643
  simp only [CollatzResearch.WordTrace]
  refine ⟨424655096826874311199583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 283103397884582874133055 424655096826874311199583)
  ·
    refine ⟨636982645240311466799375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 424655096826874311199583 636982645240311466799375)
    ·
      refine ⟨955473967860467200199063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 636982645240311466799375 955473967860467200199063)
      ·
        refine ⟨1433210951790700800298595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 955473967860467200199063 1433210951790700800298595)
        ·
          refine ⟨2149816427686051200447893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1433210951790700800298595 2149816427686051200447893)
          ·
            refine ⟨100772645047783650020995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2149816427686051200447893 100772645047783650020995)
            ·
              refine ⟨151158967571675475031493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100772645047783650020995 151158967571675475031493)
              ·
                refine ⟨28342306419689151568405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151158967571675475031493 28342306419689151568405)
                ·
                  refine ⟨1328545613422928979769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28342306419689151568405 1328545613422928979769)
                  ·
                    rfl

theorem cell22_11643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 6].length) (baseStart_11643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11643 prefixEnd_11643 := by exact prefixLift 11643
  have htrace : WordTrace (prefixWord ++ tailWord_11643) baseStart_11643 baseEnd_11643 := by
    simpa [prefixWord, tailWord_11643, baseEnd_11643] using wordTrace_append hprefix tailTrace_11643
  have hstable : (prefixWord ++ tailWord_11643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11643).length < 2 ^ (prefixWord ++ tailWord_11643).sum := by decide
  have hdescent : baseEnd_11643 < baseStart_11643 := by decide
  rcases family_descends (prefixWord ++ tailWord_11643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11677 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 6]
def baseStart_11677 : Nat := 118140960795 + 11677 * 2 ^ 59
def prefixEnd_11677 : Nat := 4983230072969 + 3 ^ 40 * 11677 * 2
def baseEnd_11677 : Nat := 1332425245034677196401

theorem tailTrace_11677 : CollatzResearch.WordTrace tailWord_11677 prefixEnd_11677 1332425245034677196401 := by
  unfold tailWord_11677
  simp only [CollatzResearch.WordTrace]
  refine ⟨425895178703698117937285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 283930119135798745291523 425895178703698117937285)
  ·
    refine ⟨79855346006943397113241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 425895178703698117937285 79855346006943397113241)
    ·
      refine ⟨59891509505207547834931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79855346006943397113241 59891509505207547834931)
      ·
        refine ⟨89837264257811321752397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59891509505207547834931 89837264257811321752397)
        ·
          refine ⟨33688974096679245657149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89837264257811321752397 33688974096679245657149)
          ·
            refine ⟨12633365286254717121431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33688974096679245657149 12633365286254717121431)
            ·
              refine ⟨18950047929382075682147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12633365286254717121431 18950047929382075682147)
              ·
                refine ⟨28425071894073113523221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18950047929382075682147 28425071894073113523221)
                ·
                  refine ⟨1332425245034677196401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28425071894073113523221 1332425245034677196401)
                  ·
                    rfl

theorem cell22_11677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_11677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11677 prefixEnd_11677 := by exact prefixLift 11677
  have htrace : WordTrace (prefixWord ++ tailWord_11677) baseStart_11677 baseEnd_11677 := by
    simpa [prefixWord, tailWord_11677, baseEnd_11677] using wordTrace_append hprefix tailTrace_11677
  have hstable : (prefixWord ++ tailWord_11677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11677).length < 2 ^ (prefixWord ++ tailWord_11677).sum := by decide
  have hdescent : baseEnd_11677 < baseStart_11677 := by decide
  rcases family_descends (prefixWord ++ tailWord_11677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11754 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 3, 3]
def baseStart_11754 : Nat := 118140960795 + 11754 * 2 ^ 59
def prefixEnd_11754 : Nat := 4983230072969 + 3 ^ 40 * 11754 * 2
def baseEnd_11754 : Nat := 4023634408701497413967

theorem tailTrace_11754 : CollatzResearch.WordTrace tailWord_11754 prefixEnd_11754 4023634408701497413967 := by
  unfold tailWord_11754
  simp only [CollatzResearch.WordTrace]
  refine ⟨107175899856185067122579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 285802399616493512326877 107175899856185067122579)
  ·
    refine ⟨160763849784277600683869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107175899856185067122579 160763849784277600683869)
    ·
      refine ⟨60286443669104100256451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160763849784277600683869 60286443669104100256451)
      ·
        refine ⟨90429665503656150384677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60286443669104100256451 90429665503656150384677)
        ·
          refine ⟨16955562281935528197127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90429665503656150384677 16955562281935528197127)
          ·
            refine ⟨25433343422903292295691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16955562281935528197127 25433343422903292295691)
            ·
              refine ⟨38150015134354938443537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25433343422903292295691 38150015134354938443537)
              ·
                refine ⟨28612511350766203832653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38150015134354938443537 28612511350766203832653)
                ·
                  refine ⟨10729691756537326437245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28612511350766203832653 10729691756537326437245)
                  ·
                    refine ⟨4023634408701497413967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10729691756537326437245 4023634408701497413967)
                    ·
                      rfl

theorem cell22_11754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_11754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11754 prefixEnd_11754 := by exact prefixLift 11754
  have htrace : WordTrace (prefixWord ++ tailWord_11754) baseStart_11754 baseEnd_11754 := by
    simpa [prefixWord, tailWord_11754, baseEnd_11754] using wordTrace_append hprefix tailTrace_11754
  have hstable : (prefixWord ++ tailWord_11754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11754).length < 2 ^ (prefixWord ++ tailWord_11754).sum := by decide
  have hdescent : baseEnd_11754 < baseStart_11754 := by decide
  rcases family_descends (prefixWord ++ tailWord_11754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11795 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 6]
def baseStart_11795 : Nat := 118140960795 + 11795 * 2 ^ 59
def prefixEnd_11795 : Nat := 4983230072969 + 3 ^ 40 * 11795 * 2
def baseEnd_11795 : Nat := 1345889848863685712947

theorem tailTrace_11795 : CollatzResearch.WordTrace tailWord_11795 prefixEnd_11795 1345889848863685712947 := by
  unfold tailWord_11795
  simp only [CollatzResearch.WordTrace]
  refine ⟨430198992276204270732839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 286799328184136180488559 430198992276204270732839)
  ·
    refine ⟨645298488414306406099259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 430198992276204270732839 645298488414306406099259)
    ·
      refine ⟨967947732621459609148889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 645298488414306406099259 967947732621459609148889)
      ·
        refine ⟨725960799466094706861667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 967947732621459609148889 725960799466094706861667)
        ·
          refine ⟨1088941199199142060292501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725960799466094706861667 1088941199199142060292501)
          ·
            refine ⟨51044118712459784076211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1088941199199142060292501 51044118712459784076211)
            ·
              refine ⟨76566178068689676114317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51044118712459784076211 76566178068689676114317)
              ·
                refine ⟨28712316775758628542869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76566178068689676114317 28712316775758628542869)
                ·
                  refine ⟨1345889848863685712947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28712316775758628542869 1345889848863685712947)
                  ·
                    rfl

theorem cell22_11795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 6].length) (baseStart_11795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11795 prefixEnd_11795 := by exact prefixLift 11795
  have htrace : WordTrace (prefixWord ++ tailWord_11795) baseStart_11795 baseEnd_11795 := by
    simpa [prefixWord, tailWord_11795, baseEnd_11795] using wordTrace_append hprefix tailTrace_11795
  have hstable : (prefixWord ++ tailWord_11795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11795).length < 2 ^ (prefixWord ++ tailWord_11795).sum := by decide
  have hdescent : baseEnd_11795 < baseStart_11795 := by decide
  rcases family_descends (prefixWord ++ tailWord_11795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11827 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 4, 3]
def baseStart_11827 : Nat := 118140960795 + 11827 * 2 ^ 59
def prefixEnd_11827 : Nat := 4983230072969 + 3 ^ 40 * 11827 * 2
def baseEnd_11827 : Nat := 4048623800553640338743

theorem tailTrace_11827 : CollatzResearch.WordTrace tailWord_11827 prefixEnd_11827 4048623800553640338743 := by
  unfold tailWord_11827
  simp only [CollatzResearch.WordTrace]
  refine ⟨431366128160273735897735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 287577418773515823931823 431366128160273735897735)
  ·
    refine ⟨647049192240410603846603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 431366128160273735897735 647049192240410603846603)
    ·
      refine ⟨970573788360615905769905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 647049192240410603846603 970573788360615905769905)
      ·
        refine ⟨727930341270461929327429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 970573788360615905769905 727930341270461929327429)
        ·
          refine ⟨136486938988211611748893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 727930341270461929327429 136486938988211611748893)
          ·
            refine ⟨51182602120579354405835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136486938988211611748893 51182602120579354405835)
            ·
              refine ⟨76773903180869031608753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51182602120579354405835 76773903180869031608753)
              ·
                refine ⟨57580427385651773706565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76773903180869031608753 57580427385651773706565)
                ·
                  refine ⟨10796330134809707569981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57580427385651773706565 10796330134809707569981)
                  ·
                    refine ⟨4048623800553640338743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10796330134809707569981 4048623800553640338743)
                    ·
                      rfl

theorem cell22_11827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 3].length) (baseStart_11827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11827 prefixEnd_11827 := by exact prefixLift 11827
  have htrace : WordTrace (prefixWord ++ tailWord_11827) baseStart_11827 baseEnd_11827 := by
    simpa [prefixWord, tailWord_11827, baseEnd_11827] using wordTrace_append hprefix tailTrace_11827
  have hstable : (prefixWord ++ tailWord_11827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11827).length < 2 ^ (prefixWord ++ tailWord_11827).sum := by decide
  have hdescent : baseEnd_11827 < baseStart_11827 := by decide
  rcases family_descends (prefixWord ++ tailWord_11827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11829 : List Nat := [1, 3, 3, 1, 1, 3, 3, 3, 4]
def baseStart_11829 : Nat := 118140960795 + 11829 * 2 ^ 59
def prefixEnd_11829 : Nat := 4983230072969 + 3 ^ 40 * 11829 * 2
def baseEnd_11829 : Nat := 1349769480475433929579

theorem tailTrace_11829 : CollatzResearch.WordTrace tailWord_11829 prefixEnd_11829 1349769480475433929579 := by
  unfold tailWord_11829
  simp only [CollatzResearch.WordTrace]
  refine ⟨431439074153028077470541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 287626049435352051647027 431439074153028077470541)
  ·
    refine ⟨161789652807385529051453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 431439074153028077470541 161789652807385529051453)
    ·
      refine ⟨60671119802769573394295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161789652807385529051453 60671119802769573394295)
      ·
        refine ⟨91006679704154360091443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60671119802769573394295 91006679704154360091443)
        ·
          refine ⟨136510019556231540137165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91006679704154360091443 136510019556231540137165)
          ·
            refine ⟨51191257333586827551437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136510019556231540137165 51191257333586827551437)
            ·
              refine ⟨19196721500095060331789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51191257333586827551437 19196721500095060331789)
              ·
                refine ⟨7198770562535647624421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19196721500095060331789 7198770562535647624421)
                ·
                  refine ⟨1349769480475433929579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7198770562535647624421 1349769480475433929579)
                  ·
                    rfl

theorem cell22_11829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_11829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11829 prefixEnd_11829 := by exact prefixLift 11829
  have htrace : WordTrace (prefixWord ++ tailWord_11829) baseStart_11829 baseEnd_11829 := by
    simpa [prefixWord, tailWord_11829, baseEnd_11829] using wordTrace_append hprefix tailTrace_11829
  have hstable : (prefixWord ++ tailWord_11829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11829).length < 2 ^ (prefixWord ++ tailWord_11829).sum := by decide
  have hdescent : baseEnd_11829 < baseStart_11829 := by decide
  rcases family_descends (prefixWord ++ tailWord_11829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11872 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 5, 3]
def baseStart_11872 : Nat := 118140960795 + 11872 * 2 ^ 59
def prefixEnd_11872 : Nat := 4983230072969 + 3 ^ 40 * 11872 * 2
def baseEnd_11872 : Nat := 4064028220188522963605

theorem tailTrace_11872 : CollatzResearch.WordTrace tailWord_11872 prefixEnd_11872 4064028220188522963605 := by
  unfold tailWord_11872
  simp only [CollatzResearch.WordTrace]
  refine ⟨216503706498623210642935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 288671608664830947523913 216503706498623210642935)
  ·
    refine ⟨324755559747934815964403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216503706498623210642935 324755559747934815964403)
    ·
      refine ⟨487133339621902223946605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324755559747934815964403 487133339621902223946605)
      ·
        refine ⟨182675002358213333979977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 487133339621902223946605 182675002358213333979977)
        ·
          refine ⟨137006251768660000484983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182675002358213333979977 137006251768660000484983)
          ·
            refine ⟨205509377652990000727475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137006251768660000484983 205509377652990000727475)
            ·
              refine ⟨308264066479485001091213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205509377652990000727475 308264066479485001091213)
              ·
                refine ⟨115599024929806875409205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308264066479485001091213 115599024929806875409205)
                ·
                  refine ⟨10837408587169394569613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115599024929806875409205 10837408587169394569613)
                  ·
                    refine ⟨4064028220188522963605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10837408587169394569613 4064028220188522963605)
                    ·
                      rfl

theorem cell22_11872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 5, 3].length) (baseStart_11872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11872 prefixEnd_11872 := by exact prefixLift 11872
  have htrace : WordTrace (prefixWord ++ tailWord_11872) baseStart_11872 baseEnd_11872 := by
    simpa [prefixWord, tailWord_11872, baseEnd_11872] using wordTrace_append hprefix tailTrace_11872
  have hstable : (prefixWord ++ tailWord_11872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11872).length < 2 ^ (prefixWord ++ tailWord_11872).sum := by decide
  have hdescent : baseEnd_11872 < baseStart_11872 := by decide
  rcases family_descends (prefixWord ++ tailWord_11872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11964 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 6]
def baseStart_11964 : Nat := 118140960795 + 11964 * 2 ^ 59
def prefixEnd_11964 : Nat := 4983230072969 + 3 ^ 40 * 11964 * 2
def baseEnd_11964 : Nat := 1365173900110316554441

theorem tailTrace_11964 : CollatzResearch.WordTrace tailWord_11964 prefixEnd_11964 1365173900110316554441 := by
  unfold tailWord_11964
  simp only [CollatzResearch.WordTrace]
  refine ⟨218181464331973066817473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 290908619109297422423297 218181464331973066817473)
  ·
    refine ⟨163636098248979800113105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218181464331973066817473 163636098248979800113105)
    ·
      refine ⟨122727073686734850084829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163636098248979800113105 122727073686734850084829)
      ·
        refine ⟨46022652632525568781811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122727073686734850084829 46022652632525568781811)
        ·
          refine ⟨69033978948788353172717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46022652632525568781811 69033978948788353172717)
          ·
            refine ⟨25887742105795632439769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69033978948788353172717 25887742105795632439769)
            ·
              refine ⟨19415806579346724329827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25887742105795632439769 19415806579346724329827)
              ·
                refine ⟨29123709869020086494741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19415806579346724329827 29123709869020086494741)
                ·
                  refine ⟨1365173900110316554441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29123709869020086494741 1365173900110316554441)
                  ·
                    rfl

theorem cell22_11964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_11964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11964 prefixEnd_11964 := by exact prefixLift 11964
  have htrace : WordTrace (prefixWord ++ tailWord_11964) baseStart_11964 baseEnd_11964 := by
    simpa [prefixWord, tailWord_11964, baseEnd_11964] using wordTrace_append hprefix tailTrace_11964
  have hstable : (prefixWord ++ tailWord_11964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11964).length < 2 ^ (prefixWord ++ tailWord_11964).sum := by decide
  have hdescent : baseEnd_11964 < baseStart_11964 := by decide
  rcases family_descends (prefixWord ++ tailWord_11964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11979 : List Nat := [1, 1, 1, 1, 3, 2, 1, 7, 2, 3]
def baseStart_11979 : Nat := 118140960795 + 11979 * 2 ^ 59
def prefixEnd_11979 : Nat := 4983230072969 + 3 ^ 40 * 11979 * 2
def baseEnd_11979 : Nat := 4100656506875910538277

theorem tailTrace_11979 : CollatzResearch.WordTrace tailWord_11979 prefixEnd_11979 4100656506875910538277 := by
  unfold tailWord_11979
  simp only [CollatzResearch.WordTrace]
  refine ⟨436910023609603695430991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 291273349073069130287327 436910023609603695430991)
  ·
    refine ⟨655365035414405543146487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 436910023609603695430991 655365035414405543146487)
    ·
      refine ⟨983047553121608314719731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 655365035414405543146487 983047553121608314719731)
      ·
        refine ⟨1474571329682412472079597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983047553121608314719731 1474571329682412472079597)
        ·
          refine ⟨552964248630904677029849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1474571329682412472079597 552964248630904677029849)
          ·
            refine ⟨414723186473178507772387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552964248630904677029849 414723186473178507772387)
            ·
              refine ⟨622084779709767761658581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414723186473178507772387 622084779709767761658581)
              ·
                refine ⟨14580112024447681913873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 622084779709767761658581 14580112024447681913873)
                ·
                  refine ⟨10935084018335761435405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14580112024447681913873 10935084018335761435405)
                  ·
                    refine ⟨4100656506875910538277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10935084018335761435405 4100656506875910538277)
                    ·
                      rfl

theorem cell22_11979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 3].length) (baseStart_11979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11979 prefixEnd_11979 := by exact prefixLift 11979
  have htrace : WordTrace (prefixWord ++ tailWord_11979) baseStart_11979 baseEnd_11979 := by
    simpa [prefixWord, tailWord_11979, baseEnd_11979] using wordTrace_append hprefix tailTrace_11979
  have hstable : (prefixWord ++ tailWord_11979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11979).length < 2 ^ (prefixWord ++ tailWord_11979).sum := by decide
  have hdescent : baseEnd_11979 < baseStart_11979 := by decide
  rcases family_descends (prefixWord ++ tailWord_11979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11981 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 6]
def baseStart_11981 : Nat := 118140960795 + 11981 * 2 ^ 59
def prefixEnd_11981 : Nat := 4983230072969 + 3 ^ 40 * 11981 * 2
def baseEnd_11981 : Nat := 1367113715916190662757

theorem tailTrace_11981 : CollatzResearch.WordTrace tailWord_11981 prefixEnd_11981 1367113715916190662757 := by
  unfold tailWord_11981
  simp only [CollatzResearch.WordTrace]
  refine ⟨436982969602358037003797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 291321979734905358002531 436982969602358037003797)
  ·
    refine ⟨20483576700110532984553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 436982969602358037003797 20483576700110532984553)
    ·
      refine ⟨15362682525082899738415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20483576700110532984553 15362682525082899738415)
      ·
        refine ⟨23044023787624349607623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15362682525082899738415 23044023787624349607623)
        ·
          refine ⟨34566035681436524411435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23044023787624349607623 34566035681436524411435)
          ·
            refine ⟨51849053522154786617153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34566035681436524411435 51849053522154786617153)
            ·
              refine ⟨38886790141616089962865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51849053522154786617153 38886790141616089962865)
              ·
                refine ⟨29165092606212067472149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38886790141616089962865 29165092606212067472149)
                ·
                  refine ⟨1367113715916190662757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29165092606212067472149 1367113715916190662757)
                  ·
                    rfl

theorem cell22_11981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_11981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11981 prefixEnd_11981 := by exact prefixLift 11981
  have htrace : WordTrace (prefixWord ++ tailWord_11981) baseStart_11981 baseEnd_11981 := by
    simpa [prefixWord, tailWord_11981, baseEnd_11981] using wordTrace_append hprefix tailTrace_11981
  have hstable : (prefixWord ++ tailWord_11981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11981).length < 2 ^ (prefixWord ++ tailWord_11981).sum := by decide
  have hdescent : baseEnd_11981 < baseStart_11981 := by decide
  rcases family_descends (prefixWord ++ tailWord_11981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11992 : List Nat := [2, 1, 2, 2, 3, 1, 3, 8]
def baseStart_11992 : Nat := 118140960795 + 11992 * 2 ^ 59
def prefixEnd_11992 : Nat := 4983230072969 + 3 ^ 40 * 11992 * 2
def baseEnd_11992 : Nat := 456122963616467773693

theorem tailTrace_11992 : CollatzResearch.WordTrace tailWord_11992 prefixEnd_11992 456122963616467773693 := by
  unfold tailWord_11992
  simp only [CollatzResearch.WordTrace]
  refine ⟨218692086281253457827115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 291589448375004610436153 218692086281253457827115)
  ·
    refine ⟨328038129421880186740673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218692086281253457827115 328038129421880186740673)
    ·
      refine ⟨246028597066410140055505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328038129421880186740673 246028597066410140055505)
      ·
        refine ⟨184521447799807605041629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246028597066410140055505 184521447799807605041629)
        ·
          refine ⟨69195542924927851890611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184521447799807605041629 69195542924927851890611)
          ·
            refine ⟨103793314387391777835917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69195542924927851890611 103793314387391777835917)
            ·
              refine ⟨38922492895271916688469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103793314387391777835917 38922492895271916688469)
              ·
                refine ⟨456122963616467773693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 38922492895271916688469 456122963616467773693)
                ·
                  rfl

theorem cell22_11992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 8].length) (baseStart_11992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_11992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_11992 prefixEnd_11992 := by exact prefixLift 11992
  have htrace : WordTrace (prefixWord ++ tailWord_11992) baseStart_11992 baseEnd_11992 := by
    simpa [prefixWord, tailWord_11992, baseEnd_11992] using wordTrace_append hprefix tailTrace_11992
  have hstable : (prefixWord ++ tailWord_11992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11992).length < 2 ^ (prefixWord ++ tailWord_11992).sum := by decide
  have hdescent : baseEnd_11992 < baseStart_11992 := by decide
  rcases family_descends (prefixWord ++ tailWord_11992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12024 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 3, 3]
def baseStart_12024 : Nat := 118140960795 + 12024 * 2 ^ 59
def prefixEnd_12024 : Nat := 4983230072969 + 3 ^ 40 * 12024 * 2
def baseEnd_12024 : Nat := 4116060926510793163139

theorem tailTrace_12024 : CollatzResearch.WordTrace tailWord_12024 prefixEnd_12024 4116060926510793163139 := by
  unfold tailWord_12024
  simp only [CollatzResearch.WordTrace]
  refine ⟨219275654223288190409563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 292367538964384253879417 219275654223288190409563)
  ·
    refine ⟨328913481334932285614345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219275654223288190409563 328913481334932285614345)
    ·
      refine ⟨246685111001199214210759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328913481334932285614345 246685111001199214210759)
      ·
        refine ⟨370027666501798821316139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246685111001199214210759 370027666501798821316139)
        ·
          refine ⟨555041499752698231974209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370027666501798821316139 555041499752698231974209)
          ·
            refine ⟨416281124814523673980657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 555041499752698231974209 416281124814523673980657)
            ·
              refine ⟨312210843610892755485493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416281124814523673980657 312210843610892755485493)
              ·
                refine ⟨29269766588521195826765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312210843610892755485493 29269766588521195826765)
                ·
                  refine ⟨10976162470695448435037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29269766588521195826765 10976162470695448435037)
                  ·
                    refine ⟨4116060926510793163139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10976162470695448435037 4116060926510793163139)
                    ·
                      rfl

theorem cell22_12024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_12024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12024 prefixEnd_12024 := by exact prefixLift 12024
  have htrace : WordTrace (prefixWord ++ tailWord_12024) baseStart_12024 baseEnd_12024 := by
    simpa [prefixWord, tailWord_12024, baseEnd_12024] using wordTrace_append hprefix tailTrace_12024
  have hstable : (prefixWord ++ tailWord_12024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12024).length < 2 ^ (prefixWord ++ tailWord_12024).sum := by decide
  have hdescent : baseEnd_12024 < baseStart_12024 := by decide
  rcases family_descends (prefixWord ++ tailWord_12024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12086 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_12086 : Nat := 118140960795 + 12086 * 2 ^ 59
def prefixEnd_12086 : Nat := 4983230072969 + 3 ^ 40 * 12086 * 2
def baseEnd_12086 : Nat := 4137284793563298112949

theorem tailTrace_12086 : CollatzResearch.WordTrace tailWord_12086 prefixEnd_12086 4137284793563298112949 := by
  unfold tailWord_12086
  simp only [CollatzResearch.WordTrace]
  refine ⟨27550789638872560598507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 293875089481307313050741 27550789638872560598507)
  ·
    refine ⟨41326184458308840897761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27550789638872560598507 41326184458308840897761)
    ·
      refine ⟨30994638343731630673321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41326184458308840897761 30994638343731630673321)
      ·
        refine ⟨23245978757798723004991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30994638343731630673321 23245978757798723004991)
        ·
          refine ⟨34868968136698084507487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23245978757798723004991 34868968136698084507487)
          ·
            refine ⟨52303452205047126761231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34868968136698084507487 52303452205047126761231)
            ·
              refine ⟨78455178307570690141847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52303452205047126761231 78455178307570690141847)
              ·
                refine ⟨117682767461356035212771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78455178307570690141847 117682767461356035212771)
                ·
                  refine ⟨176524151192034052819157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117682767461356035212771 176524151192034052819157)
                  ·
                    refine ⟨4137284793563298112949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 176524151192034052819157 4137284793563298112949)
                    ·
                      rfl

theorem cell22_12086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_12086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12086 prefixEnd_12086 := by exact prefixLift 12086
  have htrace : WordTrace (prefixWord ++ tailWord_12086) baseStart_12086 baseEnd_12086 := by
    simpa [prefixWord, tailWord_12086, baseEnd_12086] using wordTrace_append hprefix tailTrace_12086
  have hstable : (prefixWord ++ tailWord_12086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12086).length < 2 ^ (prefixWord ++ tailWord_12086).sum := by decide
  have hdescent : baseEnd_12086 < baseStart_12086 := by decide
  rcases family_descends (prefixWord ++ tailWord_12086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12099 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 6]
def baseStart_12099 : Nat := 118140960795 + 12099 * 2 ^ 59
def prefixEnd_12099 : Nat := 4983230072969 + 3 ^ 40 * 12099 * 2
def baseEnd_12099 : Nat := 1380578319745199179303

theorem tailTrace_12099 : CollatzResearch.WordTrace tailWord_12099 prefixEnd_12099 1380578319745199179303 := by
  unfold tailWord_12099
  simp only [CollatzResearch.WordTrace]
  refine ⟨441286783174864189799351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 294191188783242793199567 441286783174864189799351)
  ·
    refine ⟨661930174762296284699027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 441286783174864189799351 661930174762296284699027)
    ·
      refine ⟨992895262143444427048541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 661930174762296284699027 992895262143444427048541)
      ·
        refine ⟨372335723303791660143203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 992895262143444427048541 372335723303791660143203)
        ·
          refine ⟨558503584955687490214805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372335723303791660143203 558503584955687490214805)
          ·
            refine ⟨26179855544797851103819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 558503584955687490214805 26179855544797851103819)
            ·
              refine ⟨39269783317196776655729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26179855544797851103819 39269783317196776655729)
              ·
                refine ⟨29452337487897582491797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39269783317196776655729 29452337487897582491797)
                ·
                  refine ⟨1380578319745199179303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29452337487897582491797 1380578319745199179303)
                  ·
                    rfl

theorem cell22_12099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 6].length) (baseStart_12099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12099 prefixEnd_12099 := by exact prefixLift 12099
  have htrace : WordTrace (prefixWord ++ tailWord_12099) baseStart_12099 baseEnd_12099 := by
    simpa [prefixWord, tailWord_12099, baseEnd_12099] using wordTrace_append hprefix tailTrace_12099
  have hstable : (prefixWord ++ tailWord_12099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12099).length < 2 ^ (prefixWord ++ tailWord_12099).sum := by decide
  have hdescent : baseEnd_12099 < baseStart_12099 := by decide
  rcases family_descends (prefixWord ++ tailWord_12099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12129 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 4, 4]
def baseStart_12129 : Nat := 118140960795 + 12129 * 2 ^ 59
def prefixEnd_12129 : Nat := 4983230072969 + 3 ^ 40 * 12129 * 2
def baseEnd_12129 : Nat := 4152004572325519287817

theorem tailTrace_12129 : CollatzResearch.WordTrace tailWord_12129 prefixEnd_12129 4152004572325519287817 := by
  unfold tailWord_12129
  simp only [CollatzResearch.WordTrace]
  refine ⟨442380973066179313391441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 294920648710786208927627 442380973066179313391441)
  ·
    refine ⟨331785729799634485043581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 442380973066179313391441 331785729799634485043581)
    ·
      refine ⟨124419648674862931891343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 331785729799634485043581 124419648674862931891343)
      ·
        refine ⟨186629473012294397837015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124419648674862931891343 186629473012294397837015)
        ·
          refine ⟨279944209518441596755523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186629473012294397837015 279944209518441596755523)
          ·
            refine ⟨419916314277662395133285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279944209518441596755523 419916314277662395133285)
            ·
              refine ⟨78734308927061699087491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 419916314277662395133285 78734308927061699087491)
              ·
                refine ⟨118101463390592548631237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78734308927061699087491 118101463390592548631237)
                ·
                  refine ⟨22144024385736102868357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118101463390592548631237 22144024385736102868357)
                  ·
                    refine ⟨4152004572325519287817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22144024385736102868357 4152004572325519287817)
                    ·
                      rfl

theorem cell22_12129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_12129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12129 prefixEnd_12129 := by exact prefixLift 12129
  have htrace : WordTrace (prefixWord ++ tailWord_12129) baseStart_12129 baseEnd_12129 := by
    simpa [prefixWord, tailWord_12129, baseEnd_12129] using wordTrace_append hprefix tailTrace_12129
  have hstable : (prefixWord ++ tailWord_12129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12129).length < 2 ^ (prefixWord ++ tailWord_12129).sum := by decide
  have hdescent : baseEnd_12129 < baseStart_12129 := by decide
  rcases family_descends (prefixWord ++ tailWord_12129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12281 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 1, 6]
def baseStart_12281 : Nat := 118140960795 + 12281 * 2 ^ 59
def prefixEnd_12281 : Nat := 4983230072969 + 3 ^ 40 * 12281 * 2
def baseEnd_12281 : Nat := 4204037278647789487351

theorem tailTrace_12281 : CollatzResearch.WordTrace tailWord_12281 prefixEnd_12281 4204037278647789487351 := by
  unfold tailWord_12281
  simp only [CollatzResearch.WordTrace]
  refine ⟨447924868515509272924697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 298616579010339515283131 447924868515509272924697)
  ·
    refine ⟨335943651386631954693523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 447924868515509272924697 335943651386631954693523)
    ·
      refine ⟨503915477079947932040285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335943651386631954693523 503915477079947932040285)
      ·
        refine ⟨188968303904980474515107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 503915477079947932040285 188968303904980474515107)
        ·
          refine ⟨283452455857470711772661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188968303904980474515107 283452455857470711772661)
          ·
            refine ⟨26573667736637879228687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 283452455857470711772661 26573667736637879228687)
            ·
              refine ⟨39860501604956818843031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26573667736637879228687 39860501604956818843031)
              ·
                refine ⟨59790752407435228264547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39860501604956818843031 59790752407435228264547)
                ·
                  refine ⟨89686128611152842396821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59790752407435228264547 89686128611152842396821)
                  ·
                    refine ⟨4204037278647789487351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89686128611152842396821 4204037278647789487351)
                    ·
                      rfl

theorem cell22_12281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_12281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12281 prefixEnd_12281 := by exact prefixLift 12281
  have htrace : WordTrace (prefixWord ++ tailWord_12281) baseStart_12281 baseEnd_12281 := by
    simpa [prefixWord, tailWord_12281, baseEnd_12281] using wordTrace_append hprefix tailTrace_12281
  have hstable : (prefixWord ++ tailWord_12281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12281).length < 2 ^ (prefixWord ++ tailWord_12281).sum := by decide
  have hdescent : baseEnd_12281 < baseStart_12281 := by decide
  rcases family_descends (prefixWord ++ tailWord_12281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12317 : List Nat := [1, 4, 2, 2, 2, 2, 3, 1, 2, 3]
def baseStart_12317 : Nat := 118140960795 + 12317 * 2 ^ 59
def prefixEnd_12317 : Nat := 4983230072969 + 3 ^ 40 * 12317 * 2
def baseEnd_12317 : Nat := 4216360814355695587241

theorem tailTrace_12317 : CollatzResearch.WordTrace tailWord_12317 prefixEnd_12317 4216360814355695587241 := by
  unfold tailWord_12317
  simp only [CollatzResearch.WordTrace]
  refine ⟨449237896385087421235205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 299491930923391614156803 449237896385087421235205)
  ·
    refine ⟨84232105572203891481601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 449237896385087421235205 84232105572203891481601)
    ·
      refine ⟨63174079179152918611201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84232105572203891481601 63174079179152918611201)
      ·
        refine ⟨47380559384364688958401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63174079179152918611201 47380559384364688958401)
        ·
          refine ⟨35535419538273516718801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47380559384364688958401 35535419538273516718801)
          ·
            refine ⟨26651564653705137539101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35535419538273516718801 26651564653705137539101)
            ·
              refine ⟨9994336745139426577163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26651564653705137539101 9994336745139426577163)
              ·
                refine ⟨14991505117709139865745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9994336745139426577163 14991505117709139865745)
                ·
                  refine ⟨11243628838281854899309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14991505117709139865745 11243628838281854899309)
                  ·
                    refine ⟨4216360814355695587241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11243628838281854899309 4216360814355695587241)
                    ·
                      rfl

theorem cell22_12317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_12317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12317 prefixEnd_12317 := by exact prefixLift 12317
  have htrace : WordTrace (prefixWord ++ tailWord_12317) baseStart_12317 baseEnd_12317 := by
    simpa [prefixWord, tailWord_12317, baseEnd_12317] using wordTrace_append hprefix tailTrace_12317
  have hstable : (prefixWord ++ tailWord_12317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12317).length < 2 ^ (prefixWord ++ tailWord_12317).sum := by decide
  have hdescent : baseEnd_12317 < baseStart_12317 := by decide
  rcases family_descends (prefixWord ++ tailWord_12317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12330 : List Nat := [3, 1, 4, 1, 2, 3, 2, 6]
def baseStart_12330 : Nat := 118140960795 + 12330 * 2 ^ 59
def prefixEnd_12330 : Nat := 4983230072969 + 3 ^ 40 * 12330 * 2
def baseEnd_12330 : Nat := 468978997780888334689

theorem tailTrace_12330 : CollatzResearch.WordTrace tailWord_12330 prefixEnd_12330 468978997780888334689 := by
  unfold tailWord_12330
  simp only [CollatzResearch.WordTrace]
  refine ⟨112428011334497660364611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 299808030225327094305629 112428011334497660364611)
  ·
    refine ⟨168642017001746490546917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112428011334497660364611 168642017001746490546917)
    ·
      refine ⟨31620378187827466977547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168642017001746490546917 31620378187827466977547)
      ·
        refine ⟨47430567281741200466321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31620378187827466977547 47430567281741200466321)
        ·
          refine ⟨35572925461305900349741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47430567281741200466321 35572925461305900349741)
          ·
            refine ⟨13339847047989712631153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35572925461305900349741 13339847047989712631153)
            ·
              refine ⟨10004885285992284473365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13339847047989712631153 10004885285992284473365)
              ·
                refine ⟨468978997780888334689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10004885285992284473365 468978997780888334689)
                ·
                  rfl

theorem cell22_12330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 6].length) (baseStart_12330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12330 prefixEnd_12330 := by exact prefixLift 12330
  have htrace : WordTrace (prefixWord ++ tailWord_12330) baseStart_12330 baseEnd_12330 := by
    simpa [prefixWord, tailWord_12330, baseEnd_12330] using wordTrace_append hprefix tailTrace_12330
  have hstable : (prefixWord ++ tailWord_12330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12330).length < 2 ^ (prefixWord ++ tailWord_12330).sum := by decide
  have hdescent : baseEnd_12330 < baseStart_12330 := by decide
  rcases family_descends (prefixWord ++ tailWord_12330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12341 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 7]
def baseStart_12341 : Nat := 118140960795 + 12341 * 2 ^ 59
def prefixEnd_12341 : Nat := 4983230072969 + 3 ^ 40 * 12341 * 2
def baseEnd_12341 : Nat := 1408192168275877662389

theorem tailTrace_12341 : CollatzResearch.WordTrace tailWord_12341 prefixEnd_12341 1408192168275877662389 := by
  unfold tailWord_12341
  simp only [CollatzResearch.WordTrace]
  refine ⟨450113248298139520108877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 300075498865426346739251 450113248298139520108877)
  ·
    refine ⟨168792468111802320040829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 450113248298139520108877 168792468111802320040829)
    ·
      refine ⟨63297175541925870015311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168792468111802320040829 63297175541925870015311)
      ·
        refine ⟨94945763312888805022967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63297175541925870015311 94945763312888805022967)
        ·
          refine ⟨142418644969333207534451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94945763312888805022967 142418644969333207534451)
          ·
            refine ⟨213627967453999811301677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142418644969333207534451 213627967453999811301677)
            ·
              refine ⟨80110487795249929238129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213627967453999811301677 80110487795249929238129)
              ·
                refine ⟨60082865846437446928597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80110487795249929238129 60082865846437446928597)
                ·
                  refine ⟨1408192168275877662389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 60082865846437446928597 1408192168275877662389)
                  ·
                    rfl

theorem cell22_12341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_12341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12341 prefixEnd_12341 := by exact prefixLift 12341
  have htrace : WordTrace (prefixWord ++ tailWord_12341) baseStart_12341 baseEnd_12341 := by
    simpa [prefixWord, tailWord_12341, baseEnd_12341] using wordTrace_append hprefix tailTrace_12341
  have hstable : (prefixWord ++ tailWord_12341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12341).length < 2 ^ (prefixWord ++ tailWord_12341).sum := by decide
  have hdescent : baseEnd_12341 < baseStart_12341 := by decide
  rcases family_descends (prefixWord ++ tailWord_12341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12416 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 3, 6]
def baseStart_12416 : Nat := 118140960795 + 12416 * 2 ^ 59
def prefixEnd_12416 : Nat := 4983230072969 + 3 ^ 40 * 12416 * 2
def baseEnd_12416 : Nat := 4250250537552437361937

theorem tailTrace_12416 : CollatzResearch.WordTrace tailWord_12416 prefixEnd_12416 4250250537552437361937 := by
  unfold tailWord_12416
  simp only [CollatzResearch.WordTrace]
  refine ⟨226424361513213664544551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 301899148684284886059401 226424361513213664544551)
  ·
    refine ⟨339636542269820496816827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226424361513213664544551 339636542269820496816827)
    ·
      refine ⟨509454813404730745225241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339636542269820496816827 509454813404730745225241)
      ·
        refine ⟨382091110053548058918931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509454813404730745225241 382091110053548058918931)
        ·
          refine ⟨573136665080322088378397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382091110053548058918931 573136665080322088378397)
          ·
            refine ⟨214926249405120783141899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 573136665080322088378397 214926249405120783141899)
            ·
              refine ⟨322389374107681174712849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214926249405120783141899 322389374107681174712849)
              ·
                refine ⟨241792030580760881034637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322389374107681174712849 241792030580760881034637)
                ·
                  refine ⟨90672011467785330387989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241792030580760881034637 90672011467785330387989)
                  ·
                    refine ⟨4250250537552437361937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90672011467785330387989 4250250537552437361937)
                    ·
                      rfl

theorem cell22_12416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_12416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12416 prefixEnd_12416 := by exact prefixLift 12416
  have htrace : WordTrace (prefixWord ++ tailWord_12416) baseStart_12416 baseEnd_12416 := by
    simpa [prefixWord, tailWord_12416, baseEnd_12416] using wordTrace_append hprefix tailTrace_12416
  have hstable : (prefixWord ++ tailWord_12416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12416).length < 2 ^ (prefixWord ++ tailWord_12416).sum := by decide
  have hdescent : baseEnd_12416 < baseStart_12416 := by decide
  rcases family_descends (prefixWord ++ tailWord_12416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12420 : List Nat := [2, 3, 2, 1, 2, 1, 3, 4, 4]
def baseStart_12420 : Nat := 118140960795 + 12420 * 2 ^ 59
def prefixEnd_12420 : Nat := 4983230072969 + 3 ^ 40 * 12420 * 2
def baseEnd_12420 : Nat := 1417206606432586753975

theorem tailTrace_12420 : CollatzResearch.WordTrace tailWord_12420 prefixEnd_12420 1417206606432586753975 := by
  unfold tailWord_12420
  simp only [CollatzResearch.WordTrace]
  refine ⟨226497307505968006117357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 301996410007957341489809 226497307505968006117357)
  ·
    refine ⟨84936490314738002294009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226497307505968006117357 84936490314738002294009)
    ·
      refine ⟨63702367736053501720507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84936490314738002294009 63702367736053501720507)
      ·
        refine ⟨95553551604080252580761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63702367736053501720507 95553551604080252580761)
        ·
          refine ⟨71665163703060189435571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95553551604080252580761 71665163703060189435571)
          ·
            refine ⟨107497745554590284153357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71665163703060189435571 107497745554590284153357)
            ·
              refine ⟨40311654582971356557509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107497745554590284153357 40311654582971356557509)
              ·
                refine ⟨7558435234307129354533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40311654582971356557509 7558435234307129354533)
                ·
                  refine ⟨1417206606432586753975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7558435234307129354533 1417206606432586753975)
                  ·
                    rfl

theorem cell22_12420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_12420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12420 prefixEnd_12420 := by exact prefixLift 12420
  have htrace : WordTrace (prefixWord ++ tailWord_12420) baseStart_12420 baseEnd_12420 := by
    simpa [prefixWord, tailWord_12420, baseEnd_12420] using wordTrace_append hprefix tailTrace_12420
  have hstable : (prefixWord ++ tailWord_12420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12420).length < 2 ^ (prefixWord ++ tailWord_12420).sum := by decide
  have hdescent : baseEnd_12420 < baseStart_12420 := by decide
  rcases family_descends (prefixWord ++ tailWord_12420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12450 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_12450 : Nat := 118140960795 + 12450 * 2 ^ 59
def prefixEnd_12450 : Nat := 4983230072969 + 3 ^ 40 * 12450 * 2
def baseEnd_12450 : Nat := 4261889432387682011833

theorem tailTrace_12450 : CollatzResearch.WordTrace tailWord_12450 prefixEnd_12450 4261889432387682011833 := by
  unfold tailWord_12450
  simp only [CollatzResearch.WordTrace]
  refine ⟨113522201225812783956701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 302725869935500757217869 113522201225812783956701)
  ·
    refine ⟨42570825459679793983763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113522201225812783956701 42570825459679793983763)
    ·
      refine ⟨63856238189519690975645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42570825459679793983763 63856238189519690975645)
      ·
        refine ⟨23946089321069884115867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63856238189519690975645 23946089321069884115867)
        ·
          refine ⟨35919133981604826173801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23946089321069884115867 35919133981604826173801)
          ·
            refine ⟨26939350486203619630351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35919133981604826173801 26939350486203619630351)
            ·
              refine ⟨40409025729305429445527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26939350486203619630351 40409025729305429445527)
              ·
                refine ⟨60613538593958144168291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40409025729305429445527 60613538593958144168291)
                ·
                  refine ⟨90920307890937216252437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60613538593958144168291 90920307890937216252437)
                  ·
                    refine ⟨4261889432387682011833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90920307890937216252437 4261889432387682011833)
                    ·
                      rfl

theorem cell22_12450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_12450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12450 prefixEnd_12450 := by exact prefixLift 12450
  have htrace : WordTrace (prefixWord ++ tailWord_12450) baseStart_12450 baseEnd_12450 := by
    simpa [prefixWord, tailWord_12450, baseEnd_12450] using wordTrace_append hprefix tailTrace_12450
  have hstable : (prefixWord ++ tailWord_12450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12450).length < 2 ^ (prefixWord ++ tailWord_12450).sum := by decide
  have hdescent : baseEnd_12450 < baseStart_12450 := by decide
  rcases family_descends (prefixWord ++ tailWord_12450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12463 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 7, 3]
def baseStart_12463 : Nat := 118140960795 + 12463 * 2 ^ 59
def prefixEnd_12463 : Nat := 4983230072969 + 3 ^ 40 * 12463 * 2
def baseEnd_12463 : Nat := 4266339598059981436793

theorem tailTrace_12463 : CollatzResearch.WordTrace tailWord_12463 prefixEnd_12463 4266339598059981436793 := by
  unfold tailWord_12463
  simp only [CollatzResearch.WordTrace]
  refine ⟨454562953856154356050043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 303041969237436237366695 454562953856154356050043)
  ·
    refine ⟨681844430784231534075065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 454562953856154356050043 681844430784231534075065)
    ·
      refine ⟨511383323088173650556299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 681844430784231534075065 511383323088173650556299)
      ·
        refine ⟨767074984632260475834449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511383323088173650556299 767074984632260475834449)
        ·
          refine ⟨575306238474195356875837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767074984632260475834449 575306238474195356875837)
          ·
            refine ⟨215739839427823258828439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 575306238474195356875837 215739839427823258828439)
            ·
              refine ⟨323609759141734888242659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215739839427823258828439 323609759141734888242659)
              ·
                refine ⟨485414638712602332363989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323609759141734888242659 485414638712602332363989)
                ·
                  refine ⟨11376905594826617164781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 485414638712602332363989 11376905594826617164781)
                  ·
                    refine ⟨4266339598059981436793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11376905594826617164781 4266339598059981436793)
                    ·
                      rfl

theorem cell22_12463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 7, 3].length) (baseStart_12463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12463 prefixEnd_12463 := by exact prefixLift 12463
  have htrace : WordTrace (prefixWord ++ tailWord_12463) baseStart_12463 baseEnd_12463 := by
    simpa [prefixWord, tailWord_12463, baseEnd_12463] using wordTrace_append hprefix tailTrace_12463
  have hstable : (prefixWord ++ tailWord_12463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12463).length < 2 ^ (prefixWord ++ tailWord_12463).sum := by decide
  have hdescent : baseEnd_12463 < baseStart_12463 := by decide
  rcases family_descends (prefixWord ++ tailWord_12463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12480 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 3, 3]
def baseStart_12480 : Nat := 118140960795 + 12480 * 2 ^ 59
def prefixEnd_12480 : Nat := 4983230072969 + 3 ^ 40 * 12480 * 2
def baseEnd_12480 : Nat := 4272159045477603761741

theorem tailTrace_12480 : CollatzResearch.WordTrace tailWord_12480 prefixEnd_12480 4272159045477603761741 := by
  unfold tailWord_12480
  simp only [CollatzResearch.WordTrace]
  refine ⟨227591497397283129709447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 303455329863044172945929 227591497397283129709447)
  ·
    refine ⟨341387246095924694564171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227591497397283129709447 341387246095924694564171)
    ·
      refine ⟨512080869143887041846257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341387246095924694564171 512080869143887041846257)
      ·
        refine ⟨384060651857915281384693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512080869143887041846257 384060651857915281384693)
        ·
          refine ⟨36005686111679557629815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 384060651857915281384693 36005686111679557629815)
          ·
            refine ⟨54008529167519336444723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36005686111679557629815 54008529167519336444723)
            ·
              refine ⟨81012793751279004667085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54008529167519336444723 81012793751279004667085)
              ·
                refine ⟨30379797656729626750157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81012793751279004667085 30379797656729626750157)
                ·
                  refine ⟨11392424121273610031309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30379797656729626750157 11392424121273610031309)
                  ·
                    refine ⟨4272159045477603761741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11392424121273610031309 4272159045477603761741)
                    ·
                      rfl

theorem cell22_12480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 3, 3].length) (baseStart_12480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12480 prefixEnd_12480 := by exact prefixLift 12480
  have htrace : WordTrace (prefixWord ++ tailWord_12480) baseStart_12480 baseEnd_12480 := by
    simpa [prefixWord, tailWord_12480, baseEnd_12480] using wordTrace_append hprefix tailTrace_12480
  have hstable : (prefixWord ++ tailWord_12480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12480).length < 2 ^ (prefixWord ++ tailWord_12480).sum := by decide
  have hdescent : baseEnd_12480 < baseStart_12480 := by decide
  rcases family_descends (prefixWord ++ tailWord_12480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12645 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 7]
def baseStart_12645 : Nat := 118140960795 + 12645 * 2 ^ 59
def prefixEnd_12645 : Nat := 4983230072969 + 3 ^ 40 * 12645 * 2
def baseEnd_12645 : Nat := 1442880639157391128745

theorem tailTrace_12645 : CollatzResearch.WordTrace tailWord_12645 prefixEnd_12645 1442880639157391128745 := by
  unfold tailWord_12645
  simp only [CollatzResearch.WordTrace]
  refine ⟨461201039196799439175389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 307467359464532959450259 461201039196799439175389)
  ·
    refine ⟨172950389698799789690771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 461201039196799439175389 172950389698799789690771)
    ·
      refine ⟨259425584548199684536157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172950389698799789690771 259425584548199684536157)
      ·
        refine ⟨97284594205574881701059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259425584548199684536157 97284594205574881701059)
        ·
          refine ⟨145926891308362322551589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97284594205574881701059 145926891308362322551589)
          ·
            refine ⟨27361292120317935478423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145926891308362322551589 27361292120317935478423)
            ·
              refine ⟨41041938180476903217635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27361292120317935478423 41041938180476903217635)
              ·
                refine ⟨61562907270715354826453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41041938180476903217635 61562907270715354826453)
                ·
                  refine ⟨1442880639157391128745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 61562907270715354826453 1442880639157391128745)
                  ·
                    rfl

theorem cell22_12645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_12645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12645 prefixEnd_12645 := by exact prefixLift 12645
  have htrace : WordTrace (prefixWord ++ tailWord_12645) baseStart_12645 baseEnd_12645 := by
    simpa [prefixWord, tailWord_12645, baseEnd_12645] using wordTrace_append hprefix tailTrace_12645
  have hstable : (prefixWord ++ tailWord_12645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12645).length < 2 ^ (prefixWord ++ tailWord_12645).sum := by decide
  have hdescent : baseEnd_12645 < baseStart_12645 := by decide
  rcases family_descends (prefixWord ++ tailWord_12645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12707 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 6]
def baseStart_12707 : Nat := 118140960795 + 12707 * 2 ^ 59
def prefixEnd_12707 : Nat := 4983230072969 + 3 ^ 40 * 12707 * 2
def baseEnd_12707 : Nat := 1449955261508226112015

theorem tailTrace_12707 : CollatzResearch.WordTrace tailWord_12707 prefixEnd_12707 1449955261508226112015 := by
  unfold tailWord_12707
  simp only [CollatzResearch.WordTrace]
  refine ⟨463462364972184027932375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 308974909981456018621583 463462364972184027932375)
  ·
    refine ⟨695193547458276041898563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 463462364972184027932375 695193547458276041898563)
    ·
      refine ⟨1042790321187414062847845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 695193547458276041898563 1042790321187414062847845)
      ·
        refine ⟨195523185222640136783971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1042790321187414062847845 195523185222640136783971)
        ·
          refine ⟨293284777833960205175957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195523185222640136783971 293284777833960205175957)
          ·
            refine ⟨13747723960966884617623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 293284777833960205175957 13747723960966884617623)
            ·
              refine ⟨20621585941450326926435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13747723960966884617623 20621585941450326926435)
              ·
                refine ⟨30932378912175490389653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20621585941450326926435 30932378912175490389653)
                ·
                  refine ⟨1449955261508226112015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30932378912175490389653 1449955261508226112015)
                  ·
                    rfl

theorem cell22_12707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 6].length) (baseStart_12707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12707 prefixEnd_12707 := by exact prefixLift 12707
  have htrace : WordTrace (prefixWord ++ tailWord_12707) baseStart_12707 baseEnd_12707 := by
    simpa [prefixWord, tailWord_12707, baseEnd_12707] using wordTrace_append hprefix tailTrace_12707
  have hstable : (prefixWord ++ tailWord_12707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12707).length < 2 ^ (prefixWord ++ tailWord_12707).sum := by decide
  have hdescent : baseEnd_12707 < baseStart_12707 := by decide
  rcases family_descends (prefixWord ++ tailWord_12707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12756 : List Nat := [2, 4, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_12756 : Nat := 118140960795 + 12756 * 2 ^ 59
def prefixEnd_12756 : Nat := 4983230072969 + 3 ^ 40 * 12756 * 2
def baseEnd_12756 : Nat := 4366639485904883860895

theorem tailTrace_12756 : CollatzResearch.WordTrace tailWord_12756 prefixEnd_12756 4366639485904883860895 := by
  unfold tailWord_12756
  simp only [CollatzResearch.WordTrace]
  refine ⟨232624770897332698233061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 310166361196443597644081 232624770897332698233061)
  ·
    refine ⟨43617144543249880918699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 232624770897332698233061 43617144543249880918699)
    ·
      refine ⟨65425716814874821378049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43617144543249880918699 65425716814874821378049)
      ·
        refine ⟨49069287611156116033537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65425716814874821378049 49069287611156116033537)
        ·
          refine ⟨36801965708367087025153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49069287611156116033537 36801965708367087025153)
          ·
            refine ⟨27601474281275315268865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36801965708367087025153 27601474281275315268865)
            ·
              refine ⟨20701105710956486451649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27601474281275315268865 20701105710956486451649)
              ·
                refine ⟨15525829283217364838737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20701105710956486451649 15525829283217364838737)
                ·
                  refine ⟨11644371962413023629053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15525829283217364838737 11644371962413023629053)
                  ·
                    refine ⟨4366639485904883860895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11644371962413023629053 4366639485904883860895)
                    ·
                      rfl

theorem cell22_12756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_12756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12756 prefixEnd_12756 := by exact prefixLift 12756
  have htrace : WordTrace (prefixWord ++ tailWord_12756) baseStart_12756 baseEnd_12756 := by
    simpa [prefixWord, tailWord_12756, baseEnd_12756] using wordTrace_append hprefix tailTrace_12756
  have hstable : (prefixWord ++ tailWord_12756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12756).length < 2 ^ (prefixWord ++ tailWord_12756).sum := by decide
  have hdescent : baseEnd_12756 < baseStart_12756 := by decide
  rcases family_descends (prefixWord ++ tailWord_12756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12795 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 6, 5]
def baseStart_12795 : Nat := 118140960795 + 12795 * 2 ^ 59
def prefixEnd_12795 : Nat := 4983230072969 + 3 ^ 40 * 12795 * 2
def baseEnd_12795 : Nat := 4379989982921782135775

theorem tailTrace_12795 : CollatzResearch.WordTrace tailWord_12795 prefixEnd_12795 4379989982921782135775 := by
  unfold tailWord_12795
  simp only [CollatzResearch.WordTrace]
  refine ⟨466671988653375057135839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 311114659102250038090559 466671988653375057135839)
  ·
    refine ⟨700007982980062585703759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 466671988653375057135839 700007982980062585703759)
    ·
      refine ⟨1050011974470093878555639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 700007982980062585703759 1050011974470093878555639)
      ·
        refine ⟨1575017961705140817833459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050011974470093878555639 1575017961705140817833459)
        ·
          refine ⟨2362526942557711226750189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1575017961705140817833459 2362526942557711226750189)
          ·
            refine ⟨885947603459141710031321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2362526942557711226750189 885947603459141710031321)
            ·
              refine ⟨664460702594356282523491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885947603459141710031321 664460702594356282523491)
              ·
                refine ⟨996691053891534423785237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664460702594356282523491 996691053891534423785237)
                ·
                  refine ⟨46719893151165676114933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 996691053891534423785237 46719893151165676114933)
                  ·
                    refine ⟨4379989982921782135775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46719893151165676114933 4379989982921782135775)
                    ·
                      rfl

theorem cell22_12795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 5].length) (baseStart_12795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12795 prefixEnd_12795 := by exact prefixLift 12795
  have htrace : WordTrace (prefixWord ++ tailWord_12795) baseStart_12795 baseEnd_12795 := by
    simpa [prefixWord, tailWord_12795, baseEnd_12795] using wordTrace_append hprefix tailTrace_12795
  have hstable : (prefixWord ++ tailWord_12795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12795).length < 2 ^ (prefixWord ++ tailWord_12795).sum := by decide
  have hdescent : baseEnd_12795 < baseStart_12795 := by decide
  rcases family_descends (prefixWord ++ tailWord_12795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12801 : List Nat := [1, 2, 4, 1, 3, 1, 1, 5, 1, 3]
def baseStart_12801 : Nat := 118140960795 + 12801 * 2 ^ 59
def prefixEnd_12801 : Nat := 4983230072969 + 3 ^ 40 * 12801 * 2
def baseEnd_12801 : Nat := 4382043905539766485757

theorem tailTrace_12801 : CollatzResearch.WordTrace tailWord_12801 prefixEnd_12801 4382043905539766485757 := by
  unfold tailWord_12801
  simp only [CollatzResearch.WordTrace]
  refine ⟨466890826631638081854257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 311260551087758721236171 466890826631638081854257)
  ·
    refine ⟨350168119973728561390693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 466890826631638081854257 350168119973728561390693)
    ·
      refine ⟨65656522495074105260755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 350168119973728561390693 65656522495074105260755)
      ·
        refine ⟨98484783742611157891133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65656522495074105260755 98484783742611157891133)
        ·
          refine ⟨36931793903479184209175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98484783742611157891133 36931793903479184209175)
          ·
            refine ⟨55397690855218776313763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36931793903479184209175 55397690855218776313763)
            ·
              refine ⟨83096536282828164470645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55397690855218776313763 83096536282828164470645)
              ·
                refine ⟨7790300276515140419123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83096536282828164470645 7790300276515140419123)
                ·
                  refine ⟨11685450414772710628685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7790300276515140419123 11685450414772710628685)
                  ·
                    refine ⟨4382043905539766485757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11685450414772710628685 4382043905539766485757)
                    ·
                      rfl

theorem cell22_12801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_12801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12801 prefixEnd_12801 := by exact prefixLift 12801
  have htrace : WordTrace (prefixWord ++ tailWord_12801) baseStart_12801 baseEnd_12801 := by
    simpa [prefixWord, tailWord_12801, baseEnd_12801] using wordTrace_append hprefix tailTrace_12801
  have hstable : (prefixWord ++ tailWord_12801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12801).length < 2 ^ (prefixWord ++ tailWord_12801).sum := by decide
  have hdescent : baseEnd_12801 < baseStart_12801 := by decide
  rcases family_descends (prefixWord ++ tailWord_12801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12812 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_12812 : Nat := 118140960795 + 12812 * 2 ^ 59
def prefixEnd_12812 : Nat := 4983230072969 + 3 ^ 40 * 12812 * 2
def baseEnd_12812 : Nat := 4385809430339404460723

theorem tailTrace_12812 : CollatzResearch.WordTrace tailWord_12812 prefixEnd_12812 4385809430339404460723 := by
  unfold tailWord_12812
  simp only [CollatzResearch.WordTrace]
  refine ⟨233646014795893480252345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 311528019727857973669793 233646014795893480252345)
  ·
    refine ⟨175234511096920110189259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233646014795893480252345 175234511096920110189259)
    ·
      refine ⟨262851766645380165283889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175234511096920110189259 262851766645380165283889)
      ·
        refine ⟨197138824984035123962917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262851766645380165283889 197138824984035123962917)
        ·
          refine ⟨36963529684506585743047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197138824984035123962917 36963529684506585743047)
          ·
            refine ⟨55445294526759878614571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36963529684506585743047 55445294526759878614571)
            ·
              refine ⟨83167941790139817921857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55445294526759878614571 83167941790139817921857)
              ·
                refine ⟨62375956342604863441393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83167941790139817921857 62375956342604863441393)
                ·
                  refine ⟨46781967256953647581045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62375956342604863441393 46781967256953647581045)
                  ·
                    refine ⟨4385809430339404460723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46781967256953647581045 4385809430339404460723)
                    ·
                      rfl

theorem cell22_12812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_12812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12812 prefixEnd_12812 := by exact prefixLift 12812
  have htrace : WordTrace (prefixWord ++ tailWord_12812) baseStart_12812 baseEnd_12812 := by
    simpa [prefixWord, tailWord_12812, baseEnd_12812] using wordTrace_append hprefix tailTrace_12812
  have hstable : (prefixWord ++ tailWord_12812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12812).length < 2 ^ (prefixWord ++ tailWord_12812).sum := by decide
  have hdescent : baseEnd_12812 < baseStart_12812 := by decide
  rcases family_descends (prefixWord ++ tailWord_12812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12814 : List Nat := [4, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_12814 : Nat := 118140960795 + 12814 * 2 ^ 59
def prefixEnd_12814 : Nat := 4983230072969 + 3 ^ 40 * 12814 * 2
def baseEnd_12814 : Nat := 1462164690404021970239

theorem tailTrace_12814 : CollatzResearch.WordTrace tailWord_12814 prefixEnd_12814 1462164690404021970239 := by
  unfold tailWord_12814
  simp only [CollatzResearch.WordTrace]
  refine ⟨58420621948067662759687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 311576650389694201384997 58420621948067662759687)
  ·
    refine ⟨87630932922101494139531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58420621948067662759687 87630932922101494139531)
    ·
      refine ⟨131446399383152241209297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87630932922101494139531 131446399383152241209297)
      ·
        refine ⟨98584799537364180906973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131446399383152241209297 98584799537364180906973)
        ·
          refine ⟨36969299826511567840115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98584799537364180906973 36969299826511567840115)
          ·
            refine ⟨55453949739767351760173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36969299826511567840115 55453949739767351760173)
            ·
              refine ⟨20795231152412756910065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55453949739767351760173 20795231152412756910065)
              ·
                refine ⟨15596423364309567682549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20795231152412756910065 15596423364309567682549)
                ·
                  refine ⟨1462164690404021970239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15596423364309567682549 1462164690404021970239)
                  ·
                    rfl

theorem cell22_12814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_12814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12814 prefixEnd_12814 := by exact prefixLift 12814
  have htrace : WordTrace (prefixWord ++ tailWord_12814) baseStart_12814 baseEnd_12814 := by
    simpa [prefixWord, tailWord_12814, baseEnd_12814] using wordTrace_append hprefix tailTrace_12814
  have hstable : (prefixWord ++ tailWord_12814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12814).length < 2 ^ (prefixWord ++ tailWord_12814).sum := by decide
  have hdescent : baseEnd_12814 < baseStart_12814 := by decide
  rcases family_descends (prefixWord ++ tailWord_12814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12825 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 10]
def baseStart_12825 : Nat := 118140960795 + 12825 * 2 ^ 59
def prefixEnd_12825 : Nat := 4983230072969 + 3 ^ 40 * 12825 * 2
def baseEnd_12825 : Nat := 1463419865337234628561

theorem tailTrace_12825 : CollatzResearch.WordTrace tailWord_12825 prefixEnd_12825 1463419865337234628561 := by
  unfold tailWord_12825
  simp only [CollatzResearch.WordTrace]
  refine ⟨467766178544690180727929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 311844119029793453818619 467766178544690180727929)
  ·
    refine ⟨350824633908517635545947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 467766178544690180727929 350824633908517635545947)
    ·
      refine ⟨526236950862776453318921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350824633908517635545947 526236950862776453318921)
      ·
        refine ⟨394677713147082339989191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526236950862776453318921 394677713147082339989191)
        ·
          refine ⟨592016569720623509983787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394677713147082339989191 592016569720623509983787)
          ·
            refine ⟨888024854580935264975681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592016569720623509983787 888024854580935264975681)
            ·
              refine ⟨666018640935701448731761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888024854580935264975681 666018640935701448731761)
              ·
                refine ⟨499513980701776086548821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666018640935701448731761 499513980701776086548821)
                ·
                  refine ⟨1463419865337234628561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 499513980701776086548821 1463419865337234628561)
                  ·
                    rfl

theorem cell22_12825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_12825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12825 prefixEnd_12825 := by exact prefixLift 12825
  have htrace : WordTrace (prefixWord ++ tailWord_12825) baseStart_12825 baseEnd_12825 := by
    simpa [prefixWord, tailWord_12825, baseEnd_12825] using wordTrace_append hprefix tailTrace_12825
  have hstable : (prefixWord ++ tailWord_12825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12825).length < 2 ^ (prefixWord ++ tailWord_12825).sum := by decide
  have hdescent : baseEnd_12825 < baseStart_12825 := by decide
  rcases family_descends (prefixWord ++ tailWord_12825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12852 : List Nat := [2, 5, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_12852 : Nat := 118140960795 + 12852 * 2 ^ 59
def prefixEnd_12852 : Nat := 4983230072969 + 3 ^ 40 * 12852 * 2
def baseEnd_12852 : Nat := 4399502247792633460601

theorem tailTrace_12852 : CollatzResearch.WordTrace tailWord_12852 prefixEnd_12852 4399502247792633460601 := by
  unfold tailWord_12852
  simp only [CollatzResearch.WordTrace]
  refine ⟨234375474723436895980405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 312500632964582527973873 234375474723436895980405)
  ·
    refine ⟨21972700755322208998163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234375474723436895980405 21972700755322208998163)
    ·
      refine ⟨32959051132983313497245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21972700755322208998163 32959051132983313497245)
      ·
        refine ⟨12359644174868742561467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32959051132983313497245 12359644174868742561467)
        ·
          refine ⟨18539466262303113842201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12359644174868742561467 18539466262303113842201)
          ·
            refine ⟨13904599696727335381651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18539466262303113842201 13904599696727335381651)
            ·
              refine ⟨20856899545091003072477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13904599696727335381651 20856899545091003072477)
              ·
                refine ⟨7821337329409126152179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20856899545091003072477 7821337329409126152179)
                ·
                  refine ⟨11732005994113689228269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7821337329409126152179 11732005994113689228269)
                  ·
                    refine ⟨4399502247792633460601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11732005994113689228269 4399502247792633460601)
                    ·
                      rfl

theorem cell22_12852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_12852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12852 prefixEnd_12852 := by exact prefixLift 12852
  have htrace : WordTrace (prefixWord ++ tailWord_12852) baseStart_12852 baseEnd_12852 := by
    simpa [prefixWord, tailWord_12852, baseEnd_12852] using wordTrace_append hprefix tailTrace_12852
  have hstable : (prefixWord ++ tailWord_12852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12852).length < 2 ^ (prefixWord ++ tailWord_12852).sum := by decide
  have hdescent : baseEnd_12852 < baseStart_12852 := by decide
  rcases family_descends (prefixWord ++ tailWord_12852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12857 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 3, 5]
def baseStart_12857 : Nat := 118140960795 + 12857 * 2 ^ 59
def prefixEnd_12857 : Nat := 4983230072969 + 3 ^ 40 * 12857 * 2
def baseEnd_12857 : Nat := 4401213849974287085585

theorem tailTrace_12857 : CollatzResearch.WordTrace tailWord_12857 prefixEnd_12857 4401213849974287085585 := by
  unfold tailWord_12857
  simp only [CollatzResearch.WordTrace]
  refine ⟨468933314428759645892825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 312622209619173097261883 468933314428759645892825)
  ·
    refine ⟨351699985821569734419619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 468933314428759645892825 351699985821569734419619)
    ·
      refine ⟨527549978732354601629429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351699985821569734419619 527549978732354601629429)
      ·
        refine ⟨49457810506158243902759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 527549978732354601629429 49457810506158243902759)
        ·
          refine ⟨74186715759237365854139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49457810506158243902759 74186715759237365854139)
          ·
            refine ⟨111280073638856048781209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74186715759237365854139 111280073638856048781209)
            ·
              refine ⟨83460055229142036585907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111280073638856048781209 83460055229142036585907)
              ·
                refine ⟨125190082843713054878861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83460055229142036585907 125190082843713054878861)
                ·
                  refine ⟨46946281066392395579573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125190082843713054878861 46946281066392395579573)
                  ·
                    refine ⟨4401213849974287085585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46946281066392395579573 4401213849974287085585)
                    ·
                      rfl

theorem cell22_12857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_12857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12857 prefixEnd_12857 := by exact prefixLift 12857
  have htrace : WordTrace (prefixWord ++ tailWord_12857) baseStart_12857 baseEnd_12857 := by
    simpa [prefixWord, tailWord_12857, baseEnd_12857] using wordTrace_append hprefix tailTrace_12857
  have hstable : (prefixWord ++ tailWord_12857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12857).length < 2 ^ (prefixWord ++ tailWord_12857).sum := by decide
  have hdescent : baseEnd_12857 < baseStart_12857 := by decide
  rcases family_descends (prefixWord ++ tailWord_12857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12874 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 4, 3]
def baseStart_12874 : Nat := 118140960795 + 12874 * 2 ^ 59
def prefixEnd_12874 : Nat := 4983230072969 + 3 ^ 40 * 12874 * 2
def baseEnd_12874 : Nat := 4407033297391909410533

theorem tailTrace_12874 : CollatzResearch.WordTrace tailWord_12874 prefixEnd_12874 4407033297391909410533 := by
  unfold tailWord_12874
  simp only [CollatzResearch.WordTrace]
  refine ⟨117388338841792887315419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 313035570244781032841117 117388338841792887315419)
  ·
    refine ⟨176082508262689330973129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117388338841792887315419 176082508262689330973129)
    ·
      refine ⟨132061881197016998229847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176082508262689330973129 132061881197016998229847)
      ·
        refine ⟨198092821795525497344771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132061881197016998229847 198092821795525497344771)
        ·
          refine ⟨297139232693288246017157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198092821795525497344771 297139232693288246017157)
          ·
            refine ⟨55713606129991546128217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 297139232693288246017157 55713606129991546128217)
            ·
              refine ⟨41785204597493659596163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55713606129991546128217 41785204597493659596163)
              ·
                refine ⟨62677806896240489394245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41785204597493659596163 62677806896240489394245)
                ·
                  refine ⟨11752088793045091761421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62677806896240489394245 11752088793045091761421)
                  ·
                    refine ⟨4407033297391909410533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11752088793045091761421 4407033297391909410533)
                    ·
                      rfl

theorem cell22_12874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_12874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12874 prefixEnd_12874 := by exact prefixLift 12874
  have htrace : WordTrace (prefixWord ++ tailWord_12874) baseStart_12874 baseEnd_12874 := by
    simpa [prefixWord, tailWord_12874, baseEnd_12874] using wordTrace_append hprefix tailTrace_12874
  have hstable : (prefixWord ++ tailWord_12874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12874).length < 2 ^ (prefixWord ++ tailWord_12874).sum := by decide
  have hdescent : baseEnd_12874 < baseStart_12874 := by decide
  rcases family_descends (prefixWord ++ tailWord_12874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12876 : List Nat := [2, 2, 1, 3, 1, 2, 5, 2, 4]
def baseStart_12876 : Nat := 118140960795 + 12876 * 2 ^ 59
def prefixEnd_12876 : Nat := 4983230072969 + 3 ^ 40 * 12876 * 2
def baseEnd_12876 : Nat := 1469239312754856953509

theorem tailTrace_12876 : CollatzResearch.WordTrace tailWord_12876 prefixEnd_12876 1469239312754856953509 := by
  unfold tailWord_12876
  simp only [CollatzResearch.WordTrace]
  refine ⟨234813150679962945417241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 313084200906617260556321 234813150679962945417241)
  ·
    refine ⟨176109863009972209062931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234813150679962945417241 176109863009972209062931)
    ·
      refine ⟨264164794514958313594397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176109863009972209062931 264164794514958313594397)
      ·
        refine ⟨99061797943109367597899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264164794514958313594397 99061797943109367597899)
        ·
          refine ⟨148592696914664051396849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99061797943109367597899 148592696914664051396849)
          ·
            refine ⟨111444522685998038547637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148592696914664051396849 111444522685998038547637)
            ·
              refine ⟨10447924001812316113841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111444522685998038547637 10447924001812316113841)
              ·
                refine ⟨7835943001359237085381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10447924001812316113841 7835943001359237085381)
                ·
                  refine ⟨1469239312754856953509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7835943001359237085381 1469239312754856953509)
                  ·
                    rfl

theorem cell22_12876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_12876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12876 prefixEnd_12876 := by exact prefixLift 12876
  have htrace : WordTrace (prefixWord ++ tailWord_12876) baseStart_12876 baseEnd_12876 := by
    simpa [prefixWord, tailWord_12876, baseEnd_12876] using wordTrace_append hprefix tailTrace_12876
  have hstable : (prefixWord ++ tailWord_12876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12876).length < 2 ^ (prefixWord ++ tailWord_12876).sum := by decide
  have hdescent : baseEnd_12876 < baseStart_12876 := by decide
  rcases family_descends (prefixWord ++ tailWord_12876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12887 : List Nat := [1, 1, 3, 2, 2, 2, 4, 7]
def baseStart_12887 : Nat := 118140960795 + 12887 * 2 ^ 59
def prefixEnd_12887 : Nat := 4983230072969 + 3 ^ 40 * 12887 * 2
def baseEnd_12887 : Nat := 490164829229356537277

theorem tailTrace_12887 : CollatzResearch.WordTrace tailWord_12887 prefixEnd_12887 490164829229356537277 := by
  unfold tailWord_12887
  simp only [CollatzResearch.WordTrace]
  refine ⟨470027504320074769484915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 313351669546716512989943 470027504320074769484915)
  ·
    refine ⟨705041256480112154227373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 470027504320074769484915 705041256480112154227373)
    ·
      refine ⟨264390471180042057835265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 705041256480112154227373 264390471180042057835265)
      ·
        refine ⟨198292853385031543376449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264390471180042057835265 198292853385031543376449)
        ·
          refine ⟨148719640038773657532337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198292853385031543376449 148719640038773657532337)
          ·
            refine ⟨111539730029080243149253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148719640038773657532337 111539730029080243149253)
            ·
              refine ⟨20913699380452545590485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111539730029080243149253 20913699380452545590485)
              ·
                refine ⟨490164829229356537277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20913699380452545590485 490164829229356537277)
                ·
                  rfl

theorem cell22_12887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 7].length) (baseStart_12887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12887 prefixEnd_12887 := by exact prefixLift 12887
  have htrace : WordTrace (prefixWord ++ tailWord_12887) baseStart_12887 baseEnd_12887 := by
    simpa [prefixWord, tailWord_12887, baseEnd_12887] using wordTrace_append hprefix tailTrace_12887
  have hstable : (prefixWord ++ tailWord_12887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12887).length < 2 ^ (prefixWord ++ tailWord_12887).sum := by decide
  have hdescent : baseEnd_12887 < baseStart_12887 := by decide
  rcases family_descends (prefixWord ++ tailWord_12887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12947 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 2, 5]
def baseStart_12947 : Nat := 118140960795 + 12947 * 2 ^ 59
def prefixEnd_12947 : Nat := 4983230072969 + 3 ^ 40 * 12947 * 2
def baseEnd_12947 : Nat := 4432022689244052335309

theorem tailTrace_12947 : CollatzResearch.WordTrace tailWord_12947 prefixEnd_12947 4432022689244052335309 := by
  unfold tailWord_12947
  simp only [CollatzResearch.WordTrace]
  refine ⟨472215884102705016669095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 314810589401803344446063 472215884102705016669095)
  ·
    refine ⟨708323826154057525003643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 472215884102705016669095 708323826154057525003643)
    ·
      refine ⟨1062485739231086287505465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 708323826154057525003643 1062485739231086287505465)
      ·
        refine ⟨796864304423314715629099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1062485739231086287505465 796864304423314715629099)
        ·
          refine ⟨1195296456634972073443649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796864304423314715629099 1195296456634972073443649)
          ·
            refine ⟨896472342476229055082737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1195296456634972073443649 896472342476229055082737)
            ·
              refine ⟨672354256857171791312053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896472342476229055082737 672354256857171791312053)
              ·
                refine ⟨63033211580359855435505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 672354256857171791312053 63033211580359855435505)
                ·
                  refine ⟨47274908685269891576629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63033211580359855435505 47274908685269891576629)
                  ·
                    refine ⟨4432022689244052335309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47274908685269891576629 4432022689244052335309)
                    ·
                      rfl

theorem cell22_12947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 5].length) (baseStart_12947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12947 prefixEnd_12947 := by exact prefixLift 12947
  have htrace : WordTrace (prefixWord ++ tailWord_12947) baseStart_12947 baseEnd_12947 := by
    simpa [prefixWord, tailWord_12947, baseEnd_12947] using wordTrace_append hprefix tailTrace_12947
  have hstable : (prefixWord ++ tailWord_12947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12947).length < 2 ^ (prefixWord ++ tailWord_12947).sum := by decide
  have hdescent : baseEnd_12947 < baseStart_12947 := by decide
  rcases family_descends (prefixWord ++ tailWord_12947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12983 : List Nat := [1, 1, 3, 1, 7, 1, 1, 2, 5]
def baseStart_12983 : Nat := 118140960795 + 12983 * 2 ^ 59
def prefixEnd_12983 : Nat := 4983230072969 + 3 ^ 40 * 12983 * 2
def baseEnd_12983 : Nat := 1481448741650652811733

theorem tailTrace_12983 : CollatzResearch.WordTrace tailWord_12983 prefixEnd_12983 1481448741650652811733 := by
  unfold tailWord_12983
  simp only [CollatzResearch.WordTrace]
  refine ⟨473528911972283164979603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 315685941314855443319735 473528911972283164979603)
  ·
    refine ⟨710293367958424747469405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 473528911972283164979603 710293367958424747469405)
    ·
      refine ⟨266360012984409280301027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 710293367958424747469405 266360012984409280301027)
      ·
        refine ⟨399540019476613920451541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266360012984409280301027 399540019476613920451541)
        ·
          refine ⟨9364219206483138760583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 399540019476613920451541 9364219206483138760583)
          ·
            refine ⟨14046328809724708140875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9364219206483138760583 14046328809724708140875)
            ·
              refine ⟨21069493214587062211313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14046328809724708140875 21069493214587062211313)
              ·
                refine ⟨15802119910940296658485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21069493214587062211313 15802119910940296658485)
                ·
                  refine ⟨1481448741650652811733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15802119910940296658485 1481448741650652811733)
                  ·
                    rfl

theorem cell22_12983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 5].length) (baseStart_12983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_12983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_12983 prefixEnd_12983 := by exact prefixLift 12983
  have htrace : WordTrace (prefixWord ++ tailWord_12983) baseStart_12983 baseEnd_12983 := by
    simpa [prefixWord, tailWord_12983, baseEnd_12983] using wordTrace_append hprefix tailTrace_12983
  have hstable : (prefixWord ++ tailWord_12983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12983).length < 2 ^ (prefixWord ++ tailWord_12983).sum := by decide
  have hdescent : baseEnd_12983 < baseStart_12983 := by decide
  rcases family_descends (prefixWord ++ tailWord_12983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13024 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 2, 4]
def baseStart_13024 : Nat := 118140960795 + 13024 * 2 ^ 59
def prefixEnd_13024 : Nat := 4983230072969 + 3 ^ 40 * 13024 * 2
def baseEnd_13024 : Nat := 4458381362841518160073

theorem tailTrace_13024 : CollatzResearch.WordTrace tailWord_13024 prefixEnd_13024 4458381362841518160073 := by
  unfold tailWord_13024
  simp only [CollatzResearch.WordTrace]
  refine ⟨237512152411873583611063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 316682869882498111481417 237512152411873583611063)
  ·
    refine ⟨356268228617810375416595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237512152411873583611063 356268228617810375416595)
    ·
      refine ⟨534402342926715563124893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356268228617810375416595 534402342926715563124893)
      ·
        refine ⟨200400878597518336171835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 534402342926715563124893 200400878597518336171835)
        ·
          refine ⟨300601317896277504257753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200400878597518336171835 300601317896277504257753)
          ·
            refine ⟨225450988422208128193315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300601317896277504257753 225450988422208128193315)
            ·
              refine ⟨338176482633312192289973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225450988422208128193315 338176482633312192289973)
              ·
                refine ⟨31704045246873018027185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 338176482633312192289973 31704045246873018027185)
                ·
                  refine ⟨23778033935154763520389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31704045246873018027185 23778033935154763520389)
                  ·
                    refine ⟨4458381362841518160073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23778033935154763520389 4458381362841518160073)
                    ·
                      rfl

theorem cell22_13024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_13024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13024 prefixEnd_13024 := by exact prefixLift 13024
  have htrace : WordTrace (prefixWord ++ tailWord_13024) baseStart_13024 baseEnd_13024 := by
    simpa [prefixWord, tailWord_13024, baseEnd_13024] using wordTrace_append hprefix tailTrace_13024
  have hstable : (prefixWord ++ tailWord_13024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13024).length < 2 ^ (prefixWord ++ tailWord_13024).sum := by decide
  have hdescent : baseEnd_13024 < baseStart_13024 := by decide
  rcases family_descends (prefixWord ++ tailWord_13024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13028 : List Nat := [2, 3, 1, 1, 1, 6, 1, 3, 4]
def baseStart_13028 : Nat := 118140960795 + 13028 * 2 ^ 59
def prefixEnd_13028 : Nat := 4983230072969 + 3 ^ 40 * 13028 * 2
def baseEnd_13028 : Nat := 1486583548195613686687

theorem tailTrace_13028 : CollatzResearch.WordTrace tailWord_13028 prefixEnd_13028 1486583548195613686687 := by
  unfold tailWord_13028
  simp only [CollatzResearch.WordTrace]
  refine ⟨237585098404627925183869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 316780131206170566911825 237585098404627925183869)
  ·
    refine ⟨89094411901735471943951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237585098404627925183869 89094411901735471943951)
    ·
      refine ⟨133641617852603207915927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89094411901735471943951 133641617852603207915927)
      ·
        refine ⟨200462426778904811873891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133641617852603207915927 200462426778904811873891)
        ·
          refine ⟨300693640168357217810837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200462426778904811873891 300693640168357217810837)
          ·
            refine ⟨14095014382891744584883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 300693640168357217810837 14095014382891744584883)
            ·
              refine ⟨21142521574337616877325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14095014382891744584883 21142521574337616877325)
              ·
                refine ⟨7928445590376606328997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21142521574337616877325 7928445590376606328997)
                ·
                  refine ⟨1486583548195613686687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7928445590376606328997 1486583548195613686687)
                  ·
                    rfl

theorem cell22_13028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_13028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13028 prefixEnd_13028 := by exact prefixLift 13028
  have htrace : WordTrace (prefixWord ++ tailWord_13028) baseStart_13028 baseEnd_13028 := by
    simpa [prefixWord, tailWord_13028, baseEnd_13028] using wordTrace_append hprefix tailTrace_13028
  have hstable : (prefixWord ++ tailWord_13028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13028).length < 2 ^ (prefixWord ++ tailWord_13028).sum := by decide
  have hdescent : baseEnd_13028 < baseStart_13028 := by decide
  rcases family_descends (prefixWord ++ tailWord_13028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13039 : List Nat := [1, 1, 2, 1, 5, 4, 8]
def baseStart_13039 : Nat := 118140960795 + 13039 * 2 ^ 59
def prefixEnd_13039 : Nat := 4983230072969 + 3 ^ 40 * 13039 * 2
def baseEnd_13039 : Nat := 165315413680980705001

theorem tailTrace_13039 : CollatzResearch.WordTrace tailWord_13039 prefixEnd_13039 165315413680980705001 := by
  unfold tailWord_13039
  simp only [CollatzResearch.WordTrace]
  refine ⟨475571399769404729018171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 317047599846269819345447 475571399769404729018171)
  ·
    refine ⟨713357099654107093527257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 475571399769404729018171 713357099654107093527257)
    ·
      refine ⟨535017824740580320145443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 713357099654107093527257 535017824740580320145443)
      ·
        refine ⟨802526737110870480218165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535017824740580320145443 802526737110870480218165)
        ·
          refine ⟨75236881604144107520453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 802526737110870480218165 75236881604144107520453)
          ·
            refine ⟨14106915300777020160085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75236881604144107520453 14106915300777020160085)
            ·
              refine ⟨165315413680980705001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 14106915300777020160085 165315413680980705001)
              ·
                rfl

theorem cell22_13039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 8].length) (baseStart_13039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13039 prefixEnd_13039 := by exact prefixLift 13039
  have htrace : WordTrace (prefixWord ++ tailWord_13039) baseStart_13039 baseEnd_13039 := by
    simpa [prefixWord, tailWord_13039, baseEnd_13039] using wordTrace_append hprefix tailTrace_13039
  have hstable : (prefixWord ++ tailWord_13039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13039).length < 2 ^ (prefixWord ++ tailWord_13039).sum := by decide
  have hdescent : baseEnd_13039 < baseStart_13039 := by decide
  rcases family_descends (prefixWord ++ tailWord_13039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13129 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 8]
def baseStart_13129 : Nat := 118140960795 + 13129 * 2 ^ 59
def prefixEnd_13129 : Nat := 4983230072969 + 3 ^ 40 * 13129 * 2
def baseEnd_13129 : Nat := 1498108336218748094917

theorem tailTrace_13129 : CollatzResearch.WordTrace tailWord_13129 prefixEnd_13129 1498108336218748094917 := by
  unfold tailWord_13129
  simp only [CollatzResearch.WordTrace]
  refine ⟨478853969443350099794441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 319235979628900066529627 478853969443350099794441)
  ·
    refine ⟨359140477082512574845831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 478853969443350099794441 359140477082512574845831)
    ·
      refine ⟨538710715623768862268747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359140477082512574845831 538710715623768862268747)
      ·
        refine ⟨808066073435653293403121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538710715623768862268747 808066073435653293403121)
        ·
          refine ⟨606049555076739970052341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 808066073435653293403121 606049555076739970052341)
          ·
            refine ⟨56817145788444372192407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 606049555076739970052341 56817145788444372192407)
            ·
              refine ⟨85225718682666558288611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56817145788444372192407 85225718682666558288611)
              ·
                refine ⟨127838578023999837432917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85225718682666558288611 127838578023999837432917)
                ·
                  refine ⟨1498108336218748094917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 127838578023999837432917 1498108336218748094917)
                  ·
                    rfl

theorem cell22_13129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_13129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13129 prefixEnd_13129 := by exact prefixLift 13129
  have htrace : WordTrace (prefixWord ++ tailWord_13129) baseStart_13129 baseEnd_13129 := by
    simpa [prefixWord, tailWord_13129, baseEnd_13129] using wordTrace_append hprefix tailTrace_13129
  have hstable : (prefixWord ++ tailWord_13129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13129).length < 2 ^ (prefixWord ++ tailWord_13129).sum := by decide
  have hdescent : baseEnd_13129 < baseStart_13129 := by decide
  rcases family_descends (prefixWord ++ tailWord_13129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13182 : List Nat := [4, 2, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_13182 : Nat := 118140960795 + 13182 * 2 ^ 59
def prefixEnd_13182 : Nat := 4983230072969 + 3 ^ 40 * 13182 * 2
def baseEnd_13182 : Nat := 4512467991781772709589

theorem tailTrace_13182 : CollatzResearch.WordTrace tailWord_13182 prefixEnd_13182 4512467991781772709589 := by
  unfold tailWord_13182
  simp only [CollatzResearch.WordTrace]
  refine ⟨60098379781417518934225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 320524692167560100982533 60098379781417518934225)
  ·
    refine ⟨45073784836063139200669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60098379781417518934225 45073784836063139200669)
    ·
      refine ⟨16902669313523677200251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45073784836063139200669 16902669313523677200251)
      ·
        refine ⟨25354003970285515800377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16902669313523677200251 25354003970285515800377)
        ·
          refine ⟨19015502977714136850283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25354003970285515800377 19015502977714136850283)
          ·
            refine ⟨28523254466571205275425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19015502977714136850283 28523254466571205275425)
            ·
              refine ⟨21392440849928403956569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28523254466571205275425 21392440849928403956569)
              ·
                refine ⟨16044330637446302967427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21392440849928403956569 16044330637446302967427)
                ·
                  refine ⟨24066495956169454451141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16044330637446302967427 24066495956169454451141)
                  ·
                    refine ⟨4512467991781772709589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24066495956169454451141 4512467991781772709589)
                    ·
                      rfl

theorem cell22_13182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_13182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13182 prefixEnd_13182 := by exact prefixLift 13182
  have htrace : WordTrace (prefixWord ++ tailWord_13182) baseStart_13182 baseEnd_13182 := by
    simpa [prefixWord, tailWord_13182, baseEnd_13182] using wordTrace_append hprefix tailTrace_13182
  have hstable : (prefixWord ++ tailWord_13182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13182).length < 2 ^ (prefixWord ++ tailWord_13182).sum := by decide
  have hdescent : baseEnd_13182 < baseStart_13182 := by decide
  rcases family_descends (prefixWord ++ tailWord_13182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13191 : List Nat := [1, 1, 4, 2, 3, 2, 1, 8]
def baseStart_13191 : Nat := 118140960795 + 13191 * 2 ^ 59
def prefixEnd_13191 : Nat := 4983230072969 + 3 ^ 40 * 13191 * 2
def baseEnd_13191 : Nat := 501727652856527692729

theorem tailTrace_13191 : CollatzResearch.WordTrace tailWord_13191 prefixEnd_13191 501727652856527692729 := by
  unfold tailWord_13191
  simp only [CollatzResearch.WordTrace]
  refine ⟨481115295218734688551427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 320743530145823125700951 481115295218734688551427)
  ·
    refine ⟨721672942828102032827141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 481115295218734688551427 721672942828102032827141)
    ·
      refine ⟨135313676780269131155089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 721672942828102032827141 135313676780269131155089)
      ·
        refine ⟨101485257585201848366317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135313676780269131155089 101485257585201848366317)
        ·
          refine ⟨38056971594450693137369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101485257585201848366317 38056971594450693137369)
          ·
            refine ⟨28542728695838019853027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38056971594450693137369 28542728695838019853027)
            ·
              refine ⟨42814093043757029779541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28542728695838019853027 42814093043757029779541)
              ·
                refine ⟨501727652856527692729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 42814093043757029779541 501727652856527692729)
                ·
                  rfl

theorem cell22_13191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 8].length) (baseStart_13191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13191 prefixEnd_13191 := by exact prefixLift 13191
  have htrace : WordTrace (prefixWord ++ tailWord_13191) baseStart_13191 baseEnd_13191 := by
    simpa [prefixWord, tailWord_13191, baseEnd_13191] using wordTrace_append hprefix tailTrace_13191
  have hstable : (prefixWord ++ tailWord_13191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13191).length < 2 ^ (prefixWord ++ tailWord_13191).sum := by decide
  have hdescent : baseEnd_13191 < baseStart_13191 := by decide
  rcases family_descends (prefixWord ++ tailWord_13191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13270 : List Nat := [5, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_13270 : Nat := 118140960795 + 13270 * 2 ^ 59
def prefixEnd_13270 : Nat := 4983230072969 + 3 ^ 40 * 13270 * 2
def baseEnd_13270 : Nat := 1514197396726292169773

theorem tailTrace_13270 : CollatzResearch.WordTrace tailWord_13270 prefixEnd_13270 1514197396726292169773 := by
  unfold tailWord_13270
  simp only [CollatzResearch.WordTrace]
  refine ⟨30249791370783198792329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 322664441288354120451509 30249791370783198792329)
  ·
    refine ⟨22687343528087399094247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30249791370783198792329 22687343528087399094247)
    ·
      refine ⟨34031015292131098641371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22687343528087399094247 34031015292131098641371)
      ·
        refine ⟨51046522938196647962057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34031015292131098641371 51046522938196647962057)
        ·
          refine ⟨38284892203647485971543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51046522938196647962057 38284892203647485971543)
          ·
            refine ⟨57427338305471228957315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38284892203647485971543 57427338305471228957315)
            ·
              refine ⟨86141007458206843435973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57427338305471228957315 86141007458206843435973)
              ·
                refine ⟨16151438898413783144245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86141007458206843435973 16151438898413783144245)
                ·
                  refine ⟨1514197396726292169773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16151438898413783144245 1514197396726292169773)
                  ·
                    rfl

theorem cell22_13270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_13270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13270 prefixEnd_13270 := by exact prefixLift 13270
  have htrace : WordTrace (prefixWord ++ tailWord_13270) baseStart_13270 baseEnd_13270 := by
    simpa [prefixWord, tailWord_13270, baseEnd_13270] using wordTrace_append hprefix tailTrace_13270
  have hstable : (prefixWord ++ tailWord_13270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13270).length < 2 ^ (prefixWord ++ tailWord_13270).sum := by decide
  have hdescent : baseEnd_13270 < baseStart_13270 := by decide
  rcases family_descends (prefixWord ++ tailWord_13270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13274 : List Nat := [3, 1, 1, 2, 4, 3, 2, 2, 1, 3]
def baseStart_13274 : Nat := 118140960795 + 13274 * 2 ^ 59
def prefixEnd_13274 : Nat := 4983230072969 + 3 ^ 40 * 13274 * 2
def baseEnd_13274 : Nat := 4543961471924199409307

theorem tailTrace_13274 : CollatzResearch.WordTrace tailWord_13274 prefixEnd_13274 4543961471924199409307 := by
  unfold tailWord_13274
  simp only [CollatzResearch.WordTrace]
  refine ⟨121035638479509965955719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 322761702612026575881917 121035638479509965955719)
  ·
    refine ⟨181553457719264948933579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121035638479509965955719 181553457719264948933579)
    ·
      refine ⟨272330186578897423400369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181553457719264948933579 272330186578897423400369)
      ·
        refine ⟨204247639934173067550277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272330186578897423400369 204247639934173067550277)
        ·
          refine ⟨38296432487657450165677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204247639934173067550277 38296432487657450165677)
          ·
            refine ⟨14361162182871543812129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38296432487657450165677 14361162182871543812129)
            ·
              refine ⟨10770871637153657859097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14361162182871543812129 10770871637153657859097)
              ·
                refine ⟨8078153727865243394323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10770871637153657859097 8078153727865243394323)
                ·
                  refine ⟨12117230591797865091485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8078153727865243394323 12117230591797865091485)
                  ·
                    refine ⟨4543961471924199409307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12117230591797865091485 4543961471924199409307)
                    ·
                      rfl

theorem cell22_13274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_13274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13274 prefixEnd_13274 := by exact prefixLift 13274
  have htrace : WordTrace (prefixWord ++ tailWord_13274) baseStart_13274 baseEnd_13274 := by
    simpa [prefixWord, tailWord_13274, baseEnd_13274] using wordTrace_append hprefix tailTrace_13274
  have hstable : (prefixWord ++ tailWord_13274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13274).length < 2 ^ (prefixWord ++ tailWord_13274).sum := by decide
  have hdescent : baseEnd_13274 < baseStart_13274 := by decide
  rcases family_descends (prefixWord ++ tailWord_13274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13281 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 6]
def baseStart_13281 : Nat := 118140960795 + 13281 * 2 ^ 59
def prefixEnd_13281 : Nat := 4983230072969 + 3 ^ 40 * 13281 * 2
def baseEnd_13281 : Nat := 1515452571659504828095

theorem tailTrace_13281 : CollatzResearch.WordTrace tailWord_13281 prefixEnd_13281 1515452571659504828095 := by
  unfold tailWord_13281
  simp only [CollatzResearch.WordTrace]
  refine ⟨484397864892680059327697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 322931909928453372885131 484397864892680059327697)
  ·
    refine ⟨363298398669510044495773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 484397864892680059327697 363298398669510044495773)
    ·
      refine ⟨136236899501066266685915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363298398669510044495773 136236899501066266685915)
      ·
        refine ⟨204355349251599400028873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136236899501066266685915 204355349251599400028873)
        ·
          refine ⟨153266511938699550021655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204355349251599400028873 153266511938699550021655)
          ·
            refine ⟨229899767908049325032483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153266511938699550021655 229899767908049325032483)
            ·
              refine ⟨344849651862073987548725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229899767908049325032483 344849651862073987548725)
              ·
                refine ⟨32329654862069436332693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 344849651862073987548725 32329654862069436332693)
                ·
                  refine ⟨1515452571659504828095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32329654862069436332693 1515452571659504828095)
                  ·
                    rfl

theorem cell22_13281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 6].length) (baseStart_13281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13281 prefixEnd_13281 := by exact prefixLift 13281
  have htrace : WordTrace (prefixWord ++ tailWord_13281) baseStart_13281 baseEnd_13281 := by
    simpa [prefixWord, tailWord_13281, baseEnd_13281] using wordTrace_append hprefix tailTrace_13281
  have hstable : (prefixWord ++ tailWord_13281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13281).length < 2 ^ (prefixWord ++ tailWord_13281).sum := by decide
  have hdescent : baseEnd_13281 < baseStart_13281 := by decide
  rcases family_descends (prefixWord ++ tailWord_13281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13285 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 2, 5]
def baseStart_13285 : Nat := 118140960795 + 13285 * 2 ^ 59
def prefixEnd_13285 : Nat := 4983230072969 + 3 ^ 40 * 13285 * 2
def baseEnd_13285 : Nat := 4547726996723837384273

theorem tailTrace_13285 : CollatzResearch.WordTrace tailWord_13285 prefixEnd_13285 4547726996723837384273 := by
  unfold tailWord_13285
  simp only [CollatzResearch.WordTrace]
  refine ⟨484543756878188742473309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 323029171252125828315539 484543756878188742473309)
  ·
    refine ⟨181703908829320778427491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 484543756878188742473309 181703908829320778427491)
    ·
      refine ⟨272555863243981167641237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181703908829320778427491 272555863243981167641237)
      ·
        refine ⟨12776056089561617233183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 272555863243981167641237 12776056089561617233183)
        ·
          refine ⟨19164084134342425849775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12776056089561617233183 19164084134342425849775)
          ·
            refine ⟨28746126201513638774663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19164084134342425849775 28746126201513638774663)
            ·
              refine ⟨43119189302270458161995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28746126201513638774663 43119189302270458161995)
              ·
                refine ⟨64678783953405687242993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43119189302270458161995 64678783953405687242993)
                ·
                  refine ⟨48509087965054265432245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64678783953405687242993 48509087965054265432245)
                  ·
                    refine ⟨4547726996723837384273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48509087965054265432245 4547726996723837384273)
                    ·
                      rfl

theorem cell22_13285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_13285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13285 prefixEnd_13285 := by exact prefixLift 13285
  have htrace : WordTrace (prefixWord ++ tailWord_13285) baseStart_13285 baseEnd_13285 := by
    simpa [prefixWord, tailWord_13285, baseEnd_13285] using wordTrace_append hprefix tailTrace_13285
  have hstable : (prefixWord ++ tailWord_13285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13285).length < 2 ^ (prefixWord ++ tailWord_13285).sum := by decide
  have hdescent : baseEnd_13285 < baseStart_13285 := by decide
  rcases family_descends (prefixWord ++ tailWord_13285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13313 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 1, 5]
def baseStart_13313 : Nat := 118140960795 + 13313 * 2 ^ 59
def prefixEnd_13313 : Nat := 4983230072969 + 3 ^ 40 * 13313 * 2
def baseEnd_13313 : Nat := 4557311968941097684187

theorem tailTrace_13313 : CollatzResearch.WordTrace tailWord_13313 prefixEnd_13313 4557311968941097684187 := by
  unfold tailWord_13313
  simp only [CollatzResearch.WordTrace]
  refine ⟨485565000776749524492593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 323710000517833016328395 485565000776749524492593)
  ·
    refine ⟨364173750582562143369445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 485565000776749524492593 364173750582562143369445)
    ·
      refine ⟨68282578234230401881771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364173750582562143369445 68282578234230401881771)
      ·
        refine ⟨102423867351345602822657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68282578234230401881771 102423867351345602822657)
        ·
          refine ⟨76817900513509202116993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102423867351345602822657 76817900513509202116993)
          ·
            refine ⟨57613425385131901587745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76817900513509202116993 57613425385131901587745)
            ·
              refine ⟨43210069038848926190809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57613425385131901587745 43210069038848926190809)
              ·
                refine ⟨32407551779136694643107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43210069038848926190809 32407551779136694643107)
                ·
                  refine ⟨48611327668705041964661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32407551779136694643107 48611327668705041964661)
                  ·
                    refine ⟨4557311968941097684187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48611327668705041964661 4557311968941097684187)
                    ·
                      rfl

theorem cell22_13313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_13313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13313 prefixEnd_13313 := by exact prefixLift 13313
  have htrace : WordTrace (prefixWord ++ tailWord_13313) baseStart_13313 baseEnd_13313 := by
    simpa [prefixWord, tailWord_13313, baseEnd_13313] using wordTrace_append hprefix tailTrace_13313
  have hstable : (prefixWord ++ tailWord_13313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13313).length < 2 ^ (prefixWord ++ tailWord_13313).sum := by decide
  have hdescent : baseEnd_13313 < baseStart_13313 := by decide
  rcases family_descends (prefixWord ++ tailWord_13313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13347 : List Nat := [1, 1, 1, 4, 3, 3, 3, 1, 2, 3]
def baseStart_13347 : Nat := 118140960795 + 13347 * 2 ^ 59
def prefixEnd_13347 : Nat := 4983230072969 + 3 ^ 40 * 13347 * 2
def baseEnd_13347 : Nat := 4568950863776342334083

theorem tailTrace_13347 : CollatzResearch.WordTrace tailWord_13347 prefixEnd_13347 4568950863776342334083 := by
  unfold tailWord_13347
  simp only [CollatzResearch.WordTrace]
  refine ⟨486805082653573331230295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 324536721769048887486863 486805082653573331230295)
  ·
    refine ⟨730207623980359996845443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 486805082653573331230295 730207623980359996845443)
    ·
      refine ⟨1095311435970539995268165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 730207623980359996845443 1095311435970539995268165)
      ·
        refine ⟨205370894244476249112781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1095311435970539995268165 205370894244476249112781)
        ·
          refine ⟨77014085341678593417293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205370894244476249112781 77014085341678593417293)
          ·
            refine ⟨28880282003129472531485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77014085341678593417293 28880282003129472531485)
            ·
              refine ⟨10830105751173552199307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28880282003129472531485 10830105751173552199307)
              ·
                refine ⟨16245158626760328298961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10830105751173552199307 16245158626760328298961)
                ·
                  refine ⟨12183868970070246224221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16245158626760328298961 12183868970070246224221)
                  ·
                    refine ⟨4568950863776342334083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12183868970070246224221 4568950863776342334083)
                    ·
                      rfl

theorem cell22_13347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 2, 3].length) (baseStart_13347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13347 prefixEnd_13347 := by exact prefixLift 13347
  have htrace : WordTrace (prefixWord ++ tailWord_13347) baseStart_13347 baseEnd_13347 := by
    simpa [prefixWord, tailWord_13347, baseEnd_13347] using wordTrace_append hprefix tailTrace_13347
  have hstable : (prefixWord ++ tailWord_13347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13347).length < 2 ^ (prefixWord ++ tailWord_13347).sum := by decide
  have hdescent : baseEnd_13347 < baseStart_13347 := by decide
  rcases family_descends (prefixWord ++ tailWord_13347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13358 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_13358 : Nat := 118140960795 + 13358 * 2 ^ 59
def prefixEnd_13358 : Nat := 4983230072969 + 3 ^ 40 * 13358 * 2
def baseEnd_13358 : Nat := 4572716388575980309049

theorem tailTrace_13358 : CollatzResearch.WordTrace tailWord_13358 prefixEnd_13358 4572716388575980309049 := by
  unfold tailWord_13358
  simp only [CollatzResearch.WordTrace]
  refine ⟨60900785701715276235091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 324804190409148139920485 60900785701715276235091)
  ·
    refine ⟨91351178552572914352637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60900785701715276235091 91351178552572914352637)
    ·
      refine ⟨34256691957214842882239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91351178552572914352637 34256691957214842882239)
      ·
        refine ⟨51385037935822264323359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34256691957214842882239 51385037935822264323359)
        ·
          refine ⟨77077556903733396485039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51385037935822264323359 77077556903733396485039)
          ·
            refine ⟨115616335355600094727559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77077556903733396485039 115616335355600094727559)
            ·
              refine ⟨173424503033400142091339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115616335355600094727559 173424503033400142091339)
              ·
                refine ⟨260136754550100213137009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173424503033400142091339 260136754550100213137009)
                ·
                  refine ⟨195102565912575159852757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260136754550100213137009 195102565912575159852757)
                  ·
                    refine ⟨4572716388575980309049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 195102565912575159852757 4572716388575980309049)
                    ·
                      rfl

theorem cell22_13358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_13358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13358 prefixEnd_13358 := by exact prefixLift 13358
  have htrace : WordTrace (prefixWord ++ tailWord_13358) baseStart_13358 baseEnd_13358 := by
    simpa [prefixWord, tailWord_13358, baseEnd_13358] using wordTrace_append hprefix tailTrace_13358
  have hstable : (prefixWord ++ tailWord_13358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13358).length < 2 ^ (prefixWord ++ tailWord_13358).sum := by decide
  have hdescent : baseEnd_13358 < baseStart_13358 := by decide
  rcases family_descends (prefixWord ++ tailWord_13358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13388 : List Nat := [2, 2, 1, 3, 1, 1, 1, 6, 5]
def baseStart_13388 : Nat := 118140960795 + 13388 * 2 ^ 59
def prefixEnd_13388 : Nat := 4983230072969 + 3 ^ 40 * 13388 * 2
def baseEnd_13388 : Nat := 1527662000555300686319

theorem tailTrace_13388 : CollatzResearch.WordTrace tailWord_13388 prefixEnd_13388 1527662000555300686319 := by
  unfold tailWord_13388
  simp only [CollatzResearch.WordTrace]
  refine ⟨244150237752518666736409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 325533650336691555648545 244150237752518666736409)
  ·
    refine ⟨183112678314389000052307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244150237752518666736409 183112678314389000052307)
    ·
      refine ⟨274669017471583500078461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183112678314389000052307 274669017471583500078461)
      ·
        refine ⟨103000881551843812529423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274669017471583500078461 103000881551843812529423)
        ·
          refine ⟨154501322327765718794135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103000881551843812529423 154501322327765718794135)
          ·
            refine ⟨231751983491648578191203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154501322327765718794135 231751983491648578191203)
            ·
              refine ⟨347627975237472867286805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231751983491648578191203 347627975237472867286805)
              ·
                refine ⟨16295061339256540654069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 347627975237472867286805 16295061339256540654069)
                ·
                  refine ⟨1527662000555300686319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16295061339256540654069 1527662000555300686319)
                  ·
                    rfl

theorem cell22_13388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_13388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13388 prefixEnd_13388 := by exact prefixLift 13388
  have htrace : WordTrace (prefixWord ++ tailWord_13388) baseStart_13388 baseEnd_13388 := by
    simpa [prefixWord, tailWord_13388, baseEnd_13388] using wordTrace_append hprefix tailTrace_13388
  have hstable : (prefixWord ++ tailWord_13388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13388).length < 2 ^ (prefixWord ++ tailWord_13388).sum := by decide
  have hdescent : baseEnd_13388 < baseStart_13388 := by decide
  rcases family_descends (prefixWord ++ tailWord_13388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13398 : List Nat := [5, 2, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_13398 : Nat := 118140960795 + 13398 * 2 ^ 59
def prefixEnd_13398 : Nat := 4983230072969 + 3 ^ 40 * 13398 * 2
def baseEnd_13398 : Nat := 4586409206029209308927

theorem tailTrace_13398 : CollatzResearch.WordTrace tailWord_13398 prefixEnd_13398 4586409206029209308927 := by
  unfold tailWord_13398
  simp only [CollatzResearch.WordTrace]
  refine ⟨30541575341800565083553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 325776803645872694224565 30541575341800565083553)
  ·
    refine ⟨22906181506350423812665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30541575341800565083553 22906181506350423812665)
    ·
      refine ⟨17179636129762817859499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22906181506350423812665 17179636129762817859499)
      ·
        refine ⟨25769454194644226789249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17179636129762817859499 25769454194644226789249)
        ·
          refine ⟨19327090645983170091937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25769454194644226789249 19327090645983170091937)
          ·
            refine ⟨14495317984487377568953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19327090645983170091937 14495317984487377568953)
            ·
              refine ⟨10871488488365533176715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14495317984487377568953 10871488488365533176715)
              ·
                refine ⟨16307232732548299765073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10871488488365533176715 16307232732548299765073)
                ·
                  refine ⟨12230424549411224823805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16307232732548299765073 12230424549411224823805)
                  ·
                    refine ⟨4586409206029209308927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12230424549411224823805 4586409206029209308927)
                    ·
                      rfl

theorem cell22_13398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_13398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13398 prefixEnd_13398 := by exact prefixLift 13398
  have htrace : WordTrace (prefixWord ++ tailWord_13398) baseStart_13398 baseEnd_13398 := by
    simpa [prefixWord, tailWord_13398, baseEnd_13398] using wordTrace_append hprefix tailTrace_13398
  have hstable : (prefixWord ++ tailWord_13398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13398).length < 2 ^ (prefixWord ++ tailWord_13398).sum := by decide
  have hdescent : baseEnd_13398 < baseStart_13398 := by decide
  rcases family_descends (prefixWord ++ tailWord_13398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13482 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 1, 5]
def baseStart_13482 : Nat := 118140960795 + 13482 * 2 ^ 59
def prefixEnd_13482 : Nat := 4983230072969 + 3 ^ 40 * 13482 * 2
def baseEnd_13482 : Nat := 4615164122680990208669

theorem tailTrace_13482 : CollatzResearch.WordTrace tailWord_13482 prefixEnd_13482 4615164122680990208669 := by
  unfold tailWord_13482
  simp only [CollatzResearch.WordTrace]
  refine ⟨122932234291122846848675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 327819291442994258263133 122932234291122846848675)
  ·
    refine ⟨184398351436684270273013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122932234291122846848675 184398351436684270273013)
    ·
      refine ⟨17287345447189150338095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184398351436684270273013 17287345447189150338095)
      ·
        refine ⟨25931018170783725507143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17287345447189150338095 25931018170783725507143)
        ·
          refine ⟨38896527256175588260715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25931018170783725507143 38896527256175588260715)
          ·
            refine ⟨58344790884263382391073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38896527256175588260715 58344790884263382391073)
            ·
              refine ⟨43758593163197536793305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58344790884263382391073 43758593163197536793305)
              ·
                refine ⟨32818944872398152594979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43758593163197536793305 32818944872398152594979)
                ·
                  refine ⟨49228417308597228892469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32818944872398152594979 49228417308597228892469)
                  ·
                    refine ⟨4615164122680990208669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49228417308597228892469 4615164122680990208669)
                    ·
                      rfl

theorem cell22_13482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_13482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13482 prefixEnd_13482 := by exact prefixLift 13482
  have htrace : WordTrace (prefixWord ++ tailWord_13482) baseStart_13482 baseEnd_13482 := by
    simpa [prefixWord, tailWord_13482, baseEnd_13482] using wordTrace_append hprefix tailTrace_13482
  have hstable : (prefixWord ++ tailWord_13482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13482).length < 2 ^ (prefixWord ++ tailWord_13482).sum := by decide
  have hdescent : baseEnd_13482 < baseStart_13482 := by decide
  rcases family_descends (prefixWord ++ tailWord_13482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13604 : List Nat := [2, 3, 1, 3, 1, 1, 5, 1, 1, 4]
def baseStart_13604 : Nat := 118140960795 + 13604 * 2 ^ 59
def prefixEnd_13604 : Nat := 4983230072969 + 3 ^ 40 * 13604 * 2
def baseEnd_13604 : Nat := 4656927215913338658295

theorem tailTrace_13604 : CollatzResearch.WordTrace tailWord_13604 prefixEnd_13604 4656927215913338658295 := by
  unfold tailWord_13604
  simp only [CollatzResearch.WordTrace]
  refine ⟨248089321361253111667933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 330785761815004148890577 248089321361253111667933)
  ·
    refine ⟨93033495510469916875475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248089321361253111667933 93033495510469916875475)
    ·
      refine ⟨139550243265704875313213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93033495510469916875475 139550243265704875313213)
      ·
        refine ⟨52331341224639328242455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139550243265704875313213 52331341224639328242455)
        ·
          refine ⟨78497011836958992363683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52331341224639328242455 78497011836958992363683)
          ·
            refine ⟨117745517755438488545525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78497011836958992363683 117745517755438488545525)
            ·
              refine ⟨11038642289572358301143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117745517755438488545525 11038642289572358301143)
              ·
                refine ⟨16557963434358537451715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11038642289572358301143 16557963434358537451715)
                ·
                  refine ⟨24836945151537806177573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16557963434358537451715 24836945151537806177573)
                  ·
                    refine ⟨4656927215913338658295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24836945151537806177573 4656927215913338658295)
                    ·
                      rfl

theorem cell22_13604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_13604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13604 prefixEnd_13604 := by exact prefixLift 13604
  have htrace : WordTrace (prefixWord ++ tailWord_13604) baseStart_13604 baseEnd_13604 := by
    simpa [prefixWord, tailWord_13604, baseEnd_13604] using wordTrace_append hprefix tailTrace_13604
  have hstable : (prefixWord ++ tailWord_13604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13604).length < 2 ^ (prefixWord ++ tailWord_13604).sum := by decide
  have hdescent : baseEnd_13604 < baseStart_13604 := by decide
  rcases family_descends (prefixWord ++ tailWord_13604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13619 : List Nat := [1, 1, 1, 2, 5, 2, 4, 2, 4]
def baseStart_13619 : Nat := 118140960795 + 13619 * 2 ^ 59
def prefixEnd_13619 : Nat := 4983230072969 + 3 ^ 40 * 13619 * 2
def baseEnd_13619 : Nat := 1554020674152766511083

theorem tailTrace_13619 : CollatzResearch.WordTrace tailWord_13619 prefixEnd_13619 1554020674152766511083 := by
  unfold tailWord_13619
  simp only [CollatzResearch.WordTrace]
  refine ⟨496725737668163785131911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 331150491778775856754607 496725737668163785131911)
  ·
    refine ⟨745088606502245677697867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 496725737668163785131911 745088606502245677697867)
    ·
      refine ⟨1117632909753368516546801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 745088606502245677697867 1117632909753368516546801)
      ·
        refine ⟨838224682315026387410101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1117632909753368516546801 838224682315026387410101)
        ·
          refine ⟨78583563967033723819697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 838224682315026387410101 78583563967033723819697)
          ·
            refine ⟨58937672975275292864773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78583563967033723819697 58937672975275292864773)
            ·
              refine ⟨11050813682864117412145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58937672975275292864773 11050813682864117412145)
              ·
                refine ⟨8288110262148088059109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11050813682864117412145 8288110262148088059109)
                ·
                  refine ⟨1554020674152766511083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8288110262148088059109 1554020674152766511083)
                  ·
                    rfl

theorem cell22_13619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 4].length) (baseStart_13619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13619 prefixEnd_13619 := by exact prefixLift 13619
  have htrace : WordTrace (prefixWord ++ tailWord_13619) baseStart_13619 baseEnd_13619 := by
    simpa [prefixWord, tailWord_13619, baseEnd_13619] using wordTrace_append hprefix tailTrace_13619
  have hstable : (prefixWord ++ tailWord_13619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13619).length < 2 ^ (prefixWord ++ tailWord_13619).sum := by decide
  have hdescent : baseEnd_13619 < baseStart_13619 := by decide
  rcases family_descends (prefixWord ++ tailWord_13619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13679 : List Nat := [1, 1, 2, 1, 3, 1, 3, 6, 1, 3]
def baseStart_13679 : Nat := 118140960795 + 13679 * 2 ^ 59
def prefixEnd_13679 : Nat := 4983230072969 + 3 ^ 40 * 13679 * 2
def baseEnd_13679 : Nat := 4682601248638143033065

theorem tailTrace_13679 : CollatzResearch.WordTrace tailWord_13679 prefixEnd_13679 4682601248638143033065 := by
  unfold tailWord_13679
  simp only [CollatzResearch.WordTrace]
  refine ⟨498914117450794032316091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 332609411633862688210727 498914117450794032316091)
  ·
    refine ⟨748371176176191048474137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 498914117450794032316091 748371176176191048474137)
    ·
      refine ⟨561278382132143286355603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 748371176176191048474137 561278382132143286355603)
      ·
        refine ⟨841917573198214929533405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561278382132143286355603 841917573198214929533405)
        ·
          refine ⟨315719089949330598575027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 841917573198214929533405 315719089949330598575027)
          ·
            refine ⟨473578634923995897862541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315719089949330598575027 473578634923995897862541)
            ·
              refine ⟨177591988096498461698453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473578634923995897862541 177591988096498461698453)
              ·
                refine ⟨8324624442023365392115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177591988096498461698453 8324624442023365392115)
                ·
                  refine ⟨12486936663035048088173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8324624442023365392115 12486936663035048088173)
                  ·
                    refine ⟨4682601248638143033065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12486936663035048088173 4682601248638143033065)
                    ·
                      rfl

theorem cell22_13679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 1, 3].length) (baseStart_13679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13679 prefixEnd_13679 := by exact prefixLift 13679
  have htrace : WordTrace (prefixWord ++ tailWord_13679) baseStart_13679 baseEnd_13679 := by
    simpa [prefixWord, tailWord_13679, baseEnd_13679] using wordTrace_append hprefix tailTrace_13679
  have hstable : (prefixWord ++ tailWord_13679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13679).length < 2 ^ (prefixWord ++ tailWord_13679).sum := by decide
  have hdescent : baseEnd_13679 < baseStart_13679 := by decide
  rcases family_descends (prefixWord ++ tailWord_13679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13786 : List Nat := [3, 1, 1, 2, 3, 3, 2, 2, 2, 3]
def baseStart_13786 : Nat := 118140960795 + 13786 * 2 ^ 59
def prefixEnd_13786 : Nat := 4983230072969 + 3 ^ 40 * 13786 * 2
def baseEnd_13786 : Nat := 4719229535325530607737

theorem tailTrace_13786 : CollatzResearch.WordTrace tailWord_13786 prefixEnd_13786 4719229535325530607737 := by
  unfold tailWord_13786
  simp only [CollatzResearch.WordTrace]
  refine ⟨125704182015787826615303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 335211152042100870974141 125704182015787826615303)
  ·
    refine ⟨188556273023681739922955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125704182015787826615303 188556273023681739922955)
    ·
      refine ⟨282834409535522609884433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188556273023681739922955 282834409535522609884433)
      ·
        refine ⟨212125807151641957413325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282834409535522609884433 212125807151641957413325)
        ·
          refine ⟨79547177681865734029997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 212125807151641957413325 79547177681865734029997)
          ·
            refine ⟨29830191630699650261249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79547177681865734029997 29830191630699650261249)
            ·
              refine ⟨22372643723024737695937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29830191630699650261249 22372643723024737695937)
              ·
                refine ⟨16779482792268553271953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22372643723024737695937 16779482792268553271953)
                ·
                  refine ⟨12584612094201414953965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16779482792268553271953 12584612094201414953965)
                  ·
                    refine ⟨4719229535325530607737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12584612094201414953965 4719229535325530607737)
                    ·
                      rfl

theorem cell22_13786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_13786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13786 prefixEnd_13786 := by exact prefixLift 13786
  have htrace : WordTrace (prefixWord ++ tailWord_13786) baseStart_13786 baseEnd_13786 := by
    simpa [prefixWord, tailWord_13786, baseEnd_13786] using wordTrace_append hprefix tailTrace_13786
  have hstable : (prefixWord ++ tailWord_13786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13786).length < 2 ^ (prefixWord ++ tailWord_13786).sum := by decide
  have hdescent : baseEnd_13786 < baseStart_13786 := by decide
  rcases family_descends (prefixWord ++ tailWord_13786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13799 : List Nat := [1, 1, 5, 2, 1, 4, 1, 7]
def baseStart_13799 : Nat := 118140960795 + 13799 * 2 ^ 59
def prefixEnd_13799 : Nat := 4983230072969 + 3 ^ 40 * 13799 * 2
def baseEnd_13799 : Nat := 524853300110870003633

theorem tailTrace_13799 : CollatzResearch.WordTrace tailWord_13799 prefixEnd_13799 524853300110870003633 := by
  unfold tailWord_13799
  simp only [CollatzResearch.WordTrace]
  refine ⟨503290877016054526684451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 335527251344036351122967 503290877016054526684451)
  ·
    refine ⟨754936315524081790026677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 503290877016054526684451 754936315524081790026677)
    ·
      refine ⟨70775279580382667815001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 754936315524081790026677 70775279580382667815001)
      ·
        refine ⟨53081459685287000861251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70775279580382667815001 53081459685287000861251)
        ·
          refine ⟨79622189527930501291877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53081459685287000861251 79622189527930501291877)
          ·
            refine ⟨14929160536486968992227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79622189527930501291877 14929160536486968992227)
            ·
              refine ⟨22393740804730453488341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14929160536486968992227 22393740804730453488341)
              ·
                refine ⟨524853300110870003633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22393740804730453488341 524853300110870003633)
                ·
                  rfl

theorem cell22_13799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 7].length) (baseStart_13799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13799 prefixEnd_13799 := by exact prefixLift 13799
  have htrace : WordTrace (prefixWord ++ tailWord_13799) baseStart_13799 baseEnd_13799 := by
    simpa [prefixWord, tailWord_13799, baseEnd_13799] using wordTrace_append hprefix tailTrace_13799
  have hstable : (prefixWord ++ tailWord_13799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13799).length < 2 ^ (prefixWord ++ tailWord_13799).sum := by decide
  have hdescent : baseEnd_13799 < baseStart_13799 := by decide
  rcases family_descends (prefixWord ++ tailWord_13799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13837 : List Nat := [1, 7, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_13837 : Nat := 118140960795 + 13837 * 2 ^ 59
def prefixEnd_13837 : Nat := 4983230072969 + 3 ^ 40 * 13837 * 2
def baseEnd_13837 : Nat := 4736687877578397582581

theorem tailTrace_13837 : CollatzResearch.WordTrace tailWord_13837 prefixEnd_13837 4736687877578397582581 := by
  unfold tailWord_13837
  simp only [CollatzResearch.WordTrace]
  refine ⟨504676850878387016567765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 336451233918924677711843 504676850878387016567765)
  ·
    refine ⟨11828363692462195700807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 504676850878387016567765 11828363692462195700807)
    ·
      refine ⟨17742545538693293551211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11828363692462195700807 17742545538693293551211)
      ·
        refine ⟨26613818308039940326817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17742545538693293551211 26613818308039940326817)
        ·
          refine ⟨19960363731029955245113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26613818308039940326817 19960363731029955245113)
          ·
            refine ⟨14970272798272466433835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19960363731029955245113 14970272798272466433835)
            ·
              refine ⟨22455409197408699650753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14970272798272466433835 22455409197408699650753)
              ·
                refine ⟨16841556898056524738065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22455409197408699650753 16841556898056524738065)
                ·
                  refine ⟨12631167673542393553549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16841556898056524738065 12631167673542393553549)
                  ·
                    refine ⟨4736687877578397582581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12631167673542393553549 4736687877578397582581)
                    ·
                      rfl

theorem cell22_13837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_13837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13837 prefixEnd_13837 := by exact prefixLift 13837
  have htrace : WordTrace (prefixWord ++ tailWord_13837) baseStart_13837 baseEnd_13837 := by
    simpa [prefixWord, tailWord_13837, baseEnd_13837] using wordTrace_append hprefix tailTrace_13837
  have hstable : (prefixWord ++ tailWord_13837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13837).length < 2 ^ (prefixWord ++ tailWord_13837).sum := by decide
  have hdescent : baseEnd_13837 < baseStart_13837 := by decide
  rcases family_descends (prefixWord ++ tailWord_13837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13854 : List Nat := [4, 3, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_13854 : Nat := 118140960795 + 13854 * 2 ^ 59
def prefixEnd_13854 : Nat := 4983230072969 + 3 ^ 40 * 13854 * 2
def baseEnd_13854 : Nat := 4742507324996019907529

theorem tailTrace_13854 : CollatzResearch.WordTrace tailWord_13854 prefixEnd_13854 4742507324996019907529 := by
  unfold tailWord_13854
  simp only [CollatzResearch.WordTrace]
  refine ⟨63162111477099864992077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 336864594544532613291077 63162111477099864992077)
  ·
    refine ⟨23685791803912449372029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63162111477099864992077 23685791803912449372029)
    ·
      refine ⟨8882171926467168514511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23685791803912449372029 8882171926467168514511)
      ·
        refine ⟨13323257889700752771767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8882171926467168514511 13323257889700752771767)
        ·
          refine ⟨19984886834551129157651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13323257889700752771767 19984886834551129157651)
          ·
            refine ⟨29977330251826693736477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19984886834551129157651 29977330251826693736477)
            ·
              refine ⟨11241498844435010151179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29977330251826693736477 11241498844435010151179)
              ·
                refine ⟨16862248266652515226769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11241498844435010151179 16862248266652515226769)
                ·
                  refine ⟨12646686199989386420077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16862248266652515226769 12646686199989386420077)
                  ·
                    refine ⟨4742507324996019907529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12646686199989386420077 4742507324996019907529)
                    ·
                      rfl

theorem cell22_13854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_13854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13854 prefixEnd_13854 := by exact prefixLift 13854
  have htrace : WordTrace (prefixWord ++ tailWord_13854) baseStart_13854 baseEnd_13854 := by
    simpa [prefixWord, tailWord_13854, baseEnd_13854] using wordTrace_append hprefix tailTrace_13854
  have hstable : (prefixWord ++ tailWord_13854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13854).length < 2 ^ (prefixWord ++ tailWord_13854).sum := by decide
  have hdescent : baseEnd_13854 < baseStart_13854 := by decide
  rcases family_descends (prefixWord ++ tailWord_13854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13904 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 4, 3]
def baseStart_13904 : Nat := 118140960795 + 13904 * 2 ^ 59
def prefixEnd_13904 : Nat := 4983230072969 + 3 ^ 40 * 13904 * 2
def baseEnd_13904 : Nat := 4759623346812556157375

theorem tailTrace_13904 : CollatzResearch.WordTrace tailWord_13904 prefixEnd_13904 4759623346812556157375 := by
  unfold tailWord_13904
  simp only [CollatzResearch.WordTrace]
  refine ⟨253560270817828729628383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 338080361090438306171177 253560270817828729628383)
  ·
    refine ⟨380340406226743094442575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253560270817828729628383 380340406226743094442575)
    ·
      refine ⟨570510609340114641663863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380340406226743094442575 570510609340114641663863)
      ·
        refine ⟨855765914010171962495795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570510609340114641663863 855765914010171962495795)
        ·
          refine ⟨1283648871015257943743693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855765914010171962495795 1283648871015257943743693)
          ·
            refine ⟨481368326630721728903885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1283648871015257943743693 481368326630721728903885)
            ·
              refine ⟨180513122486520648338957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 481368326630721728903885 180513122486520648338957)
              ·
                refine ⟨67692420932445243127109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180513122486520648338957 67692420932445243127109)
                ·
                  refine ⟨12692328924833483086333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67692420932445243127109 12692328924833483086333)
                  ·
                    refine ⟨4759623346812556157375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12692328924833483086333 4759623346812556157375)
                    ·
                      rfl

theorem cell22_13904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 4, 3].length) (baseStart_13904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13904 prefixEnd_13904 := by exact prefixLift 13904
  have htrace : WordTrace (prefixWord ++ tailWord_13904) baseStart_13904 baseEnd_13904 := by
    simpa [prefixWord, tailWord_13904, baseEnd_13904] using wordTrace_append hprefix tailTrace_13904
  have hstable : (prefixWord ++ tailWord_13904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13904).length < 2 ^ (prefixWord ++ tailWord_13904).sum := by decide
  have hdescent : baseEnd_13904 < baseStart_13904 := by decide
  rcases family_descends (prefixWord ++ tailWord_13904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13906 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 6]
def baseStart_13906 : Nat := 118140960795 + 13906 * 2 ^ 59
def prefixEnd_13906 : Nat := 4983230072969 + 3 ^ 40 * 13906 * 2
def baseEnd_13906 : Nat := 1586769329228405869123

theorem tailTrace_13906 : CollatzResearch.WordTrace tailWord_13906 prefixEnd_13906 1586769329228405869123 := by
  unfold tailWord_13906
  simp only [CollatzResearch.WordTrace]
  refine ⟨126798371907102950207393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 338128991752274533886381 126798371907102950207393)
  ·
    refine ⟨95098778930327212655545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126798371907102950207393 95098778930327212655545)
    ·
      refine ⟨71324084197745409491659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95098778930327212655545 71324084197745409491659)
      ·
        refine ⟨106986126296618114237489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71324084197745409491659 106986126296618114237489)
        ·
          refine ⟨80239594722463585678117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106986126296618114237489 80239594722463585678117)
          ·
            refine ⟨15044924010461922314647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80239594722463585678117 15044924010461922314647)
            ·
              refine ⟨22567386015692883471971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15044924010461922314647 22567386015692883471971)
              ·
                refine ⟨33851079023539325207957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22567386015692883471971 33851079023539325207957)
                ·
                  refine ⟨1586769329228405869123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33851079023539325207957 1586769329228405869123)
                  ·
                    rfl

theorem cell22_13906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_13906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13906 prefixEnd_13906 := by exact prefixLift 13906
  have htrace : WordTrace (prefixWord ++ tailWord_13906) baseStart_13906 baseEnd_13906 := by
    simpa [prefixWord, tailWord_13906, baseEnd_13906] using wordTrace_append hprefix tailTrace_13906
  have hstable : (prefixWord ++ tailWord_13906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13906).length < 2 ^ (prefixWord ++ tailWord_13906).sum := by decide
  have hdescent : baseEnd_13906 < baseStart_13906 := by decide
  rcases family_descends (prefixWord ++ tailWord_13906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13921 : List Nat := [1, 2, 3, 1, 1, 3, 3, 3, 2, 3]
def baseStart_13921 : Nat := 118140960795 + 13921 * 2 ^ 59
def prefixEnd_13921 : Nat := 4983230072969 + 3 ^ 40 * 13921 * 2
def baseEnd_13921 : Nat := 4765442794230178482323

theorem tailTrace_13921 : CollatzResearch.WordTrace tailWord_13921 prefixEnd_13921 4765442794230178482323 := by
  unfold tailWord_13921
  simp only [CollatzResearch.WordTrace]
  refine ⟨507740582574069362625617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 338493721716046241750411 507740582574069362625617)
  ·
    refine ⟨380805436930552021969213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 507740582574069362625617 380805436930552021969213)
    ·
      refine ⟨142802038848957008238455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380805436930552021969213 142802038848957008238455)
      ·
        refine ⟨214203058273435512357683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142802038848957008238455 214203058273435512357683)
        ·
          refine ⟨321304587410153268536525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214203058273435512357683 321304587410153268536525)
          ·
            refine ⟨120489220278807475701197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321304587410153268536525 120489220278807475701197)
            ·
              refine ⟨45183457604552803387949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120489220278807475701197 45183457604552803387949)
              ·
                refine ⟨16943796601707301270481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45183457604552803387949 16943796601707301270481)
                ·
                  refine ⟨12707847451280475952861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16943796601707301270481 12707847451280475952861)
                  ·
                    refine ⟨4765442794230178482323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12707847451280475952861 4765442794230178482323)
                    ·
                      rfl

theorem cell22_13921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_13921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13921 prefixEnd_13921 := by exact prefixLift 13921
  have htrace : WordTrace (prefixWord ++ tailWord_13921) baseStart_13921 baseEnd_13921 := by
    simpa [prefixWord, tailWord_13921, baseEnd_13921] using wordTrace_append hprefix tailTrace_13921
  have hstable : (prefixWord ++ tailWord_13921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13921).length < 2 ^ (prefixWord ++ tailWord_13921).sum := by decide
  have hdescent : baseEnd_13921 < baseStart_13921 := by decide
  rcases family_descends (prefixWord ++ tailWord_13921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13936 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 2, 4]
def baseStart_13936 : Nat := 118140960795 + 13936 * 2 ^ 59
def prefixEnd_13936 : Nat := 4983230072969 + 3 ^ 40 * 13936 * 2
def baseEnd_13936 : Nat := 4770577600775139357277

theorem tailTrace_13936 : CollatzResearch.WordTrace tailWord_13936 prefixEnd_13936 4770577600775139357277 := by
  unfold tailWord_13936
  simp only [CollatzResearch.WordTrace]
  refine ⟨254143838759863462210831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 338858451679817949614441 254143838759863462210831)
  ·
    refine ⟨381215758139795193316247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254143838759863462210831 381215758139795193316247)
    ·
      refine ⟨571823637209692789974371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381215758139795193316247 571823637209692789974371)
      ·
        refine ⟨857735455814539184961557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571823637209692789974371 857735455814539184961557)
        ·
          refine ⟨40206349491306524295073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 857735455814539184961557 40206349491306524295073)
          ·
            refine ⟨30154762118479893221305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40206349491306524295073 30154762118479893221305)
            ·
              refine ⟨22616071588859919915979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30154762118479893221305 22616071588859919915979)
              ·
                refine ⟨33924107383289879873969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22616071588859919915979 33924107383289879873969)
                ·
                  refine ⟨25443080537467409905477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33924107383289879873969 25443080537467409905477)
                  ·
                    refine ⟨4770577600775139357277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25443080537467409905477 4770577600775139357277)
                    ·
                      rfl

theorem cell22_13936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_13936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_13936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_13936 prefixEnd_13936 := by exact prefixLift 13936
  have htrace : WordTrace (prefixWord ++ tailWord_13936) baseStart_13936 baseEnd_13936 := by
    simpa [prefixWord, tailWord_13936, baseEnd_13936] using wordTrace_append hprefix tailTrace_13936
  have hstable : (prefixWord ++ tailWord_13936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13936).length < 2 ^ (prefixWord ++ tailWord_13936).sum := by decide
  have hdescent : baseEnd_13936 < baseStart_13936 := by decide
  rcases family_descends (prefixWord ++ tailWord_13936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14058 : List Nat := [3, 1, 3, 1, 1, 1, 5, 3, 4]
def baseStart_14058 : Nat := 118140960795 + 14058 * 2 ^ 59
def prefixEnd_14058 : Nat := 4983230072969 + 3 ^ 40 * 14058 * 2
def baseEnd_14058 : Nat := 1604113564669162602301

theorem tailTrace_14058 : CollatzResearch.WordTrace tailWord_14058 prefixEnd_14058 1604113564669162602301 := by
  unfold tailWord_14058
  simp only [CollatzResearch.WordTrace]
  refine ⟨128184345769435440090707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 341824922051827840241885 128184345769435440090707)
  ·
    refine ⟨192276518654153160136061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128184345769435440090707 192276518654153160136061)
    ·
      refine ⟨72103694495307435051023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192276518654153160136061 72103694495307435051023)
      ·
        refine ⟨108155541742961152576535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72103694495307435051023 108155541742961152576535)
        ·
          refine ⟨162233312614441728864803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108155541742961152576535 162233312614441728864803)
          ·
            refine ⟨243349968921662593297205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162233312614441728864803 243349968921662593297205)
            ·
              refine ⟨22814059586405868121613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243349968921662593297205 22814059586405868121613)
              ·
                refine ⟨8555272344902200545605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22814059586405868121613 8555272344902200545605)
                ·
                  refine ⟨1604113564669162602301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8555272344902200545605 1604113564669162602301)
                  ·
                    rfl

theorem cell22_14058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_14058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14058 prefixEnd_14058 := by exact prefixLift 14058
  have htrace : WordTrace (prefixWord ++ tailWord_14058) baseStart_14058 baseEnd_14058 := by
    simpa [prefixWord, tailWord_14058, baseEnd_14058] using wordTrace_append hprefix tailTrace_14058
  have hstable : (prefixWord ++ tailWord_14058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14058).length < 2 ^ (prefixWord ++ tailWord_14058).sum := by decide
  have hdescent : baseEnd_14058 < baseStart_14058 := by decide
  rcases family_descends (prefixWord ++ tailWord_14058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14090 : List Nat := [3, 1, 2, 2, 1, 3, 4, 1, 2, 3]
def baseStart_14090 : Nat := 118140960795 + 14090 * 2 ^ 59
def prefixEnd_14090 : Nat := 4983230072969 + 3 ^ 40 * 14090 * 2
def baseEnd_14090 : Nat := 4823294947970071006805

theorem tailTrace_14090 : CollatzResearch.WordTrace tailWord_14090 prefixEnd_14090 4823294947970071006805 := by
  unfold tailWord_14090
  simp only [CollatzResearch.WordTrace]
  refine ⟨128476129740452806381931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 342603012641207483685149 128476129740452806381931)
  ·
    refine ⟨192714194610679209572897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128476129740452806381931 192714194610679209572897)
    ·
      refine ⟨144535645958009407179673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192714194610679209572897 144535645958009407179673)
      ·
        refine ⟨108401734468507055384755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144535645958009407179673 108401734468507055384755)
        ·
          refine ⟨162602601702760583077133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108401734468507055384755 162602601702760583077133)
          ·
            refine ⟨60975975638535218653925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162602601702760583077133 60975975638535218653925)
            ·
              refine ⟨11432995432225353497611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60975975638535218653925 11432995432225353497611)
              ·
                refine ⟨17149493148338030246417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11432995432225353497611 17149493148338030246417)
                ·
                  refine ⟨12862119861253522684813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17149493148338030246417 12862119861253522684813)
                  ·
                    refine ⟨4823294947970071006805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12862119861253522684813 4823294947970071006805)
                    ·
                      rfl

theorem cell22_14090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_14090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14090 prefixEnd_14090 := by exact prefixLift 14090
  have htrace : WordTrace (prefixWord ++ tailWord_14090) baseStart_14090 baseEnd_14090 := by
    simpa [prefixWord, tailWord_14090, baseEnd_14090] using wordTrace_append hprefix tailTrace_14090
  have hstable : (prefixWord ++ tailWord_14090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14090).length < 2 ^ (prefixWord ++ tailWord_14090).sum := by decide
  have hdescent : baseEnd_14090 < baseStart_14090 := by decide
  rcases family_descends (prefixWord ++ tailWord_14090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14099 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 4, 6]
def baseStart_14099 : Nat := 118140960795 + 14099 * 2 ^ 59
def prefixEnd_14099 : Nat := 4983230072969 + 3 ^ 40 * 14099 * 2
def baseEnd_14099 : Nat := 4826375831897047531777

theorem tailTrace_14099 : CollatzResearch.WordTrace tailWord_14099 prefixEnd_14099 4826375831897047531777 := by
  unfold tailWord_14099
  simp only [CollatzResearch.WordTrace]
  refine ⟨514232775929205762605351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 342821850619470508403567 514232775929205762605351)
  ·
    refine ⟨771349163893808643908027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 514232775929205762605351 771349163893808643908027)
    ·
      refine ⟨1157023745840712965862041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 771349163893808643908027 1157023745840712965862041)
      ·
        refine ⟨867767809380534724396531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1157023745840712965862041 867767809380534724396531)
        ·
          refine ⟨1301651714070802086594797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867767809380534724396531 1301651714070802086594797)
          ·
            refine ⟨488119392776550782473049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1301651714070802086594797 488119392776550782473049)
            ·
              refine ⟨366089544582413086854787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488119392776550782473049 366089544582413086854787)
              ·
                refine ⟨549134316873619630282181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366089544582413086854787 549134316873619630282181)
                ·
                  refine ⟨102962684413803680677909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 549134316873619630282181 102962684413803680677909)
                  ·
                    refine ⟨4826375831897047531777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102962684413803680677909 4826375831897047531777)
                    ·
                      rfl

theorem cell22_14099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 6].length) (baseStart_14099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14099 prefixEnd_14099 := by exact prefixLift 14099
  have htrace : WordTrace (prefixWord ++ tailWord_14099) baseStart_14099 baseEnd_14099 := by
    simpa [prefixWord, tailWord_14099, baseEnd_14099] using wordTrace_append hprefix tailTrace_14099
  have hstable : (prefixWord ++ tailWord_14099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14099).length < 2 ^ (prefixWord ++ tailWord_14099).sum := by decide
  have hdescent : baseEnd_14099 < baseStart_14099 := by decide
  rcases family_descends (prefixWord ++ tailWord_14099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14193 : List Nat := [1, 2, 2, 2, 1, 3, 1, 6, 4]
def baseStart_14193 : Nat := 118140960795 + 14193 * 2 ^ 59
def prefixEnd_14193 : Nat := 4983230072969 + 3 ^ 40 * 14193 * 2
def baseEnd_14193 : Nat := 1619517984304045227163

theorem tailTrace_14193 : CollatzResearch.WordTrace tailWord_14193 prefixEnd_14193 1619517984304045227163 := by
  unfold tailWord_14193
  simp only [CollatzResearch.WordTrace]
  refine ⟨517661237588659816527233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 345107491725773211018155 517661237588659816527233)
  ·
    refine ⟨388245928191494862395425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 517661237588659816527233 388245928191494862395425)
    ·
      refine ⟨291184446143621146796569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388245928191494862395425 291184446143621146796569)
      ·
        refine ⟨218388334607715860097427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291184446143621146796569 218388334607715860097427)
        ·
          refine ⟨327582501911573790146141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218388334607715860097427 327582501911573790146141)
          ·
            refine ⟨122843438216840171304803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327582501911573790146141 122843438216840171304803)
            ·
              refine ⟨184265157325260256957205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122843438216840171304803 184265157325260256957205)
              ·
                refine ⟨8637429249621574544869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184265157325260256957205 8637429249621574544869)
                ·
                  refine ⟨1619517984304045227163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8637429249621574544869 1619517984304045227163)
                  ·
                    rfl

theorem cell22_14193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 4].length) (baseStart_14193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14193 prefixEnd_14193 := by exact prefixLift 14193
  have htrace : WordTrace (prefixWord ++ tailWord_14193) baseStart_14193 baseEnd_14193 := by
    simpa [prefixWord, tailWord_14193, baseEnd_14193] using wordTrace_append hprefix tailTrace_14193
  have hstable : (prefixWord ++ tailWord_14193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14193).length < 2 ^ (prefixWord ++ tailWord_14193).sum := by decide
  have hdescent : baseEnd_14193 < baseStart_14193 := by decide
  rcases family_descends (prefixWord ++ tailWord_14193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14266 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 9]
def baseStart_14266 : Nat := 118140960795 + 14266 * 2 ^ 59
def prefixEnd_14266 : Nat := 4983230072969 + 3 ^ 40 * 14266 * 2
def baseEnd_14266 : Nat := 1627847781588092868755

theorem tailTrace_14266 : CollatzResearch.WordTrace tailWord_14266 prefixEnd_14266 1627847781588092868755 := by
  unfold tailWord_14266
  simp only [CollatzResearch.WordTrace]
  refine ⟨130080941581048320983663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 346882510882795522623101 130080941581048320983663)
  ·
    refine ⟨195121412371572481475495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130080941581048320983663 195121412371572481475495)
    ·
      refine ⟨292682118557358722213243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195121412371572481475495 292682118557358722213243)
      ·
        refine ⟨439023177836038083319865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292682118557358722213243 439023177836038083319865)
        ·
          refine ⟨329267383377028562489899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439023177836038083319865 329267383377028562489899)
          ·
            refine ⟨493901075065542843734849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329267383377028562489899 493901075065542843734849)
            ·
              refine ⟨370425806299157132801137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493901075065542843734849 370425806299157132801137)
              ·
                refine ⟨277819354724367849600853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370425806299157132801137 277819354724367849600853)
                ·
                  refine ⟨1627847781588092868755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 277819354724367849600853 1627847781588092868755)
                  ·
                    rfl

theorem cell22_14266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_14266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14266 prefixEnd_14266 := by exact prefixLift 14266
  have htrace : WordTrace (prefixWord ++ tailWord_14266) baseStart_14266 baseEnd_14266 := by
    simpa [prefixWord, tailWord_14266, baseEnd_14266] using wordTrace_append hprefix tailTrace_14266
  have hstable : (prefixWord ++ tailWord_14266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14266).length < 2 ^ (prefixWord ++ tailWord_14266).sum := by decide
  have hdescent : baseEnd_14266 < baseStart_14266 := by decide
  rcases family_descends (prefixWord ++ tailWord_14266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14281 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 1, 7]
def baseStart_14281 : Nat := 118140960795 + 14281 * 2 ^ 59
def prefixEnd_14281 : Nat := 4983230072969 + 3 ^ 40 * 14281 * 2
def baseEnd_14281 : Nat := 4888678151309239481219

theorem tailTrace_14281 : CollatzResearch.WordTrace tailWord_14281 prefixEnd_14281 4888678151309239481219 := by
  unfold tailWord_14281
  simp only [CollatzResearch.WordTrace]
  refine ⟨520870861269850845730697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 347247240846567230487131 520870861269850845730697)
  ·
    refine ⟨390653145952388134298023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 520870861269850845730697 390653145952388134298023)
    ·
      refine ⟨585979718928582201447035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390653145952388134298023 585979718928582201447035)
      ·
        refine ⟨878969578392873302170553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585979718928582201447035 878969578392873302170553)
        ·
          refine ⟨659227183794654976627915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 878969578392873302170553 659227183794654976627915)
          ·
            refine ⟨988840775691982464941873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659227183794654976627915 988840775691982464941873)
            ·
              refine ⟨741630581768986848706405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988840775691982464941873 741630581768986848706405)
              ·
                refine ⟨139055734081685034132451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 741630581768986848706405 139055734081685034132451)
                ·
                  refine ⟨208583601122527551198677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139055734081685034132451 208583601122527551198677)
                  ·
                    refine ⟨4888678151309239481219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 208583601122527551198677 4888678151309239481219)
                    ·
                      rfl

theorem cell22_14281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_14281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14281 prefixEnd_14281 := by exact prefixLift 14281
  have htrace : WordTrace (prefixWord ++ tailWord_14281) baseStart_14281 baseEnd_14281 := by
    simpa [prefixWord, tailWord_14281, baseEnd_14281] using wordTrace_append hprefix tailTrace_14281
  have hstable : (prefixWord ++ tailWord_14281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14281).length < 2 ^ (prefixWord ++ tailWord_14281).sum := by decide
  have hdescent : baseEnd_14281 < baseStart_14281 := by decide
  rcases family_descends (prefixWord ++ tailWord_14281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14360 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 4, 3]
def baseStart_14360 : Nat := 118140960795 + 14360 * 2 ^ 59
def prefixEnd_14360 : Nat := 4983230072969 + 3 ^ 40 * 14360 * 2
def baseEnd_14360 : Nat := 4915721465779366755977

theorem tailTrace_14360 : CollatzResearch.WordTrace tailWord_14360 prefixEnd_14360 4915721465779366755977 := by
  unfold tailWord_14360
  simp only [CollatzResearch.WordTrace]
  refine ⟨261876113991823668928267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 349168151989098225237689 261876113991823668928267)
  ·
    refine ⟨392814170987735503392401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261876113991823668928267 392814170987735503392401)
    ·
      refine ⟨294610628240801627544301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392814170987735503392401 294610628240801627544301)
      ·
        refine ⟨110478985590300610329113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294610628240801627544301 110478985590300610329113)
        ·
          refine ⟨82859239192725457746835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110478985590300610329113 82859239192725457746835)
          ·
            refine ⟨124288858789088186620253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82859239192725457746835 124288858789088186620253)
            ·
              refine ⟨46608322045908069982595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124288858789088186620253 46608322045908069982595)
              ·
                refine ⟨69912483068862104973893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46608322045908069982595 69912483068862104973893)
                ·
                  refine ⟨13108590575411644682605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69912483068862104973893 13108590575411644682605)
                  ·
                    refine ⟨4915721465779366755977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13108590575411644682605 4915721465779366755977)
                    ·
                      rfl

theorem cell22_14360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_14360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14360 prefixEnd_14360 := by exact prefixLift 14360
  have htrace : WordTrace (prefixWord ++ tailWord_14360) baseStart_14360 baseEnd_14360 := by
    simpa [prefixWord, tailWord_14360, baseEnd_14360] using wordTrace_append hprefix tailTrace_14360
  have hstable : (prefixWord ++ tailWord_14360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14360).length < 2 ^ (prefixWord ++ tailWord_14360).sum := by decide
  have hdescent : baseEnd_14360 < baseStart_14360 := by decide
  rcases family_descends (prefixWord ++ tailWord_14360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14390 : List Nat := [5, 1, 2, 1, 1, 1, 3, 8]
def baseStart_14390 : Nat := 118140960795 + 14390 * 2 ^ 59
def prefixEnd_14390 : Nat := 4983230072969 + 3 ^ 40 * 14390 * 2
def baseEnd_14390 : Nat := 547332342096587611765

theorem tailTrace_14390 : CollatzResearch.WordTrace tailWord_14390 prefixEnd_14390 547332342096587611765 := by
  unfold tailWord_14390
  simp only [CollatzResearch.WordTrace]
  refine ⟨32802901117185153840539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 349897611916641640965749 32802901117185153840539)
  ·
    refine ⟨49204351675777730760809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32802901117185153840539 49204351675777730760809)
    ·
      refine ⟨36903263756833298070607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49204351675777730760809 36903263756833298070607)
      ·
        refine ⟨55354895635249947105911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36903263756833298070607 55354895635249947105911)
        ·
          refine ⟨83032343452874920658867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55354895635249947105911 83032343452874920658867)
          ·
            refine ⟨124548515179312380988301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83032343452874920658867 124548515179312380988301)
            ·
              refine ⟨46705693192242142870613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124548515179312380988301 46705693192242142870613)
              ·
                refine ⟨547332342096587611765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 46705693192242142870613 547332342096587611765)
                ·
                  rfl

theorem cell22_14390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_14390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14390 prefixEnd_14390 := by exact prefixLift 14390
  have htrace : WordTrace (prefixWord ++ tailWord_14390) baseStart_14390 baseEnd_14390 := by
    simpa [prefixWord, tailWord_14390, baseEnd_14390] using wordTrace_append hprefix tailTrace_14390
  have hstable : (prefixWord ++ tailWord_14390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14390).length < 2 ^ (prefixWord ++ tailWord_14390).sum := by decide
  have hdescent : baseEnd_14390 < baseStart_14390 := by decide
  rcases family_descends (prefixWord ++ tailWord_14390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14433 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 1, 7]
def baseStart_14433 : Nat := 118140960795 + 14433 * 2 ^ 59
def prefixEnd_14433 : Nat := 4983230072969 + 3 ^ 40 * 14433 * 2
def baseEnd_14433 : Nat := 4940710857631509680753

theorem tailTrace_14433 : CollatzResearch.WordTrace tailWord_14433 prefixEnd_14433 4940710857631509680753 := by
  unfold tailWord_14433
  simp only [CollatzResearch.WordTrace]
  refine ⟨526414756719180805263953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 350943171146120536842635 526414756719180805263953)
  ·
    refine ⟨394811067539385603947965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 526414756719180805263953 394811067539385603947965)
    ·
      refine ⟨148054150327269601480487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 394811067539385603947965 148054150327269601480487)
      ·
        refine ⟨222081225490904402220731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148054150327269601480487 222081225490904402220731)
        ·
          refine ⟨333121838236356603331097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222081225490904402220731 333121838236356603331097)
          ·
            refine ⟨249841378677267452498323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333121838236356603331097 249841378677267452498323)
            ·
              refine ⟨374762068015901178747485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249841378677267452498323 374762068015901178747485)
              ·
                refine ⟨140535775505962942030307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374762068015901178747485 140535775505962942030307)
                ·
                  refine ⟨210803663258944413045461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140535775505962942030307 210803663258944413045461)
                  ·
                    refine ⟨4940710857631509680753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 210803663258944413045461 4940710857631509680753)
                    ·
                      rfl

theorem cell22_14433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_14433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14433 prefixEnd_14433 := by exact prefixLift 14433
  have htrace : WordTrace (prefixWord ++ tailWord_14433) baseStart_14433 baseEnd_14433 := by
    simpa [prefixWord, tailWord_14433, baseEnd_14433] using wordTrace_append hprefix tailTrace_14433
  have hstable : (prefixWord ++ tailWord_14433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14433).length < 2 ^ (prefixWord ++ tailWord_14433).sum := by decide
  have hdescent : baseEnd_14433 < baseStart_14433 := by decide
  rcases family_descends (prefixWord ++ tailWord_14433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14484 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_14484 : Nat := 118140960795 + 14484 * 2 ^ 59
def prefixEnd_14484 : Nat := 4983230072969 + 3 ^ 40 * 14484 * 2
def baseEnd_14484 : Nat := 4958169199884376655597

theorem tailTrace_14484 : CollatzResearch.WordTrace tailWord_14484 prefixEnd_14484 4958169199884376655597 := by
  unfold tailWord_14484
  simp only [CollatzResearch.WordTrace]
  refine ⟨264137439767208257685253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 352183253022944343580337 264137439767208257685253)
  ·
    refine ⟨49525769956351548315985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264137439767208257685253 49525769956351548315985)
    ·
      refine ⟨37144327467263661236989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49525769956351548315985 37144327467263661236989)
      ·
        refine ⟨13929122800223872963871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37144327467263661236989 13929122800223872963871)
        ·
          refine ⟨20893684200335809445807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13929122800223872963871 20893684200335809445807)
          ·
            refine ⟨31340526300503714168711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20893684200335809445807 31340526300503714168711)
            ·
              refine ⟨47010789450755571253067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31340526300503714168711 47010789450755571253067)
              ·
                refine ⟨70516184176133356879601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47010789450755571253067 70516184176133356879601)
                ·
                  refine ⟨52887138132100017659701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70516184176133356879601 52887138132100017659701)
                  ·
                    refine ⟨4958169199884376655597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52887138132100017659701 4958169199884376655597)
                    ·
                      rfl

theorem cell22_14484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_14484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14484 prefixEnd_14484 := by exact prefixLift 14484
  have htrace : WordTrace (prefixWord ++ tailWord_14484) baseStart_14484 baseEnd_14484 := by
    simpa [prefixWord, tailWord_14484, baseEnd_14484] using wordTrace_append hprefix tailTrace_14484
  have hstable : (prefixWord ++ tailWord_14484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14484).length < 2 ^ (prefixWord ++ tailWord_14484).sum := by decide
  have hdescent : baseEnd_14484 < baseStart_14484 := by decide
  rcases family_descends (prefixWord ++ tailWord_14484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14546 : List Nat := [3, 2, 2, 2, 1, 3, 3, 1, 2, 3]
def baseStart_14546 : Nat := 118140960795 + 14546 * 2 ^ 59
def prefixEnd_14546 : Nat := 4983230072969 + 3 ^ 40 * 14546 * 2
def baseEnd_14546 : Nat := 4979393066936881605407

theorem tailTrace_14546 : CollatzResearch.WordTrace tailWord_14546 prefixEnd_14546 4979393066936881605407 := by
  unfold tailWord_14546
  simp only [CollatzResearch.WordTrace]
  refine ⟨132634051327450276031873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 353690803539867402751661 132634051327450276031873)
  ·
    refine ⟨99475538495587707023905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132634051327450276031873 99475538495587707023905)
    ·
      refine ⟨74606653871690780267929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99475538495587707023905 74606653871690780267929)
      ·
        refine ⟨55954990403768085200947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74606653871690780267929 55954990403768085200947)
        ·
          refine ⟨83932485605652127801421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55954990403768085200947 83932485605652127801421)
          ·
            refine ⟨31474682102119547925533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83932485605652127801421 31474682102119547925533)
            ·
              refine ⟨11803005788294830472075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31474682102119547925533 11803005788294830472075)
              ·
                refine ⟨17704508682442245708113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11803005788294830472075 17704508682442245708113)
                ·
                  refine ⟨13278381511831684281085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17704508682442245708113 13278381511831684281085)
                  ·
                    refine ⟨4979393066936881605407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13278381511831684281085 4979393066936881605407)
                    ·
                      rfl

theorem cell22_14546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_14546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14546 prefixEnd_14546 := by exact prefixLift 14546
  have htrace : WordTrace (prefixWord ++ tailWord_14546) baseStart_14546 baseEnd_14546 := by
    simpa [prefixWord, tailWord_14546, baseEnd_14546] using wordTrace_append hprefix tailTrace_14546
  have hstable : (prefixWord ++ tailWord_14546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14546).length < 2 ^ (prefixWord ++ tailWord_14546).sum := by decide
  have hdescent : baseEnd_14546 < baseStart_14546 := by decide
  rcases family_descends (prefixWord ++ tailWord_14546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14570 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 9]
def baseStart_14570 : Nat := 118140960795 + 14570 * 2 ^ 59
def prefixEnd_14570 : Nat := 4983230072969 + 3 ^ 40 * 14570 * 2
def baseEnd_14570 : Nat := 1662536252469606335111

theorem tailTrace_14570 : CollatzResearch.WordTrace tailWord_14570 prefixEnd_14570 1662536252469606335111 := by
  unfold tailWord_14570
  simp only [CollatzResearch.WordTrace]
  refine ⟨132852889305713300750291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 354274371481902135334109 132852889305713300750291)
  ·
    refine ⟨199279333958569951125437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132852889305713300750291 199279333958569951125437)
    ·
      refine ⟨74729750234463731672039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199279333958569951125437 74729750234463731672039)
      ·
        refine ⟨112094625351695597508059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74729750234463731672039 112094625351695597508059)
        ·
          refine ⟨168141938027543396262089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112094625351695597508059 168141938027543396262089)
          ·
            refine ⟨126106453520657547196567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168141938027543396262089 126106453520657547196567)
            ·
              refine ⟨189159680280986320794851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126106453520657547196567 189159680280986320794851)
              ·
                refine ⟨283739520421479481192277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189159680280986320794851 283739520421479481192277)
                ·
                  refine ⟨1662536252469606335111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 283739520421479481192277 1662536252469606335111)
                  ·
                    rfl

theorem cell22_14570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_14570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14570 prefixEnd_14570 := by exact prefixLift 14570
  have htrace : WordTrace (prefixWord ++ tailWord_14570) baseStart_14570 baseEnd_14570 := by
    simpa [prefixWord, tailWord_14570, baseEnd_14570] using wordTrace_append hprefix tailTrace_14570
  have hstable : (prefixWord ++ tailWord_14570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14570).length < 2 ^ (prefixWord ++ tailWord_14570).sum := by decide
  have hdescent : baseEnd_14570 < baseStart_14570 := by decide
  rcases family_descends (prefixWord ++ tailWord_14570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14585 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 2, 5]
def baseStart_14585 : Nat := 118140960795 + 14585 * 2 ^ 59
def prefixEnd_14585 : Nat := 4983230072969 + 3 ^ 40 * 14585 * 2
def baseEnd_14585 : Nat := 4992743563953779880287

theorem tailTrace_14585 : CollatzResearch.WordTrace tailWord_14585 prefixEnd_14585 4992743563953779880287 := by
  unfold tailWord_14585
  simp only [CollatzResearch.WordTrace]
  refine ⟨531958652168510764797209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 354639101445673843198139 531958652168510764797209)
  ·
    refine ⟨398968989126383073597907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 531958652168510764797209 398968989126383073597907)
    ·
      refine ⟨598453483689574610396861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398968989126383073597907 598453483689574610396861)
      ·
        refine ⟨224420056383590478898823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 598453483689574610396861 224420056383590478898823)
        ·
          refine ⟨336630084575385718348235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224420056383590478898823 336630084575385718348235)
          ·
            refine ⟨504945126863078577522353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336630084575385718348235 504945126863078577522353)
            ·
              refine ⟨378708845147308933141765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504945126863078577522353 378708845147308933141765)
              ·
                refine ⟨71007908465120424964081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378708845147308933141765 71007908465120424964081)
                ·
                  refine ⟨53255931348840318723061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71007908465120424964081 53255931348840318723061)
                  ·
                    refine ⟨4992743563953779880287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53255931348840318723061 4992743563953779880287)
                    ·
                      rfl

theorem cell22_14585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_14585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14585 prefixEnd_14585 := by exact prefixLift 14585
  have htrace : WordTrace (prefixWord ++ tailWord_14585) baseStart_14585 baseEnd_14585 := by
    simpa [prefixWord, tailWord_14585, baseEnd_14585] using wordTrace_append hprefix tailTrace_14585
  have hstable : (prefixWord ++ tailWord_14585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14585).length < 2 ^ (prefixWord ++ tailWord_14585).sum := by decide
  have hdescent : baseEnd_14585 < baseStart_14585 := by decide
  rcases family_descends (prefixWord ++ tailWord_14585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14591 : List Nat := [1, 1, 2, 2, 1, 4, 5, 2, 1, 3]
def baseStart_14591 : Nat := 118140960795 + 14591 * 2 ^ 59
def prefixEnd_14591 : Nat := 4983230072969 + 3 ^ 40 * 14591 * 2
def baseEnd_14591 : Nat := 4994797486571764230269

theorem tailTrace_14591 : CollatzResearch.WordTrace tailWord_14591 prefixEnd_14591 4994797486571764230269 := by
  unfold tailWord_14591
  simp only [CollatzResearch.WordTrace]
  refine ⟨532177490146773789515627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 354784993431182526343751 532177490146773789515627)
  ·
    refine ⟨798266235220160684273441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 532177490146773789515627 798266235220160684273441)
    ·
      refine ⟨598699676415120513205081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 798266235220160684273441 598699676415120513205081)
      ·
        refine ⟨449024757311340384903811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598699676415120513205081 449024757311340384903811)
        ·
          refine ⟨673537135967010577355717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449024757311340384903811 673537135967010577355717)
          ·
            refine ⟨126288212993814483254197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 673537135967010577355717 126288212993814483254197)
            ·
              refine ⟨11839519968170107805081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126288212993814483254197 11839519968170107805081)
              ·
                refine ⟨8879639976127580853811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11839519968170107805081 8879639976127580853811)
                ·
                  refine ⟨13319459964191371280717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8879639976127580853811 13319459964191371280717)
                  ·
                    refine ⟨4994797486571764230269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13319459964191371280717 4994797486571764230269)
                    ·
                      rfl

theorem cell22_14591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 1, 3].length) (baseStart_14591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14591 prefixEnd_14591 := by exact prefixLift 14591
  have htrace : WordTrace (prefixWord ++ tailWord_14591) baseStart_14591 baseEnd_14591 := by
    simpa [prefixWord, tailWord_14591, baseEnd_14591] using wordTrace_append hprefix tailTrace_14591
  have hstable : (prefixWord ++ tailWord_14591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14591).length < 2 ^ (prefixWord ++ tailWord_14591).sum := by decide
  have hdescent : baseEnd_14591 < baseStart_14591 := by decide
  rcases family_descends (prefixWord ++ tailWord_14591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14647 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 4, 3]
def baseStart_14647 : Nat := 118140960795 + 14647 * 2 ^ 59
def prefixEnd_14647 : Nat := 4983230072969 + 3 ^ 40 * 14647 * 2
def baseEnd_14647 : Nat := 5013967431006284830097

theorem tailTrace_14647 : CollatzResearch.WordTrace tailWord_14647 prefixEnd_14647 5013967431006284830097 := by
  unfold tailWord_14647
  simp only [CollatzResearch.WordTrace]
  refine ⟨534219977943895353554195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 356146651962596902369463 534219977943895353554195)
  ·
    refine ⟨801329966915843030331293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 534219977943895353554195 801329966915843030331293)
    ·
      refine ⟨300498737593441136374235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 801329966915843030331293 300498737593441136374235)
      ·
        refine ⟨450748106390161704561353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300498737593441136374235 450748106390161704561353)
        ·
          refine ⟨338061079792621278421015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450748106390161704561353 338061079792621278421015)
          ·
            refine ⟨507091619688931917631523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338061079792621278421015 507091619688931917631523)
            ·
              refine ⟨760637429533397876447285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507091619688931917631523 760637429533397876447285)
              ·
                refine ⟨71309759018756050916933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 760637429533397876447285 71309759018756050916933)
                ·
                  refine ⟨13370579816016759546925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71309759018756050916933 13370579816016759546925)
                  ·
                    refine ⟨5013967431006284830097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13370579816016759546925 5013967431006284830097)
                    ·
                      rfl

theorem cell22_14647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_14647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14647 prefixEnd_14647 := by exact prefixLift 14647
  have htrace : WordTrace (prefixWord ++ tailWord_14647) baseStart_14647 baseEnd_14647 := by
    simpa [prefixWord, tailWord_14647, baseEnd_14647] using wordTrace_append hprefix tailTrace_14647
  have hstable : (prefixWord ++ tailWord_14647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14647).length < 2 ^ (prefixWord ++ tailWord_14647).sum := by decide
  have hdescent : baseEnd_14647 < baseStart_14647 := by decide
  rcases family_descends (prefixWord ++ tailWord_14647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14664 : List Nat := [2, 1, 3, 1, 1, 2, 4, 3, 2, 3]
def baseStart_14664 : Nat := 118140960795 + 14664 * 2 ^ 59
def prefixEnd_14664 : Nat := 4983230072969 + 3 ^ 40 * 14664 * 2
def baseEnd_14664 : Nat := 5019786878423907155045

theorem tailTrace_14664 : CollatzResearch.WordTrace tailWord_14664 prefixEnd_14664 5019786878423907155045 := by
  unfold tailWord_14664
  simp only [CollatzResearch.WordTrace]
  refine ⟨267420009441153628461523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 356560012588204837948697 267420009441153628461523)
  ·
    refine ⟨401130014161730442692285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267420009441153628461523 401130014161730442692285)
    ·
      refine ⟨150423755310648916009607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401130014161730442692285 150423755310648916009607)
      ·
        refine ⟨225635632965973374014411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150423755310648916009607 225635632965973374014411)
        ·
          refine ⟨338453449448960061021617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225635632965973374014411 338453449448960061021617)
          ·
            refine ⟨253840087086720045766213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338453449448960061021617 253840087086720045766213)
            ·
              refine ⟨47595016328760008581165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253840087086720045766213 47595016328760008581165)
              ·
                refine ⟨17848131123285003217937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47595016328760008581165 17848131123285003217937)
                ·
                  refine ⟨13386098342463752413453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17848131123285003217937 13386098342463752413453)
                  ·
                    refine ⟨5019786878423907155045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13386098342463752413453 5019786878423907155045)
                    ·
                      rfl

theorem cell22_14664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_14664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14664 prefixEnd_14664 := by exact prefixLift 14664
  have htrace : WordTrace (prefixWord ++ tailWord_14664) baseStart_14664 baseEnd_14664 := by
    simpa [prefixWord, tailWord_14664, baseEnd_14664] using wordTrace_append hprefix tailTrace_14664
  have hstable : (prefixWord ++ tailWord_14664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14664).length < 2 ^ (prefixWord ++ tailWord_14664).sum := by decide
  have hdescent : baseEnd_14664 < baseStart_14664 := by decide
  rcases family_descends (prefixWord ++ tailWord_14664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14675 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 1, 9]
def baseStart_14675 : Nat := 118140960795 + 14675 * 2 ^ 59
def prefixEnd_14675 : Nat := 4983230072969 + 3 ^ 40 * 14675 * 2
def baseEnd_14675 : Nat := 5023552403223545130011

theorem tailTrace_14675 : CollatzResearch.WordTrace tailWord_14675 prefixEnd_14675 5023552403223545130011 := by
  unfold tailWord_14675
  simp only [CollatzResearch.WordTrace]
  refine ⟨535241221842456135573479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 356827481228304090382319 535241221842456135573479)
  ·
    refine ⟨802861832763684203360219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 535241221842456135573479 802861832763684203360219)
    ·
      refine ⟨1204292749145526305040329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802861832763684203360219 1204292749145526305040329)
      ·
        refine ⟨903219561859144728780247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1204292749145526305040329 903219561859144728780247)
        ·
          refine ⟨1354829342788717093170371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903219561859144728780247 1354829342788717093170371)
          ·
            refine ⟨2032244014183075639755557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354829342788717093170371 2032244014183075639755557)
            ·
              refine ⟨381045752659326682454167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2032244014183075639755557 381045752659326682454167)
              ·
                refine ⟨571568628988990023681251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381045752659326682454167 571568628988990023681251)
                ·
                  refine ⟨857352943483485035521877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571568628988990023681251 857352943483485035521877)
                  ·
                    refine ⟨5023552403223545130011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 857352943483485035521877 5023552403223545130011)
                    ·
                      rfl

theorem cell22_14675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_14675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14675 prefixEnd_14675 := by exact prefixLift 14675
  have htrace : WordTrace (prefixWord ++ tailWord_14675) baseStart_14675 baseEnd_14675 := by
    simpa [prefixWord, tailWord_14675, baseEnd_14675] using wordTrace_append hprefix tailTrace_14675
  have hstable : (prefixWord ++ tailWord_14675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14675).length < 2 ^ (prefixWord ++ tailWord_14675).sum := by decide
  have hdescent : baseEnd_14675 < baseStart_14675 := by decide
  rcases family_descends (prefixWord ++ tailWord_14675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14698 : List Nat := [3, 1, 3, 3, 1, 3, 1, 2, 2, 3]
def baseStart_14698 : Nat := 118140960795 + 14698 * 2 ^ 59
def prefixEnd_14698 : Nat := 4983230072969 + 3 ^ 40 * 14698 * 2
def baseEnd_14698 : Nat := 5031425773259151804941

theorem tailTrace_14698 : CollatzResearch.WordTrace tailWord_14698 prefixEnd_14698 5031425773259151804941 := by
  unfold tailWord_14698
  simp only [CollatzResearch.WordTrace]
  refine ⟨134020025189782765915187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 357386733839420709107165 134020025189782765915187)
  ·
    refine ⟨201030037784674148872781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134020025189782765915187 201030037784674148872781)
    ·
      refine ⟨75386264169252805827293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201030037784674148872781 75386264169252805827293)
      ·
        refine ⟨28269849063469802185235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75386264169252805827293 28269849063469802185235)
        ·
          refine ⟨42404773595204703277853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28269849063469802185235 42404773595204703277853)
          ·
            refine ⟨15901790098201763729195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42404773595204703277853 15901790098201763729195)
            ·
              refine ⟨23852685147302645593793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15901790098201763729195 23852685147302645593793)
              ·
                refine ⟨17889513860476984195345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23852685147302645593793 17889513860476984195345)
                ·
                  refine ⟨13417135395357738146509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17889513860476984195345 13417135395357738146509)
                  ·
                    refine ⟨5031425773259151804941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13417135395357738146509 5031425773259151804941)
                    ·
                      rfl

theorem cell22_14698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_14698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14698 prefixEnd_14698 := by exact prefixLift 14698
  have htrace : WordTrace (prefixWord ++ tailWord_14698) baseStart_14698 baseEnd_14698 := by
    simpa [prefixWord, tailWord_14698, baseEnd_14698] using wordTrace_append hprefix tailTrace_14698
  have hstable : (prefixWord ++ tailWord_14698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14698).length < 2 ^ (prefixWord ++ tailWord_14698).sum := by decide
  have hdescent : baseEnd_14698 < baseStart_14698 := by decide
  rcases family_descends (prefixWord ++ tailWord_14698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14773 : List Nat := [1, 3, 3, 2, 3, 2, 2, 1, 5]
def baseStart_14773 : Nat := 118140960795 + 14773 * 2 ^ 59
def prefixEnd_14773 : Nat := 4983230072969 + 3 ^ 40 * 14773 * 2
def baseEnd_14773 : Nat := 1685699935327985393237

theorem tailTrace_14773 : CollatzResearch.WordTrace tailWord_14773 prefixEnd_14773 1685699935327985393237 := by
  unfold tailWord_14773
  simp only [CollatzResearch.WordTrace]
  refine ⟨538815575487418872640973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 359210383658279248427315 538815575487418872640973)
  ·
    refine ⟨202055840807782077240365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 538815575487418872640973 202055840807782077240365)
    ·
      refine ⟨75770940302918278965137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202055840807782077240365 75770940302918278965137)
      ·
        refine ⟨56828205227188709223853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75770940302918278965137 56828205227188709223853)
        ·
          refine ⟨21310576960195765958945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56828205227188709223853 21310576960195765958945)
          ·
            refine ⟨15982932720146824469209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21310576960195765958945 15982932720146824469209)
            ·
              refine ⟨11987199540110118351907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15982932720146824469209 11987199540110118351907)
              ·
                refine ⟨17980799310165177527861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11987199540110118351907 17980799310165177527861)
                ·
                  refine ⟨1685699935327985393237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17980799310165177527861 1685699935327985393237)
                  ·
                    rfl

theorem cell22_14773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_14773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14773 prefixEnd_14773 := by exact prefixLift 14773
  have htrace : WordTrace (prefixWord ++ tailWord_14773) baseStart_14773 baseEnd_14773 := by
    simpa [prefixWord, tailWord_14773, baseEnd_14773] using wordTrace_append hprefix tailTrace_14773
  have hstable : (prefixWord ++ tailWord_14773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14773).length < 2 ^ (prefixWord ++ tailWord_14773).sum := by decide
  have hdescent : baseEnd_14773 < baseStart_14773 := by decide
  rcases family_descends (prefixWord ++ tailWord_14773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14816 : List Nat := [2, 1, 1, 3, 1, 1, 6, 2, 2, 3]
def baseStart_14816 : Nat := 118140960795 + 14816 * 2 ^ 59
def prefixEnd_14816 : Nat := 4983230072969 + 3 ^ 40 * 14816 * 2
def baseEnd_14816 : Nat := 5071819584746177354579

theorem tailTrace_14816 : CollatzResearch.WordTrace tailWord_14816 prefixEnd_14816 5071819584746177354579 := by
  unfold tailWord_14816
  simp only [CollatzResearch.WordTrace]
  refine ⟨270191957165818608228151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 360255942887758144304201 270191957165818608228151)
  ·
    refine ⟨405287935748727912342227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270191957165818608228151 405287935748727912342227)
    ·
      refine ⟨607931903623091868513341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405287935748727912342227 607931903623091868513341)
      ·
        refine ⟨227974463858659450692503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607931903623091868513341 227974463858659450692503)
        ·
          refine ⟨341961695787989176038755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227974463858659450692503 341961695787989176038755)
          ·
            refine ⟨512942543681983764058133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341961695787989176038755 512942543681983764058133)
            ·
              refine ⟨24044181735092988940225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 512942543681983764058133 24044181735092988940225)
              ·
                refine ⟨18033136301319741705169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24044181735092988940225 18033136301319741705169)
                ·
                  refine ⟨13524852225989806278877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18033136301319741705169 13524852225989806278877)
                  ·
                    refine ⟨5071819584746177354579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13524852225989806278877 5071819584746177354579)
                    ·
                      rfl

theorem cell22_14816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 2, 3].length) (baseStart_14816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14816 prefixEnd_14816 := by exact prefixLift 14816
  have htrace : WordTrace (prefixWord ++ tailWord_14816) baseStart_14816 baseEnd_14816 := by
    simpa [prefixWord, tailWord_14816, baseEnd_14816] using wordTrace_append hprefix tailTrace_14816
  have hstable : (prefixWord ++ tailWord_14816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14816).length < 2 ^ (prefixWord ++ tailWord_14816).sum := by decide
  have hdescent : baseEnd_14816 < baseStart_14816 := by decide
  rcases family_descends (prefixWord ++ tailWord_14816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14854 : List Nat := [6, 2, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_14854 : Nat := 118140960795 + 14854 * 2 ^ 59
def prefixEnd_14854 : Nat := 4983230072969 + 3 ^ 40 * 14854 * 2
def baseEnd_14854 : Nat := 5084827761326744904463

theorem tailTrace_14854 : CollatzResearch.WordTrace tailWord_14854 prefixEnd_14854 5084827761326744904463 := by
  unfold tailWord_14854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16930309006061553323113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 361179925462646470893077 16930309006061553323113)
  ·
    refine ⟨12697731754546164992335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16930309006061553323113 12697731754546164992335)
    ·
      refine ⟨19046597631819247488503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12697731754546164992335 19046597631819247488503)
      ·
        refine ⟨28569896447728871232755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19046597631819247488503 28569896447728871232755)
        ·
          refine ⟨42854844671593306849133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28569896447728871232755 42854844671593306849133)
          ·
            refine ⟨16070566751847490068425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42854844671593306849133 16070566751847490068425)
            ·
              refine ⟨12052925063885617551319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16070566751847490068425 12052925063885617551319)
              ·
                refine ⟨18079387595828426326979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12052925063885617551319 18079387595828426326979)
                ·
                  refine ⟨27119081393742639490469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18079387595828426326979 27119081393742639490469)
                  ·
                    refine ⟨5084827761326744904463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27119081393742639490469 5084827761326744904463)
                    ·
                      rfl

theorem cell22_14854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_14854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14854 prefixEnd_14854 := by exact prefixLift 14854
  have htrace : WordTrace (prefixWord ++ tailWord_14854) baseStart_14854 baseEnd_14854 := by
    simpa [prefixWord, tailWord_14854, baseEnd_14854] using wordTrace_append hprefix tailTrace_14854
  have hstable : (prefixWord ++ tailWord_14854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14854).length < 2 ^ (prefixWord ++ tailWord_14854).sum := by decide
  have hdescent : baseEnd_14854 < baseStart_14854 := by decide
  rcases family_descends (prefixWord ++ tailWord_14854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14936 : List Nat := [2, 1, 2, 2, 1, 2, 2, 6, 4]
def baseStart_14936 : Nat := 118140960795 + 14936 * 2 ^ 59
def prefixEnd_14936 : Nat := 4983230072969 + 3 ^ 40 * 14936 * 2
def baseEnd_14936 : Nat := 1704299345701954784737

theorem tailTrace_14936 : CollatzResearch.WordTrace tailWord_14936 prefixEnd_14936 1704299345701954784737 := by
  unfold tailWord_14936
  simp only [CollatzResearch.WordTrace]
  refine ⟨272380336948448855412331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 363173782597931807216441 272380336948448855412331)
  ·
    refine ⟨408570505422673283118497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272380336948448855412331 408570505422673283118497)
    ·
      refine ⟨306427879067004962338873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408570505422673283118497 306427879067004962338873)
      ·
        refine ⟨229820909300253721754155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306427879067004962338873 229820909300253721754155)
        ·
          refine ⟨344731363950380582631233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229820909300253721754155 344731363950380582631233)
          ·
            refine ⟨258548522962785436973425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344731363950380582631233 258548522962785436973425)
            ·
              refine ⟨193911392222089077730069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258548522962785436973425 193911392222089077730069)
              ·
                refine ⟨9089596510410425518597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193911392222089077730069 9089596510410425518597)
                ·
                  refine ⟨1704299345701954784737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9089596510410425518597 1704299345701954784737)
                  ·
                    rfl

theorem cell22_14936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 4].length) (baseStart_14936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14936 prefixEnd_14936 := by exact prefixLift 14936
  have htrace : WordTrace (prefixWord ++ tailWord_14936) baseStart_14936 baseEnd_14936 := by
    simpa [prefixWord, tailWord_14936, baseEnd_14936] using wordTrace_append hprefix tailTrace_14936
  have hstable : (prefixWord ++ tailWord_14936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14936).length < 2 ^ (prefixWord ++ tailWord_14936).sum := by decide
  have hdescent : baseEnd_14936 < baseStart_14936 := by decide
  rcases family_descends (prefixWord ++ tailWord_14936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14942 : List Nat := [4, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_14942 : Nat := 118140960795 + 14942 * 2 ^ 59
def prefixEnd_14942 : Nat := 4983230072969 + 3 ^ 40 * 14942 * 2
def baseEnd_14942 : Nat := 1704983986574616234731

theorem tailTrace_14942 : CollatzResearch.WordTrace tailWord_14942 prefixEnd_14942 1704983986574616234731 := by
  unfold tailWord_14942
  simp only [CollatzResearch.WordTrace]
  refine ⟨68122438984395091942885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 363319674583440490362053 68122438984395091942885)
  ·
    refine ⟨12772957309574079739291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68122438984395091942885 12772957309574079739291)
    ·
      refine ⟨19159435964361119608937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12772957309574079739291 19159435964361119608937)
      ·
        refine ⟨14369576973270839706703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19159435964361119608937 14369576973270839706703)
        ·
          refine ⟨21554365459906259560055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14369576973270839706703 21554365459906259560055)
          ·
            refine ⟨32331548189859389340083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21554365459906259560055 32331548189859389340083)
            ·
              refine ⟨48497322284789084010125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32331548189859389340083 48497322284789084010125)
              ·
                refine ⟨18186495856795906503797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48497322284789084010125 18186495856795906503797)
                ·
                  refine ⟨1704983986574616234731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18186495856795906503797 1704983986574616234731)
                  ·
                    rfl

theorem cell22_14942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_14942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_14942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_14942 prefixEnd_14942 := by exact prefixLift 14942
  have htrace : WordTrace (prefixWord ++ tailWord_14942) baseStart_14942 baseEnd_14942 := by
    simpa [prefixWord, tailWord_14942, baseEnd_14942] using wordTrace_append hprefix tailTrace_14942
  have hstable : (prefixWord ++ tailWord_14942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14942).length < 2 ^ (prefixWord ++ tailWord_14942).sum := by decide
  have hdescent : baseEnd_14942 < baseStart_14942 := by decide
  rcases family_descends (prefixWord ++ tailWord_14942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15015 : List Nat := [1, 1, 6, 3, 1, 1, 3, 6]
def baseStart_15015 : Nat := 118140960795 + 15015 * 2 ^ 59
def prefixEnd_15015 : Nat := 4983230072969 + 3 ^ 40 * 15015 * 2
def baseEnd_15015 : Nat := 571104594619554625441

theorem tailTrace_15015 : CollatzResearch.WordTrace tailWord_15015 prefixEnd_15015 571104594619554625441 := by
  unfold tailWord_15015
  simp only [CollatzResearch.WordTrace]
  refine ⟨547642040610694202950499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 365094693740462801966999 547642040610694202950499)
  ·
    refine ⟨821463060916041304425749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 547642040610694202950499 821463060916041304425749)
    ·
      refine ⟨38506080980439436144957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 821463060916041304425749 38506080980439436144957)
      ·
        refine ⟨14439780367664788554359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38506080980439436144957 14439780367664788554359)
        ·
          refine ⟨21659670551497182831539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14439780367664788554359 21659670551497182831539)
          ·
            refine ⟨32489505827245774247309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21659670551497182831539 32489505827245774247309)
            ·
              refine ⟨12183564685217165342741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32489505827245774247309 12183564685217165342741)
              ·
                refine ⟨571104594619554625441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12183564685217165342741 571104594619554625441)
                ·
                  rfl

theorem cell22_15015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 6].length) (baseStart_15015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15015 prefixEnd_15015 := by exact prefixLift 15015
  have htrace : WordTrace (prefixWord ++ tailWord_15015) baseStart_15015 baseEnd_15015 := by
    simpa [prefixWord, tailWord_15015, baseEnd_15015] using wordTrace_append hprefix tailTrace_15015
  have hstable : (prefixWord ++ tailWord_15015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15015).length < 2 ^ (prefixWord ++ tailWord_15015).sum := by decide
  have hdescent : baseEnd_15015 < baseStart_15015 := by decide
  rcases family_descends (prefixWord ++ tailWord_15015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15024 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 3, 7]
def baseStart_15024 : Nat := 118140960795 + 15024 * 2 ^ 59
def prefixEnd_15024 : Nat := 4983230072969 + 3 ^ 40 * 15024 * 2
def baseEnd_15024 : Nat := 5143022235502968153941

theorem tailTrace_15024 : CollatzResearch.WordTrace tailWord_15024 prefixEnd_15024 5143022235502968153941 := by
  unfold tailWord_15024
  simp only [CollatzResearch.WordTrace]
  refine ⟨273985148789044370014063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 365313531718725826685417 273985148789044370014063)
  ·
    refine ⟨410977723183566555021095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273985148789044370014063 410977723183566555021095)
    ·
      refine ⟨616466584775349832531643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410977723183566555021095 616466584775349832531643)
      ·
        refine ⟨924699877163024748797465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616466584775349832531643 924699877163024748797465)
        ·
          refine ⟨693524907872268561598099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 924699877163024748797465 693524907872268561598099)
          ·
            refine ⟨1040287361808402842397149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693524907872268561598099 1040287361808402842397149)
            ·
              refine ⟨390107760678151065898931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1040287361808402842397149 390107760678151065898931)
              ·
                refine ⟨585161641017226598848397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390107760678151065898931 585161641017226598848397)
                ·
                  refine ⟨219435615381459974568149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585161641017226598848397 219435615381459974568149)
                  ·
                    refine ⟨5143022235502968153941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 219435615381459974568149 5143022235502968153941)
                    ·
                      rfl

theorem cell22_15024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_15024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15024 prefixEnd_15024 := by exact prefixLift 15024
  have htrace : WordTrace (prefixWord ++ tailWord_15024) baseStart_15024 baseEnd_15024 := by
    simpa [prefixWord, tailWord_15024, baseEnd_15024] using wordTrace_append hprefix tailTrace_15024
  have hstable : (prefixWord ++ tailWord_15024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15024).length < 2 ^ (prefixWord ++ tailWord_15024).sum := by decide
  have hdescent : baseEnd_15024 < baseStart_15024 := by decide
  rcases family_descends (prefixWord ++ tailWord_15024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15071 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 6]
def baseStart_15071 : Nat := 118140960795 + 15071 * 2 ^ 59
def prefixEnd_15071 : Nat := 4983230072969 + 3 ^ 40 * 15071 * 2
def baseEnd_15071 : Nat := 1719703765336837409599

theorem tailTrace_15071 : CollatzResearch.WordTrace tailWord_15071 prefixEnd_15071 1719703765336837409599 := by
  unfold tailWord_15071
  simp only [CollatzResearch.WordTrace]
  refine ⟨549684528407815766989067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 366456352271877177992711 549684528407815766989067)
  ·
    refine ⟨824526792611723650483601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 549684528407815766989067 824526792611723650483601)
    ·
      refine ⟨618395094458792737862701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 824526792611723650483601 618395094458792737862701)
      ·
        refine ⟨231898160422047276698513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 618395094458792737862701 231898160422047276698513)
        ·
          refine ⟨173923620316535457523885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231898160422047276698513 173923620316535457523885)
          ·
            refine ⟨65221357618700796571457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173923620316535457523885 65221357618700796571457)
            ·
              refine ⟨48916018214025597428593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65221357618700796571457 48916018214025597428593)
              ·
                refine ⟨36687013660519198071445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48916018214025597428593 36687013660519198071445)
                ·
                  refine ⟨1719703765336837409599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36687013660519198071445 1719703765336837409599)
                  ·
                    rfl

theorem cell22_15071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 6].length) (baseStart_15071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15071 prefixEnd_15071 := by exact prefixLift 15071
  have htrace : WordTrace (prefixWord ++ tailWord_15071) baseStart_15071 baseEnd_15071 := by
    simpa [prefixWord, tailWord_15071, baseEnd_15071] using wordTrace_append hprefix tailTrace_15071
  have hstable : (prefixWord ++ tailWord_15071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15071).length < 2 ^ (prefixWord ++ tailWord_15071).sum := by decide
  have hdescent : baseEnd_15071 < baseStart_15071 := by decide
  rcases family_descends (prefixWord ++ tailWord_15071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15073 : List Nat := [1, 2, 3, 1, 4, 1, 1, 4, 1, 4]
def baseStart_15073 : Nat := 118140960795 + 15073 * 2 ^ 59
def prefixEnd_15073 : Nat := 4983230072969 + 3 ^ 40 * 15073 * 2
def baseEnd_15073 : Nat := 5159795936883173678791

theorem tailTrace_15073 : CollatzResearch.WordTrace tailWord_15073 prefixEnd_15073 5159795936883173678791 := by
  unfold tailWord_15073
  simp only [CollatzResearch.WordTrace]
  refine ⟨549757474400570108561873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 366504982933713405707915 549757474400570108561873)
  ·
    refine ⟨412318105800427581421405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 549757474400570108561873 412318105800427581421405)
    ·
      refine ⟨154619289675160343033027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412318105800427581421405 154619289675160343033027)
      ·
        refine ⟨231928934512740514549541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154619289675160343033027 231928934512740514549541)
        ·
          refine ⟨43486675221138846478039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231928934512740514549541 43486675221138846478039)
          ·
            refine ⟨65230012831708269717059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43486675221138846478039 65230012831708269717059)
            ·
              refine ⟨97845019247562404575589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65230012831708269717059 97845019247562404575589)
              ·
                refine ⟨18345941108917950857923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97845019247562404575589 18345941108917950857923)
                ·
                  refine ⟨27518911663376926286885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18345941108917950857923 27518911663376926286885)
                  ·
                    refine ⟨5159795936883173678791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27518911663376926286885 5159795936883173678791)
                    ·
                      rfl

theorem cell22_15073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_15073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15073 prefixEnd_15073 := by exact prefixLift 15073
  have htrace : WordTrace (prefixWord ++ tailWord_15073) baseStart_15073 baseEnd_15073 := by
    simpa [prefixWord, tailWord_15073, baseEnd_15073] using wordTrace_append hprefix tailTrace_15073
  have hstable : (prefixWord ++ tailWord_15073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15073).length < 2 ^ (prefixWord ++ tailWord_15073).sum := by decide
  have hdescent : baseEnd_15073 < baseStart_15073 := by decide
  rcases family_descends (prefixWord ++ tailWord_15073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15103 : List Nat := [1, 1, 2, 2, 1, 3, 1, 6, 2, 3]
def baseStart_15103 : Nat := 118140960795 + 15103 * 2 ^ 59
def prefixEnd_15103 : Nat := 4983230072969 + 3 ^ 40 * 15103 * 2
def baseEnd_15103 : Nat := 5170065549973095428699

theorem tailTrace_15103 : CollatzResearch.WordTrace tailWord_15103 prefixEnd_15103 5170065549973095428699 := by
  unfold tailWord_15103
  simp only [CollatzResearch.WordTrace]
  refine ⟨550851664291885232153963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 367234442861256821435975 550851664291885232153963)
  ·
    refine ⟨826277496437827848230945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 550851664291885232153963 826277496437827848230945)
    ·
      refine ⟨619708122328370886173209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 826277496437827848230945 619708122328370886173209)
      ·
        refine ⟨464781091746278164629907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619708122328370886173209 464781091746278164629907)
        ·
          refine ⟨697171637619417246944861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464781091746278164629907 697171637619417246944861)
          ·
            refine ⟨261439364107281467604323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 697171637619417246944861 261439364107281467604323)
            ·
              refine ⟨392159046160922201406485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261439364107281467604323 392159046160922201406485)
              ·
                refine ⟨18382455288793228190929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 392159046160922201406485 18382455288793228190929)
                ·
                  refine ⟨13786841466594921143197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18382455288793228190929 13786841466594921143197)
                  ·
                    refine ⟨5170065549973095428699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13786841466594921143197 5170065549973095428699)
                    ·
                      rfl

theorem cell22_15103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 3].length) (baseStart_15103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15103 prefixEnd_15103 := by exact prefixLift 15103
  have htrace : WordTrace (prefixWord ++ tailWord_15103) baseStart_15103 baseEnd_15103 := by
    simpa [prefixWord, tailWord_15103, baseEnd_15103] using wordTrace_append hprefix tailTrace_15103
  have hstable : (prefixWord ++ tailWord_15103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15103).length < 2 ^ (prefixWord ++ tailWord_15103).sum := by decide
  have hdescent : baseEnd_15103 < baseStart_15103 := by decide
  rcases family_descends (prefixWord ++ tailWord_15103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15156 : List Nat := [2, 5, 1, 1, 4, 1, 2, 2, 4]
def baseStart_15156 : Nat := 118140960795 + 15156 * 2 ^ 59
def prefixEnd_15156 : Nat := 4983230072969 + 3 ^ 40 * 15156 * 2
def baseEnd_15156 : Nat := 1729402844366207951179

theorem tailTrace_15156 : CollatzResearch.WordTrace tailWord_15156 prefixEnd_15156 1729402844366207951179 := by
  unfold tailWord_15156
  simp only [CollatzResearch.WordTrace]
  refine ⟨276392366549937641916661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 368523155399916855888881 276392366549937641916661)
  ·
    refine ⟨25911784364056653929687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 276392366549937641916661 25911784364056653929687)
    ·
      refine ⟨38867676546084980894531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25911784364056653929687 38867676546084980894531)
      ·
        refine ⟨58301514819127471341797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38867676546084980894531 58301514819127471341797)
        ·
          refine ⟨10931534028586400876587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58301514819127471341797 10931534028586400876587)
          ·
            refine ⟨16397301042879601314881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10931534028586400876587 16397301042879601314881)
            ·
              refine ⟨12297975782159700986161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16397301042879601314881 12297975782159700986161)
              ·
                refine ⟨9223481836619775739621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12297975782159700986161 9223481836619775739621)
                ·
                  refine ⟨1729402844366207951179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9223481836619775739621 1729402844366207951179)
                  ·
                    rfl

theorem cell22_15156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_15156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15156 prefixEnd_15156 := by exact prefixLift 15156
  have htrace : WordTrace (prefixWord ++ tailWord_15156) baseStart_15156 baseEnd_15156 := by
    simpa [prefixWord, tailWord_15156, baseEnd_15156] using wordTrace_append hprefix tailTrace_15156
  have hstable : (prefixWord ++ tailWord_15156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15156).length < 2 ^ (prefixWord ++ tailWord_15156).sum := by decide
  have hdescent : baseEnd_15156 < baseStart_15156 := by decide
  rcases family_descends (prefixWord ++ tailWord_15156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15242 : List Nat := [3, 1, 2, 4, 1, 2, 2, 2, 1, 4]
def baseStart_15242 : Nat := 118140960795 + 15242 * 2 ^ 59
def prefixEnd_15242 : Nat := 4983230072969 + 3 ^ 40 * 15242 * 2
def baseEnd_15242 : Nat := 5217648090623066203273

theorem tailTrace_15242 : CollatzResearch.WordTrace tailWord_15242 prefixEnd_15242 5217648090623066203273 := by
  unfold tailWord_15242
  simp only [CollatzResearch.WordTrace]
  refine ⟨138980352697077992865995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 370614273858874647642653 138980352697077992865995)
  ·
    refine ⟨208470529045616989298993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138980352697077992865995 208470529045616989298993)
    ·
      refine ⟨156352896784212741974245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208470529045616989298993 156352896784212741974245)
      ·
        refine ⟨29316168147039889120171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156352896784212741974245 29316168147039889120171)
        ·
          refine ⟨43974252220559833680257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29316168147039889120171 43974252220559833680257)
          ·
            refine ⟨32980689165419875260193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43974252220559833680257 32980689165419875260193)
            ·
              refine ⟨24735516874064906445145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32980689165419875260193 24735516874064906445145)
              ·
                refine ⟨18551637655548679833859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24735516874064906445145 18551637655548679833859)
                ·
                  refine ⟨27827456483323019750789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18551637655548679833859 27827456483323019750789)
                  ·
                    refine ⟨5217648090623066203273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27827456483323019750789 5217648090623066203273)
                    ·
                      rfl

theorem cell22_15242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_15242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15242 prefixEnd_15242 := by exact prefixLift 15242
  have htrace : WordTrace (prefixWord ++ tailWord_15242) baseStart_15242 baseEnd_15242 := by
    simpa [prefixWord, tailWord_15242, baseEnd_15242] using wordTrace_append hprefix tailTrace_15242
  have hstable : (prefixWord ++ tailWord_15242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15242).length < 2 ^ (prefixWord ++ tailWord_15242).sum := by decide
  have hdescent : baseEnd_15242 < baseStart_15242 := by decide
  rcases family_descends (prefixWord ++ tailWord_15242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15253 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_15253 : Nat := 118140960795 + 15253 * 2 ^ 59
def prefixEnd_15253 : Nat := 4983230072969 + 3 ^ 40 * 15253 * 2
def baseEnd_15253 : Nat := 5221413615422704178239

theorem tailTrace_15253 : CollatzResearch.WordTrace tailWord_15253 prefixEnd_15253 5221413615422704178239 := by
  unfold tailWord_15253
  simp only [CollatzResearch.WordTrace]
  refine ⟨556322613748460850114413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 370881742498973900076275 556322613748460850114413)
  ·
    refine ⟨208620980155672818792905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 556322613748460850114413 208620980155672818792905)
    ·
      refine ⟨156465735116754614094679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208620980155672818792905 156465735116754614094679)
      ·
        refine ⟨234698602675131921142019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156465735116754614094679 234698602675131921142019)
        ·
          refine ⟨352047904012697881713029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234698602675131921142019 352047904012697881713029)
          ·
            refine ⟨66008982002380852821193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352047904012697881713029 66008982002380852821193)
            ·
              refine ⟨49506736501785639615895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66008982002380852821193 49506736501785639615895)
              ·
                refine ⟨74260104752678459423843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49506736501785639615895 74260104752678459423843)
                ·
                  refine ⟨111390157129017689135765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74260104752678459423843 111390157129017689135765)
                  ·
                    refine ⟨5221413615422704178239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111390157129017689135765 5221413615422704178239)
                    ·
                      rfl

theorem cell22_15253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_15253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15253 prefixEnd_15253 := by exact prefixLift 15253
  have htrace : WordTrace (prefixWord ++ tailWord_15253) baseStart_15253 baseEnd_15253 := by
    simpa [prefixWord, tailWord_15253, baseEnd_15253] using wordTrace_append hprefix tailTrace_15253
  have hstable : (prefixWord ++ tailWord_15253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15253).length < 2 ^ (prefixWord ++ tailWord_15253).sum := by decide
  have hdescent : baseEnd_15253 < baseStart_15253 := by decide
  rcases family_descends (prefixWord ++ tailWord_15253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15289 : List Nat := [1, 2, 1, 4, 2, 4, 2, 1, 2, 3]
def baseStart_15289 : Nat := 118140960795 + 15289 * 2 ^ 59
def prefixEnd_15289 : Nat := 4983230072969 + 3 ^ 40 * 15289 * 2
def baseEnd_15289 : Nat := 5233737151130610278129

theorem tailTrace_15289 : CollatzResearch.WordTrace tailWord_15289 prefixEnd_15289 5233737151130610278129 := by
  unfold tailWord_15289
  simp only [CollatzResearch.WordTrace]
  refine ⟨557635641618038998424921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 371757094412025998949947 557635641618038998424921)
  ·
    refine ⟨418226731213529248818691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 557635641618038998424921 418226731213529248818691)
    ·
      refine ⟨627340096820293873228037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418226731213529248818691 627340096820293873228037)
      ·
        refine ⟨117626268153805101230257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 627340096820293873228037 117626268153805101230257)
        ·
          refine ⟨88219701115353825922693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117626268153805101230257 88219701115353825922693)
          ·
            refine ⟨16541193959128842360505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88219701115353825922693 16541193959128842360505)
            ·
              refine ⟨12405895469346631770379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16541193959128842360505 12405895469346631770379)
              ·
                refine ⟨18608843204019947655569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12405895469346631770379 18608843204019947655569)
                ·
                  refine ⟨13956632403014960741677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18608843204019947655569 13956632403014960741677)
                  ·
                    refine ⟨5233737151130610278129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13956632403014960741677 5233737151130610278129)
                    ·
                      rfl

theorem cell22_15289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 2, 3].length) (baseStart_15289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15289 prefixEnd_15289 := by exact prefixLift 15289
  have htrace : WordTrace (prefixWord ++ tailWord_15289) baseStart_15289 baseEnd_15289 := by
    simpa [prefixWord, tailWord_15289, baseEnd_15289] using wordTrace_append hprefix tailTrace_15289
  have hstable : (prefixWord ++ tailWord_15289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15289).length < 2 ^ (prefixWord ++ tailWord_15289).sum := by decide
  have hdescent : baseEnd_15289 < baseStart_15289 := by decide
  rcases family_descends (prefixWord ++ tailWord_15289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15345 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 2, 5]
def baseStart_15345 : Nat := 118140960795 + 15345 * 2 ^ 59
def prefixEnd_15345 : Nat := 4983230072969 + 3 ^ 40 * 15345 * 2
def baseEnd_15345 : Nat := 5252907095565130877957

theorem tailTrace_15345 : CollatzResearch.WordTrace tailWord_15345 prefixEnd_15345 5252907095565130877957 := by
  unfold tailWord_15345
  simp only [CollatzResearch.WordTrace]
  refine ⟨559678129415160562463489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 373118752943440374975659 559678129415160562463489)
  ·
    refine ⟨419758597061370421847617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 559678129415160562463489 419758597061370421847617)
    ·
      refine ⟨314818947796027816385713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419758597061370421847617 314818947796027816385713)
      ·
        refine ⟨236114210847020862289285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314818947796027816385713 236114210847020862289285)
        ·
          refine ⟨44271414533816411679241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236114210847020862289285 44271414533816411679241)
          ·
            refine ⟨33203560900362308759431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44271414533816411679241 33203560900362308759431)
            ·
              refine ⟨49805341350543463139147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33203560900362308759431 49805341350543463139147)
              ·
                refine ⟨74708012025815194708721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49805341350543463139147 74708012025815194708721)
                ·
                  refine ⟨56031009019361396031541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74708012025815194708721 56031009019361396031541)
                  ·
                    refine ⟨5252907095565130877957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56031009019361396031541 5252907095565130877957)
                    ·
                      rfl

theorem cell22_15345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_15345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15345 prefixEnd_15345 := by exact prefixLift 15345
  have htrace : WordTrace (prefixWord ++ tailWord_15345) baseStart_15345 baseEnd_15345 := by
    simpa [prefixWord, tailWord_15345, baseEnd_15345] using wordTrace_append hprefix tailTrace_15345
  have hstable : (prefixWord ++ tailWord_15345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15345).length < 2 ^ (prefixWord ++ tailWord_15345).sum := by decide
  have hdescent : baseEnd_15345 < baseStart_15345 := by decide
  rcases family_descends (prefixWord ++ tailWord_15345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15403 : List Nat := [1, 1, 1, 1, 2, 1, 6, 9]
def baseStart_15403 : Nat := 118140960795 + 15403 * 2 ^ 59
def prefixEnd_15403 : Nat := 4983230072969 + 3 ^ 40 * 15403 * 2
def baseEnd_15403 : Nat := 585862408985812547531

theorem tailTrace_15403 : CollatzResearch.WordTrace tailWord_15403 prefixEnd_15403 585862408985812547531 := by
  unfold tailWord_15403
  simp only [CollatzResearch.WordTrace]
  refine ⟨561793563205036468074863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 374529042136690978716575 561793563205036468074863)
  ·
    refine ⟨842690344807554702112295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 561793563205036468074863 842690344807554702112295)
    ·
      refine ⟨1264035517211332053168443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 842690344807554702112295 1264035517211332053168443)
      ·
        refine ⟨1896053275816998079752665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264035517211332053168443 1896053275816998079752665)
        ·
          refine ⟨1422039956862748559814499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1896053275816998079752665 1422039956862748559814499)
          ·
            refine ⟨2133059935294122839721749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422039956862748559814499 2133059935294122839721749)
            ·
              refine ⟨99987184466912008111957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2133059935294122839721749 99987184466912008111957)
              ·
                refine ⟨585862408985812547531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 99987184466912008111957 585862408985812547531)
                ·
                  rfl

theorem cell22_15403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 9].length) (baseStart_15403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15403 prefixEnd_15403 := by exact prefixLift 15403
  have htrace : WordTrace (prefixWord ++ tailWord_15403) baseStart_15403 baseEnd_15403 := by
    simpa [prefixWord, tailWord_15403, baseEnd_15403] using wordTrace_append hprefix tailTrace_15403
  have hstable : (prefixWord ++ tailWord_15403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15403).length < 2 ^ (prefixWord ++ tailWord_15403).sum := by decide
  have hdescent : baseEnd_15403 < baseStart_15403 := by decide
  rcases family_descends (prefixWord ++ tailWord_15403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15420 : List Nat := [2, 2, 2, 2, 2, 3, 1, 8]
def baseStart_15420 : Nat := 118140960795 + 15420 * 2 ^ 59
def prefixEnd_15420 : Nat := 4983230072969 + 3 ^ 40 * 15420 * 2
def baseEnd_15420 : Nat := 586509014254437250303

theorem tailTrace_15420 : CollatzResearch.WordTrace tailWord_15420 prefixEnd_15420 586509014254437250303 := by
  unfold tailWord_15420
  simp only [CollatzResearch.WordTrace]
  refine ⟨281206802071724185721857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 374942402762298914295809 281206802071724185721857)
  ·
    refine ⟨210905101553793139291393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 281206802071724185721857 210905101553793139291393)
    ·
      refine ⟨158178826165344854468545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210905101553793139291393 158178826165344854468545)
      ·
        refine ⟨118634119624008640851409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158178826165344854468545 118634119624008640851409)
        ·
          refine ⟨88975589718006480638557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118634119624008640851409 88975589718006480638557)
          ·
            refine ⟨33365846144252430239459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88975589718006480638557 33365846144252430239459)
            ·
              refine ⟨50048769216378645359189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33365846144252430239459 50048769216378645359189)
              ·
                refine ⟨586509014254437250303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 50048769216378645359189 586509014254437250303)
                ·
                  rfl

theorem cell22_15420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 8].length) (baseStart_15420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15420 prefixEnd_15420 := by exact prefixLift 15420
  have htrace : WordTrace (prefixWord ++ tailWord_15420) baseStart_15420 baseEnd_15420 := by
    simpa [prefixWord, tailWord_15420, baseEnd_15420] using wordTrace_append hprefix tailTrace_15420
  have hstable : (prefixWord ++ tailWord_15420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15420).length < 2 ^ (prefixWord ++ tailWord_15420).sum := by decide
  have hdescent : baseEnd_15420 < baseStart_15420 := by decide
  rcases family_descends (prefixWord ++ tailWord_15420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15422 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_15422 : Nat := 118140960795 + 15422 * 2 ^ 59
def prefixEnd_15422 : Nat := 4983230072969 + 3 ^ 40 * 15422 * 2
def baseEnd_15422 : Nat := 5279265769162596702721

theorem tailTrace_15422 : CollatzResearch.WordTrace tailWord_15422 prefixEnd_15422 5279265769162596702721 := by
  unfold tailWord_15422
  simp only [CollatzResearch.WordTrace]
  refine ⟨70310818767025339127065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 374991033424135142011013 70310818767025339127065)
  ·
    refine ⟨52733114075269004345299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70310818767025339127065 52733114075269004345299)
    ·
      refine ⟨79099671112903506517949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52733114075269004345299 79099671112903506517949)
      ·
        refine ⟨29662376667338814944231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79099671112903506517949 29662376667338814944231)
        ·
          refine ⟨44493565001008222416347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29662376667338814944231 44493565001008222416347)
          ·
            refine ⟨66740347501512333624521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44493565001008222416347 66740347501512333624521)
            ·
              refine ⟨50055260626134250218391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66740347501512333624521 50055260626134250218391)
              ·
                refine ⟨75082890939201375327587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50055260626134250218391 75082890939201375327587)
                ·
                  refine ⟨112624336408802062991381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75082890939201375327587 112624336408802062991381)
                  ·
                    refine ⟨5279265769162596702721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112624336408802062991381 5279265769162596702721)
                    ·
                      rfl

theorem cell22_15422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_15422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15422 prefixEnd_15422 := by exact prefixLift 15422
  have htrace : WordTrace (prefixWord ++ tailWord_15422) baseStart_15422 baseEnd_15422 := by
    simpa [prefixWord, tailWord_15422, baseEnd_15422] using wordTrace_append hprefix tailTrace_15422
  have hstable : (prefixWord ++ tailWord_15422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15422).length < 2 ^ (prefixWord ++ tailWord_15422).sum := by decide
  have hdescent : baseEnd_15422 < baseStart_15422 := by decide
  rcases family_descends (prefixWord ++ tailWord_15422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15437 : List Nat := [1, 6, 1, 1, 1, 4, 8]
def baseStart_15437 : Nat := 118140960795 + 15437 * 2 ^ 59
def prefixEnd_15437 : Nat := 4983230072969 + 3 ^ 40 * 15437 * 2
def baseEnd_15437 : Nat := 195718539841020651025

theorem tailTrace_15437 : CollatzResearch.WordTrace tailWord_15437 prefixEnd_15437 195718539841020651025 := by
  unfold tailWord_15437
  simp only [CollatzResearch.WordTrace]
  refine ⟨563033645081860274812565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 375355763387906849875043 563033645081860274812565)
  ·
    refine ⟨26392202113212200381839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 563033645081860274812565 26392202113212200381839)
    ·
      refine ⟨39588303169818300572759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26392202113212200381839 39588303169818300572759)
      ·
        refine ⟨59382454754727450859139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39588303169818300572759 59382454754727450859139)
        ·
          refine ⟨89073682132091176288709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59382454754727450859139 89073682132091176288709)
          ·
            refine ⟨16701315399767095554133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89073682132091176288709 16701315399767095554133)
            ·
              refine ⟨195718539841020651025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 16701315399767095554133 195718539841020651025)
              ·
                rfl

theorem cell22_15437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 8].length) (baseStart_15437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15437 prefixEnd_15437 := by exact prefixLift 15437
  have htrace : WordTrace (prefixWord ++ tailWord_15437) baseStart_15437 baseEnd_15437 := by
    simpa [prefixWord, tailWord_15437, baseEnd_15437] using wordTrace_append hprefix tailTrace_15437
  have hstable : (prefixWord ++ tailWord_15437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15437).length < 2 ^ (prefixWord ++ tailWord_15437).sum := by decide
  have hdescent : baseEnd_15437 < baseStart_15437 := by decide
  rcases family_descends (prefixWord ++ tailWord_15437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15454 : List Nat := [4, 4, 1, 1, 1, 1, 1, 9]
def baseStart_15454 : Nat := 118140960795 + 15454 * 2 ^ 59
def prefixEnd_15454 : Nat := 4983230072969 + 3 ^ 40 * 15454 * 2
def baseEnd_15454 : Nat := 587802224791686655847

theorem tailTrace_15454 : CollatzResearch.WordTrace tailWord_15454 prefixEnd_15454 587802224791686655847 := by
  unfold tailWord_15454
  simp only [CollatzResearch.WordTrace]
  refine ⟨70456710752534022272677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 375769124013514785454277 70456710752534022272677)
  ·
    refine ⟨13210633266100129176127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70456710752534022272677 13210633266100129176127)
    ·
      refine ⟨19815949899150193764191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13210633266100129176127 19815949899150193764191)
      ·
        refine ⟨29723924848725290646287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19815949899150193764191 29723924848725290646287)
        ·
          refine ⟨44585887273087935969431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29723924848725290646287 44585887273087935969431)
          ·
            refine ⟨66878830909631903954147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44585887273087935969431 66878830909631903954147)
            ·
              refine ⟨100318246364447855931221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66878830909631903954147 100318246364447855931221)
              ·
                refine ⟨587802224791686655847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 100318246364447855931221 587802224791686655847)
                ·
                  rfl

theorem cell22_15454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_15454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15454 prefixEnd_15454 := by exact prefixLift 15454
  have htrace : WordTrace (prefixWord ++ tailWord_15454) baseStart_15454 baseEnd_15454 := by
    simpa [prefixWord, tailWord_15454, baseEnd_15454] using wordTrace_append hprefix tailTrace_15454
  have hstable : (prefixWord ++ tailWord_15454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15454).length < 2 ^ (prefixWord ++ tailWord_15454).sum := by decide
  have hdescent : baseEnd_15454 < baseStart_15454 := by decide
  rcases family_descends (prefixWord ++ tailWord_15454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15458 : List Nat := [3, 3, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_15458 : Nat := 118140960795 + 15458 * 2 ^ 59
def prefixEnd_15458 : Nat := 4983230072969 + 3 ^ 40 * 15458 * 2
def baseEnd_15458 : Nat := 5291589304870502802611

theorem tailTrace_15458 : CollatzResearch.WordTrace tailWord_15458 prefixEnd_15458 5291589304870502802611 := by
  unfold tailWord_15458
  simp only [CollatzResearch.WordTrace]
  refine ⟨140949894501445215331757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 375866385337187240884685 140949894501445215331757)
  ·
    refine ⟨52856210438041955749409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140949894501445215331757 52856210438041955749409)
    ·
      refine ⟨39642157828531466812057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52856210438041955749409 39642157828531466812057)
      ·
        refine ⟨29731618371398600109043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39642157828531466812057 29731618371398600109043)
        ·
          refine ⟨44597427557097900163565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29731618371398600109043 44597427557097900163565)
          ·
            refine ⟨16724035333911712561337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44597427557097900163565 16724035333911712561337)
            ·
              refine ⟨12543026500433784421003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16724035333911712561337 12543026500433784421003)
              ·
                refine ⟨18814539750650676631505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12543026500433784421003 18814539750650676631505)
                ·
                  refine ⟨14110904812988007473629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18814539750650676631505 14110904812988007473629)
                  ·
                    refine ⟨5291589304870502802611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14110904812988007473629 5291589304870502802611)
                    ·
                      rfl

theorem cell22_15458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_15458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15458 prefixEnd_15458 := by exact prefixLift 15458
  have htrace : WordTrace (prefixWord ++ tailWord_15458) baseStart_15458 baseEnd_15458 := by
    simpa [prefixWord, tailWord_15458, baseEnd_15458] using wordTrace_append hprefix tailTrace_15458
  have hstable : (prefixWord ++ tailWord_15458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15458).length < 2 ^ (prefixWord ++ tailWord_15458).sum := by decide
  have hdescent : baseEnd_15458 < baseStart_15458 := by decide
  rcases family_descends (prefixWord ++ tailWord_15458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15512 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 3, 4]
def baseStart_15512 : Nat := 118140960795 + 15512 * 2 ^ 59
def prefixEnd_15512 : Nat := 4983230072969 + 3 ^ 40 * 15512 * 2
def baseEnd_15512 : Nat := 5310074608432361952445

theorem tailTrace_15512 : CollatzResearch.WordTrace tailWord_15512 prefixEnd_15512 5310074608432361952445 := by
  unfold tailWord_15512
  simp only [CollatzResearch.WordTrace]
  refine ⟨282884559905074041896395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 377179413206765389195193 282884559905074041896395)
  ·
    refine ⟨424326839857611062844593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282884559905074041896395 424326839857611062844593)
    ·
      refine ⟨318245129893208297133445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424326839857611062844593 318245129893208297133445)
      ·
        refine ⟨59670961854976555712521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318245129893208297133445 59670961854976555712521)
        ·
          refine ⟨44753221391232416784391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59670961854976555712521 44753221391232416784391)
          ·
            refine ⟨67129832086848625176587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44753221391232416784391 67129832086848625176587)
            ·
              refine ⟨100694748130272937764881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67129832086848625176587 100694748130272937764881)
              ·
                refine ⟨75521061097704703323661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100694748130272937764881 75521061097704703323661)
                ·
                  refine ⟨28320397911639263746373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75521061097704703323661 28320397911639263746373)
                  ·
                    refine ⟨5310074608432361952445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28320397911639263746373 5310074608432361952445)
                    ·
                      rfl

theorem cell22_15512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_15512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15512 prefixEnd_15512 := by exact prefixLift 15512
  have htrace : WordTrace (prefixWord ++ tailWord_15512) baseStart_15512 baseEnd_15512 := by
    simpa [prefixWord, tailWord_15512, baseEnd_15512] using wordTrace_append hprefix tailTrace_15512
  have hstable : (prefixWord ++ tailWord_15512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15512).length < 2 ^ (prefixWord ++ tailWord_15512).sum := by decide
  have hdescent : baseEnd_15512 < baseStart_15512 := by decide
  rcases family_descends (prefixWord ++ tailWord_15512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15527 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 8]
def baseStart_15527 : Nat := 118140960795 + 15527 * 2 ^ 59
def prefixEnd_15527 : Nat := 4983230072969 + 3 ^ 40 * 15527 * 2
def baseEnd_15527 : Nat := 1771736471659107609133

theorem tailTrace_15527 : CollatzResearch.WordTrace tailWord_15527 prefixEnd_15527 1771736471659107609133 := by
  unfold tailWord_15527
  simp only [CollatzResearch.WordTrace]
  refine ⟨566316214755805645588835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 377544143170537097059223 566316214755805645588835)
  ·
    refine ⟨849474322133708468383253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 566316214755805645588835 849474322133708468383253)
    ·
      refine ⟨39819108850017584455465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 849474322133708468383253 39819108850017584455465)
      ·
        refine ⟨29864331637513188341599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39819108850017584455465 29864331637513188341599)
        ·
          refine ⟨44796497456269782512399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29864331637513188341599 44796497456269782512399)
          ·
            refine ⟨67194746184404673768599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44796497456269782512399 67194746184404673768599)
            ·
              refine ⟨100792119276607010652899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67194746184404673768599 100792119276607010652899)
              ·
                refine ⟨151188178914910515979349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100792119276607010652899 151188178914910515979349)
                ·
                  refine ⟨1771736471659107609133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 151188178914910515979349 1771736471659107609133)
                  ·
                    rfl

theorem cell22_15527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 8].length) (baseStart_15527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15527 prefixEnd_15527 := by exact prefixLift 15527
  have htrace : WordTrace (prefixWord ++ tailWord_15527) baseStart_15527 baseEnd_15527 := by
    simpa [prefixWord, tailWord_15527, baseEnd_15527] using wordTrace_append hprefix tailTrace_15527
  have hstable : (prefixWord ++ tailWord_15527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15527).length < 2 ^ (prefixWord ++ tailWord_15527).sum := by decide
  have hdescent : baseEnd_15527 < baseStart_15527 := by decide
  rcases family_descends (prefixWord ++ tailWord_15527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15576 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 1, 5]
def baseStart_15576 : Nat := 118140960795 + 15576 * 2 ^ 59
def prefixEnd_15576 : Nat := 4983230072969 + 3 ^ 40 * 15576 * 2
def baseEnd_15576 : Nat := 5331983116357528352249

theorem tailTrace_15576 : CollatzResearch.WordTrace tailWord_15576 prefixEnd_15576 5331983116357528352249 := by
  unfold tailWord_15576
  simp only [CollatzResearch.WordTrace]
  refine ⟨284051695789143507061291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 378735594385524676081721 284051695789143507061291)
  ·
    refine ⟨426077543683715260591937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284051695789143507061291 426077543683715260591937)
    ·
      refine ⟨319558157762786445443953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426077543683715260591937 319558157762786445443953)
      ·
        refine ⟨239668618322089834082965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319558157762786445443953 239668618322089834082965)
        ·
          refine ⟨11234466483847960972639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 239668618322089834082965 11234466483847960972639)
          ·
            refine ⟨16851699725771941458959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11234466483847960972639 16851699725771941458959)
            ·
              refine ⟨25277549588657912188439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16851699725771941458959 25277549588657912188439)
              ·
                refine ⟨37916324382986868282659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25277549588657912188439 37916324382986868282659)
                ·
                  refine ⟨56874486574480302423989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37916324382986868282659 56874486574480302423989)
                  ·
                    refine ⟨5331983116357528352249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56874486574480302423989 5331983116357528352249)
                    ·
                      rfl

theorem cell22_15576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_15576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15576 prefixEnd_15576 := by exact prefixLift 15576
  have htrace : WordTrace (prefixWord ++ tailWord_15576) baseStart_15576 baseEnd_15576 := by
    simpa [prefixWord, tailWord_15576, baseEnd_15576] using wordTrace_append hprefix tailTrace_15576
  have hstable : (prefixWord ++ tailWord_15576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15576).length < 2 ^ (prefixWord ++ tailWord_15576).sum := by decide
  have hdescent : baseEnd_15576 < baseStart_15576 := by decide
  rcases family_descends (prefixWord ++ tailWord_15576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15617 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 7]
def baseStart_15617 : Nat := 118140960795 + 15617 * 2 ^ 59
def prefixEnd_15617 : Nat := 4983230072969 + 3 ^ 40 * 15617 * 2
def baseEnd_15617 : Nat := 1782006084749029359041

theorem tailTrace_15617 : CollatzResearch.WordTrace tailWord_15617 prefixEnd_15617 1782006084749029359041 := by
  unfold tailWord_15617
  simp only [CollatzResearch.WordTrace]
  refine ⟨569598784429751016365105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 379732522953167344243403 569598784429751016365105)
  ·
    refine ⟨427199088322313262273829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 569598784429751016365105 427199088322313262273829)
    ·
      refine ⟨80099829060433736676343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427199088322313262273829 80099829060433736676343)
      ·
        refine ⟨120149743590650605014515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80099829060433736676343 120149743590650605014515)
        ·
          refine ⟨180224615385975907521773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120149743590650605014515 180224615385975907521773)
          ·
            refine ⟨67584230769740965320665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180224615385975907521773 67584230769740965320665)
            ·
              refine ⟨50688173077305723990499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67584230769740965320665 50688173077305723990499)
              ·
                refine ⟨76032259615958585985749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50688173077305723990499 76032259615958585985749)
                ·
                  refine ⟨1782006084749029359041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 76032259615958585985749 1782006084749029359041)
                  ·
                    rfl

theorem cell22_15617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 7].length) (baseStart_15617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15617 prefixEnd_15617 := by exact prefixLift 15617
  have htrace : WordTrace (prefixWord ++ tailWord_15617) baseStart_15617 baseEnd_15617 := by
    simpa [prefixWord, tailWord_15617, baseEnd_15617] using wordTrace_append hprefix tailTrace_15617
  have hstable : (prefixWord ++ tailWord_15617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15617).length < 2 ^ (prefixWord ++ tailWord_15617).sum := by decide
  have hdescent : baseEnd_15617 < baseStart_15617 := by decide
  rcases family_descends (prefixWord ++ tailWord_15617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15694 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_15694 : Nat := 118140960795 + 15694 * 2 ^ 59
def prefixEnd_15694 : Nat := 4983230072969 + 3 ^ 40 * 15694 * 2
def baseEnd_15694 : Nat := 5372376927844553901887

theorem tailTrace_15694 : CollatzResearch.WordTrace tailWord_15694 prefixEnd_15694 5372376927844553901887 := by
  unfold tailWord_15694
  simp only [CollatzResearch.WordTrace]
  refine ⟨71550900643849145864767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 381604803433862111278757 71550900643849145864767)
  ·
    refine ⟨107326350965773718797151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71550900643849145864767 107326350965773718797151)
    ·
      refine ⟨160989526448660578195727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107326350965773718797151 160989526448660578195727)
      ·
        refine ⟨241484289672990867293591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160989526448660578195727 241484289672990867293591)
        ·
          refine ⟨362226434509486300940387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241484289672990867293591 362226434509486300940387)
          ·
            refine ⟨543339651764229451410581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362226434509486300940387 543339651764229451410581)
            ·
              refine ⟨25469046176448255534871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 543339651764229451410581 25469046176448255534871)
              ·
                refine ⟨38203569264672383302307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25469046176448255534871 38203569264672383302307)
                ·
                  refine ⟨57305353897008574953461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38203569264672383302307 57305353897008574953461)
                  ·
                    refine ⟨5372376927844553901887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57305353897008574953461 5372376927844553901887)
                    ·
                      rfl

theorem cell22_15694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_15694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15694 prefixEnd_15694 := by exact prefixLift 15694
  have htrace : WordTrace (prefixWord ++ tailWord_15694) baseStart_15694 baseEnd_15694 := by
    simpa [prefixWord, tailWord_15694, baseEnd_15694] using wordTrace_append hprefix tailTrace_15694
  have hstable : (prefixWord ++ tailWord_15694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15694).length < 2 ^ (prefixWord ++ tailWord_15694).sum := by decide
  have hdescent : baseEnd_15694 < baseStart_15694 := by decide
  rcases family_descends (prefixWord ++ tailWord_15694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15737 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 1, 8]
def baseStart_15737 : Nat := 118140960795 + 15737 * 2 ^ 59
def prefixEnd_15737 : Nat := 4983230072969 + 3 ^ 40 * 15737 * 2
def baseEnd_15737 : Nat := 5387096706606775076755

theorem tailTrace_15737 : CollatzResearch.WordTrace tailWord_15737 prefixEnd_15737 5387096706606775076755 := by
  unfold tailWord_15737
  simp only [CollatzResearch.WordTrace]
  refine ⟨573975543995011510733465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 382650362663341007155643 573975543995011510733465)
  ·
    refine ⟨430481657996258633050099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 573975543995011510733465 430481657996258633050099)
    ·
      refine ⟨645722486994387949575149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430481657996258633050099 645722486994387949575149)
      ·
        refine ⟨242145932622895481090681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 645722486994387949575149 242145932622895481090681)
        ·
          refine ⟨181609449467171610818011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242145932622895481090681 181609449467171610818011)
          ·
            refine ⟨272414174200757416227017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181609449467171610818011 272414174200757416227017)
            ·
              refine ⟨204310630650568062170263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272414174200757416227017 204310630650568062170263)
              ·
                refine ⟨306465945975852093255395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204310630650568062170263 306465945975852093255395)
                ·
                  refine ⟨459698918963778139883093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306465945975852093255395 459698918963778139883093)
                  ·
                    refine ⟨5387096706606775076755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 459698918963778139883093 5387096706606775076755)
                    ·
                      rfl

theorem cell22_15737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_15737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15737 prefixEnd_15737 := by exact prefixLift 15737
  have htrace : WordTrace (prefixWord ++ tailWord_15737) baseStart_15737 baseEnd_15737 := by
    simpa [prefixWord, tailWord_15737, baseEnd_15737] using wordTrace_append hprefix tailTrace_15737
  have hstable : (prefixWord ++ tailWord_15737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15737).length < 2 ^ (prefixWord ++ tailWord_15737).sum := by decide
  have hdescent : baseEnd_15737 < baseStart_15737 := by decide
  rcases family_descends (prefixWord ++ tailWord_15737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15745 : List Nat := [1, 2, 4, 3, 2, 1, 3, 1, 2, 3]
def baseStart_15745 : Nat := 118140960795 + 15745 * 2 ^ 59
def prefixEnd_15745 : Nat := 4983230072969 + 3 ^ 40 * 15745 * 2
def baseEnd_15745 : Nat := 5389835270097420876731

theorem tailTrace_15745 : CollatzResearch.WordTrace tailWord_15745 prefixEnd_15745 5389835270097420876731 := by
  unfold tailWord_15745
  simp only [CollatzResearch.WordTrace]
  refine ⟨574267327966028877024689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 382844885310685918016459 574267327966028877024689)
  ·
    refine ⟨430700495974521657768517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 574267327966028877024689 430700495974521657768517)
    ·
      refine ⟨80756342995222810831597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 430700495974521657768517 80756342995222810831597)
      ·
        refine ⟨30283628623208554061849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80756342995222810831597 30283628623208554061849)
        ·
          refine ⟨22712721467406415546387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30283628623208554061849 22712721467406415546387)
          ·
            refine ⟨34069082201109623319581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22712721467406415546387 34069082201109623319581)
            ·
              refine ⟨12775905825416108744843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34069082201109623319581 12775905825416108744843)
              ·
                refine ⟨19163858738124163117265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12775905825416108744843 19163858738124163117265)
                ·
                  refine ⟨14372894053593122337949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19163858738124163117265 14372894053593122337949)
                  ·
                    refine ⟨5389835270097420876731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14372894053593122337949 5389835270097420876731)
                    ·
                      rfl

theorem cell22_15745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_15745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15745 prefixEnd_15745 := by exact prefixLift 15745
  have htrace : WordTrace (prefixWord ++ tailWord_15745) baseStart_15745 baseEnd_15745 := by
    simpa [prefixWord, tailWord_15745, baseEnd_15745] using wordTrace_append hprefix tailTrace_15745
  have hstable : (prefixWord ++ tailWord_15745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15745).length < 2 ^ (prefixWord ++ tailWord_15745).sum := by decide
  have hdescent : baseEnd_15745 < baseStart_15745 := by decide
  rcases family_descends (prefixWord ++ tailWord_15745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15758 : List Nat := [4, 1, 1, 4, 2, 2, 2, 6]
def baseStart_15758 : Nat := 118140960795 + 15758 * 2 ^ 59
def prefixEnd_15758 : Nat := 4983230072969 + 3 ^ 40 * 15758 * 2
def baseEnd_15758 : Nat := 599365048418857811299

theorem tailTrace_15758 : CollatzResearch.WordTrace tailWord_15758 prefixEnd_15758 599365048418857811299 := by
  unfold tailWord_15758
  simp only [CollatzResearch.WordTrace]
  refine ⟨71842684614866512155991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 383160984612621398165285 71842684614866512155991)
  ·
    refine ⟨107764026922299768233987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71842684614866512155991 107764026922299768233987)
    ·
      refine ⟨161646040383449652350981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107764026922299768233987 161646040383449652350981)
      ·
        refine ⟨30308632571896809815809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161646040383449652350981 30308632571896809815809)
        ·
          refine ⟨22731474428922607361857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30308632571896809815809 22731474428922607361857)
          ·
            refine ⟨17048605821691955521393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22731474428922607361857 17048605821691955521393)
            ·
              refine ⟨12786454366268966641045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17048605821691955521393 12786454366268966641045)
              ·
                refine ⟨599365048418857811299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12786454366268966641045 599365048418857811299)
                ·
                  rfl

theorem cell22_15758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_15758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15758 prefixEnd_15758 := by exact prefixLift 15758
  have htrace : WordTrace (prefixWord ++ tailWord_15758) baseStart_15758 baseEnd_15758 := by
    simpa [prefixWord, tailWord_15758, baseEnd_15758] using wordTrace_append hprefix tailTrace_15758
  have hstable : (prefixWord ++ tailWord_15758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15758).length < 2 ^ (prefixWord ++ tailWord_15758).sum := by decide
  have hdescent : baseEnd_15758 < baseStart_15758 := by decide
  rcases family_descends (prefixWord ++ tailWord_15758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15799 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 3, 4]
def baseStart_15799 : Nat := 118140960795 + 15799 * 2 ^ 59
def prefixEnd_15799 : Nat := 4983230072969 + 3 ^ 40 * 15799 * 2
def baseEnd_15799 : Nat := 5408320573659280026565

theorem tailTrace_15799 : CollatzResearch.WordTrace tailWord_15799 prefixEnd_15799 5408320573659280026565 := by
  unfold tailWord_15799
  simp only [CollatzResearch.WordTrace]
  refine ⟨576236869770396099490451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 384157913180264066326967 576236869770396099490451)
  ·
    refine ⟨864355304655594149235677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 576236869770396099490451 864355304655594149235677)
    ·
      refine ⟨324133239245847805963379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 864355304655594149235677 324133239245847805963379)
      ·
        refine ⟨486199858868771708945069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324133239245847805963379 486199858868771708945069)
        ·
          refine ⟨182324947075789390854401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 486199858868771708945069 182324947075789390854401)
          ·
            refine ⟨136743710306842043140801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182324947075789390854401 136743710306842043140801)
            ·
              refine ⟨102557782730131532355601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136743710306842043140801 102557782730131532355601)
              ·
                refine ⟨76918337047598649266701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102557782730131532355601 76918337047598649266701)
                ·
                  refine ⟨28844376392849493475013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76918337047598649266701 28844376392849493475013)
                  ·
                    refine ⟨5408320573659280026565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28844376392849493475013 5408320573659280026565)
                    ·
                      rfl

theorem cell22_15799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_15799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15799 prefixEnd_15799 := by exact prefixLift 15799
  have htrace : WordTrace (prefixWord ++ tailWord_15799) baseStart_15799 baseEnd_15799 := by
    simpa [prefixWord, tailWord_15799, baseEnd_15799] using wordTrace_append hprefix tailTrace_15799
  have hstable : (prefixWord ++ tailWord_15799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15799).length < 2 ^ (prefixWord ++ tailWord_15799).sum := by decide
  have hdescent : baseEnd_15799 < baseStart_15799 := by decide
  rcases family_descends (prefixWord ++ tailWord_15799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15833 : List Nat := [1, 2, 1, 2, 4, 3, 3, 1, 1, 4]
def baseStart_15833 : Nat := 118140960795 + 15833 * 2 ^ 59
def prefixEnd_15833 : Nat := 4983230072969 + 3 ^ 40 * 15833 * 2
def baseEnd_15833 : Nat := 5419959468494524676461

theorem tailTrace_15833 : CollatzResearch.WordTrace tailWord_15833 prefixEnd_15833 5419959468494524676461 := by
  unfold tailWord_15833
  simp only [CollatzResearch.WordTrace]
  refine ⟨577476951647219906228153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 384984634431479937485435 577476951647219906228153)
  ·
    refine ⟨433107713735414929671115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 577476951647219906228153 433107713735414929671115)
    ·
      refine ⟨649661570603122394506673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433107713735414929671115 649661570603122394506673)
      ·
        refine ⟨487246177952341795880005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649661570603122394506673 487246177952341795880005)
        ·
          refine ⟨91358658366064086727501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487246177952341795880005 91358658366064086727501)
          ·
            refine ⟨34259496887274032522813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91358658366064086727501 34259496887274032522813)
            ·
              refine ⟨12847311332727762196055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34259496887274032522813 12847311332727762196055)
              ·
                refine ⟨19270966999091643294083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12847311332727762196055 19270966999091643294083)
                ·
                  refine ⟨28906450498637464941125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19270966999091643294083 28906450498637464941125)
                  ·
                    refine ⟨5419959468494524676461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28906450498637464941125 5419959468494524676461)
                    ·
                      rfl

theorem cell22_15833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 1, 4].length) (baseStart_15833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_15833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_15833 prefixEnd_15833 := by exact prefixLift 15833
  have htrace : WordTrace (prefixWord ++ tailWord_15833) baseStart_15833 baseEnd_15833 := by
    simpa [prefixWord, tailWord_15833, baseEnd_15833] using wordTrace_append hprefix tailTrace_15833
  have hstable : (prefixWord ++ tailWord_15833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15833).length < 2 ^ (prefixWord ++ tailWord_15833).sum := by decide
  have hdescent : baseEnd_15833 < baseStart_15833 := by decide
  rcases family_descends (prefixWord ++ tailWord_15833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16071 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 4, 5]
def baseStart_16071 : Nat := 118140960795 + 16071 * 2 ^ 59
def prefixEnd_16071 : Nat := 4983230072969 + 3 ^ 40 * 16071 * 2
def baseEnd_16071 : Nat := 5501431732341237225731

theorem tailTrace_16071 : CollatzResearch.WordTrace tailWord_16071 prefixEnd_16071 5501431732341237225731 := by
  unfold tailWord_16071
  simp only [CollatzResearch.WordTrace]
  refine ⟨586157524784986553392067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 390771683189991035594711 586157524784986553392067)
  ·
    refine ⟨879236287177479830088101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 586157524784986553392067 879236287177479830088101)
    ·
      refine ⟨164856803845777468141519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 879236287177479830088101 164856803845777468141519)
      ·
        refine ⟨247285205768666202212279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164856803845777468141519 247285205768666202212279)
        ·
          refine ⟨370927808652999303318419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247285205768666202212279 370927808652999303318419)
          ·
            refine ⟨556391712979498954977629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370927808652999303318419 556391712979498954977629)
            ·
              refine ⟨208646892367312108116611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 556391712979498954977629 208646892367312108116611)
              ·
                refine ⟨312970338550968162174917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208646892367312108116611 312970338550968162174917)
                ·
                  refine ⟨58681938478306530407797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312970338550968162174917 58681938478306530407797)
                  ·
                    refine ⟨5501431732341237225731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58681938478306530407797 5501431732341237225731)
                    ·
                      rfl

theorem cell22_16071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_16071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16071 prefixEnd_16071 := by exact prefixLift 16071
  have htrace : WordTrace (prefixWord ++ tailWord_16071) baseStart_16071 baseEnd_16071 := by
    simpa [prefixWord, tailWord_16071, baseEnd_16071] using wordTrace_append hprefix tailTrace_16071
  have hstable : (prefixWord ++ tailWord_16071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16071).length < 2 ^ (prefixWord ++ tailWord_16071).sum := by decide
  have hdescent : baseEnd_16071 < baseStart_16071 := by decide
  rcases family_descends (prefixWord ++ tailWord_16071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16077 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_16077 : Nat := 118140960795 + 16077 * 2 ^ 59
def prefixEnd_16077 : Nat := 4983230072969 + 3 ^ 40 * 16077 * 2
def baseEnd_16077 : Nat := 5503485654959221575713

theorem tailTrace_16077 : CollatzResearch.WordTrace tailWord_16077 prefixEnd_16077 5503485654959221575713 := by
  unfold tailWord_16077
  simp only [CollatzResearch.WordTrace]
  refine ⟨586376362763249578110485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 390917575175499718740323 586376362763249578110485)
  ·
    refine ⟨27486392004527323973929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 586376362763249578110485 27486392004527323973929)
    ·
      refine ⟨20614794003395492980447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27486392004527323973929 20614794003395492980447)
      ·
        refine ⟨30922191005093239470671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20614794003395492980447 30922191005093239470671)
        ·
          refine ⟨46383286507639859206007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30922191005093239470671 46383286507639859206007)
          ·
            refine ⟨69574929761459788809011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46383286507639859206007 69574929761459788809011)
            ·
              refine ⟨104362394642189683213517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69574929761459788809011 104362394642189683213517)
              ·
                refine ⟨39135897990821131205069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104362394642189683213517 39135897990821131205069)
                ·
                  refine ⟨14675961746557924201901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39135897990821131205069 14675961746557924201901)
                  ·
                    refine ⟨5503485654959221575713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14675961746557924201901 5503485654959221575713)
                    ·
                      rfl

theorem cell22_16077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_16077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16077 prefixEnd_16077 := by exact prefixLift 16077
  have htrace : WordTrace (prefixWord ++ tailWord_16077) baseStart_16077 baseEnd_16077 := by
    simpa [prefixWord, tailWord_16077, baseEnd_16077] using wordTrace_append hprefix tailTrace_16077
  have hstable : (prefixWord ++ tailWord_16077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16077).length < 2 ^ (prefixWord ++ tailWord_16077).sum := by decide
  have hdescent : baseEnd_16077 < baseStart_16077 := by decide
  rcases family_descends (prefixWord ++ tailWord_16077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16090 : List Nat := [3, 1, 1, 2, 2, 4, 3, 1, 5]
def baseStart_16090 : Nat := 118140960795 + 16090 * 2 ^ 59
def prefixEnd_16090 : Nat := 4983230072969 + 3 ^ 40 * 16090 * 2
def baseEnd_16090 : Nat := 1835978606877173666891

theorem tailTrace_16090 : CollatzResearch.WordTrace tailWord_16090 prefixEnd_16090 1835978606877173666891 := by
  unfold tailWord_16090
  simp only [CollatzResearch.WordTrace]
  refine ⟨146712627929038199583431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 391233674477435198889149 146712627929038199583431)
  ·
    refine ⟨220068941893557299375147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146712627929038199583431 220068941893557299375147)
    ·
      refine ⟨330103412840335949062721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220068941893557299375147 330103412840335949062721)
      ·
        refine ⟨247577559630251961797041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330103412840335949062721 247577559630251961797041)
        ·
          refine ⟨185683169722688971347781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247577559630251961797041 185683169722688971347781)
          ·
            refine ⟨34815594323004182127709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185683169722688971347781 34815594323004182127709)
            ·
              refine ⟨13055847871126568297891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34815594323004182127709 13055847871126568297891)
              ·
                refine ⟨19583771806689852446837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13055847871126568297891 19583771806689852446837)
                ·
                  refine ⟨1835978606877173666891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19583771806689852446837 1835978606877173666891)
                  ·
                    rfl

theorem cell22_16090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_16090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16090 prefixEnd_16090 := by exact prefixLift 16090
  have htrace : WordTrace (prefixWord ++ tailWord_16090) baseStart_16090 baseEnd_16090 := by
    simpa [prefixWord, tailWord_16090, baseEnd_16090] using wordTrace_append hprefix tailTrace_16090
  have hstable : (prefixWord ++ tailWord_16090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16090).length < 2 ^ (prefixWord ++ tailWord_16090).sum := by decide
  have hdescent : baseEnd_16090 < baseStart_16090 := by decide
  rcases family_descends (prefixWord ++ tailWord_16090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16141 : List Nat := [1, 7, 2, 1, 1, 1, 1, 3, 5]
def baseStart_16141 : Nat := 118140960795 + 16141 * 2 ^ 59
def prefixEnd_16141 : Nat := 4983230072969 + 3 ^ 40 * 16141 * 2
def baseEnd_16141 : Nat := 1841798054294795991839

theorem tailTrace_16141 : CollatzResearch.WordTrace tailWord_16141 prefixEnd_16141 1841798054294795991839 := by
  unfold tailWord_16141
  simp only [CollatzResearch.WordTrace]
  refine ⟨588710634531388508440277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 392473756354259005626851 588710634531388508440277)
  ·
    refine ⟨13797905496829418166569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 588710634531388508440277 13797905496829418166569)
    ·
      refine ⟨10348429122622063624927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13797905496829418166569 10348429122622063624927)
      ·
        refine ⟨15522643683933095437391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10348429122622063624927 15522643683933095437391)
        ·
          refine ⟨23283965525899643156087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15522643683933095437391 23283965525899643156087)
          ·
            refine ⟨34925948288849464734131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23283965525899643156087 34925948288849464734131)
            ·
              refine ⟨52388922433274197101197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34925948288849464734131 52388922433274197101197)
              ·
                refine ⟨19645845912477823912949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52388922433274197101197 19645845912477823912949)
                ·
                  refine ⟨1841798054294795991839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19645845912477823912949 1841798054294795991839)
                  ·
                    rfl

theorem cell22_16141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_16141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16141 prefixEnd_16141 := by exact prefixLift 16141
  have htrace : WordTrace (prefixWord ++ tailWord_16141) baseStart_16141 baseEnd_16141 := by
    simpa [prefixWord, tailWord_16141, baseEnd_16141] using wordTrace_append hprefix tailTrace_16141
  have hstable : (prefixWord ++ tailWord_16141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16141).length < 2 ^ (prefixWord ++ tailWord_16141).sum := by decide
  have hdescent : baseEnd_16141 < baseStart_16141 := by decide
  rcases family_descends (prefixWord ++ tailWord_16141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16165 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 2, 4]
def baseStart_16165 : Nat := 118140960795 + 16165 * 2 ^ 59
def prefixEnd_16165 : Nat := 4983230072969 + 3 ^ 40 * 16165 * 2
def baseEnd_16165 : Nat := 5533609853356325375443

theorem tailTrace_16165 : CollatzResearch.WordTrace tailWord_16165 prefixEnd_16165 5533609853356325375443 := by
  unfold tailWord_16165
  simp only [CollatzResearch.WordTrace]
  refine ⟨589585986444440607313949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 393057324296293738209299 589585986444440607313949)
  ·
    refine ⟨221094744916665227742731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 589585986444440607313949 221094744916665227742731)
    ·
      refine ⟨331642117374997841614097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221094744916665227742731 331642117374997841614097)
      ·
        refine ⟨248731588031248381210573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331642117374997841614097 248731588031248381210573)
        ·
          refine ⟨93274345511718142953965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248731588031248381210573 93274345511718142953965)
          ·
            refine ⟨34977879566894303607737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93274345511718142953965 34977879566894303607737)
            ·
              refine ⟨26233409675170727705803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34977879566894303607737 26233409675170727705803)
              ·
                refine ⟨39350114512756091558705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26233409675170727705803 39350114512756091558705)
                ·
                  refine ⟨29512585884567068669029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39350114512756091558705 29512585884567068669029)
                  ·
                    refine ⟨5533609853356325375443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29512585884567068669029 5533609853356325375443)
                    ·
                      rfl

theorem cell22_16165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_16165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16165 prefixEnd_16165 := by exact prefixLift 16165
  have htrace : WordTrace (prefixWord ++ tailWord_16165) baseStart_16165 baseEnd_16165 := by
    simpa [prefixWord, tailWord_16165, baseEnd_16165] using wordTrace_append hprefix tailTrace_16165
  have hstable : (prefixWord ++ tailWord_16165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16165).length < 2 ^ (prefixWord ++ tailWord_16165).sum := by decide
  have hdescent : baseEnd_16165 < baseStart_16165 := by decide
  rcases family_descends (prefixWord ++ tailWord_16165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16182 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_16182 : Nat := 118140960795 + 16182 * 2 ^ 59
def prefixEnd_16182 : Nat := 4983230072969 + 3 ^ 40 * 16182 * 2
def baseEnd_16182 : Nat := 5539429300773947700391

theorem tailTrace_16182 : CollatzResearch.WordTrace tailWord_16182 prefixEnd_16182 5539429300773947700391 := by
  unfold tailWord_16182
  simp only [CollatzResearch.WordTrace]
  refine ⟨36887876711428281917675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 393470684921901673788533 36887876711428281917675)
  ·
    refine ⟨55331815067142422876513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36887876711428281917675 55331815067142422876513)
    ·
      refine ⟨41498861300356817157385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55331815067142422876513 41498861300356817157385)
      ·
        refine ⟨31124145975267612868039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41498861300356817157385 31124145975267612868039)
        ·
          refine ⟨46686218962901419302059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31124145975267612868039 46686218962901419302059)
          ·
            refine ⟨70029328444352128953089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46686218962901419302059 70029328444352128953089)
            ·
              refine ⟨52521996333264096714817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70029328444352128953089 52521996333264096714817)
              ·
                refine ⟨39391497249948072536113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52521996333264096714817 39391497249948072536113)
                ·
                  refine ⟨29543622937461054402085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39391497249948072536113 29543622937461054402085)
                  ·
                    refine ⟨5539429300773947700391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29543622937461054402085 5539429300773947700391)
                    ·
                      rfl

theorem cell22_16182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_16182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16182 prefixEnd_16182 := by exact prefixLift 16182
  have htrace : WordTrace (prefixWord ++ tailWord_16182) baseStart_16182 baseEnd_16182 := by
    simpa [prefixWord, tailWord_16182, baseEnd_16182] using wordTrace_append hprefix tailTrace_16182
  have hstable : (prefixWord ++ tailWord_16182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16182).length < 2 ^ (prefixWord ++ tailWord_16182).sum := by decide
  have hdescent : baseEnd_16182 < baseStart_16182 := by decide
  rcases family_descends (prefixWord ++ tailWord_16182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16212 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_16212 : Nat := 118140960795 + 16212 * 2 ^ 59
def prefixEnd_16212 : Nat := 4983230072969 + 3 ^ 40 * 16212 * 2
def baseEnd_16212 : Nat := 5549698913863869450299

theorem tailTrace_16212 : CollatzResearch.WordTrace tailWord_16212 prefixEnd_16212 5549698913863869450299 := by
  unfold tailWord_16212
  simp only [CollatzResearch.WordTrace]
  refine ⟨295650108637083817137445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 394200144849445089516593 295650108637083817137445)
  ·
    refine ⟨55434395369453215713271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295650108637083817137445 55434395369453215713271)
    ·
      refine ⟨83151593054179823569907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55434395369453215713271 83151593054179823569907)
      ·
        refine ⟨124727389581269735354861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83151593054179823569907 124727389581269735354861)
        ·
          refine ⟨46772771092976150758073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124727389581269735354861 46772771092976150758073)
          ·
            refine ⟨35079578319732113068555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46772771092976150758073 35079578319732113068555)
            ·
              refine ⟨52619367479598169602833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35079578319732113068555 52619367479598169602833)
              ·
                refine ⟨39464525609698627202125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52619367479598169602833 39464525609698627202125)
                ·
                  refine ⟨14799197103636985200797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39464525609698627202125 14799197103636985200797)
                  ·
                    refine ⟨5549698913863869450299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14799197103636985200797 5549698913863869450299)
                    ·
                      rfl

theorem cell22_16212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_16212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16212 prefixEnd_16212 := by exact prefixLift 16212
  have htrace : WordTrace (prefixWord ++ tailWord_16212) baseStart_16212 baseEnd_16212 := by
    simpa [prefixWord, tailWord_16212, baseEnd_16212] using wordTrace_append hprefix tailTrace_16212
  have hstable : (prefixWord ++ tailWord_16212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16212).length < 2 ^ (prefixWord ++ tailWord_16212).sum := by decide
  have hdescent : baseEnd_16212 < baseStart_16212 := by decide
  rcases family_descends (prefixWord ++ tailWord_16212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16435 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 1, 6]
def baseStart_16435 : Nat := 118140960795 + 16435 * 2 ^ 59
def prefixEnd_16435 : Nat := 4983230072969 + 3 ^ 40 * 16435 * 2
def baseEnd_16435 : Nat := 5626036371165621124615

theorem tailTrace_16435 : CollatzResearch.WordTrace tailWord_16435 prefixEnd_16435 5626036371165621124615 := by
  unfold tailWord_16435
  simp only [CollatzResearch.WordTrace]
  refine ⟨599433695466276719642759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 399622463644184479761839 599433695466276719642759)
  ·
    refine ⟨899150543199415079464139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 599433695466276719642759 899150543199415079464139)
    ·
      refine ⟨1348725814799122619196209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 899150543199415079464139 1348725814799122619196209)
      ·
        refine ⟨1011544361099341964397157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1348725814799122619196209 1011544361099341964397157)
        ·
          refine ⟨189664567706126618324467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1011544361099341964397157 189664567706126618324467)
          ·
            refine ⟨284496851559189927486701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189664567706126618324467 284496851559189927486701)
            ·
              refine ⟨106686319334696222807513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284496851559189927486701 106686319334696222807513)
              ·
                refine ⟨80014739501022167105635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106686319334696222807513 80014739501022167105635)
                ·
                  refine ⟨120022109251533250658453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80014739501022167105635 120022109251533250658453)
                  ·
                    refine ⟨5626036371165621124615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120022109251533250658453 5626036371165621124615)
                    ·
                      rfl

theorem cell22_16435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 6].length) (baseStart_16435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16435 prefixEnd_16435 := by exact prefixLift 16435
  have htrace : WordTrace (prefixWord ++ tailWord_16435) baseStart_16435 baseEnd_16435 := by
    simpa [prefixWord, tailWord_16435, baseEnd_16435] using wordTrace_append hprefix tailTrace_16435
  have hstable : (prefixWord ++ tailWord_16435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16435).length < 2 ^ (prefixWord ++ tailWord_16435).sum := by decide
  have hdescent : baseEnd_16435 < baseStart_16435 := by decide
  rcases family_descends (prefixWord ++ tailWord_16435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16437 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 1, 5]
def baseStart_16437 : Nat := 118140960795 + 16437 * 2 ^ 59
def prefixEnd_16437 : Nat := 4983230072969 + 3 ^ 40 * 16437 * 2
def baseEnd_16437 : Nat := 5626721012038282574609

theorem tailTrace_16437 : CollatzResearch.WordTrace tailWord_16437 prefixEnd_16437 5626721012038282574609 := by
  unfold tailWord_16437
  simp only [CollatzResearch.WordTrace]
  refine ⟨599506641459031061215565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 399671094306020707477043 599506641459031061215565)
  ·
    refine ⟨224814990547136647955837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 599506641459031061215565 224814990547136647955837)
    ·
      refine ⟨84305621455176242983439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224814990547136647955837 84305621455176242983439)
      ·
        refine ⟨126458432182764364475159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84305621455176242983439 126458432182764364475159)
        ·
          refine ⟨189687648274146546712739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126458432182764364475159 189687648274146546712739)
          ·
            refine ⟨284531472411219820069109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189687648274146546712739 284531472411219820069109)
            ·
              refine ⟨26674825538551858131479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284531472411219820069109 26674825538551858131479)
              ·
                refine ⟨40012238307827787197219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26674825538551858131479 40012238307827787197219)
                ·
                  refine ⟨60018357461741680795829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40012238307827787197219 60018357461741680795829)
                  ·
                    refine ⟨5626721012038282574609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60018357461741680795829 5626721012038282574609)
                    ·
                      rfl

theorem cell22_16437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_16437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16437 prefixEnd_16437 := by exact prefixLift 16437
  have htrace : WordTrace (prefixWord ++ tailWord_16437) baseStart_16437 baseEnd_16437 := by
    simpa [prefixWord, tailWord_16437, baseEnd_16437] using wordTrace_append hprefix tailTrace_16437
  have hstable : (prefixWord ++ tailWord_16437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16437).length < 2 ^ (prefixWord ++ tailWord_16437).sum := by decide
  have hdescent : baseEnd_16437 < baseStart_16437 := by decide
  rcases family_descends (prefixWord ++ tailWord_16437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16454 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_16454 : Nat := 118140960795 + 16454 * 2 ^ 59
def prefixEnd_16454 : Nat := 4983230072969 + 3 ^ 40 * 16454 * 2
def baseEnd_16454 : Nat := 5632540459455904899557

theorem tailTrace_16454 : CollatzResearch.WordTrace tailWord_16454 prefixEnd_16454 5632540459455904899557 := by
  unfold tailWord_16454
  simp only [CollatzResearch.WordTrace]
  refine ⟨18753958824920092643263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 400084454931628643056277 18753958824920092643263)
  ·
    refine ⟨28130938237380138964895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18753958824920092643263 28130938237380138964895)
    ·
      refine ⟨42196407356070208447343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28130938237380138964895 42196407356070208447343)
      ·
        refine ⟨63294611034105312671015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42196407356070208447343 63294611034105312671015)
        ·
          refine ⟨94941916551157969006523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63294611034105312671015 94941916551157969006523)
          ·
            refine ⟨142412874826736953509785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94941916551157969006523 142412874826736953509785)
            ·
              refine ⟨106809656120052715132339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142412874826736953509785 106809656120052715132339)
              ·
                refine ⟨160214484180079072698509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106809656120052715132339 160214484180079072698509)
                ·
                  refine ⟨60080431567529652261941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160214484180079072698509 60080431567529652261941)
                  ·
                    refine ⟨5632540459455904899557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60080431567529652261941 5632540459455904899557)
                    ·
                      rfl

theorem cell22_16454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_16454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16454 prefixEnd_16454 := by exact prefixLift 16454
  have htrace : WordTrace (prefixWord ++ tailWord_16454) baseStart_16454 baseEnd_16454 := by
    simpa [prefixWord, tailWord_16454, baseEnd_16454] using wordTrace_append hprefix tailTrace_16454
  have hstable : (prefixWord ++ tailWord_16454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16454).length < 2 ^ (prefixWord ++ tailWord_16454).sum := by decide
  have hdescent : baseEnd_16454 < baseStart_16454 := by decide
  rcases family_descends (prefixWord ++ tailWord_16454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16516 : List Nat := [2, 3, 2, 1, 2, 1, 2, 5, 1, 3]
def baseStart_16516 : Nat := 118140960795 + 16516 * 2 ^ 59
def prefixEnd_16516 : Nat := 4983230072969 + 3 ^ 40 * 16516 * 2
def baseEnd_16516 : Nat := 5653764326508409849367

theorem tailTrace_16516 : CollatzResearch.WordTrace tailWord_16516 prefixEnd_16516 5653764326508409849367 := by
  unfold tailWord_16516
  simp only [CollatzResearch.WordTrace]
  refine ⟨301194004086413776670701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 401592005448551702227601 301194004086413776670701)
  ·
    refine ⟨112947751532405166251513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 301194004086413776670701 112947751532405166251513)
    ·
      refine ⟨84710813649303874688635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112947751532405166251513 84710813649303874688635)
      ·
        refine ⟨127066220473955812032953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84710813649303874688635 127066220473955812032953)
        ·
          refine ⟨95299665355466859024715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127066220473955812032953 95299665355466859024715)
          ·
            refine ⟨142949498033200288537073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95299665355466859024715 142949498033200288537073)
            ·
              refine ⟨107212123524900216402805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142949498033200288537073 107212123524900216402805)
              ·
                refine ⟨10051136580459395287763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107212123524900216402805 10051136580459395287763)
                ·
                  refine ⟨15076704870689092931645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10051136580459395287763 15076704870689092931645)
                  ·
                    refine ⟨5653764326508409849367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15076704870689092931645 5653764326508409849367)
                    ·
                      rfl

theorem cell22_16516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_16516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16516 prefixEnd_16516 := by exact prefixLift 16516
  have htrace : WordTrace (prefixWord ++ tailWord_16516) baseStart_16516 baseEnd_16516 := by
    simpa [prefixWord, tailWord_16516, baseEnd_16516] using wordTrace_append hprefix tailTrace_16516
  have hstable : (prefixWord ++ tailWord_16516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16516).length < 2 ^ (prefixWord ++ tailWord_16516).sum := by decide
  have hdescent : baseEnd_16516 < baseStart_16516 := by decide
  rcases family_descends (prefixWord ++ tailWord_16516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16576 : List Nat := [2, 1, 1, 2, 5, 1, 4, 1, 1, 4]
def baseStart_16576 : Nat := 118140960795 + 16576 * 2 ^ 59
def prefixEnd_16576 : Nat := 4983230072969 + 3 ^ 40 * 16576 * 2
def baseEnd_16576 : Nat := 5674303552688253349183

theorem tailTrace_16576 : CollatzResearch.WordTrace tailWord_16576 prefixEnd_16576 5674303552688253349183 := by
  unfold tailWord_16576
  simp only [CollatzResearch.WordTrace]
  refine ⟨302288193977728900262791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 403050925303638533683721 302288193977728900262791)
  ·
    refine ⟨453432290966593350394187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302288193977728900262791 453432290966593350394187)
    ·
      refine ⟨680148436449890025591281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453432290966593350394187 680148436449890025591281)
      ·
        refine ⟨510111327337417519193461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680148436449890025591281 510111327337417519193461)
        ·
          refine ⟨47822936937882892424387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 510111327337417519193461 47822936937882892424387)
          ·
            refine ⟨71734405406824338636581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47822936937882892424387 71734405406824338636581)
            ·
              refine ⟨13450201013779563494359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71734405406824338636581 13450201013779563494359)
              ·
                refine ⟨20175301520669345241539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13450201013779563494359 20175301520669345241539)
                ·
                  refine ⟨30262952281004017862309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20175301520669345241539 30262952281004017862309)
                  ·
                    refine ⟨5674303552688253349183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30262952281004017862309 5674303552688253349183)
                    ·
                      rfl

theorem cell22_16576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 1, 4].length) (baseStart_16576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16576 prefixEnd_16576 := by exact prefixLift 16576
  have htrace : WordTrace (prefixWord ++ tailWord_16576) baseStart_16576 baseEnd_16576 := by
    simpa [prefixWord, tailWord_16576, baseEnd_16576] using wordTrace_append hprefix tailTrace_16576
  have hstable : (prefixWord ++ tailWord_16576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16576).length < 2 ^ (prefixWord ++ tailWord_16576).sum := by decide
  have hdescent : baseEnd_16576 < baseStart_16576 := by decide
  rcases family_descends (prefixWord ++ tailWord_16576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16587 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 4, 4]
def baseStart_16587 : Nat := 118140960795 + 16587 * 2 ^ 59
def prefixEnd_16587 : Nat := 4983230072969 + 3 ^ 40 * 16587 * 2
def baseEnd_16587 : Nat := 5678069077487891324149

theorem tailTrace_16587 : CollatzResearch.WordTrace tailWord_16587 prefixEnd_16587 5678069077487891324149 := by
  unfold tailWord_16587
  simp only [CollatzResearch.WordTrace]
  refine ⟨604977590915606679176015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 403318393943737786117343 604977590915606679176015)
  ·
    refine ⟨907466386373410018764023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 604977590915606679176015 907466386373410018764023)
    ·
      refine ⟨1361199579560115028146035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 907466386373410018764023 1361199579560115028146035)
      ·
        refine ⟨2041799369340172542219053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1361199579560115028146035 2041799369340172542219053)
        ·
          refine ⟨765674763502564703332145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2041799369340172542219053 765674763502564703332145)
          ·
            refine ⟨574256072626923527499109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765674763502564703332145 574256072626923527499109)
            ·
              refine ⟨107673013617548161406083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 574256072626923527499109 107673013617548161406083)
              ·
                refine ⟨161509520426322242109125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107673013617548161406083 161509520426322242109125)
                ·
                  refine ⟨30283035079935420395461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161509520426322242109125 30283035079935420395461)
                  ·
                    refine ⟨5678069077487891324149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30283035079935420395461 5678069077487891324149)
                    ·
                      rfl

theorem cell22_16587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 4].length) (baseStart_16587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16587 prefixEnd_16587 := by exact prefixLift 16587
  have htrace : WordTrace (prefixWord ++ tailWord_16587) baseStart_16587 baseEnd_16587 := by
    simpa [prefixWord, tailWord_16587, baseEnd_16587] using wordTrace_append hprefix tailTrace_16587
  have hstable : (prefixWord ++ tailWord_16587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16587).length < 2 ^ (prefixWord ++ tailWord_16587).sum := by decide
  have hdescent : baseEnd_16587 < baseStart_16587 := by decide
  rcases family_descends (prefixWord ++ tailWord_16587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16664 : List Nat := [2, 1, 2, 3, 1, 2, 3, 3, 5]
def baseStart_16664 : Nat := 118140960795 + 16664 * 2 ^ 59
def prefixEnd_16664 : Nat := 4983230072969 + 3 ^ 40 * 16664 * 2
def baseEnd_16664 : Nat := 1901475917028452382971

theorem tailTrace_16664 : CollatzResearch.WordTrace tailWord_16664 prefixEnd_16664 1901475917028452382971 := by
  unfold tailWord_16664
  simp only [CollatzResearch.WordTrace]
  refine ⟨303893005818324414864523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 405190674424432553152697 303893005818324414864523)
  ·
    refine ⟨455839508727486622296785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303893005818324414864523 455839508727486622296785)
    ·
      refine ⟨341879631545614966722589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455839508727486622296785 341879631545614966722589)
      ·
        refine ⟨128204861829605612520971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341879631545614966722589 128204861829605612520971)
        ·
          refine ⟨192307292744408418781457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128204861829605612520971 192307292744408418781457)
          ·
            refine ⟨144230469558306314086093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192307292744408418781457 144230469558306314086093)
            ·
              refine ⟨54086426084364867782285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144230469558306314086093 54086426084364867782285)
              ·
                refine ⟨20282409781636825418357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54086426084364867782285 20282409781636825418357)
                ·
                  refine ⟨1901475917028452382971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20282409781636825418357 1901475917028452382971)
                  ·
                    rfl

theorem cell22_16664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 5].length) (baseStart_16664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16664 prefixEnd_16664 := by exact prefixLift 16664
  have htrace : WordTrace (prefixWord ++ tailWord_16664) baseStart_16664 baseEnd_16664 := by
    simpa [prefixWord, tailWord_16664, baseEnd_16664] using wordTrace_append hprefix tailTrace_16664
  have hstable : (prefixWord ++ tailWord_16664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16664).length < 2 ^ (prefixWord ++ tailWord_16664).sum := by decide
  have hdescent : baseEnd_16664 < baseStart_16664 := by decide
  rcases family_descends (prefixWord ++ tailWord_16664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16702 : List Nat := [4, 2, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_16702 : Nat := 118140960795 + 16702 * 2 ^ 59
def prefixEnd_16702 : Nat := 4983230072969 + 3 ^ 40 * 16702 * 2
def baseEnd_16702 : Nat := 5717435927665924698797

theorem tailTrace_16702 : CollatzResearch.WordTrace tailWord_16702 prefixEnd_16702 5717435927665924698797 := by
  unfold tailWord_16702
  simp only [CollatzResearch.WordTrace]
  refine ⟨76146498187372664951545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 406114656999320879741573 76146498187372664951545)
  ·
    refine ⟨57109873640529498713659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76146498187372664951545 57109873640529498713659)
    ·
      refine ⟨85664810460794248070489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57109873640529498713659 85664810460794248070489)
      ·
        refine ⟨64248607845595686052867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85664810460794248070489 64248607845595686052867)
        ·
          refine ⟨96372911768393529079301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64248607845595686052867 96372911768393529079301)
          ·
            refine ⟨18069920956573786702369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96372911768393529079301 18069920956573786702369)
            ·
              refine ⟨13552440717430340026777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18069920956573786702369 13552440717430340026777)
              ·
                refine ⟨10164330538072755020083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13552440717430340026777 10164330538072755020083)
                ·
                  refine ⟨15246495807109132530125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10164330538072755020083 15246495807109132530125)
                  ·
                    refine ⟨5717435927665924698797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15246495807109132530125 5717435927665924698797)
                    ·
                      rfl

theorem cell22_16702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_16702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16702 prefixEnd_16702 := by exact prefixLift 16702
  have htrace : WordTrace (prefixWord ++ tailWord_16702) baseStart_16702 baseEnd_16702 := by
    simpa [prefixWord, tailWord_16702, baseEnd_16702] using wordTrace_append hprefix tailTrace_16702
  have hstable : (prefixWord ++ tailWord_16702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16702).length < 2 ^ (prefixWord ++ tailWord_16702).sum := by decide
  have hdescent : baseEnd_16702 < baseStart_16702 := by decide
  rcases family_descends (prefixWord ++ tailWord_16702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16739 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 1, 6]
def baseStart_16739 : Nat := 118140960795 + 16739 * 2 ^ 59
def prefixEnd_16739 : Nat := 4983230072969 + 3 ^ 40 * 16739 * 2
def baseEnd_16739 : Nat := 5730101783810161523683

theorem tailTrace_16739 : CollatzResearch.WordTrace tailWord_16739 prefixEnd_16739 5730101783810161523683 := by
  unfold tailWord_16739
  simp only [CollatzResearch.WordTrace]
  refine ⟨610521486364936638709271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 407014324243291092472847 610521486364936638709271)
  ·
    refine ⟨915782229547404958063907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 610521486364936638709271 915782229547404958063907)
    ·
      refine ⟨1373673344321107437095861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 915782229547404958063907 1373673344321107437095861)
      ·
        refine ⟨128781876030103822227737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1373673344321107437095861 128781876030103822227737)
        ·
          refine ⟨96586407022577866670803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128781876030103822227737 96586407022577866670803)
          ·
            refine ⟨144879610533866800006205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96586407022577866670803 144879610533866800006205)
            ·
              refine ⟨54329853950200050002327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144879610533866800006205 54329853950200050002327)
              ·
                refine ⟨81494780925300075003491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54329853950200050002327 81494780925300075003491)
                ·
                  refine ⟨122242171387950112505237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81494780925300075003491 122242171387950112505237)
                  ·
                    refine ⟨5730101783810161523683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122242171387950112505237 5730101783810161523683)
                    ·
                      rfl

theorem cell22_16739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 6].length) (baseStart_16739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16739 prefixEnd_16739 := by exact prefixLift 16739
  have htrace : WordTrace (prefixWord ++ tailWord_16739) baseStart_16739 baseEnd_16739 := by
    simpa [prefixWord, tailWord_16739, baseEnd_16739] using wordTrace_append hprefix tailTrace_16739
  have hstable : (prefixWord ++ tailWord_16739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16739).length < 2 ^ (prefixWord ++ tailWord_16739).sum := by decide
  have hdescent : baseEnd_16739 < baseStart_16739 := by decide
  rcases family_descends (prefixWord ++ tailWord_16739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16743 : List Nat := [1, 1, 5, 1, 3, 2, 2, 3, 4]
def baseStart_16743 : Nat := 118140960795 + 16743 * 2 ^ 59
def prefixEnd_16743 : Nat := 4983230072969 + 3 ^ 40 * 16743 * 2
def baseEnd_16743 : Nat := 1910490355185161474557

theorem tailTrace_16743 : CollatzResearch.WordTrace tailWord_16743 prefixEnd_16743 1910490355185161474557 := by
  unfold tailWord_16743
  simp only [CollatzResearch.WordTrace]
  refine ⟨610667378350445321854883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 407111585566963547903255 610667378350445321854883)
  ·
    refine ⟨916001067525667982782325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 610667378350445321854883 916001067525667982782325)
    ·
      refine ⟨85875100080531373385843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 916001067525667982782325 85875100080531373385843)
      ·
        refine ⟨128812650120797060078765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85875100080531373385843 128812650120797060078765)
        ·
          refine ⟨48304743795298897529537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128812650120797060078765 48304743795298897529537)
          ·
            refine ⟨36228557846474173147153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48304743795298897529537 36228557846474173147153)
            ·
              refine ⟨27171418384855629860365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36228557846474173147153 27171418384855629860365)
              ·
                refine ⟨10189281894320861197637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27171418384855629860365 10189281894320861197637)
                ·
                  refine ⟨1910490355185161474557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10189281894320861197637 1910490355185161474557)
                  ·
                    rfl

theorem cell22_16743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 4].length) (baseStart_16743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16743 prefixEnd_16743 := by exact prefixLift 16743
  have htrace : WordTrace (prefixWord ++ tailWord_16743) baseStart_16743 baseEnd_16743 := by
    simpa [prefixWord, tailWord_16743, baseEnd_16743] using wordTrace_append hprefix tailTrace_16743
  have hstable : (prefixWord ++ tailWord_16743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16743).length < 2 ^ (prefixWord ++ tailWord_16743).sum := by decide
  have hdescent : baseEnd_16743 < baseStart_16743 := by decide
  rcases family_descends (prefixWord ++ tailWord_16743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16754 : List Nat := [3, 2, 1, 2, 1, 4, 9]
def baseStart_16754 : Nat := 118140960795 + 16754 * 2 ^ 59
def prefixEnd_16754 : Nat := 4983230072969 + 3 ^ 40 * 16754 * 2
def baseEnd_16754 : Nat := 212416170013152681431

theorem tailTrace_16754 : CollatzResearch.WordTrace tailWord_16754 prefixEnd_16754 212416170013152681431 := by
  unfold tailWord_16754
  simp only [CollatzResearch.WordTrace]
  refine ⟨152767145327648550126329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 407379054207062800336877 152767145327648550126329)
  ·
    refine ⟨114575358995736412594747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152767145327648550126329 114575358995736412594747)
    ·
      refine ⟨171863038493604618892121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114575358995736412594747 171863038493604618892121)
      ·
        refine ⟨128897278870203464169091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171863038493604618892121 128897278870203464169091)
        ·
          refine ⟨193345918305305196253637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128897278870203464169091 193345918305305196253637)
          ·
            refine ⟨36252359682244724297557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193345918305305196253637 36252359682244724297557)
            ·
              refine ⟨212416170013152681431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 36252359682244724297557 212416170013152681431)
              ·
                rfl

theorem cell22_16754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 9].length) (baseStart_16754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16754 prefixEnd_16754 := by exact prefixLift 16754
  have htrace : WordTrace (prefixWord ++ tailWord_16754) baseStart_16754 baseEnd_16754 := by
    simpa [prefixWord, tailWord_16754, baseEnd_16754] using wordTrace_append hprefix tailTrace_16754
  have hstable : (prefixWord ++ tailWord_16754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16754).length < 2 ^ (prefixWord ++ tailWord_16754).sum := by decide
  have hdescent : baseEnd_16754 < baseStart_16754 := by decide
  rcases family_descends (prefixWord ++ tailWord_16754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16799 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 9]
def baseStart_16799 : Nat := 118140960795 + 16799 * 2 ^ 59
def prefixEnd_16799 : Nat := 4983230072969 + 3 ^ 40 * 16799 * 2
def baseEnd_16799 : Nat := 1916880336663335007833

theorem tailTrace_16799 : CollatzResearch.WordTrace tailWord_16799 prefixEnd_16799 1916880336663335007833 := by
  unfold tailWord_16799
  simp only [CollatzResearch.WordTrace]
  refine ⟨612709866147566885893451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 408473244098377923928967 612709866147566885893451)
  ·
    refine ⟨919064799221350328840177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 612709866147566885893451 919064799221350328840177)
    ·
      refine ⟨689298599416012746630133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 919064799221350328840177 689298599416012746630133)
      ·
        refine ⟨64621743695251194996575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 689298599416012746630133 64621743695251194996575)
        ·
          refine ⟨96932615542876792494863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64621743695251194996575 96932615542876792494863)
          ·
            refine ⟨145398923314315188742295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96932615542876792494863 145398923314315188742295)
            ·
              refine ⟨218098384971472783113443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145398923314315188742295 218098384971472783113443)
              ·
                refine ⟨327147577457209174670165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218098384971472783113443 327147577457209174670165)
                ·
                  refine ⟨1916880336663335007833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 327147577457209174670165 1916880336663335007833)
                  ·
                    rfl

theorem cell22_16799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 9].length) (baseStart_16799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16799 prefixEnd_16799 := by exact prefixLift 16799
  have htrace : WordTrace (prefixWord ++ tailWord_16799) baseStart_16799 baseEnd_16799 := by
    simpa [prefixWord, tailWord_16799, baseEnd_16799] using wordTrace_append hprefix tailTrace_16799
  have hstable : (prefixWord ++ tailWord_16799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16799).length < 2 ^ (prefixWord ++ tailWord_16799).sum := by decide
  have hdescent : baseEnd_16799 < baseStart_16799 := by decide
  rcases family_descends (prefixWord ++ tailWord_16799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16893 : List Nat := [1, 4, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_16893 : Nat := 118140960795 + 16893 * 2 ^ 59
def prefixEnd_16893 : Nat := 4983230072969 + 3 ^ 40 * 16893 * 2
def baseEnd_16893 : Nat := 5782819131005093173211

theorem tailTrace_16893 : CollatzResearch.WordTrace tailWord_16893 prefixEnd_16893 5782819131005093173211 := by
  unfold tailWord_16893
  simp only [CollatzResearch.WordTrace]
  refine ⟨616138327807020939815333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 410758885204680626543555 616138327807020939815333)
  ·
    refine ⟨115525936463816426215375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 616138327807020939815333 115525936463816426215375)
    ·
      refine ⟨173288904695724639323063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115525936463816426215375 173288904695724639323063)
      ·
        refine ⟨259933357043586958984595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173288904695724639323063 259933357043586958984595)
        ·
          refine ⟨389900035565380438476893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259933357043586958984595 389900035565380438476893)
          ·
            refine ⟨146212513337017664428835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 389900035565380438476893 146212513337017664428835)
            ·
              refine ⟨219318770005526496643253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146212513337017664428835 219318770005526496643253)
              ·
                refine ⟨20561134688018109060305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 219318770005526496643253 20561134688018109060305)
                ·
                  refine ⟨15420851016013581795229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20561134688018109060305 15420851016013581795229)
                  ·
                    refine ⟨5782819131005093173211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15420851016013581795229 5782819131005093173211)
                    ·
                      rfl

theorem cell22_16893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_16893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16893 prefixEnd_16893 := by exact prefixLift 16893
  have htrace : WordTrace (prefixWord ++ tailWord_16893) baseStart_16893 baseEnd_16893 := by
    simpa [prefixWord, tailWord_16893, baseEnd_16893] using wordTrace_append hprefix tailTrace_16893
  have hstable : (prefixWord ++ tailWord_16893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16893).length < 2 ^ (prefixWord ++ tailWord_16893).sum := by decide
  have hdescent : baseEnd_16893 < baseStart_16893 := by decide
  rcases family_descends (prefixWord ++ tailWord_16893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16908 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 2, 4]
def baseStart_16908 : Nat := 118140960795 + 16908 * 2 ^ 59
def prefixEnd_16908 : Nat := 4983230072969 + 3 ^ 40 * 16908 * 2
def baseEnd_16908 : Nat := 5787953937550054048165

theorem tailTrace_16908 : CollatzResearch.WordTrace tailWord_16908 prefixEnd_16908 5787953937550054048165 := by
  unfold tailWord_16908
  simp only [CollatzResearch.WordTrace]
  refine ⟨308342711376339250805689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 411123615168452334407585 308342711376339250805689)
  ·
    refine ⟨231257033532254438104267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 308342711376339250805689 231257033532254438104267)
    ·
      refine ⟨346885550298381657156401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231257033532254438104267 346885550298381657156401)
      ·
        refine ⟨260164162723786242867301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346885550298381657156401 260164162723786242867301)
        ·
          refine ⟨48780780510709920537619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 260164162723786242867301 48780780510709920537619)
          ·
            refine ⟨73171170766064880806429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48780780510709920537619 73171170766064880806429)
            ·
              refine ⟨27439189037274330302411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73171170766064880806429 27439189037274330302411)
              ·
                refine ⟨41158783555911495453617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27439189037274330302411 41158783555911495453617)
                ·
                  refine ⟨30869087666933621590213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41158783555911495453617 30869087666933621590213)
                  ·
                    refine ⟨5787953937550054048165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30869087666933621590213 5787953937550054048165)
                    ·
                      rfl

theorem cell22_16908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_16908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_16908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_16908 prefixEnd_16908 := by exact prefixLift 16908
  have htrace : WordTrace (prefixWord ++ tailWord_16908) baseStart_16908 baseEnd_16908 := by
    simpa [prefixWord, tailWord_16908, baseEnd_16908] using wordTrace_append hprefix tailTrace_16908
  have hstable : (prefixWord ++ tailWord_16908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16908).length < 2 ^ (prefixWord ++ tailWord_16908).sum := by decide
  have hdescent : baseEnd_16908 < baseStart_16908 := by decide
  rcases family_descends (prefixWord ++ tailWord_16908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17028 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_17028 : Nat := 118140960795 + 17028 * 2 ^ 59
def prefixEnd_17028 : Nat := 4983230072969 + 3 ^ 40 * 17028 * 2
def baseEnd_17028 : Nat := 5829032389909741047797

theorem tailTrace_17028 : CollatzResearch.WordTrace tailWord_17028 prefixEnd_17028 5829032389909741047797 := by
  unfold tailWord_17028
  simp only [CollatzResearch.WordTrace]
  refine ⟨310531091158969497989869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 414041454878625997319825 310531091158969497989869)
  ·
    refine ⟨116449159184613561746201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 310531091158969497989869 116449159184613561746201)
    ·
      refine ⟨87336869388460171309651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116449159184613561746201 87336869388460171309651)
      ·
        refine ⟨131005304082690256964477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87336869388460171309651 131005304082690256964477)
        ·
          refine ⟨49126989031008846361679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131005304082690256964477 49126989031008846361679)
          ·
            refine ⟨73690483546513269542519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49126989031008846361679 73690483546513269542519)
            ·
              refine ⟨110535725319769904313779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73690483546513269542519 110535725319769904313779)
              ·
                refine ⟨165803587979654856470669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110535725319769904313779 165803587979654856470669)
                ·
                  refine ⟨62176345492370571176501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165803587979654856470669 62176345492370571176501)
                  ·
                    refine ⟨5829032389909741047797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62176345492370571176501 5829032389909741047797)
                    ·
                      rfl

theorem cell22_17028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_17028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17028 prefixEnd_17028 := by exact prefixLift 17028
  have htrace : WordTrace (prefixWord ++ tailWord_17028) baseStart_17028 baseEnd_17028 := by
    simpa [prefixWord, tailWord_17028, baseEnd_17028] using wordTrace_append hprefix tailTrace_17028
  have hstable : (prefixWord ++ tailWord_17028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17028).length < 2 ^ (prefixWord ++ tailWord_17028).sum := by decide
  have hdescent : baseEnd_17028 < baseStart_17028 := by decide
  rcases family_descends (prefixWord ++ tailWord_17028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17077 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 2, 4]
def baseStart_17077 : Nat := 118140960795 + 17077 * 2 ^ 59
def prefixEnd_17077 : Nat := 4983230072969 + 3 ^ 40 * 17077 * 2
def baseEnd_17077 : Nat := 5845806091289946572647

theorem tailTrace_17077 : CollatzResearch.WordTrace tailWord_17077 prefixEnd_17077 5845806091289946572647 := by
  unfold tailWord_17077
  simp only [CollatzResearch.WordTrace]
  refine ⟨622849359140420364513485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 415232906093613576342323 622849359140420364513485)
  ·
    refine ⟨233568509677657636692557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 622849359140420364513485 233568509677657636692557)
    ·
      refine ⟨87588191129121613759709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233568509677657636692557 87588191129121613759709)
      ·
        refine ⟨32845571673420605159891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87588191129121613759709 32845571673420605159891)
        ·
          refine ⟨49268357510130907739837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32845571673420605159891 49268357510130907739837)
          ·
            refine ⟨18475634066299090402439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49268357510130907739837 18475634066299090402439)
            ·
              refine ⟨27713451099448635603659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18475634066299090402439 27713451099448635603659)
              ·
                refine ⟨41570176649172953405489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27713451099448635603659 41570176649172953405489)
                ·
                  refine ⟨31177632486879715054117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41570176649172953405489 31177632486879715054117)
                  ·
                    refine ⟨5845806091289946572647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31177632486879715054117 5845806091289946572647)
                    ·
                      rfl

theorem cell22_17077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_17077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17077 prefixEnd_17077 := by exact prefixLift 17077
  have htrace : WordTrace (prefixWord ++ tailWord_17077) baseStart_17077 baseEnd_17077 := by
    simpa [prefixWord, tailWord_17077, baseEnd_17077] using wordTrace_append hprefix tailTrace_17077
  have hstable : (prefixWord ++ tailWord_17077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17077).length < 2 ^ (prefixWord ++ tailWord_17077).sum := by decide
  have hdescent : baseEnd_17077 < baseStart_17077 := by decide
  rcases family_descends (prefixWord ++ tailWord_17077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17210 : List Nat := [3, 1, 1, 1, 7, 9]
def baseStart_17210 : Nat := 118140960795 + 17210 * 2 ^ 59
def prefixEnd_17210 : Nat := 4983230072969 + 3 ^ 40 * 17210 * 2
def baseEnd_17210 : Nat := 72732527275579419719

theorem tailTrace_17210 : CollatzResearch.WordTrace tailWord_17210 prefixEnd_17210 72732527275579419719 := by
  unfold tailWord_17210
  simp only [CollatzResearch.WordTrace]
  refine ⟨156925066914646019776271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 418466845105722719403389 156925066914646019776271)
  ·
    refine ⟨235387600371969029664407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156925066914646019776271 235387600371969029664407)
    ·
      refine ⟨353081400557953544496611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235387600371969029664407 353081400557953544496611)
      ·
        refine ⟨529622100836930316744917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353081400557953544496611 529622100836930316744917)
        ·
          refine ⟨12413017988365554298709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 529622100836930316744917 12413017988365554298709)
          ·
            refine ⟨72732527275579419719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 12413017988365554298709 72732527275579419719)
            ·
              rfl

theorem cell22_17210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 9].length) (baseStart_17210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17210 prefixEnd_17210 := by exact prefixLift 17210
  have htrace : WordTrace (prefixWord ++ tailWord_17210) baseStart_17210 baseEnd_17210 := by
    simpa [prefixWord, tailWord_17210, baseEnd_17210] using wordTrace_append hprefix tailTrace_17210
  have hstable : (prefixWord ++ tailWord_17210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17210).length < 2 ^ (prefixWord ++ tailWord_17210).sum := by decide
  have hdescent : baseEnd_17210 < baseStart_17210 := by decide
  rcases family_descends (prefixWord ++ tailWord_17210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17242 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 3, 3]
def baseStart_17242 : Nat := 118140960795 + 17242 * 2 ^ 59
def prefixEnd_17242 : Nat := 4983230072969 + 3 ^ 40 * 17242 * 2
def baseEnd_17242 : Nat := 5902288963284516197141

theorem tailTrace_17242 : CollatzResearch.WordTrace tailWord_17242 prefixEnd_17242 5902288963284516197141 := by
  unfold tailWord_17242
  simp only [CollatzResearch.WordTrace]
  refine ⟨157216850885663386067495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 419244935695102362846653 157216850885663386067495)
  ·
    refine ⟨235825276328495079101243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157216850885663386067495 235825276328495079101243)
    ·
      refine ⟨353737914492742618651865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235825276328495079101243 353737914492742618651865)
      ·
        refine ⟨265303435869556963988899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353737914492742618651865 265303435869556963988899)
        ·
          refine ⟨397955153804335445983349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265303435869556963988899 397955153804335445983349)
          ·
            refine ⟨37308295669156448060939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 397955153804335445983349 37308295669156448060939)
            ·
              refine ⟨55962443503734672091409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37308295669156448060939 55962443503734672091409)
              ·
                refine ⟨41971832627801004068557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55962443503734672091409 41971832627801004068557)
                ·
                  refine ⟨15739437235425376525709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41971832627801004068557 15739437235425376525709)
                  ·
                    refine ⟨5902288963284516197141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15739437235425376525709 5902288963284516197141)
                    ·
                      rfl

theorem cell22_17242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_17242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17242 prefixEnd_17242 := by exact prefixLift 17242
  have htrace : WordTrace (prefixWord ++ tailWord_17242) baseStart_17242 baseEnd_17242 := by
    simpa [prefixWord, tailWord_17242, baseEnd_17242] using wordTrace_append hprefix tailTrace_17242
  have hstable : (prefixWord ++ tailWord_17242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17242).length < 2 ^ (prefixWord ++ tailWord_17242).sum := by decide
  have hdescent : baseEnd_17242 < baseStart_17242 := by decide
  rcases family_descends (prefixWord ++ tailWord_17242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17315 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 1, 5]
def baseStart_17315 : Nat := 118140960795 + 17315 * 2 ^ 59
def prefixEnd_17315 : Nat := 4983230072969 + 3 ^ 40 * 17315 * 2
def baseEnd_17315 : Nat := 5927278355136659121917

theorem tailTrace_17315 : CollatzResearch.WordTrace tailWord_17315 prefixEnd_17315 5927278355136659121917 := by
  unfold tailWord_17315
  simp only [CollatzResearch.WordTrace]
  refine ⟨631529932278187011677399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 421019954852124674451599 631529932278187011677399)
  ·
    refine ⟨947294898417280517516099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 631529932278187011677399 947294898417280517516099)
    ·
      refine ⟨1420942347625920776274149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 947294898417280517516099 1420942347625920776274149)
      ·
        refine ⟨266426690179860145551403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1420942347625920776274149 266426690179860145551403)
        ·
          refine ⟨399640035269790218327105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266426690179860145551403 399640035269790218327105)
          ·
            refine ⟨299730026452342663745329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399640035269790218327105 299730026452342663745329)
            ·
              refine ⟨224797519839256997808997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299730026452342663745329 224797519839256997808997)
              ·
                refine ⟨42149534969860687089187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 224797519839256997808997 42149534969860687089187)
                ·
                  refine ⟨63224302454791030633781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42149534969860687089187 63224302454791030633781)
                  ·
                    refine ⟨5927278355136659121917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63224302454791030633781 5927278355136659121917)
                    ·
                      rfl

theorem cell22_17315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 5].length) (baseStart_17315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17315 prefixEnd_17315 := by exact prefixLift 17315
  have htrace : WordTrace (prefixWord ++ tailWord_17315) baseStart_17315 baseEnd_17315 := by
    simpa [prefixWord, tailWord_17315, baseEnd_17315] using wordTrace_append hprefix tailTrace_17315
  have hstable : (prefixWord ++ tailWord_17315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17315).length < 2 ^ (prefixWord ++ tailWord_17315).sum := by decide
  have hdescent : baseEnd_17315 < baseStart_17315 := by decide
  rcases family_descends (prefixWord ++ tailWord_17315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17362 : List Nat := [3, 2, 2, 3, 1, 1, 2, 8]
def baseStart_17362 : Nat := 118140960795 + 17362 * 2 ^ 59
def prefixEnd_17362 : Nat := 4983230072969 + 3 ^ 40 * 17362 * 2
def baseEnd_17362 : Nat := 660374157293800355197

theorem tailTrace_17362 : CollatzResearch.WordTrace tailWord_17362 prefixEnd_17362 660374157293800355197 := by
  unfold tailWord_17362
  simp only [CollatzResearch.WordTrace]
  refine ⟨158311040776978509659585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 422162775405276025758893 158311040776978509659585)
  ·
    refine ⟨118733280582733882244689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 158311040776978509659585 118733280582733882244689)
    ·
      refine ⟨89049960437050411683517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118733280582733882244689 89049960437050411683517)
      ·
        refine ⟨33393735163893904381319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89049960437050411683517 33393735163893904381319)
        ·
          refine ⟨50090602745840856571979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33393735163893904381319 50090602745840856571979)
          ·
            refine ⟨75135904118761284857969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50090602745840856571979 75135904118761284857969)
            ·
              refine ⟨56351928089070963643477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75135904118761284857969 56351928089070963643477)
              ·
                refine ⟨660374157293800355197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 56351928089070963643477 660374157293800355197)
                ·
                  rfl

theorem cell22_17362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_17362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17362 prefixEnd_17362 := by exact prefixLift 17362
  have htrace : WordTrace (prefixWord ++ tailWord_17362) baseStart_17362 baseEnd_17362 := by
    simpa [prefixWord, tailWord_17362, baseEnd_17362] using wordTrace_append hprefix tailTrace_17362
  have hstable : (prefixWord ++ tailWord_17362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17362).length < 2 ^ (prefixWord ++ tailWord_17362).sum := by decide
  have hdescent : baseEnd_17362 < baseStart_17362 := by decide
  rcases family_descends (prefixWord ++ tailWord_17362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17364 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_17364 : Nat := 118140960795 + 17364 * 2 ^ 59
def prefixEnd_17364 : Nat := 4983230072969 + 3 ^ 40 * 17364 * 2
def baseEnd_17364 : Nat := 5944052056516864646767

theorem tailTrace_17364 : CollatzResearch.WordTrace tailWord_17364 prefixEnd_17364 5944052056516864646767 := by
  unfold tailWord_17364
  simp only [CollatzResearch.WordTrace]
  refine ⟨316658554550334190105573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 422211406067112253474097 316658554550334190105573)
  ·
    refine ⟨59373478978187660644795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 316658554550334190105573 59373478978187660644795)
    ·
      refine ⟨89060218467281490967193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59373478978187660644795 89060218467281490967193)
      ·
        refine ⟨66795163850461118225395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89060218467281490967193 66795163850461118225395)
        ·
          refine ⟨100192745775691677338093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66795163850461118225395 100192745775691677338093)
          ·
            refine ⟨37572279665884379001785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100192745775691677338093 37572279665884379001785)
            ·
              refine ⟨28179209749413284251339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37572279665884379001785 28179209749413284251339)
              ·
                refine ⟨42268814624119926377009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28179209749413284251339 42268814624119926377009)
                ·
                  refine ⟨31701610968089944782757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42268814624119926377009 31701610968089944782757)
                  ·
                    refine ⟨5944052056516864646767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31701610968089944782757 5944052056516864646767)
                    ·
                      rfl

theorem cell22_17364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_17364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17364 prefixEnd_17364 := by exact prefixLift 17364
  have htrace : WordTrace (prefixWord ++ tailWord_17364) baseStart_17364 baseEnd_17364 := by
    simpa [prefixWord, tailWord_17364, baseEnd_17364] using wordTrace_append hprefix tailTrace_17364
  have hstable : (prefixWord ++ tailWord_17364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17364).length < 2 ^ (prefixWord ++ tailWord_17364).sum := by decide
  have hdescent : baseEnd_17364 < baseStart_17364 := by decide
  rcases family_descends (prefixWord ++ tailWord_17364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17452 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 6]
def baseStart_17452 : Nat := 118140960795 + 17452 * 2 ^ 59
def prefixEnd_17452 : Nat := 4983230072969 + 3 ^ 40 * 17452 * 2
def baseEnd_17452 : Nat := 1991392084971322815499

theorem tailTrace_17452 : CollatzResearch.WordTrace tailWord_17452 prefixEnd_17452 1991392084971322815499 := by
  unfold tailWord_17452
  simp only [CollatzResearch.WordTrace]
  refine ⟨318263366390929704707305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 424351155187906272943073 318263366390929704707305)
  ·
    refine ⟨238697524793197278530479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 318263366390929704707305 238697524793197278530479)
    ·
      refine ⟨358046287189795917795719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238697524793197278530479 358046287189795917795719)
      ·
        refine ⟨537069430784693876693579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358046287189795917795719 537069430784693876693579)
        ·
          refine ⟨805604146177040815040369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537069430784693876693579 805604146177040815040369)
          ·
            refine ⟨604203109632780611280277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 805604146177040815040369 604203109632780611280277)
            ·
              refine ⟨28322020764036591153763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 604203109632780611280277 28322020764036591153763)
              ·
                refine ⟨42483031146054886730645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28322020764036591153763 42483031146054886730645)
                ·
                  refine ⟨1991392084971322815499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42483031146054886730645 1991392084971322815499)
                  ·
                    rfl

theorem cell22_17452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_17452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17452 prefixEnd_17452 := by exact prefixLift 17452
  have htrace : WordTrace (prefixWord ++ tailWord_17452) baseStart_17452 baseEnd_17452 := by
    simpa [prefixWord, tailWord_17452, baseEnd_17452] using wordTrace_append hprefix tailTrace_17452
  have hstable : (prefixWord ++ tailWord_17452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17452).length < 2 ^ (prefixWord ++ tailWord_17452).sum := by decide
  have hdescent : baseEnd_17452 < baseStart_17452 := by decide
  rcases family_descends (prefixWord ++ tailWord_17452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17467 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 8, 3]
def baseStart_17467 : Nat := 118140960795 + 17467 * 2 ^ 59
def prefixEnd_17467 : Nat := 4983230072969 + 3 ^ 40 * 17467 * 2
def baseEnd_17467 : Nat := 5979311061458929321451

theorem tailTrace_17467 : CollatzResearch.WordTrace tailWord_17467 prefixEnd_17467 5979311061458929321451 := by
  unfold tailWord_17467
  simp only [CollatzResearch.WordTrace]
  refine ⟨637073827727516971210655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 424715885151677980807103 637073827727516971210655)
  ·
    refine ⟨955610741591275456815983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 637073827727516971210655 955610741591275456815983)
    ·
      refine ⟨1433416112386913185223975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 955610741591275456815983 1433416112386913185223975)
      ·
        refine ⟨2150124168580369777835963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433416112386913185223975 2150124168580369777835963)
        ·
          refine ⟨3225186252870554666753945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2150124168580369777835963 3225186252870554666753945)
          ·
            refine ⟨2418889689652916000065459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3225186252870554666753945 2418889689652916000065459)
            ·
              refine ⟨3628334534479374000098189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2418889689652916000065459 3628334534479374000098189)
              ·
                refine ⟨1360625450429765250036821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3628334534479374000098189 1360625450429765250036821)
                ·
                  refine ⟨15944829497223811523869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1360625450429765250036821 15944829497223811523869)
                  ·
                    refine ⟨5979311061458929321451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15944829497223811523869 5979311061458929321451)
                    ·
                      rfl

theorem cell22_17467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 3].length) (baseStart_17467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17467 prefixEnd_17467 := by exact prefixLift 17467
  have htrace : WordTrace (prefixWord ++ tailWord_17467) baseStart_17467 baseEnd_17467 := by
    simpa [prefixWord, tailWord_17467, baseEnd_17467] using wordTrace_append hprefix tailTrace_17467
  have hstable : (prefixWord ++ tailWord_17467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17467).length < 2 ^ (prefixWord ++ tailWord_17467).sum := by decide
  have hdescent : baseEnd_17467 < baseStart_17467 := by decide
  rcases family_descends (prefixWord ++ tailWord_17467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17482 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_17482 : Nat := 118140960795 + 17482 * 2 ^ 59
def prefixEnd_17482 : Nat := 4983230072969 + 3 ^ 40 * 17482 * 2
def baseEnd_17482 : Nat := 5984445868003890196405

theorem tailTrace_17482 : CollatzResearch.WordTrace tailWord_17482 prefixEnd_17482 5984445868003890196405 := by
  unfold tailWord_17482
  simp only [CollatzResearch.WordTrace]
  refine ⟨159405230668293633251675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 425080615115449688671133 159405230668293633251675)
  ·
    refine ⟨239107846002440449877513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159405230668293633251675 239107846002440449877513)
    ·
      refine ⟨179330884501830337408135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239107846002440449877513 179330884501830337408135)
      ·
        refine ⟨268996326752745506112203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179330884501830337408135 268996326752745506112203)
        ·
          refine ⟨403494490129118259168305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268996326752745506112203 403494490129118259168305)
          ·
            refine ⟨302620867596838694376229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403494490129118259168305 302620867596838694376229)
            ·
              refine ⟨56741412674407255195543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 302620867596838694376229 56741412674407255195543)
              ·
                refine ⟨85112119011610882793315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56741412674407255195543 85112119011610882793315)
                ·
                  refine ⟨127668178517416324189973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85112119011610882793315 127668178517416324189973)
                  ·
                    refine ⟨5984445868003890196405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 127668178517416324189973 5984445868003890196405)
                    ·
                      rfl

theorem cell22_17482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_17482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17482 prefixEnd_17482 := by exact prefixLift 17482
  have htrace : WordTrace (prefixWord ++ tailWord_17482) baseStart_17482 baseEnd_17482 := by
    simpa [prefixWord, tailWord_17482, baseEnd_17482] using wordTrace_append hprefix tailTrace_17482
  have hstable : (prefixWord ++ tailWord_17482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17482).length < 2 ^ (prefixWord ++ tailWord_17482).sum := by decide
  have hdescent : baseEnd_17482 < baseStart_17482 := by decide
  rcases family_descends (prefixWord ++ tailWord_17482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17514 : List Nat := [3, 1, 3, 2, 2, 2, 2, 7]
def baseStart_17514 : Nat := 118140960795 + 17514 * 2 ^ 59
def prefixEnd_17514 : Nat := 4983230072969 + 3 ^ 40 * 17514 * 2
def baseEnd_17514 : Nat := 666155569107385932923

theorem tailTrace_17514 : CollatzResearch.WordTrace tailWord_17514 prefixEnd_17514 666155569107385932923 := by
  unfold tailWord_17514
  simp only [CollatzResearch.WordTrace]
  refine ⟨159697014639310999542899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 425858705704829332114397 159697014639310999542899)
  ·
    refine ⟨239545521958966499314349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159697014639310999542899 239545521958966499314349)
    ·
      refine ⟨89829570734612437242881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239545521958966499314349 89829570734612437242881)
      ·
        refine ⟨67372178050959327932161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89829570734612437242881 67372178050959327932161)
        ·
          refine ⟨50529133538219495949121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67372178050959327932161 50529133538219495949121)
          ·
            refine ⟨37896850153664621961841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50529133538219495949121 37896850153664621961841)
            ·
              refine ⟨28422637615248466471381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37896850153664621961841 28422637615248466471381)
              ·
                refine ⟨666155569107385932923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28422637615248466471381 666155569107385932923)
                ·
                  rfl

theorem cell22_17514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_17514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17514 prefixEnd_17514 := by exact prefixLift 17514
  have htrace : WordTrace (prefixWord ++ tailWord_17514) baseStart_17514 baseEnd_17514 := by
    simpa [prefixWord, tailWord_17514, baseEnd_17514] using wordTrace_append hprefix tailTrace_17514
  have hstable : (prefixWord ++ tailWord_17514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17514).length < 2 ^ (prefixWord ++ tailWord_17514).sum := by decide
  have hdescent : baseEnd_17514 < baseStart_17514 := by decide
  rcases family_descends (prefixWord ++ tailWord_17514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17518 : List Nat := [4, 1, 2, 2, 1, 2, 4, 1, 2, 3]
def baseStart_17518 : Nat := 118140960795 + 17518 * 2 ^ 59
def prefixEnd_17518 : Nat := 4983230072969 + 3 ^ 40 * 17518 * 2
def baseEnd_17518 : Nat := 5996769403711796296295

theorem tailTrace_17518 : CollatzResearch.WordTrace tailWord_17518 prefixEnd_17518 5996769403711796296295 := by
  unfold tailWord_17518
  simp only [CollatzResearch.WordTrace]
  refine ⟨79866743817844085164651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 425955967028501787544805 79866743817844085164651)
  ·
    refine ⟨119800115726766127746977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79866743817844085164651 119800115726766127746977)
    ·
      refine ⟨89850086795074595810233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119800115726766127746977 89850086795074595810233)
      ·
        refine ⟨67387565096305946857675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89850086795074595810233 67387565096305946857675)
        ·
          refine ⟨101081347644458920286513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67387565096305946857675 101081347644458920286513)
          ·
            refine ⟨75811010733344190214885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101081347644458920286513 75811010733344190214885)
            ·
              refine ⟨14214564512502035665291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75811010733344190214885 14214564512502035665291)
              ·
                refine ⟨21321846768753053497937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14214564512502035665291 21321846768753053497937)
                ·
                  refine ⟨15991385076564790123453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21321846768753053497937 15991385076564790123453)
                  ·
                    refine ⟨5996769403711796296295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15991385076564790123453 5996769403711796296295)
                    ·
                      rfl

theorem cell22_17518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_17518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17518 prefixEnd_17518 := by exact prefixLift 17518
  have htrace : WordTrace (prefixWord ++ tailWord_17518) baseStart_17518 baseEnd_17518 := by
    simpa [prefixWord, tailWord_17518, baseEnd_17518] using wordTrace_append hprefix tailTrace_17518
  have hstable : (prefixWord ++ tailWord_17518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17518).length < 2 ^ (prefixWord ++ tailWord_17518).sum := by decide
  have hdescent : baseEnd_17518 < baseStart_17518 := by decide
  rcases family_descends (prefixWord ++ tailWord_17518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17559 : List Nat := [1, 1, 3, 3, 3, 1, 1, 4, 5]
def baseStart_17559 : Nat := 118140960795 + 17559 * 2 ^ 59
def prefixEnd_17559 : Nat := 4983230072969 + 3 ^ 40 * 17559 * 2
def baseEnd_17559 : Nat := 2003601513867118673723

theorem tailTrace_17559 : CollatzResearch.WordTrace tailWord_17559 prefixEnd_17559 2003601513867118673723 := by
  unfold tailWord_17559
  simp only [CollatzResearch.WordTrace]
  refine ⟨640429343394216683559731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 426952895596144455706487 640429343394216683559731)
  ·
    refine ⟨960644015091325025339597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 640429343394216683559731 960644015091325025339597)
    ·
      refine ⟨360241505659246884502349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 960644015091325025339597 360241505659246884502349)
      ·
        refine ⟨135090564622217581688381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 360241505659246884502349 135090564622217581688381)
        ·
          refine ⟨50658961733331593133143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135090564622217581688381 50658961733331593133143)
          ·
            refine ⟨75988442599997389699715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50658961733331593133143 75988442599997389699715)
            ·
              refine ⟨113982663899996084549573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75988442599997389699715 113982663899996084549573)
              ·
                refine ⟨21371749481249265853045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113982663899996084549573 21371749481249265853045)
                ·
                  refine ⟨2003601513867118673723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21371749481249265853045 2003601513867118673723)
                  ·
                    rfl

theorem cell22_17559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 5].length) (baseStart_17559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17559 prefixEnd_17559 := by exact prefixLift 17559
  have htrace : WordTrace (prefixWord ++ tailWord_17559) baseStart_17559 baseEnd_17559 := by
    simpa [prefixWord, tailWord_17559, baseEnd_17559] using wordTrace_append hprefix tailTrace_17559
  have hstable : (prefixWord ++ tailWord_17559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17559).length < 2 ^ (prefixWord ++ tailWord_17559).sum := by decide
  have hdescent : baseEnd_17559 < baseStart_17559 := by decide
  rcases family_descends (prefixWord ++ tailWord_17559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17587 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 8]
def baseStart_17587 : Nat := 118140960795 + 17587 * 2 ^ 59
def prefixEnd_17587 : Nat := 4983230072969 + 3 ^ 40 * 17587 * 2
def baseEnd_17587 : Nat := 2006796504606205440361

theorem tailTrace_17587 : CollatzResearch.WordTrace tailWord_17587 prefixEnd_17587 2006796504606205440361 := by
  unfold tailWord_17587
  simp only [CollatzResearch.WordTrace]
  refine ⟨641450587292777465579015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 427633724861851643719343 641450587292777465579015)
  ·
    refine ⟨962175880939166198368523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 641450587292777465579015 962175880939166198368523)
    ·
      refine ⟨1443263821408749297552785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 962175880939166198368523 1443263821408749297552785)
      ·
        refine ⟨1082447866056561973164589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1443263821408749297552785 1082447866056561973164589)
        ·
          refine ⟨405917949771210739936721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1082447866056561973164589 405917949771210739936721)
          ·
            refine ⟨304438462328408054952541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405917949771210739936721 304438462328408054952541)
            ·
              refine ⟨114164423373153020607203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 304438462328408054952541 114164423373153020607203)
              ·
                refine ⟨171246635059729530910805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114164423373153020607203 171246635059729530910805)
                ·
                  refine ⟨2006796504606205440361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 171246635059729530910805 2006796504606205440361)
                  ·
                    rfl

theorem cell22_17587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 8].length) (baseStart_17587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17587 prefixEnd_17587 := by exact prefixLift 17587
  have htrace : WordTrace (prefixWord ++ tailWord_17587) baseStart_17587 baseEnd_17587 := by
    simpa [prefixWord, tailWord_17587, baseEnd_17587] using wordTrace_append hprefix tailTrace_17587
  have hstable : (prefixWord ++ tailWord_17587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17587).length < 2 ^ (prefixWord ++ tailWord_17587).sum := by decide
  have hdescent : baseEnd_17587 < baseStart_17587 := by decide
  rcases family_descends (prefixWord ++ tailWord_17587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17619 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 4, 3]
def baseStart_17619 : Nat := 118140960795 + 17619 * 2 ^ 59
def prefixEnd_17619 : Nat := 4983230072969 + 3 ^ 40 * 17619 * 2
def baseEnd_17619 : Nat := 6031343767781199520985

theorem tailTrace_17619 : CollatzResearch.WordTrace tailWord_17619 prefixEnd_17619 6031343767781199520985 := by
  unfold tailWord_17619
  simp only [CollatzResearch.WordTrace]
  refine ⟨642617723176846930743911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 428411815451231287162607 642617723176846930743911)
  ·
    refine ⟨963926584765270396115867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 642617723176846930743911 963926584765270396115867)
    ·
      refine ⟨1445889877147905594173801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 963926584765270396115867 1445889877147905594173801)
      ·
        refine ⟨1084417407860929195630351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1445889877147905594173801 1084417407860929195630351)
        ·
          refine ⟨1626626111791393793445527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1084417407860929195630351 1626626111791393793445527)
          ·
            refine ⟨2439939167687090690168291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1626626111791393793445527 2439939167687090690168291)
            ·
              refine ⟨3659908751530636035252437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2439939167687090690168291 3659908751530636035252437)
              ·
                refine ⟨85779111363999282076229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3659908751530636035252437 85779111363999282076229)
                ·
                  refine ⟨16083583380749865389293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85779111363999282076229 16083583380749865389293)
                  ·
                    refine ⟨6031343767781199520985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16083583380749865389293 6031343767781199520985)
                    ·
                      rfl

theorem cell22_17619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 3].length) (baseStart_17619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17619 prefixEnd_17619 := by exact prefixLift 17619
  have htrace : WordTrace (prefixWord ++ tailWord_17619) baseStart_17619 baseEnd_17619 := by
    simpa [prefixWord, tailWord_17619, baseEnd_17619] using wordTrace_append hprefix tailTrace_17619
  have hstable : (prefixWord ++ tailWord_17619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17619).length < 2 ^ (prefixWord ++ tailWord_17619).sum := by decide
  have hdescent : baseEnd_17619 < baseStart_17619 := by decide
  rcases family_descends (prefixWord ++ tailWord_17619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17621 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 6]
def baseStart_17621 : Nat := 118140960795 + 17621 * 2 ^ 59
def prefixEnd_17621 : Nat := 4983230072969 + 3 ^ 40 * 17621 * 2
def baseEnd_17621 : Nat := 2010676136217953656993

theorem tailTrace_17621 : CollatzResearch.WordTrace tailWord_17621 prefixEnd_17621 2010676136217953656993 := by
  unfold tailWord_17621
  simp only [CollatzResearch.WordTrace]
  refine ⟨642690669169601272316717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 428460446113067514877811 642690669169601272316717)
  ·
    refine ⟨241009000938600477118769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 642690669169601272316717 241009000938600477118769)
    ·
      refine ⟨180756750703950357839077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241009000938600477118769 180756750703950357839077)
      ·
        refine ⟨33891890756990692094827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180756750703950357839077 33891890756990692094827)
        ·
          refine ⟨50837836135486038142241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33891890756990692094827 50837836135486038142241)
          ·
            refine ⟨38128377101614528606681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50837836135486038142241 38128377101614528606681)
            ·
              refine ⟨28596282826210896455011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38128377101614528606681 28596282826210896455011)
              ·
                refine ⟨42894424239316344682517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28596282826210896455011 42894424239316344682517)
                ·
                  refine ⟨2010676136217953656993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42894424239316344682517 2010676136217953656993)
                  ·
                    rfl

theorem cell22_17621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_17621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17621 prefixEnd_17621 := by exact prefixLift 17621
  have htrace : WordTrace (prefixWord ++ tailWord_17621) baseStart_17621 baseEnd_17621 := by
    simpa [prefixWord, tailWord_17621, baseEnd_17621] using wordTrace_append hprefix tailTrace_17621
  have hstable : (prefixWord ++ tailWord_17621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17621).length < 2 ^ (prefixWord ++ tailWord_17621).sum := by decide
  have hdescent : baseEnd_17621 < baseStart_17621 := by decide
  rcases family_descends (prefixWord ++ tailWord_17621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17636 : List Nat := [2, 3, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_17636 : Nat := 118140960795 + 17636 * 2 ^ 59
def prefixEnd_17636 : Nat := 4983230072969 + 3 ^ 40 * 17636 * 2
def baseEnd_17636 : Nat := 6037163215198821845933

theorem tailTrace_17636 : CollatzResearch.WordTrace tailWord_17636 prefixEnd_17636 6037163215198821845933 := by
  unfold tailWord_17636
  simp only [CollatzResearch.WordTrace]
  refine ⟨321618882057629417056381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 428825176076839222741841 321618882057629417056381)
  ·
    refine ⟨120607080771611031396143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 321618882057629417056381 120607080771611031396143)
    ·
      refine ⟨180910621157416547094215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120607080771611031396143 180910621157416547094215)
      ·
        refine ⟨271365931736124820641323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180910621157416547094215 271365931736124820641323)
        ·
          refine ⟨407048897604187230961985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271365931736124820641323 407048897604187230961985)
          ·
            refine ⟨305286673203140423221489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407048897604187230961985 305286673203140423221489)
            ·
              refine ⟨228965004902355317416117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305286673203140423221489 228965004902355317416117)
              ·
                refine ⟨21465469209595811007761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228965004902355317416117 21465469209595811007761)
                ·
                  refine ⟨16099101907196858255821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21465469209595811007761 16099101907196858255821)
                  ·
                    refine ⟨6037163215198821845933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16099101907196858255821 6037163215198821845933)
                    ·
                      rfl

theorem cell22_17636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_17636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17636 prefixEnd_17636 := by exact prefixLift 17636
  have htrace : WordTrace (prefixWord ++ tailWord_17636) baseStart_17636 baseEnd_17636 := by
    simpa [prefixWord, tailWord_17636, baseEnd_17636] using wordTrace_append hprefix tailTrace_17636
  have hstable : (prefixWord ++ tailWord_17636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17636).length < 2 ^ (prefixWord ++ tailWord_17636).sum := by decide
  have hdescent : baseEnd_17636 < baseStart_17636 := by decide
  rcases family_descends (prefixWord ++ tailWord_17636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17726 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_17726 : Nat := 118140960795 + 17726 * 2 ^ 59
def prefixEnd_17726 : Nat := 4983230072969 + 3 ^ 40 * 17726 * 2
def baseEnd_17726 : Nat := 6067972054468587095657

theorem tailTrace_17726 : CollatzResearch.WordTrace tailWord_17726 prefixEnd_17726 6067972054468587095657 := by
  unfold tailWord_17726
  simp only [CollatzResearch.WordTrace]
  refine ⟨80815041723650525611129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 431013555859469469926021 80815041723650525611129)
  ·
    refine ⟨60611281292737894208347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80815041723650525611129 60611281292737894208347)
    ·
      refine ⟨90916921939106841312521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60611281292737894208347 90916921939106841312521)
      ·
        refine ⟨68187691454330130984391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90916921939106841312521 68187691454330130984391)
        ·
          refine ⟨102281537181495196476587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68187691454330130984391 102281537181495196476587)
          ·
            refine ⟨153422305772242794714881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102281537181495196476587 153422305772242794714881)
            ·
              refine ⟨115066729329182096036161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153422305772242794714881 115066729329182096036161)
              ·
                refine ⟨86300046996886572027121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115066729329182096036161 86300046996886572027121)
                ·
                  refine ⟨64725035247664929020341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86300046996886572027121 64725035247664929020341)
                  ·
                    refine ⟨6067972054468587095657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64725035247664929020341 6067972054468587095657)
                    ·
                      rfl

theorem cell22_17726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_17726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17726 prefixEnd_17726 := by exact prefixLift 17726
  have htrace : WordTrace (prefixWord ++ tailWord_17726) baseStart_17726 baseEnd_17726 := by
    simpa [prefixWord, tailWord_17726, baseEnd_17726] using wordTrace_append hprefix tailTrace_17726
  have hstable : (prefixWord ++ tailWord_17726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17726).length < 2 ^ (prefixWord ++ tailWord_17726).sum := by decide
  have hdescent : baseEnd_17726 < baseStart_17726 := by decide
  rcases family_descends (prefixWord ++ tailWord_17726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17732 : List Nat := [2, 3, 4, 1, 1, 2, 1, 4, 1, 3]
def baseStart_17732 : Nat := 118140960795 + 17732 * 2 ^ 59
def prefixEnd_17732 : Nat := 4983230072969 + 3 ^ 40 * 17732 * 2
def baseEnd_17732 : Nat := 6070025977086571445639

theorem tailTrace_17732 : CollatzResearch.WordTrace tailWord_17732 prefixEnd_17732 6070025977086571445639 := by
  unfold tailWord_17732
  simp only [CollatzResearch.WordTrace]
  refine ⟨323369585883733614803725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 431159447844978153071633 323369585883733614803725)
  ·
    refine ⟨121263594706400105551397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 323369585883733614803725 121263594706400105551397)
    ·
      refine ⟨22736924007450019790887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121263594706400105551397 22736924007450019790887)
      ·
        refine ⟨34105386011175029686331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22736924007450019790887 34105386011175029686331)
        ·
          refine ⟨51158079016762544529497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34105386011175029686331 51158079016762544529497)
          ·
            refine ⟨38368559262571908397123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51158079016762544529497 38368559262571908397123)
            ·
              refine ⟨57552838893857862595685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38368559262571908397123 57552838893857862595685)
              ·
                refine ⟨10791157292598349236691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57552838893857862595685 10791157292598349236691)
                ·
                  refine ⟨16186735938897523855037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10791157292598349236691 16186735938897523855037)
                  ·
                    refine ⟨6070025977086571445639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16186735938897523855037 6070025977086571445639)
                    ·
                      rfl

theorem cell22_17732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_17732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17732 prefixEnd_17732 := by exact prefixLift 17732
  have htrace : WordTrace (prefixWord ++ tailWord_17732) baseStart_17732 baseEnd_17732 := by
    simpa [prefixWord, tailWord_17732, baseEnd_17732] using wordTrace_append hprefix tailTrace_17732
  have hstable : (prefixWord ++ tailWord_17732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17732).length < 2 ^ (prefixWord ++ tailWord_17732).sum := by decide
  have hdescent : baseEnd_17732 < baseStart_17732 := by decide
  rcases family_descends (prefixWord ++ tailWord_17732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17773 : List Nat := [1, 5, 1, 1, 1, 3, 1, 5, 4]
def baseStart_17773 : Nat := 118140960795 + 17773 * 2 ^ 59
def prefixEnd_17773 : Nat := 4983230072969 + 3 ^ 40 * 17773 * 2
def baseEnd_17773 : Nat := 2028020371658710390171

theorem tailTrace_17773 : CollatzResearch.WordTrace tailWord_17773 prefixEnd_17773 2028020371658710390171 := by
  unfold tailWord_17773
  simp only [CollatzResearch.WordTrace]
  refine ⟨648234564618931231849973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 432156376412620821233315 648234564618931231849973)
  ·
    refine ⟨60771990433024802985935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 648234564618931231849973 60771990433024802985935)
    ·
      refine ⟨91157985649537204478903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60771990433024802985935 91157985649537204478903)
      ·
        refine ⟨136736978474305806718355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91157985649537204478903 136736978474305806718355)
        ·
          refine ⟨205105467711458710077533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136736978474305806718355 205105467711458710077533)
          ·
            refine ⟨76914550391797016279075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205105467711458710077533 76914550391797016279075)
            ·
              refine ⟨115371825587695524418613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76914550391797016279075 115371825587695524418613)
              ·
                refine ⟨10816108648846455414245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115371825587695524418613 10816108648846455414245)
                ·
                  refine ⟨2028020371658710390171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10816108648846455414245 2028020371658710390171)
                  ·
                    rfl

theorem cell22_17773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_17773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17773 prefixEnd_17773 := by exact prefixLift 17773
  have htrace : WordTrace (prefixWord ++ tailWord_17773) baseStart_17773 baseEnd_17773 := by
    simpa [prefixWord, tailWord_17773, baseEnd_17773] using wordTrace_append hprefix tailTrace_17773
  have hstable : (prefixWord ++ tailWord_17773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17773).length < 2 ^ (prefixWord ++ tailWord_17773).sum := by decide
  have hdescent : baseEnd_17773 < baseStart_17773 := by decide
  rcases family_descends (prefixWord ++ tailWord_17773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17901 : List Nat := [1, 5, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_17901 : Nat := 118140960795 + 17901 * 2 ^ 59
def prefixEnd_17901 : Nat := 4983230072969 + 3 ^ 40 * 17901 * 2
def baseEnd_17901 : Nat := 6127878130826463970121

theorem tailTrace_17901 : CollatzResearch.WordTrace tailWord_17901 prefixEnd_17901 6127878130826463970121 := by
  unfold tailWord_17901
  simp only [CollatzResearch.WordTrace]
  refine ⟨652903108155209092509557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 435268738770139395006371 652903108155209092509557)
  ·
    refine ⟨61209666389550852422771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 652903108155209092509557 61209666389550852422771)
    ·
      refine ⟨91814499584326278634157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61209666389550852422771 91814499584326278634157)
      ·
        refine ⟨34430437344122354487809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91814499584326278634157 34430437344122354487809)
        ·
          refine ⟨25822828008091765865857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34430437344122354487809 25822828008091765865857)
          ·
            refine ⟨19367121006068824399393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25822828008091765865857 19367121006068824399393)
            ·
              refine ⟨14525340754551618299545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19367121006068824399393 14525340754551618299545)
              ·
                refine ⟨10894005565913713724659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14525340754551618299545 10894005565913713724659)
                ·
                  refine ⟨16341008348870570586989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10894005565913713724659 16341008348870570586989)
                  ·
                    refine ⟨6127878130826463970121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16341008348870570586989 6127878130826463970121)
                    ·
                      rfl

theorem cell22_17901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_17901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17901 prefixEnd_17901 := by exact prefixLift 17901
  have htrace : WordTrace (prefixWord ++ tailWord_17901) baseStart_17901 baseEnd_17901 := by
    simpa [prefixWord, tailWord_17901, baseEnd_17901] using wordTrace_append hprefix tailTrace_17901
  have hstable : (prefixWord ++ tailWord_17901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17901).length < 2 ^ (prefixWord ++ tailWord_17901).sum := by decide
  have hdescent : baseEnd_17901 < baseStart_17901 := by decide
  rcases family_descends (prefixWord ++ tailWord_17901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17944 : List Nat := [2, 1, 2, 3, 5, 1, 2, 1, 1, 4]
def baseStart_17944 : Nat := 118140960795 + 17944 * 2 ^ 59
def prefixEnd_17944 : Nat := 4983230072969 + 3 ^ 40 * 17944 * 2
def baseEnd_17944 : Nat := 6142597909588685144989

theorem tailTrace_17944 : CollatzResearch.WordTrace tailWord_17944 prefixEnd_17944 6142597909588685144989 := by
  unfold tailWord_17944
  simp only [CollatzResearch.WordTrace]
  refine ⟨327235723499713718162443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 436314297999618290883257 327235723499713718162443)
  ·
    refine ⟨490853585249570577243665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 327235723499713718162443 490853585249570577243665)
    ·
      refine ⟨368140188937177932932749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 490853585249570577243665 368140188937177932932749)
      ·
        refine ⟨138052570851441724849781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 368140188937177932932749 138052570851441724849781)
        ·
          refine ⟨12942428517322661704667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 138052570851441724849781 12942428517322661704667)
          ·
            refine ⟨19413642775983992557001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12942428517322661704667 19413642775983992557001)
            ·
              refine ⟨14560232081987994417751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19413642775983992557001 14560232081987994417751)
              ·
                refine ⟨21840348122981991626627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14560232081987994417751 21840348122981991626627)
                ·
                  refine ⟨32760522184472987439941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21840348122981991626627 32760522184472987439941)
                  ·
                    refine ⟨6142597909588685144989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32760522184472987439941 6142597909588685144989)
                    ·
                      rfl

theorem cell22_17944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_17944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17944 prefixEnd_17944 := by exact prefixLift 17944
  have htrace : WordTrace (prefixWord ++ tailWord_17944) baseStart_17944 baseEnd_17944 := by
    simpa [prefixWord, tailWord_17944, baseEnd_17944] using wordTrace_append hprefix tailTrace_17944
  have hstable : (prefixWord ++ tailWord_17944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17944).length < 2 ^ (prefixWord ++ tailWord_17944).sum := by decide
  have hdescent : baseEnd_17944 < baseStart_17944 := by decide
  rcases family_descends (prefixWord ++ tailWord_17944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17974 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_17974 : Nat := 118140960795 + 17974 * 2 ^ 59
def prefixEnd_17974 : Nat := 4983230072969 + 3 ^ 40 * 17974 * 2
def baseEnd_17974 : Nat := 6152867522678606894897

theorem tailTrace_17974 : CollatzResearch.WordTrace tailWord_17974 prefixEnd_17974 6152867522678606894897 := by
  unfold tailWord_17974
  simp only [CollatzResearch.WordTrace]
  refine ⟨40972852305671409994811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 437043757927161706611317 40972852305671409994811)
  ·
    refine ⟨61459278458507114992217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40972852305671409994811 61459278458507114992217)
    ·
      refine ⟨46094458843880336244163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61459278458507114992217 46094458843880336244163)
      ·
        refine ⟨69141688265820504366245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46094458843880336244163 69141688265820504366245)
        ·
          refine ⟨12964066549841344568671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69141688265820504366245 12964066549841344568671)
          ·
            refine ⟨19446099824762016853007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12964066549841344568671 19446099824762016853007)
            ·
              refine ⟨29169149737143025279511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19446099824762016853007 29169149737143025279511)
              ·
                refine ⟨43753724605714537919267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29169149737143025279511 43753724605714537919267)
                ·
                  refine ⟨65630586908571806878901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43753724605714537919267 65630586908571806878901)
                  ·
                    refine ⟨6152867522678606894897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65630586908571806878901 6152867522678606894897)
                    ·
                      rfl

theorem cell22_17974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_17974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17974 prefixEnd_17974 := by exact prefixLift 17974
  have htrace : WordTrace (prefixWord ++ tailWord_17974) baseStart_17974 baseEnd_17974 := by
    simpa [prefixWord, tailWord_17974, baseEnd_17974] using wordTrace_append hprefix tailTrace_17974
  have hstable : (prefixWord ++ tailWord_17974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17974).length < 2 ^ (prefixWord ++ tailWord_17974).sum := by decide
  have hdescent : baseEnd_17974 < baseStart_17974 := by decide
  rcases family_descends (prefixWord ++ tailWord_17974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17985 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 3, 3]
def baseStart_17985 : Nat := 118140960795 + 17985 * 2 ^ 59
def prefixEnd_17985 : Nat := 4983230072969 + 3 ^ 40 * 17985 * 2
def baseEnd_17985 : Nat := 6156633047478244869863

theorem tailTrace_17985 : CollatzResearch.WordTrace tailWord_17985 prefixEnd_17985 6156633047478244869863 := by
  unfold tailWord_17985
  simp only [CollatzResearch.WordTrace]
  refine ⟨655966839850891438567409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 437311226567260959044939 655966839850891438567409)
  ·
    refine ⟨491975129888168578925557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 655966839850891438567409 491975129888168578925557)
    ·
      refine ⟨46122668427015804274271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 491975129888168578925557 46122668427015804274271)
      ·
        refine ⟨69184002640523706411407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46122668427015804274271 69184002640523706411407)
        ·
          refine ⟨103776003960785559617111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69184002640523706411407 103776003960785559617111)
          ·
            refine ⟨155664005941178339425667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103776003960785559617111 155664005941178339425667)
            ·
              refine ⟨233496008911767509138501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155664005941178339425667 233496008911767509138501)
              ·
                refine ⟨43780501670956407963469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 233496008911767509138501 43780501670956407963469)
                ·
                  refine ⟨16417688126608652986301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43780501670956407963469 16417688126608652986301)
                  ·
                    refine ⟨6156633047478244869863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16417688126608652986301 6156633047478244869863)
                    ·
                      rfl

theorem cell22_17985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_17985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_17985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_17985 prefixEnd_17985 := by exact prefixLift 17985
  have htrace : WordTrace (prefixWord ++ tailWord_17985) baseStart_17985 baseEnd_17985 := by
    simpa [prefixWord, tailWord_17985, baseEnd_17985] using wordTrace_append hprefix tailTrace_17985
  have hstable : (prefixWord ++ tailWord_17985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17985).length < 2 ^ (prefixWord ++ tailWord_17985).sum := by decide
  have hdescent : baseEnd_17985 < baseStart_17985 := by decide
  rcases family_descends (prefixWord ++ tailWord_17985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18019 : List Nat := [1, 1, 1, 5, 1, 4, 3, 2, 1, 3]
def baseStart_18019 : Nat := 118140960795 + 18019 * 2 ^ 59
def prefixEnd_18019 : Nat := 4983230072969 + 3 ^ 40 * 18019 * 2
def baseEnd_18019 : Nat := 6168271942313489519759

theorem tailTrace_18019 : CollatzResearch.WordTrace tailWord_18019 prefixEnd_18019 6168271942313489519759 := by
  unfold tailWord_18019
  simp only [CollatzResearch.WordTrace]
  refine ⟨657206921727715245305111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 438137947818476830203407 657206921727715245305111)
  ·
    refine ⟨985810382591572867957667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 657206921727715245305111 985810382591572867957667)
    ·
      refine ⟨1478715573887359301936501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 985810382591572867957667 1478715573887359301936501)
      ·
        refine ⟨138629585051939934556547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1478715573887359301936501 138629585051939934556547)
        ·
          refine ⟨207944377577909901834821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138629585051939934556547 207944377577909901834821)
          ·
            refine ⟨38989570795858106594029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207944377577909901834821 38989570795858106594029)
            ·
              refine ⟨14621089048446789972761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38989570795858106594029 14621089048446789972761)
              ·
                refine ⟨10965816786335092479571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14621089048446789972761 10965816786335092479571)
                ·
                  refine ⟨16448725179502638719357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10965816786335092479571 16448725179502638719357)
                  ·
                    refine ⟨6168271942313489519759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16448725179502638719357 6168271942313489519759)
                    ·
                      rfl

theorem cell22_18019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 1, 3].length) (baseStart_18019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18019 prefixEnd_18019 := by exact prefixLift 18019
  have htrace : WordTrace (prefixWord ++ tailWord_18019) baseStart_18019 baseEnd_18019 := by
    simpa [prefixWord, tailWord_18019, baseEnd_18019] using wordTrace_append hprefix tailTrace_18019
  have hstable : (prefixWord ++ tailWord_18019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18019).length < 2 ^ (prefixWord ++ tailWord_18019).sum := by decide
  have hdescent : baseEnd_18019 < baseStart_18019 := by decide
  rcases family_descends (prefixWord ++ tailWord_18019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18028 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_18028 : Nat := 118140960795 + 18028 * 2 ^ 59
def prefixEnd_18028 : Nat := 4983230072969 + 3 ^ 40 * 18028 * 2
def baseEnd_18028 : Nat := 6171352826240466044731

theorem tailTrace_18028 : CollatzResearch.WordTrace tailWord_18028 prefixEnd_18028 6171352826240466044731 := by
  unfold tailWord_18028
  simp only [CollatzResearch.WordTrace]
  refine ⟨328767589347554891191369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 438356785796739854921825 328767589347554891191369)
  ·
    refine ⟨246575692010666168393527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 328767589347554891191369 246575692010666168393527)
    ·
      refine ⟨369863538015999252590291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246575692010666168393527 369863538015999252590291)
      ·
        refine ⟨554795307023998878885437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369863538015999252590291 554795307023998878885437)
        ·
          refine ⟨208048240133999579582039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 554795307023998878885437 208048240133999579582039)
          ·
            refine ⟨312072360200999369373059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208048240133999579582039 312072360200999369373059)
            ·
              refine ⟨468108540301499054059589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312072360200999369373059 468108540301499054059589)
              ·
                refine ⟨87770351306531072636173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 468108540301499054059589 87770351306531072636173)
                ·
                  refine ⟨32913881739949152238565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87770351306531072636173 32913881739949152238565)
                  ·
                    refine ⟨6171352826240466044731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32913881739949152238565 6171352826240466044731)
                    ·
                      rfl

theorem cell22_18028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_18028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18028 prefixEnd_18028 := by exact prefixLift 18028
  have htrace : WordTrace (prefixWord ++ tailWord_18028) baseStart_18028 baseEnd_18028 := by
    simpa [prefixWord, tailWord_18028, baseEnd_18028] using wordTrace_append hprefix tailTrace_18028
  have hstable : (prefixWord ++ tailWord_18028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18028).length < 2 ^ (prefixWord ++ tailWord_18028).sum := by decide
  have hdescent : baseEnd_18028 < baseStart_18028 := by decide
  rcases family_descends (prefixWord ++ tailWord_18028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18032 : List Nat := [2, 1, 1, 1, 6, 3, 2, 1, 5]
def baseStart_18032 : Nat := 118140960795 + 18032 * 2 ^ 59
def prefixEnd_18032 : Nat := 4983230072969 + 3 ^ 40 * 18032 * 2
def baseEnd_18032 : Nat := 2057574035995262981573

theorem tailTrace_18032 : CollatzResearch.WordTrace tailWord_18032 prefixEnd_18032 2057574035995262981573 := by
  unfold tailWord_18032
  simp only [CollatzResearch.WordTrace]
  refine ⟨328840535340309232764175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 438454047120412310352233 328840535340309232764175)
  ·
    refine ⟨493260803010463849146263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 328840535340309232764175 493260803010463849146263)
    ·
      refine ⟨739891204515695773719395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 493260803010463849146263 739891204515695773719395)
      ·
        refine ⟨1109836806773543660579093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739891204515695773719395 1109836806773543660579093)
        ·
          refine ⟨52023600317509859089645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1109836806773543660579093 52023600317509859089645)
          ·
            refine ⟨19508850119066197158617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52023600317509859089645 19508850119066197158617)
            ·
              refine ⟨14631637589299647868963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19508850119066197158617 14631637589299647868963)
              ·
                refine ⟨21947456383949471803445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14631637589299647868963 21947456383949471803445)
                ·
                  refine ⟨2057574035995262981573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21947456383949471803445 2057574035995262981573)
                  ·
                    rfl

theorem cell22_18032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 5].length) (baseStart_18032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18032 prefixEnd_18032 := by exact prefixLift 18032
  have htrace : WordTrace (prefixWord ++ tailWord_18032) baseStart_18032 baseEnd_18032 := by
    simpa [prefixWord, tailWord_18032, baseEnd_18032] using wordTrace_append hprefix tailTrace_18032
  have hstable : (prefixWord ++ tailWord_18032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18032).length < 2 ^ (prefixWord ++ tailWord_18032).sum := by decide
  have hdescent : baseEnd_18032 < baseStart_18032 := by decide
  rcases family_descends (prefixWord ++ tailWord_18032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18045 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_18045 : Nat := 118140960795 + 18045 * 2 ^ 59
def prefixEnd_18045 : Nat := 4983230072969 + 3 ^ 40 * 18045 * 2
def baseEnd_18045 : Nat := 6177172273658088369679

theorem tailTrace_18045 : CollatzResearch.WordTrace tailWord_18045 prefixEnd_18045 6177172273658088369679 := by
  unfold tailWord_18045
  simp only [CollatzResearch.WordTrace]
  refine ⟨658155219633521685751589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 438770146422347790501059 658155219633521685751589)
  ·
    refine ⟨123404103681285316078423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 658155219633521685751589 123404103681285316078423)
    ·
      refine ⟨185106155521927974117635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123404103681285316078423 185106155521927974117635)
      ·
        refine ⟨277659233282891961176453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185106155521927974117635 277659233282891961176453)
        ·
          refine ⟨52061106240542242720585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 277659233282891961176453 52061106240542242720585)
          ·
            refine ⟨39045829680406682040439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52061106240542242720585 39045829680406682040439)
            ·
              refine ⟨58568744520610023060659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39045829680406682040439 58568744520610023060659)
              ·
                refine ⟨87853116780915034590989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58568744520610023060659 87853116780915034590989)
                ·
                  refine ⟨32944918792843137971621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87853116780915034590989 32944918792843137971621)
                  ·
                    refine ⟨6177172273658088369679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32944918792843137971621 6177172273658088369679)
                    ·
                      rfl

theorem cell22_18045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_18045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18045 prefixEnd_18045 := by exact prefixLift 18045
  have htrace : WordTrace (prefixWord ++ tailWord_18045) baseStart_18045 baseEnd_18045 := by
    simpa [prefixWord, tailWord_18045, baseEnd_18045] using wordTrace_append hprefix tailTrace_18045
  have hstable : (prefixWord ++ tailWord_18045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18045).length < 2 ^ (prefixWord ++ tailWord_18045).sum := by decide
  have hdescent : baseEnd_18045 < baseStart_18045 := by decide
  rcases family_descends (prefixWord ++ tailWord_18045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18060 : List Nat := [2, 2, 1, 2, 1, 1, 4, 5, 4]
def baseStart_18060 : Nat := 118140960795 + 18060 * 2 ^ 59
def prefixEnd_18060 : Nat := 4983230072969 + 3 ^ 40 * 18060 * 2
def baseEnd_18060 : Nat := 2060769026734349748211

theorem tailTrace_18060 : CollatzResearch.WordTrace tailWord_18060 prefixEnd_18060 2060769026734349748211 := by
  unfold tailWord_18060
  simp only [CollatzResearch.WordTrace]
  refine ⟨329351157289589623773817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 439134876386119498365089 329351157289589623773817)
  ·
    refine ⟨247013367967192217830363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 329351157289589623773817 247013367967192217830363)
    ·
      refine ⟨370520051950788326745545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247013367967192217830363 370520051950788326745545)
      ·
        refine ⟨277890038963091245059159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 370520051950788326745545 277890038963091245059159)
        ·
          refine ⟨416835058444636867588739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277890038963091245059159 416835058444636867588739)
          ·
            refine ⟨625252587666955301383109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416835058444636867588739 625252587666955301383109)
            ·
              refine ⟨117234860187554119009333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 625252587666955301383109 117234860187554119009333)
              ·
                refine ⟨10990768142583198657125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117234860187554119009333 10990768142583198657125)
                ·
                  refine ⟨2060769026734349748211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10990768142583198657125 2060769026734349748211)
                  ·
                    rfl

theorem cell22_18060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_18060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18060 prefixEnd_18060 := by exact prefixLift 18060
  have htrace : WordTrace (prefixWord ++ tailWord_18060) baseStart_18060 baseEnd_18060 := by
    simpa [prefixWord, tailWord_18060, baseEnd_18060] using wordTrace_append hprefix tailTrace_18060
  have hstable : (prefixWord ++ tailWord_18060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18060).length < 2 ^ (prefixWord ++ tailWord_18060).sum := by decide
  have hdescent : baseEnd_18060 < baseStart_18060 := by decide
  rcases family_descends (prefixWord ++ tailWord_18060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18073 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 4, 4]
def baseStart_18073 : Nat := 118140960795 + 18073 * 2 ^ 59
def prefixEnd_18073 : Nat := 4983230072969 + 3 ^ 40 * 18073 * 2
def baseEnd_18073 : Nat := 6186757245875348669593

theorem tailTrace_18073 : CollatzResearch.WordTrace tailWord_18073 prefixEnd_18073 6186757245875348669593 := by
  unfold tailWord_18073
  simp only [CollatzResearch.WordTrace]
  refine ⟨659176463532082467770873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 439450975688054978513915 659176463532082467770873)
  ·
    refine ⟨494382347649061850828155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 659176463532082467770873 494382347649061850828155)
    ·
      refine ⟨741573521473592776242233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494382347649061850828155 741573521473592776242233)
      ·
        refine ⟨556180141105194582181675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 741573521473592776242233 556180141105194582181675)
        ·
          refine ⟨834270211657791873272513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556180141105194582181675 834270211657791873272513)
          ·
            refine ⟨625702658743343904954385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 834270211657791873272513 625702658743343904954385)
            ·
              refine ⟨469276994057507928715789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 625702658743343904954385 469276994057507928715789)
              ·
                refine ⟨175978872771565473268421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 469276994057507928715789 175978872771565473268421)
                ·
                  refine ⟨32996038644668526237829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175978872771565473268421 32996038644668526237829)
                  ·
                    refine ⟨6186757245875348669593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32996038644668526237829 6186757245875348669593)
                    ·
                      rfl

theorem cell22_18073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_18073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_18073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_18073 prefixEnd_18073 := by exact prefixLift 18073
  have htrace : WordTrace (prefixWord ++ tailWord_18073) baseStart_18073 baseEnd_18073 := by
    simpa [prefixWord, tailWord_18073, baseEnd_18073] using wordTrace_append hprefix tailTrace_18073
  have hstable : (prefixWord ++ tailWord_18073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18073).length < 2 ^ (prefixWord ++ tailWord_18073).sum := by decide
  have hdescent : baseEnd_18073 < baseStart_18073 := by decide
  rcases family_descends (prefixWord ++ tailWord_18073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
