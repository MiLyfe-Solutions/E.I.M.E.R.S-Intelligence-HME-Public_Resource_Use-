import V185TrunkScan23Chunk1363

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8078764 : List Nat := [2, 2, 1, 1, 1, 1, 6, 4, 1, 2, 2]
def baseStart_8078764 : Nat := 118140960795 + 8078764 * 2 ^ 59
def prefixEnd_8078764 : Nat := 4983230072969 + 3 ^ 40 * 8078764 * 2
def baseEnd_8078764 : Nat := 4148289026239535032396447

theorem tailTrace_8078764 : CollatzResearch.WordTrace tailWord_8078764 prefixEnd_8078764 4148289026239535032396447 := by
  unfold tailWord_8078764
  simp only [CollatzResearch.WordTrace]
  refine ⟨147328365052012622944677673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196437820069350163926236897 147328365052012622944677673)
  ·
    refine ⟨110496273789009467208508255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147328365052012622944677673 110496273789009467208508255)
    ·
      refine ⟨165744410683514200812762383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110496273789009467208508255 165744410683514200812762383)
      ·
        refine ⟨248616616025271301219143575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165744410683514200812762383 248616616025271301219143575)
        ·
          refine ⟨372924924037906951828715363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248616616025271301219143575 372924924037906951828715363)
          ·
            refine ⟨559387386056860427743073045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372924924037906951828715363 559387386056860427743073045)
            ·
              refine ⟨26221283721415332550456549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 559387386056860427743073045 26221283721415332550456549)
              ·
                refine ⟨4916490697765374853210603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26221283721415332550456549 4916490697765374853210603)
                ·
                  refine ⟨7374736046648062279815905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916490697765374853210603 7374736046648062279815905)
                  ·
                    refine ⟨5531052034986046709861929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7374736046648062279815905 5531052034986046709861929)
                    ·
                      refine ⟨4148289026239535032396447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5531052034986046709861929 4148289026239535032396447)
                      ·
                        rfl

theorem cell23_8078764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 1, 2, 2].length) (baseStart_8078764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078764 prefixEnd_8078764 := by exact prefixLift 8078764
  have htrace : WordTrace (prefixWord ++ tailWord_8078764) baseStart_8078764 baseEnd_8078764 := by
    simpa [prefixWord, tailWord_8078764, baseEnd_8078764] using wordTrace_append hprefix tailTrace_8078764
  have hstable : (prefixWord ++ tailWord_8078764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078764).length < 2 ^ (prefixWord ++ tailWord_8078764).sum := by decide
  have hdescent : baseEnd_8078764 < baseStart_8078764 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078777 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 1, 2, 4]
def baseStart_8078777 : Nat := 118140960795 + 8078777 * 2 ^ 59
def prefixEnd_8078777 : Nat := 4983230072969 + 3 ^ 40 * 8078777 * 2
def baseEnd_8078777 : Nat := 4148295701488043481533887

theorem tailTrace_8078777 : CollatzResearch.WordTrace tailWord_8078777 prefixEnd_8078777 4148295701488043481533887 := by
  unfold tailWord_8078777
  simp only [CollatzResearch.WordTrace]
  refine ⟨294657204252978149109578585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196438136168652099406385723 294657204252978149109578585)
  ·
    refine ⟨220992903189733611832183939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294657204252978149109578585 220992903189733611832183939)
    ·
      refine ⟨331489354784600417748275909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220992903189733611832183939 331489354784600417748275909)
      ·
        refine ⟨62154254022112578327801733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331489354784600417748275909 62154254022112578327801733)
        ·
          refine ⟨11653922629146108436462825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62154254022112578327801733 11653922629146108436462825)
          ·
            refine ⟨8740441971859581327347119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11653922629146108436462825 8740441971859581327347119)
            ·
              refine ⟨13110662957789371991020679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8740441971859581327347119 13110662957789371991020679)
              ·
                refine ⟨19665994436684057986531019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13110662957789371991020679 19665994436684057986531019)
                ·
                  refine ⟨29498991655026086979796529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19665994436684057986531019 29498991655026086979796529)
                  ·
                    refine ⟨22124243741269565234847397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29498991655026086979796529 22124243741269565234847397)
                    ·
                      refine ⟨4148295701488043481533887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22124243741269565234847397 4148295701488043481533887)
                      ·
                        rfl

theorem cell23_8078777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_8078777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078777 prefixEnd_8078777 := by exact prefixLift 8078777
  have htrace : WordTrace (prefixWord ++ tailWord_8078777) baseStart_8078777 baseEnd_8078777 := by
    simpa [prefixWord, tailWord_8078777, baseEnd_8078777] using wordTrace_append hprefix tailTrace_8078777
  have hstable : (prefixWord ++ tailWord_8078777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078777).length < 2 ^ (prefixWord ++ tailWord_8078777).sum := by decide
  have hdescent : baseEnd_8078777 < baseStart_8078777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078877 : List Nat := [1, 4, 2, 2, 1, 1, 3, 4, 5]
def baseStart_8078877 : Nat := 118140960795 + 8078877 * 2 ^ 59
def prefixEnd_8078877 : Nat := 4983230072969 + 3 ^ 40 * 8078877 * 2
def baseEnd_8078877 : Nat := 460927449950388121142603

theorem tailTrace_8078877 : CollatzResearch.WordTrace tailWord_8078877 prefixEnd_8078877 460927449950388121142603 := by
  unfold tailWord_8078877
  simp only [CollatzResearch.WordTrace]
  refine ⟨294660851552615866188218885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196440567701743910792145923 294660851552615866188218885)
  ·
    refine ⟨55248909666115474910291041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294660851552615866188218885 55248909666115474910291041)
    ·
      refine ⟨41436682249586606182718281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55248909666115474910291041 41436682249586606182718281)
      ·
        refine ⟨31077511687189954637038711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41436682249586606182718281 31077511687189954637038711)
        ·
          refine ⟨46616267530784931955558067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31077511687189954637038711 46616267530784931955558067)
          ·
            refine ⟨69924401296177397933337101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46616267530784931955558067 69924401296177397933337101)
            ·
              refine ⟨26221650486066524225001413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69924401296177397933337101 26221650486066524225001413)
              ·
                refine ⟨4916559466137473292187765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26221650486066524225001413 4916559466137473292187765)
                ·
                  refine ⟨460927449950388121142603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4916559466137473292187765 460927449950388121142603)
                  ·
                    rfl

theorem cell23_8078877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_8078877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078877 prefixEnd_8078877 := by exact prefixLift 8078877
  have htrace : WordTrace (prefixWord ++ tailWord_8078877) baseStart_8078877 baseEnd_8078877 := by
    simpa [prefixWord, tailWord_8078877, baseEnd_8078877] using wordTrace_append hprefix tailTrace_8078877
  have hstable : (prefixWord ++ tailWord_8078877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078877).length < 2 ^ (prefixWord ++ tailWord_8078877).sum := by decide
  have hdescent : baseEnd_8078877 < baseStart_8078877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078890 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 1, 7]
def baseStart_8078890 : Nat := 118140960795 + 8078890 * 2 ^ 59
def prefixEnd_8078890 : Nat := 4983230072969 + 3 ^ 40 * 8078890 * 2
def baseEnd_8078890 : Nat := 1382784574934000513140289

theorem tailTrace_8078890 : CollatzResearch.WordTrace tailWord_8078890 prefixEnd_8078890 1382784574934000513140289 := by
  unfold tailWord_8078890
  simp only [CollatzResearch.WordTrace]
  refine ⟨73665331425392192352110531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196440883801045846272294749 73665331425392192352110531)
  ·
    refine ⟨110497997138088288528165797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73665331425392192352110531 110497997138088288528165797)
    ·
      refine ⟨20718374463391554099031087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110497997138088288528165797 20718374463391554099031087)
      ·
        refine ⟨31077561695087331148546631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20718374463391554099031087 31077561695087331148546631)
        ·
          refine ⟨46616342542630996722819947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31077561695087331148546631 46616342542630996722819947)
          ·
            refine ⟨69924513813946495084229921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46616342542630996722819947 69924513813946495084229921)
            ·
              refine ⟨52443385360459871313172441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69924513813946495084229921 52443385360459871313172441)
              ·
                refine ⟨39332539020344903484879331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52443385360459871313172441 39332539020344903484879331)
                ·
                  refine ⟨58998808530517355227318997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39332539020344903484879331 58998808530517355227318997)
                  ·
                    refine ⟨1382784574934000513140289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58998808530517355227318997 1382784574934000513140289)
                    ·
                      rfl

theorem cell23_8078890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_8078890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078890 prefixEnd_8078890 := by exact prefixLift 8078890
  have htrace : WordTrace (prefixWord ++ tailWord_8078890) baseStart_8078890 baseEnd_8078890 := by
    simpa [prefixWord, tailWord_8078890, baseEnd_8078890] using wordTrace_append hprefix tailTrace_8078890
  have hstable : (prefixWord ++ tailWord_8078890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078890).length < 2 ^ (prefixWord ++ tailWord_8078890).sum := by decide
  have hdescent : baseEnd_8078890 < baseStart_8078890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079021 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_8079021 : Nat := 118140960795 + 8079021 * 2 ^ 59
def prefixEnd_8079021 : Nat := 4983230072969 + 3 ^ 40 * 8079021 * 2
def baseEnd_8079021 : Nat := 4148420990767740526882765

theorem tailTrace_8079021 : CollatzResearch.WordTrace tailWord_8079021 prefixEnd_8079021 4148420990767740526882765 := by
  unfold tailWord_8079021
  simp only [CollatzResearch.WordTrace]
  refine ⟨294666103664094178781460917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196444069109396119187640611 294666103664094178781460917)
  ·
    refine ⟨27624947218508829260761961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294666103664094178781460917 27624947218508829260761961)
    ·
      refine ⟨20718710413881621945571471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27624947218508829260761961 20718710413881621945571471)
      ·
        refine ⟨31078065620822432918357207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20718710413881621945571471 31078065620822432918357207)
        ·
          refine ⟨46617098431233649377535811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31078065620822432918357207 46617098431233649377535811)
          ·
            refine ⟨69925647646850474066303717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46617098431233649377535811 69925647646850474066303717)
            ·
              refine ⟨13111058933784463887431947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69925647646850474066303717 13111058933784463887431947)
              ·
                refine ⟨19666588400676695831147921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13111058933784463887431947 19666588400676695831147921)
                ·
                  refine ⟨14749941300507521873360941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19666588400676695831147921 14749941300507521873360941)
                  ·
                    refine ⟨5531227987690320702510353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14749941300507521873360941 5531227987690320702510353)
                    ·
                      refine ⟨4148420990767740526882765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5531227987690320702510353 4148420990767740526882765)
                      ·
                        rfl

theorem cell23_8079021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_8079021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079021 prefixEnd_8079021 := by exact prefixLift 8079021
  have htrace : WordTrace (prefixWord ++ tailWord_8079021) baseStart_8079021 baseEnd_8079021 := by
    simpa [prefixWord, tailWord_8079021, baseEnd_8079021] using wordTrace_append hprefix tailTrace_8079021
  have hstable : (prefixWord ++ tailWord_8079021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079021).length < 2 ^ (prefixWord ++ tailWord_8079021).sum := by decide
  have hdescent : baseEnd_8079021 < baseStart_8079021 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079057 : List Nat := [1, 2, 2, 1, 2, 6, 1, 8]
def baseStart_8079057 : Nat := 118140960795 + 8079057 * 2 ^ 59
def prefixEnd_8079057 : Nat := 4983230072969 + 3 ^ 40 * 8079057 * 2
def baseEnd_8079057 : Nat := 153645906521159347630837

theorem tailTrace_8079057 : CollatzResearch.WordTrace tailWord_8079057 prefixEnd_8079057 153645906521159347630837 := by
  unfold tailWord_8079057
  simp only [CollatzResearch.WordTrace]
  refine ⟨294667416691963756929771425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196444944461309171286514283 294667416691963756929771425)
  ·
    refine ⟨221000562518972817697328569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294667416691963756929771425 221000562518972817697328569)
    ·
      refine ⟨165750421889229613272996427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221000562518972817697328569 165750421889229613272996427)
      ·
        refine ⟨248625632833844419909494641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165750421889229613272996427 248625632833844419909494641)
        ·
          refine ⟨186469224625383314932120981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248625632833844419909494641 186469224625383314932120981)
          ·
            refine ⟨8740744904314842887443171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 186469224625383314932120981 8740744904314842887443171)
            ·
              refine ⟨13111117356472264331164757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8740744904314842887443171 13111117356472264331164757)
              ·
                refine ⟨153645906521159347630837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13111117356472264331164757 153645906521159347630837)
                ·
                  rfl

theorem cell23_8079057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 8].length) (baseStart_8079057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079057 prefixEnd_8079057 := by exact prefixLift 8079057
  have htrace : WordTrace (prefixWord ++ tailWord_8079057) baseStart_8079057 baseEnd_8079057 := by
    simpa [prefixWord, tailWord_8079057, baseEnd_8079057] using wordTrace_append hprefix tailTrace_8079057
  have hstable : (prefixWord ++ tailWord_8079057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079057).length < 2 ^ (prefixWord ++ tailWord_8079057).sum := by decide
  have hdescent : baseEnd_8079057 < baseStart_8079057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079085 : List Nat := [1, 5, 1, 2, 1, 3, 2, 3, 1, 2, 2]
def baseStart_8079085 : Nat := 118140960795 + 8079085 * 2 ^ 59
def prefixEnd_8079085 : Nat := 4983230072969 + 3 ^ 40 * 8079085 * 2
def baseEnd_8079085 : Nat := 4148453853529628276482471

theorem tailTrace_8079085 : CollatzResearch.WordTrace tailWord_8079085 prefixEnd_8079085 4148453853529628276482471 := by
  unfold tailWord_8079085
  simp only [CollatzResearch.WordTrace]
  refine ⟨294668437935862317711790709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196445625290574878474527139 294668437935862317711790709)
  ·
    refine ⟨27625166056487092285480379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294668437935862317711790709 27625166056487092285480379)
    ·
      refine ⟨41437749084730638428220569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27625166056487092285480379 41437749084730638428220569)
      ·
        refine ⟨31078311813547978821165427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41437749084730638428220569 31078311813547978821165427)
        ·
          refine ⟨46617467720321968231748141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31078311813547978821165427 46617467720321968231748141)
          ·
            refine ⟨17481550395120738086905553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46617467720321968231748141 17481550395120738086905553)
            ·
              refine ⟨13111162796340553565179165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17481550395120738086905553 13111162796340553565179165)
              ·
                refine ⟨4916686048627707586942187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13111162796340553565179165 4916686048627707586942187)
                ·
                  refine ⟨7375029072941561380413281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916686048627707586942187 7375029072941561380413281)
                  ·
                    refine ⟨5531271804706171035309961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7375029072941561380413281 5531271804706171035309961)
                    ·
                      refine ⟨4148453853529628276482471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5531271804706171035309961 4148453853529628276482471)
                      ·
                        rfl

theorem cell23_8079085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_8079085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079085 prefixEnd_8079085 := by exact prefixLift 8079085
  have htrace : WordTrace (prefixWord ++ tailWord_8079085) baseStart_8079085 baseEnd_8079085 := by
    simpa [prefixWord, tailWord_8079085, baseEnd_8079085] using wordTrace_append hprefix tailTrace_8079085
  have hstable : (prefixWord ++ tailWord_8079085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079085).length < 2 ^ (prefixWord ++ tailWord_8079085).sum := by decide
  have hdescent : baseEnd_8079085 < baseStart_8079085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079120 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12]
def baseStart_8079120 : Nat := 118140960795 + 8079120 * 2 ^ 59
def prefixEnd_8079120 : Nat := 4983230072969 + 3 ^ 40 * 8079120 * 2
def baseEnd_8079120 : Nat := 4148471825352535639544809

theorem tailTrace_8079120 : CollatzResearch.WordTrace tailWord_8079120 prefixEnd_8079120 4148471825352535639544809 := by
  unfold tailWord_8079120
  simp only [CollatzResearch.WordTrace]
  refine ⟨147334857245367759344657407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196446476327157012459543209 147334857245367759344657407)
  ·
    refine ⟨221002285868051639016986111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147334857245367759344657407 221002285868051639016986111)
    ·
      refine ⟨331503428802077458525479167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221002285868051639016986111 331503428802077458525479167)
      ·
        refine ⟨497255143203116187788218751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331503428802077458525479167 497255143203116187788218751)
        ·
          refine ⟨745882714804674281682328127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497255143203116187788218751 745882714804674281682328127)
          ·
            refine ⟨1118824072207011422523492191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745882714804674281682328127 1118824072207011422523492191)
            ·
              refine ⟨1678236108310517133785238287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118824072207011422523492191 1678236108310517133785238287)
              ·
                refine ⟨2517354162465775700677857431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678236108310517133785238287 2517354162465775700677857431)
                ·
                  refine ⟨3776031243698663551016786147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517354162465775700677857431 3776031243698663551016786147)
                  ·
                    refine ⟨5664046865547995326525179221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3776031243698663551016786147 5664046865547995326525179221)
                    ·
                      refine ⟨4148471825352535639544809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 12 5664046865547995326525179221 4148471825352535639544809)
                      ·
                        rfl

theorem cell23_8079120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_8079120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079120 prefixEnd_8079120 := by exact prefixLift 8079120
  have htrace : WordTrace (prefixWord ++ tailWord_8079120) baseStart_8079120 baseEnd_8079120 := by
    simpa [prefixWord, tailWord_8079120, baseEnd_8079120] using wordTrace_append hprefix tailTrace_8079120
  have hstable : (prefixWord ++ tailWord_8079120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079120).length < 2 ^ (prefixWord ++ tailWord_8079120).sum := by decide
  have hdescent : baseEnd_8079120 < baseStart_8079120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079141 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 4, 2, 2]
def baseStart_8079141 : Nat := 118140960795 + 8079141 * 2 ^ 59
def prefixEnd_8079141 : Nat := 4983230072969 + 3 ^ 40 * 8079141 * 2
def baseEnd_8079141 : Nat := 4148482608446280057382213

theorem tailTrace_8079141 : CollatzResearch.WordTrace tailWord_8079141 prefixEnd_8079141 4148482608446280057382213 := by
  unfold tailWord_8079141
  simp only [CollatzResearch.WordTrace]
  refine ⟨294670480423659439275829277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196446986949106292850552851 294670480423659439275829277)
  ·
    refine ⟨110501430158872289728435979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294670480423659439275829277 110501430158872289728435979)
    ·
      refine ⟨165752145238308434592653969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110501430158872289728435979 165752145238308434592653969)
      ·
        refine ⟨124314108928731325944490477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165752145238308434592653969 124314108928731325944490477)
        ·
          refine ⟨46617790848274247229183929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124314108928731325944490477 46617790848274247229183929)
          ·
            refine ⟨34963343136205685421887947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46617790848274247229183929 34963343136205685421887947)
            ·
              refine ⟨52445014704308528132831921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34963343136205685421887947 52445014704308528132831921)
              ·
                refine ⟨39333761028231396099623941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52445014704308528132831921 39333761028231396099623941)
                ·
                  refine ⟨7375080192793386768679489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39333761028231396099623941 7375080192793386768679489)
                  ·
                    refine ⟨5531310144595040076509617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7375080192793386768679489 5531310144595040076509617)
                    ·
                      refine ⟨4148482608446280057382213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5531310144595040076509617 4148482608446280057382213)
                      ·
                        rfl

theorem cell23_8079141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_8079141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079141 prefixEnd_8079141 := by exact prefixLift 8079141
  have htrace : WordTrace (prefixWord ++ tailWord_8079141) baseStart_8079141 baseEnd_8079141 := by
    simpa [prefixWord, tailWord_8079141, baseEnd_8079141] using wordTrace_append hprefix tailTrace_8079141
  have hstable : (prefixWord ++ tailWord_8079141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079141).length < 2 ^ (prefixWord ++ tailWord_8079141).sum := by decide
  have hdescent : baseEnd_8079141 < baseStart_8079141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079144 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_8079144 : Nat := 118140960795 + 8079144 * 2 ^ 59
def prefixEnd_8079144 : Nat := 4983230072969 + 3 ^ 40 * 8079144 * 2
def baseEnd_8079144 : Nat := 4148484148888243545644699

theorem tailTrace_8079144 : CollatzResearch.WordTrace tailWord_8079144 prefixEnd_8079144 4148484148888243545644699 := by
  unfold tailWord_8079144
  simp only [CollatzResearch.WordTrace]
  refine ⟨147335294921324285394094243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196447059895099047192125657 147335294921324285394094243)
  ·
    refine ⟨221002942381986428091141365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147335294921324285394094243 221002942381986428091141365)
    ·
      refine ⟨20719025848311227633544503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221002942381986428091141365 20719025848311227633544503)
      ·
        refine ⟨31078538772466841450316755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20719025848311227633544503 31078538772466841450316755)
        ·
          refine ⟨46617808158700262175475133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31078538772466841450316755 46617808158700262175475133)
          ·
            refine ⟨17481678059512598315803175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46617808158700262175475133 17481678059512598315803175)
            ·
              refine ⟨26222517089268897473704763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17481678059512598315803175 26222517089268897473704763)
              ·
                refine ⟨39333775633903346210557145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26222517089268897473704763 39333775633903346210557145)
                ·
                  refine ⟨29500331725427509657917859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39333775633903346210557145 29500331725427509657917859)
                  ·
                    refine ⟨44250497588141264486876789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29500331725427509657917859 44250497588141264486876789)
                    ·
                      refine ⟨4148484148888243545644699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44250497588141264486876789 4148484148888243545644699)
                      ·
                        rfl

theorem cell23_8079144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_8079144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079144 prefixEnd_8079144 := by exact prefixLift 8079144
  have htrace : WordTrace (prefixWord ++ tailWord_8079144) baseStart_8079144 baseEnd_8079144 := by
    simpa [prefixWord, tailWord_8079144, baseEnd_8079144] using wordTrace_append hprefix tailTrace_8079144
  have hstable : (prefixWord ++ tailWord_8079144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079144).length < 2 ^ (prefixWord ++ tailWord_8079144).sum := by decide
  have hdescent : baseEnd_8079144 < baseStart_8079144 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079164 : List Nat := [2, 2, 2, 2, 1, 1, 2, 6, 5]
def baseStart_8079164 : Nat := 118140960795 + 8079164 * 2 ^ 59
def prefixEnd_8079164 : Nat := 4983230072969 + 3 ^ 40 * 8079164 * 2
def baseEnd_8079164 : Nat := 460943824277925940821623

theorem tailTrace_8079164 : CollatzResearch.WordTrace tailWord_8079164 prefixEnd_8079164 460943824277925940821623 := by
  unfold tailWord_8079164
  simp only [CollatzResearch.WordTrace]
  refine ⟨147335659651288057101958273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196447546201717409469277697 147335659651288057101958273)
  ·
    refine ⟨110501744738466042826468705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147335659651288057101958273 110501744738466042826468705)
    ·
      refine ⟨82876308553849532119851529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110501744738466042826468705 82876308553849532119851529)
      ·
        refine ⟨62157231415387149089888647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82876308553849532119851529 62157231415387149089888647)
        ·
          refine ⟨93235847123080723634832971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62157231415387149089888647 93235847123080723634832971)
          ·
            refine ⟨139853770684621085452249457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93235847123080723634832971 139853770684621085452249457)
            ·
              refine ⟨104890328013465814089187093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139853770684621085452249457 104890328013465814089187093)
              ·
                refine ⟨4916734125631210035430645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104890328013465814089187093 4916734125631210035430645)
                ·
                  refine ⟨460943824277925940821623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4916734125631210035430645 460943824277925940821623)
                  ·
                    rfl

theorem cell23_8079164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 5].length) (baseStart_8079164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079164 prefixEnd_8079164 := by exact prefixLift 8079164
  have htrace : WordTrace (prefixWord ++ tailWord_8079164) baseStart_8079164 baseEnd_8079164 := by
    simpa [prefixWord, tailWord_8079164, baseEnd_8079164] using wordTrace_append hprefix tailTrace_8079164
  have hstable : (prefixWord ++ tailWord_8079164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079164).length < 2 ^ (prefixWord ++ tailWord_8079164).sum := by decide
  have hdescent : baseEnd_8079164 < baseStart_8079164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079177 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 4, 5]
def baseStart_8079177 : Nat := 118140960795 + 8079177 * 2 ^ 59
def prefixEnd_8079177 : Nat := 4983230072969 + 3 ^ 40 * 8079177 * 2
def baseEnd_8079177 : Nat := 1382833697916613972177349

theorem tailTrace_8079177 : CollatzResearch.WordTrace tailWord_8079177 prefixEnd_8079177 1382833697916613972177349 := by
  unfold tailWord_8079177
  simp only [CollatzResearch.WordTrace]
  refine ⟨294671793451529017424139785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196447862301019344949426523 294671793451529017424139785)
  ·
    refine ⟨221003845088646763068104839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294671793451529017424139785 221003845088646763068104839)
    ·
      refine ⟨331505767632970144602157259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221003845088646763068104839 331505767632970144602157259)
      ·
        refine ⟨497258651449455216903235889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331505767632970144602157259 497258651449455216903235889)
        ·
          refine ⟨372943988587091412677426917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497258651449455216903235889 372943988587091412677426917)
          ·
            refine ⟨69926997860079639877017547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372943988587091412677426917 69926997860079639877017547)
            ·
              refine ⟨104890496790119459815526321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69926997860079639877017547 104890496790119459815526321)
              ·
                refine ⟨78667872592589594861644741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104890496790119459815526321 78667872592589594861644741)
                ·
                  refine ⟨14750226111110549036558389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78667872592589594861644741 14750226111110549036558389)
                  ·
                    refine ⟨1382833697916613972177349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14750226111110549036558389 1382833697916613972177349)
                    ·
                      rfl

theorem cell23_8079177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 5].length) (baseStart_8079177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079177 prefixEnd_8079177 := by exact prefixLift 8079177
  have htrace : WordTrace (prefixWord ++ tailWord_8079177) baseStart_8079177 baseEnd_8079177 := by
    simpa [prefixWord, tailWord_8079177, baseEnd_8079177] using wordTrace_append hprefix tailTrace_8079177
  have hstable : (prefixWord ++ tailWord_8079177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079177).length < 2 ^ (prefixWord ++ tailWord_8079177).sum := by decide
  have hdescent : baseEnd_8079177 < baseStart_8079177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079194 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 2, 5]
def baseStart_8079194 : Nat := 118140960795 + 8079194 * 2 ^ 59
def prefixEnd_8079194 : Nat := 4983230072969 + 3 ^ 40 * 8079194 * 2
def baseEnd_8079194 : Nat := 1382836607640322783339823

theorem tailTrace_8079194 : CollatzResearch.WordTrace tailWord_8079194 prefixEnd_8079194 1382836607640322783339823 := by
  unfold tailWord_8079194
  simp only [CollatzResearch.WordTrace]
  refine ⟨73668103373116857331877159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196448275661644952885005757 73668103373116857331877159)
  ·
    refine ⟨110502155059675285997815739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73668103373116857331877159 110502155059675285997815739)
    ·
      refine ⟨165753232589512928996723609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110502155059675285997815739 165753232589512928996723609)
      ·
        refine ⟨124314924442134696747542707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165753232589512928996723609 124314924442134696747542707)
        ·
          refine ⟨186472386663202045121314061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124314924442134696747542707 186472386663202045121314061)
          ·
            refine ⟨69927144998700766920492773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186472386663202045121314061 69927144998700766920492773)
            ·
              refine ⟨13111339687256393797592395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69927144998700766920492773 13111339687256393797592395)
              ·
                refine ⟨19667009530884590696388593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13111339687256393797592395 19667009530884590696388593)
                ·
                  refine ⟨14750257148163443022291445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19667009530884590696388593 14750257148163443022291445)
                  ·
                    refine ⟨1382836607640322783339823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14750257148163443022291445 1382836607640322783339823)
                    ·
                      rfl

theorem cell23_8079194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_8079194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079194 prefixEnd_8079194 := by exact prefixLift 8079194
  have htrace : WordTrace (prefixWord ++ tailWord_8079194) baseStart_8079194 baseEnd_8079194 := by
    simpa [prefixWord, tailWord_8079194, baseEnd_8079194] using wordTrace_append hprefix tailTrace_8079194
  have hstable : (prefixWord ++ tailWord_8079194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079194).length < 2 ^ (prefixWord ++ tailWord_8079194).sum := by decide
  have hdescent : baseEnd_8079194 < baseStart_8079194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079217 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_8079217 : Nat := 118140960795 + 8079217 * 2 ^ 59
def prefixEnd_8079217 : Nat := 4983230072969 + 3 ^ 40 * 8079217 * 2
def baseEnd_8079217 : Nat := 4148521632976021760031863

theorem tailTrace_8079217 : CollatzResearch.WordTrace tailWord_8079217 prefixEnd_8079217 4148521632976021760031863 := by
  unfold tailWord_8079217
  simp only [CollatzResearch.WordTrace]
  refine ⟨294673252371384104255595905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196448834914256069503730603 294673252371384104255595905)
  ·
    refine ⟨221004939278538078191696929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294673252371384104255595905 221004939278538078191696929)
    ·
      refine ⟨165753704458903558643772697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221004939278538078191696929 165753704458903558643772697)
      ·
        refine ⟨124315278344177668982829523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165753704458903558643772697 124315278344177668982829523)
        ·
          refine ⟨186472917516266503474244285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124315278344177668982829523 186472917516266503474244285)
          ·
            refine ⟨69927344068599938802841607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186472917516266503474244285 69927344068599938802841607)
            ·
              refine ⟨104891016102899908204262411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69927344068599938802841607 104891016102899908204262411)
              ·
                refine ⟨157336524154349862306393617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104891016102899908204262411 157336524154349862306393617)
                ·
                  refine ⟨118002393115762396729795213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157336524154349862306393617 118002393115762396729795213)
                  ·
                    refine ⟨44250897418410898773673205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118002393115762396729795213 44250897418410898773673205)
                    ·
                      refine ⟨4148521632976021760031863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44250897418410898773673205 4148521632976021760031863)
                      ·
                        rfl

theorem cell23_8079217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_8079217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079217 prefixEnd_8079217 := by exact prefixLift 8079217
  have htrace : WordTrace (prefixWord ++ tailWord_8079217) baseStart_8079217 baseEnd_8079217 := by
    simpa [prefixWord, tailWord_8079217, baseEnd_8079217] using wordTrace_append hprefix tailTrace_8079217
  have hstable : (prefixWord ++ tailWord_8079217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079217).length < 2 ^ (prefixWord ++ tailWord_8079217).sum := by decide
  have hdescent : baseEnd_8079217 < baseStart_8079217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079227 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 4]
def baseStart_8079227 : Nat := 118140960795 + 8079227 * 2 ^ 59
def prefixEnd_8079227 : Nat := 4983230072969 + 3 ^ 40 * 8079227 * 2
def baseEnd_8079227 : Nat := 4148526767782566720906817

theorem tailTrace_8079227 : CollatzResearch.WordTrace tailWord_8079227 prefixEnd_8079227 4148526767782566720906817 := by
  unfold tailWord_8079227
  simp only [CollatzResearch.WordTrace]
  refine ⟨294673617101347875963459935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196449078067565250642306623 294673617101347875963459935)
  ·
    refine ⟨442010425652021813945189903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294673617101347875963459935 442010425652021813945189903)
    ·
      refine ⟨663015638478032720917784855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442010425652021813945189903 663015638478032720917784855)
      ·
        refine ⟨994523457717049081376677283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663015638478032720917784855 994523457717049081376677283)
        ·
          refine ⟨1491785186575573622065015925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994523457717049081376677283 1491785186575573622065015925)
          ·
            refine ⟨139854861241460027068595243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1491785186575573622065015925 139854861241460027068595243)
            ·
              refine ⟨209782291862190040602892865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139854861241460027068595243 209782291862190040602892865)
              ·
                refine ⟨157336718896642530452169649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209782291862190040602892865 157336718896642530452169649)
                ·
                  refine ⟨118002539172481897839127237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157336718896642530452169649 118002539172481897839127237)
                  ·
                    refine ⟨22125476094840355844836357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118002539172481897839127237 22125476094840355844836357)
                    ·
                      refine ⟨4148526767782566720906817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22125476094840355844836357 4148526767782566720906817)
                      ·
                        rfl

theorem cell23_8079227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 4].length) (baseStart_8079227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079227 prefixEnd_8079227 := by exact prefixLift 8079227
  have htrace : WordTrace (prefixWord ++ tailWord_8079227) baseStart_8079227 baseEnd_8079227 := by
    simpa [prefixWord, tailWord_8079227, baseEnd_8079227] using wordTrace_append hprefix tailTrace_8079227
  have hstable : (prefixWord ++ tailWord_8079227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079227).length < 2 ^ (prefixWord ++ tailWord_8079227).sum := by decide
  have hdescent : baseEnd_8079227 < baseStart_8079227 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079258 : List Nat := [3, 1, 1, 4, 2, 1, 1, 5, 1, 4]
def baseStart_8079258 : Nat := 118140960795 + 8079258 * 2 ^ 59
def prefixEnd_8079258 : Nat := 4983230072969 + 3 ^ 40 * 8079258 * 2
def baseEnd_8079258 : Nat := 1382847561894285366539725

theorem tailTrace_8079258 : CollatzResearch.WordTrace tailWord_8079258 prefixEnd_8079258 1382847561894285366539725 := by
  unfold tailWord_8079258
  simp only [CollatzResearch.WordTrace]
  refine ⟨73668686941058892064459607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196449831842823712171892285 73668686941058892064459607)
  ·
    refine ⟨110503030411588338096689411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73668686941058892064459607 110503030411588338096689411)
    ·
      refine ⟨165754545617382507145034117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110503030411588338096689411 165754545617382507145034117)
      ·
        refine ⟨31078977303259220089693897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165754545617382507145034117 31078977303259220089693897)
        ·
          refine ⟨23309232977444415067270423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31078977303259220089693897 23309232977444415067270423)
          ·
            refine ⟨34963849466166622600905635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23309232977444415067270423 34963849466166622600905635)
            ·
              refine ⟨52445774199249933901358453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34963849466166622600905635 52445774199249933901358453)
              ·
                refine ⟨4916791331179681303252355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52445774199249933901358453 4916791331179681303252355)
                ·
                  refine ⟨7375186996769521954878533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916791331179681303252355 7375186996769521954878533)
                  ·
                    refine ⟨1382847561894285366539725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7375186996769521954878533 1382847561894285366539725)
                    ·
                      rfl

theorem cell23_8079258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_8079258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079258 prefixEnd_8079258 := by exact prefixLift 8079258
  have htrace : WordTrace (prefixWord ++ tailWord_8079258) baseStart_8079258 baseEnd_8079258 := by
    simpa [prefixWord, tailWord_8079258, baseEnd_8079258] using wordTrace_append hprefix tailTrace_8079258
  have hstable : (prefixWord ++ tailWord_8079258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079258).length < 2 ^ (prefixWord ++ tailWord_8079258).sum := by decide
  have hdescent : baseEnd_8079258 < baseStart_8079258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079271 : List Nat := [1, 1, 6, 1, 2, 1, 3, 2, 6]
def baseStart_8079271 : Nat := 118140960795 + 8079271 * 2 ^ 59
def prefixEnd_8079271 : Nat := 4983230072969 + 3 ^ 40 * 8079271 * 2
def baseEnd_8079271 : Nat := 460949928992373838750735

theorem tailTrace_8079271 : CollatzResearch.WordTrace tailWord_8079271 prefixEnd_8079271 460949928992373838750735 := by
  unfold tailWord_8079271
  simp only [CollatzResearch.WordTrace]
  refine ⟨294675221913188471478061667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196450147942125647652041111 294675221913188471478061667)
  ·
    refine ⟨442012832869782707217092501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294675221913188471478061667 442012832869782707217092501)
    ·
      refine ⟨20719351540771064400801211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 442012832869782707217092501 20719351540771064400801211)
      ·
        refine ⟨31079027311156596601201817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20719351540771064400801211 31079027311156596601201817)
        ·
          refine ⟨23309270483367447450901363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31079027311156596601201817 23309270483367447450901363)
          ·
            refine ⟨34963905725051171176352045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23309270483367447450901363 34963905725051171176352045)
            ·
              refine ⟨13111464646894189191132017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34963905725051171176352045 13111464646894189191132017)
              ·
                refine ⟨9833598485170641893349013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13111464646894189191132017 9833598485170641893349013)
                ·
                  refine ⟨460949928992373838750735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9833598485170641893349013 460949928992373838750735)
                  ·
                    rfl

theorem cell23_8079271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 6].length) (baseStart_8079271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079271 prefixEnd_8079271 := by exact prefixLift 8079271
  have htrace : WordTrace (prefixWord ++ tailWord_8079271) baseStart_8079271 baseEnd_8079271 := by
    simpa [prefixWord, tailWord_8079271, baseEnd_8079271] using wordTrace_append hprefix tailTrace_8079271
  have hstable : (prefixWord ++ tailWord_8079271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079271).length < 2 ^ (prefixWord ++ tailWord_8079271).sum := by decide
  have hdescent : baseEnd_8079271 < baseStart_8079271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079325 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_8079325 : Nat := 118140960795 + 8079325 * 2 ^ 59
def prefixEnd_8079325 : Nat := 4983230072969 + 3 ^ 40 * 8079325 * 2
def baseEnd_8079325 : Nat := 4148577088886707337481367

theorem tailTrace_8079325 : CollatzResearch.WordTrace tailWord_8079325 prefixEnd_8079325 4148577088886707337481367 := by
  unfold tailWord_8079325
  simp only [CollatzResearch.WordTrace]
  refine ⟨294677191454992838700527429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196451460969995225800351619 294677191454992838700527429)
  ·
    refine ⟨55251973397811157256348893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294677191454992838700527429 55251973397811157256348893)
    ·
      refine ⟨20719490024179183971130835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55251973397811157256348893 20719490024179183971130835)
      ·
        refine ⟨31079235036268775956696253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20719490024179183971130835 31079235036268775956696253)
        ·
          refine ⟨11654713138600790983761095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31079235036268775956696253 11654713138600790983761095)
          ·
            refine ⟨17482069707901186475641643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11654713138600790983761095 17482069707901186475641643)
            ·
              refine ⟨26223104561851779713462465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17482069707901186475641643 26223104561851779713462465)
              ·
                refine ⟨19667328421388834785096849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26223104561851779713462465 19667328421388834785096849)
                ·
                  refine ⟨14750496316041626088822637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19667328421388834785096849 14750496316041626088822637)
                  ·
                    refine ⟨5531436118515609783308489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14750496316041626088822637 5531436118515609783308489)
                    ·
                      refine ⟨4148577088886707337481367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5531436118515609783308489 4148577088886707337481367)
                      ·
                        rfl

theorem cell23_8079325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_8079325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079325 prefixEnd_8079325 := by exact prefixLift 8079325
  have htrace : WordTrace (prefixWord ++ tailWord_8079325) baseStart_8079325 baseEnd_8079325 := by
    simpa [prefixWord, tailWord_8079325, baseEnd_8079325] using wordTrace_append hprefix tailTrace_8079325
  have hstable : (prefixWord ++ tailWord_8079325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079325).length < 2 ^ (prefixWord ++ tailWord_8079325).sum := by decide
  have hdescent : baseEnd_8079325 < baseStart_8079325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079331 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 4, 4]
def baseStart_8079331 : Nat := 118140960795 + 8079331 * 2 ^ 59
def prefixEnd_8079331 : Nat := 4983230072969 + 3 ^ 40 * 8079331 * 2
def baseEnd_8079331 : Nat := 1382860056590211438002113

theorem tailTrace_8079331 : CollatzResearch.WordTrace tailWord_8079331 prefixEnd_8079331 1382860056590211438002113 := by
  unfold tailWord_8079331
  simp only [CollatzResearch.WordTrace]
  refine ⟨294677410292971101725245847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196451606861980734483497231 294677410292971101725245847)
  ·
    refine ⟨442016115439456652587868771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294677410292971101725245847 442016115439456652587868771)
    ·
      refine ⟨663024173159184978881803157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442016115439456652587868771 663024173159184978881803157)
      ·
        refine ⟨31079258116836795885084523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 663024173159184978881803157 31079258116836795885084523)
        ·
          refine ⟨46618887175255193827626785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31079258116836795885084523 46618887175255193827626785)
          ·
            refine ⟨34964165381441395370720089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46618887175255193827626785 34964165381441395370720089)
            ·
              refine ⟨26223124036081046528040067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34964165381441395370720089 26223124036081046528040067)
              ·
                refine ⟨39334686054121569792060101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26223124036081046528040067 39334686054121569792060101)
                ·
                  refine ⟨7375253635147794336011269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39334686054121569792060101 7375253635147794336011269)
                  ·
                    refine ⟨1382860056590211438002113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7375253635147794336011269 1382860056590211438002113)
                    ·
                      rfl

theorem cell23_8079331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 4].length) (baseStart_8079331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079331 prefixEnd_8079331 := by exact prefixLift 8079331
  have htrace : WordTrace (prefixWord ++ tailWord_8079331) baseStart_8079331 baseEnd_8079331 := by
    simpa [prefixWord, tailWord_8079331, baseEnd_8079331] using wordTrace_append hprefix tailTrace_8079331
  have hstable : (prefixWord ++ tailWord_8079331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079331).length < 2 ^ (prefixWord ++ tailWord_8079331).sum := by decide
  have hdescent : baseEnd_8079331 < baseStart_8079331 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079371 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 3]
def baseStart_8079371 : Nat := 118140960795 + 8079371 * 2 ^ 59
def prefixEnd_8079371 : Nat := 4983230072969 + 3 ^ 40 * 8079371 * 2
def baseEnd_8079371 : Nat := 4148600708996814157506155

theorem tailTrace_8079371 : CollatzResearch.WordTrace tailWord_8079371 prefixEnd_8079371 4148600708996814157506155 := by
  unfold tailWord_8079371
  simp only [CollatzResearch.WordTrace]
  refine ⟨294678869212826188556701967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196452579475217459037801311 294678869212826188556701967)
  ·
    refine ⟨442018303819239282835052951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294678869212826188556701967 442018303819239282835052951)
    ·
      refine ⟨663027455728858924252579427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442018303819239282835052951 663027455728858924252579427)
      ·
        refine ⟨994541183593288386378869141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663027455728858924252579427 994541183593288386378869141)
        ·
          refine ⟨46619117980935393111509491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 994541183593288386378869141 46619117980935393111509491)
          ·
            refine ⟨69928676971403089667264237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46619117980935393111509491 69928676971403089667264237)
            ·
              refine ⟨26223253864276158625224089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69928676971403089667264237 26223253864276158625224089)
              ·
                refine ⟨19667440398207118968918067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26223253864276158625224089 19667440398207118968918067)
                ·
                  refine ⟨29501160597310678453377101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19667440398207118968918067 29501160597310678453377101)
                  ·
                    refine ⟨11062935223991504420016413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29501160597310678453377101 11062935223991504420016413)
                    ·
                      refine ⟨4148600708996814157506155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11062935223991504420016413 4148600708996814157506155)
                      ·
                        rfl

theorem cell23_8079371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 3].length) (baseStart_8079371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079371 prefixEnd_8079371 := by exact prefixLift 8079371
  have htrace : WordTrace (prefixWord ++ tailWord_8079371) baseStart_8079371 baseEnd_8079371 := by
    simpa [prefixWord, tailWord_8079371, baseEnd_8079371] using wordTrace_append hprefix tailTrace_8079371
  have hstable : (prefixWord ++ tailWord_8079371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079371).length < 2 ^ (prefixWord ++ tailWord_8079371).sum := by decide
  have hdescent : baseEnd_8079371 < baseStart_8079371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079389 : List Nat := [1, 4, 2, 2, 2, 1, 4, 2, 1, 2, 2]
def baseStart_8079389 : Nat := 118140960795 + 8079389 * 2 ^ 59
def prefixEnd_8079389 : Nat := 4983230072969 + 3 ^ 40 * 8079389 * 2
def baseEnd_8079389 : Nat := 4148609951648595087081073

theorem tailTrace_8079389 : CollatzResearch.WordTrace tailWord_8079389 prefixEnd_8079389 4148609951648595087081073 := by
  unfold tailWord_8079389
  simp only [CollatzResearch.WordTrace]
  refine ⟨294679525726760977630857221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196453017151173985087238147 294679525726760977630857221)
  ·
    refine ⟨55252411073767683305785729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294679525726760977630857221 55252411073767683305785729)
    ·
      refine ⟨41439308305325762479339297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55252411073767683305785729 41439308305325762479339297)
      ·
        refine ⟨31079481228994321859504473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41439308305325762479339297 31079481228994321859504473)
        ·
          refine ⟨23309610921745741394628355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31079481228994321859504473 23309610921745741394628355)
          ·
            refine ⟨34964416382618612091942533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23309610921745741394628355 34964416382618612091942533)
            ·
              refine ⟨6555828071740989767239225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34964416382618612091942533 6555828071740989767239225)
              ·
                refine ⟨4916871053805742325429419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6555828071740989767239225 4916871053805742325429419)
                ·
                  refine ⟨7375306580708613488144129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916871053805742325429419 7375306580708613488144129)
                  ·
                    refine ⟨5531479935531460116108097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7375306580708613488144129 5531479935531460116108097)
                    ·
                      refine ⟨4148609951648595087081073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5531479935531460116108097 4148609951648595087081073)
                      ·
                        rfl

theorem cell23_8079389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_8079389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079389 prefixEnd_8079389 := by exact prefixLift 8079389
  have htrace : WordTrace (prefixWord ++ tailWord_8079389) baseStart_8079389 baseEnd_8079389 := by
    simpa [prefixWord, tailWord_8079389, baseEnd_8079389] using wordTrace_append hprefix tailTrace_8079389
  have hstable : (prefixWord ++ tailWord_8079389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079389).length < 2 ^ (prefixWord ++ tailWord_8079389).sum := by decide
  have hdescent : baseEnd_8079389 < baseStart_8079389 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079434 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 11]
def baseStart_8079434 : Nat := 118140960795 + 8079434 * 2 ^ 59
def prefixEnd_8079434 : Nat := 4983230072969 + 3 ^ 40 * 8079434 * 2
def baseEnd_8079434 : Nat := 460959228697560823446485

theorem tailTrace_8079434 : CollatzResearch.WordTrace tailWord_8079434 prefixEnd_8079434 460959228697560823446485 := by
  unfold tailWord_8079434
  simp only [CollatzResearch.WordTrace]
  refine ⟨73670291752899487579061339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196454111341065300210830237 73670291752899487579061339)
  ·
    refine ⟨110505437629349231368592009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73670291752899487579061339 110505437629349231368592009)
    ·
      refine ⟨82879078222011923526444007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110505437629349231368592009 82879078222011923526444007)
      ·
        refine ⟨124318617333017885289666011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82879078222011923526444007 124318617333017885289666011)
        ·
          refine ⟨186477925999526827934499017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124318617333017885289666011 186477925999526827934499017)
          ·
            refine ⟨139858444499645120950874263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186477925999526827934499017 139858444499645120950874263)
            ·
              refine ⟨209787666749467681426311395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139858444499645120950874263 209787666749467681426311395)
              ·
                refine ⟨314681500124201522139467093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209787666749467681426311395 314681500124201522139467093)
                ·
                  refine ⟨460959228697560823446485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 314681500124201522139467093 460959228697560823446485)
                  ·
                    rfl

theorem cell23_8079434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_8079434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079434 prefixEnd_8079434 := by exact prefixLift 8079434
  have htrace : WordTrace (prefixWord ++ tailWord_8079434) baseStart_8079434 baseEnd_8079434 := by
    simpa [prefixWord, tailWord_8079434, baseEnd_8079434] using wordTrace_append hprefix tailTrace_8079434
  have hstable : (prefixWord ++ tailWord_8079434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079434).length < 2 ^ (prefixWord ++ tailWord_8079434).sum := by decide
  have hdescent : baseEnd_8079434 < baseStart_8079434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079445 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 4, 2, 2]
def baseStart_8079445 : Nat := 118140960795 + 8079445 * 2 ^ 59
def prefixEnd_8079445 : Nat := 4983230072969 + 3 ^ 40 * 8079445 * 2
def baseEnd_8079445 : Nat := 4148638706565246867980815

theorem tailTrace_8079445 : CollatzResearch.WordTrace tailWord_8079445 prefixEnd_8079445 4148638706565246867980815 := by
  unfold tailWord_8079445
  simp only [CollatzResearch.WordTrace]
  refine ⟨294681568214558099194895789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196454378809705399463263859 294681568214558099194895789)
  ·
    refine ⟨110505588080459287198085921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294681568214558099194895789 110505588080459287198085921)
    ·
      refine ⟨82879191060344465398564441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110505588080459287198085921 82879191060344465398564441)
      ·
        refine ⟨62159393295258349048923331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82879191060344465398564441 62159393295258349048923331)
        ·
          refine ⟨93239089942887523573384997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62159393295258349048923331 93239089942887523573384997)
          ·
            refine ⟨17482329364291410670009687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93239089942887523573384997 17482329364291410670009687)
            ·
              refine ⟨26223494046437116005014531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17482329364291410670009687 26223494046437116005014531)
              ·
                refine ⟨39335241069655674007521797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26223494046437116005014531 39335241069655674007521797)
                ·
                  refine ⟨7375357700560438876410337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39335241069655674007521797 7375357700560438876410337)
                  ·
                    refine ⟨5531518275420329157307753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7375357700560438876410337 5531518275420329157307753)
                    ·
                      refine ⟨4148638706565246867980815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5531518275420329157307753 4148638706565246867980815)
                      ·
                        rfl

theorem cell23_8079445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_8079445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079445 prefixEnd_8079445 := by exact prefixLift 8079445
  have htrace : WordTrace (prefixWord ++ tailWord_8079445) baseStart_8079445 baseEnd_8079445 := by
    simpa [prefixWord, tailWord_8079445, baseEnd_8079445] using wordTrace_append hprefix tailTrace_8079445
  have hstable : (prefixWord ++ tailWord_8079445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079445).length < 2 ^ (prefixWord ++ tailWord_8079445).sum := by decide
  have hdescent : baseEnd_8079445 < baseStart_8079445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079481 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 1, 7]
def baseStart_8079481 : Nat := 118140960795 + 8079481 * 2 ^ 59
def prefixEnd_8079481 : Nat := 4983230072969 + 3 ^ 40 * 8079481 * 2
def baseEnd_8079481 : Nat := 1382885730622936242376883

theorem tailTrace_8079481 : CollatzResearch.WordTrace tailWord_8079481 prefixEnd_8079481 1382885730622936242376883 := by
  unfold tailWord_8079481
  simp only [CollatzResearch.WordTrace]
  refine ⟨294682881242427677343206297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196455254161618451562137531 294682881242427677343206297)
  ·
    refine ⟨221012160931820758007404723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294682881242427677343206297 221012160931820758007404723)
    ·
      refine ⟨331518241397731137011107085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221012160931820758007404723 331518241397731137011107085)
      ·
        refine ⟨124319340524149176379165157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331518241397731137011107085 124319340524149176379165157)
        ·
          refine ⟨23309876348277970571093467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124319340524149176379165157 23309876348277970571093467)
          ·
            refine ⟨34964814522416955856640201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23309876348277970571093467 34964814522416955856640201)
            ·
              refine ⟨26223610891812716892480151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34964814522416955856640201 26223610891812716892480151)
              ·
                refine ⟨39335416337719075338720227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26223610891812716892480151 39335416337719075338720227)
                ·
                  refine ⟨59003124506578613008080341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39335416337719075338720227 59003124506578613008080341)
                  ·
                    refine ⟨1382885730622936242376883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59003124506578613008080341 1382885730622936242376883)
                    ·
                      rfl

theorem cell23_8079481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 7].length) (baseStart_8079481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079481 prefixEnd_8079481 := by exact prefixLift 8079481
  have htrace : WordTrace (prefixWord ++ tailWord_8079481) baseStart_8079481 baseEnd_8079481 := by
    simpa [prefixWord, tailWord_8079481, baseEnd_8079481] using wordTrace_append hprefix tailTrace_8079481
  have hstable : (prefixWord ++ tailWord_8079481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079481).length < 2 ^ (prefixWord ++ tailWord_8079481).sum := by decide
  have hdescent : baseEnd_8079481 < baseStart_8079481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079485 : List Nat := [1, 4, 1, 1, 3, 4, 1, 3, 5]
def baseStart_8079485 : Nat := 118140960795 + 8079485 * 2 ^ 59
def prefixEnd_8079485 : Nat := 4983230072969 + 3 ^ 40 * 8079485 * 2
def baseEnd_8079485 : Nat := 460962138421269634608959

theorem tailTrace_8079485 : CollatzResearch.WordTrace tailWord_8079485 prefixEnd_8079485 460962138421269634608959 := by
  unfold tailWord_8079485
  simp only [CollatzResearch.WordTrace]
  refine ⟨294683027134413186026351909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196455351422942124017567939 294683027134413186026351909)
  ·
    refine ⟨55253067587702472379940983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294683027134413186026351909 55253067587702472379940983)
    ·
      refine ⟨82879601381553708569911475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55253067587702472379940983 82879601381553708569911475)
      ·
        refine ⟨124319402072330562854867213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82879601381553708569911475 124319402072330562854867213)
        ·
          refine ⟨46619775777123961070575205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124319402072330562854867213 46619775777123961070575205)
          ·
            refine ⟨8741207958210742700732851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46619775777123961070575205 8741207958210742700732851)
            ·
              refine ⟨13111811937316114051099277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8741207958210742700732851 13111811937316114051099277)
              ·
                refine ⟨4916929476493542769162229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13111811937316114051099277 4916929476493542769162229)
                ·
                  refine ⟨460962138421269634608959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4916929476493542769162229 460962138421269634608959)
                  ·
                    rfl

theorem cell23_8079485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_8079485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079485 prefixEnd_8079485 := by exact prefixLift 8079485
  have htrace : WordTrace (prefixWord ++ tailWord_8079485) baseStart_8079485 baseEnd_8079485 := by
    simpa [prefixWord, tailWord_8079485, baseEnd_8079485] using wordTrace_append hprefix tailTrace_8079485
  have hstable : (prefixWord ++ tailWord_8079485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079485).length < 2 ^ (prefixWord ++ tailWord_8079485).sum := by decide
  have hdescent : baseEnd_8079485 < baseStart_8079485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079498 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 2, 5]
def baseStart_8079498 : Nat := 118140960795 + 8079498 * 2 ^ 59
def prefixEnd_8079498 : Nat := 4983230072969 + 3 ^ 40 * 8079498 * 2
def baseEnd_8079498 : Nat := 1382888640346645053539357

theorem tailTrace_8079498 : CollatzResearch.WordTrace tailWord_8079498 prefixEnd_8079498 1382888640346645053539357 := by
  unfold tailWord_8079498
  simp only [CollatzResearch.WordTrace]
  refine ⟨73670875320841522311643787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196455667522244059497716765 73670875320841522311643787)
  ·
    refine ⟨110506312981262283467465681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73670875320841522311643787 110506312981262283467465681)
    ·
      refine ⟨82879734735946712600599261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110506312981262283467465681 82879734735946712600599261)
      ·
        refine ⟨31079900525980017225224723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82879734735946712600599261 31079900525980017225224723)
        ·
          refine ⟨46619850788970025837837085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31079900525980017225224723 46619850788970025837837085)
          ·
            refine ⟨17482444045863759689188907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46619850788970025837837085 17482444045863759689188907)
            ·
              refine ⟨26223666068795639533783361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17482444045863759689188907 26223666068795639533783361)
              ·
                refine ⟨19667749551596729650337521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26223666068795639533783361 19667749551596729650337521)
                ·
                  refine ⟨14750812163697547237753141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19667749551596729650337521 14750812163697547237753141)
                  ·
                    refine ⟨1382888640346645053539357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14750812163697547237753141 1382888640346645053539357)
                    ·
                      rfl

theorem cell23_8079498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_8079498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079498 prefixEnd_8079498 := by exact prefixLift 8079498
  have htrace : WordTrace (prefixWord ++ tailWord_8079498) baseStart_8079498 baseEnd_8079498 := by
    simpa [prefixWord, tailWord_8079498, baseEnd_8079498] using wordTrace_append hprefix tailTrace_8079498
  have hstable : (prefixWord ++ tailWord_8079498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079498).length < 2 ^ (prefixWord ++ tailWord_8079498).sum := by decide
  have hdescent : baseEnd_8079498 < baseStart_8079498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079502 : List Nat := [4, 1, 1, 3, 3, 1, 3, 2, 5]
def baseStart_8079502 : Nat := 118140960795 + 8079502 * 2 ^ 59
def prefixEnd_8079502 : Nat := 4983230072969 + 3 ^ 40 * 8079502 * 2
def baseEnd_8079502 : Nat := 460963108329172571663117

theorem tailTrace_8079502 : CollatzResearch.WordTrace tailWord_8079502 prefixEnd_8079502 460963108329172571663117 := by
  unfold tailWord_8079502
  simp only [CollatzResearch.WordTrace]
  refine ⟨36835455896918949741215095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196455764783567731953147173 36835455896918949741215095)
  ·
    refine ⟨55253183845378424611822643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36835455896918949741215095 55253183845378424611822643)
    ·
      refine ⟨82879775768067636917733965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55253183845378424611822643 82879775768067636917733965)
      ·
        refine ⟨31079915913025363844150237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82879775768067636917733965 31079915913025363844150237)
        ·
          refine ⟨11654968467384511441556339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31079915913025363844150237 11654968467384511441556339)
          ·
            refine ⟨17482452701076767162334509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11654968467384511441556339 17482452701076767162334509)
            ·
              refine ⟨6555919762903787685875441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17482452701076767162334509 6555919762903787685875441)
              ·
                refine ⟨4916939822177840764406581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6555919762903787685875441 4916939822177840764406581)
                ·
                  refine ⟨460963108329172571663117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4916939822177840764406581 460963108329172571663117)
                  ·
                    rfl

theorem cell23_8079502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_8079502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079502 prefixEnd_8079502 := by exact prefixLift 8079502
  have htrace : WordTrace (prefixWord ++ tailWord_8079502) baseStart_8079502 baseEnd_8079502 := by
    simpa [prefixWord, tailWord_8079502, baseEnd_8079502] using wordTrace_append hprefix tailTrace_8079502
  have hstable : (prefixWord ++ tailWord_8079502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079502).length < 2 ^ (prefixWord ++ tailWord_8079502).sum := by decide
  have hdescent : baseEnd_8079502 < baseStart_8079502 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079545 : List Nat := [1, 2, 1, 4, 1, 2, 2, 5, 1, 4]
def baseStart_8079545 : Nat := 118140960795 + 8079545 * 2 ^ 59
def prefixEnd_8079545 : Nat := 4983230072969 + 3 ^ 40 * 8079545 * 2
def baseEnd_8079545 : Nat := 1382896684876898825576785

theorem tailTrace_8079545 : CollatzResearch.WordTrace tailWord_8079545 prefixEnd_8079545 1382896684876898825576785 := by
  unfold tailWord_8079545
  simp only [CollatzResearch.WordTrace]
  refine ⟨294685215514195816273536089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196456810342797210849024059 294685215514195816273536089)
  ·
    refine ⟨221013911635646862205152067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294685215514195816273536089 221013911635646862205152067)
    ·
      refine ⟨331520867453470293307728101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221013911635646862205152067 331520867453470293307728101)
      ·
        refine ⟨62160162647525679995199019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331520867453470293307728101 62160162647525679995199019)
        ·
          refine ⟨93240243971288519992798529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62160162647525679995199019 93240243971288519992798529)
          ·
            refine ⟨69930182978466389994598897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93240243971288519992798529 69930182978466389994598897)
            ·
              refine ⟨52447637233849792495949173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69930182978466389994598897 52447637233849792495949173)
              ·
                refine ⟨4916965990673418046495235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52447637233849792495949173 4916965990673418046495235)
                ·
                  refine ⟨7375448986010127069742853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916965990673418046495235 7375448986010127069742853)
                  ·
                    refine ⟨1382896684876898825576785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7375448986010127069742853 1382896684876898825576785)
                    ·
                      rfl

theorem cell23_8079545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 1, 4].length) (baseStart_8079545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079545 prefixEnd_8079545 := by exact prefixLift 8079545
  have htrace : WordTrace (prefixWord ++ tailWord_8079545) baseStart_8079545 baseEnd_8079545 := by
    simpa [prefixWord, tailWord_8079545, baseEnd_8079545] using wordTrace_append hprefix tailTrace_8079545
  have hstable : (prefixWord ++ tailWord_8079545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079545).length < 2 ^ (prefixWord ++ tailWord_8079545).sum := by decide
  have hdescent : baseEnd_8079545 < baseStart_8079545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079568 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 9, 1, 3]
def baseStart_8079568 : Nat := 118140960795 + 8079568 * 2 ^ 59
def prefixEnd_8079568 : Nat := 4983230072969 + 3 ^ 40 * 8079568 * 2
def baseEnd_8079568 : Nat := 4148701864685749886742749

theorem tailTrace_8079568 : CollatzResearch.WordTrace tailWord_8079568 prefixEnd_8079568 4148701864685749886742749 := by
  unfold tailWord_8079568
  simp only [CollatzResearch.WordTrace]
  refine ⟨147343027196556245600811679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196457369595408327467748905 147343027196556245600811679)
  ·
    refine ⟨221014540794834368401217519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147343027196556245600811679 221014540794834368401217519)
    ·
      refine ⟨331521811192251552601826279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221014540794834368401217519 331521811192251552601826279)
      ·
        refine ⟨497282716788377328902739419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331521811192251552601826279 497282716788377328902739419)
        ·
          refine ⟨745924075182565993354109129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497282716788377328902739419 745924075182565993354109129)
          ·
            refine ⟨559443056386924495015581847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745924075182565993354109129 559443056386924495015581847)
            ·
              refine ⟨839164584580386742523372771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559443056386924495015581847 839164584580386742523372771)
              ·
                refine ⟨1258746876870580113785059157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839164584580386742523372771 1258746876870580113785059157)
                ·
                  refine ⟨7375469981663555354209331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1258746876870580113785059157 7375469981663555354209331)
                  ·
                    refine ⟨11063204972495333031313997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7375469981663555354209331 11063204972495333031313997)
                    ·
                      refine ⟨4148701864685749886742749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11063204972495333031313997 4148701864685749886742749)
                      ·
                        rfl

theorem cell23_8079568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 9, 1, 3].length) (baseStart_8079568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079568 prefixEnd_8079568 := by exact prefixLift 8079568
  have htrace : WordTrace (prefixWord ++ tailWord_8079568) baseStart_8079568 baseEnd_8079568 := by
    simpa [prefixWord, tailWord_8079568, baseEnd_8079568] using wordTrace_append hprefix tailTrace_8079568
  have hstable : (prefixWord ++ tailWord_8079568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079568).length < 2 ^ (prefixWord ++ tailWord_8079568).sum := by decide
  have hdescent : baseEnd_8079568 < baseStart_8079568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079585 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 3, 1, 3]
def baseStart_8079585 : Nat := 118140960795 + 8079585 * 2 ^ 59
def prefixEnd_8079585 : Nat := 4983230072969 + 3 ^ 40 * 8079585 * 2
def baseEnd_8079585 : Nat := 4148710593856876320230171

theorem tailTrace_8079585 : CollatzResearch.WordTrace tailWord_8079585 prefixEnd_8079585 4148710593856876320230171 := by
  unfold tailWord_8079585
  simp only [CollatzResearch.WordTrace]
  refine ⟨294686674434050903104992209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196457782956033935403328139 294686674434050903104992209)
  ·
    refine ⟨221015005825538177328744157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294686674434050903104992209 221015005825538177328744157)
    ·
      refine ⟨82880627184576816498279059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221015005825538177328744157 82880627184576816498279059)
      ·
        refine ⟨124320940776865224747418589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82880627184576816498279059 124320940776865224747418589)
        ·
          refine ⟨46620352791324459280281971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124320940776865224747418589 46620352791324459280281971)
          ·
            refine ⟨69930529186986688920422957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46620352791324459280281971 69930529186986688920422957)
            ·
              refine ⟨26223948445120008345158609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69930529186986688920422957 26223948445120008345158609)
              ·
                refine ⟨19667961333840006258868957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26223948445120008345158609 19667961333840006258868957)
                ·
                  refine ⟨7375485500190002347075859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19667961333840006258868957 7375485500190002347075859)
                  ·
                    refine ⟨11063228250285003520613789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7375485500190002347075859 11063228250285003520613789)
                    ·
                      refine ⟨4148710593856876320230171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11063228250285003520613789 4148710593856876320230171)
                      ·
                        rfl

theorem cell23_8079585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_8079585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079585 prefixEnd_8079585 := by exact prefixLift 8079585
  have htrace : WordTrace (prefixWord ++ tailWord_8079585) baseStart_8079585 baseEnd_8079585 := by
    simpa [prefixWord, tailWord_8079585, baseEnd_8079585] using wordTrace_append hprefix tailTrace_8079585
  have hstable : (prefixWord ++ tailWord_8079585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079585).length < 2 ^ (prefixWord ++ tailWord_8079585).sum := by decide
  have hdescent : baseEnd_8079585 < baseStart_8079585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079586 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_8079586 : Nat := 118140960795 + 8079586 * 2 ^ 59
def prefixEnd_8079586 : Nat := 4983230072969 + 3 ^ 40 * 8079586 * 2
def baseEnd_8079586 : Nat := 4148711107337530816317667

theorem tailTrace_8079586 : CollatzResearch.WordTrace tailWord_8079586 prefixEnd_8079586 4148711107337530816317667 := by
  unfold tailWord_8079586
  simp only [CollatzResearch.WordTrace]
  refine ⟨73671677726761820068944653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196457807271364853517185741 73671677726761820068944653)
  ·
    refine ⟨27626879147535682525854245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73671677726761820068944653 27626879147535682525854245)
    ·
      refine ⟨5180039840162940473597671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27626879147535682525854245 5180039840162940473597671)
      ·
        refine ⟨7770059760244410710396507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5180039840162940473597671 7770059760244410710396507)
        ·
          refine ⟨11655089640366616065594761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7770059760244410710396507 11655089640366616065594761)
          ·
            refine ⟨8741317230274962049196071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11655089640366616065594761 8741317230274962049196071)
            ·
              refine ⟨13111975845412443073794107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8741317230274962049196071 13111975845412443073794107)
              ·
                refine ⟨19667963768118664610691161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13111975845412443073794107 19667963768118664610691161)
                ·
                  refine ⟨14750972826088998458018371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19667963768118664610691161 14750972826088998458018371)
                  ·
                    refine ⟨22126459239133497687027557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14750972826088998458018371 22126459239133497687027557)
                    ·
                      refine ⟨4148711107337530816317667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22126459239133497687027557 4148711107337530816317667)
                      ·
                        rfl

theorem cell23_8079586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_8079586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079586 prefixEnd_8079586 := by exact prefixLift 8079586
  have htrace : WordTrace (prefixWord ++ tailWord_8079586) baseStart_8079586 baseEnd_8079586 := by
    simpa [prefixWord, tailWord_8079586, baseEnd_8079586] using wordTrace_append hprefix tailTrace_8079586
  have hstable : (prefixWord ++ tailWord_8079586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079586).length < 2 ^ (prefixWord ++ tailWord_8079586).sum := by decide
  have hdescent : baseEnd_8079586 < baseStart_8079586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079588 : List Nat := [2, 3, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_8079588 : Nat := 118140960795 + 8079588 * 2 ^ 59
def prefixEnd_8079588 : Nat := 4983230072969 + 3 ^ 40 * 8079588 * 2
def baseEnd_8079588 : Nat := 1382904044766279936164219

theorem tailTrace_8079588 : CollatzResearch.WordTrace tailWord_8079588 prefixEnd_8079588 1382904044766279936164219 := by
  unfold tailWord_8079588
  simp only [CollatzResearch.WordTrace]
  refine ⟨147343391926520017308675709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196457855902026689744900945 147343391926520017308675709)
  ·
    refine ⟨55253771972445006490753391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147343391926520017308675709 55253771972445006490753391)
    ·
      refine ⟨82880657958667509736130087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55253771972445006490753391 82880657958667509736130087)
      ·
        refine ⟨124320986938001264604195131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82880657958667509736130087 124320986938001264604195131)
        ·
          refine ⟨186481480407001896906292697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124320986938001264604195131 186481480407001896906292697)
          ·
            refine ⟨139861110305251422679719523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186481480407001896906292697 139861110305251422679719523)
            ·
              refine ⟨209791665457877134019579285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139861110305251422679719523 209791665457877134019579285)
              ·
                refine ⟨9833984318337990657167779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209791665457877134019579285 9833984318337990657167779)
                ·
                  refine ⟨14750976477506985985751669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9833984318337990657167779 14750976477506985985751669)
                  ·
                    refine ⟨1382904044766279936164219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14750976477506985985751669 1382904044766279936164219)
                    ·
                      rfl

theorem cell23_8079588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_8079588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079588 prefixEnd_8079588 := by exact prefixLift 8079588
  have htrace : WordTrace (prefixWord ++ tailWord_8079588) baseStart_8079588 baseEnd_8079588 := by
    simpa [prefixWord, tailWord_8079588, baseEnd_8079588] using wordTrace_append hprefix tailTrace_8079588
  have hstable : (prefixWord ++ tailWord_8079588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079588).length < 2 ^ (prefixWord ++ tailWord_8079588).sum := by decide
  have hdescent : baseEnd_8079588 < baseStart_8079588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079608 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 1, 8, 2]
def baseStart_8079608 : Nat := 118140960795 + 8079608 * 2 ^ 59
def prefixEnd_8079608 : Nat := 4983230072969 + 3 ^ 40 * 8079608 * 2
def baseEnd_8079608 : Nat := 4148722403911929730242565

theorem tailTrace_8079608 : CollatzResearch.WordTrace tailWord_8079608 prefixEnd_8079608 4148722403911929730242565 := by
  unfold tailWord_8079608
  simp only [CollatzResearch.WordTrace]
  refine ⟨147343756656483789016539739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196458342208645052022052985 147343756656483789016539739)
  ·
    refine ⟨221015634984725683524809609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147343756656483789016539739 221015634984725683524809609)
    ·
      refine ⟨165761726238544262643607207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221015634984725683524809609 165761726238544262643607207)
      ·
        refine ⟨248642589357816393965410811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165761726238544262643607207 248642589357816393965410811)
        ·
          refine ⟨372963884036724590948116217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248642589357816393965410811 372963884036724590948116217)
          ·
            refine ⟨279722913027543443211087163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372963884036724590948116217 279722913027543443211087163)
            ·
              refine ⟨419584369541315164816630745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279722913027543443211087163 419584369541315164816630745)
              ·
                refine ⟨314688277155986373612473059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419584369541315164816630745 314688277155986373612473059)
                ·
                  refine ⟨472032415733979560418709589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314688277155986373612473059 472032415733979560418709589)
                  ·
                    refine ⟨5531629871882572973656753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 472032415733979560418709589 5531629871882572973656753)
                    ·
                      refine ⟨4148722403911929730242565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5531629871882572973656753 4148722403911929730242565)
                      ·
                        rfl

theorem cell23_8079608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 8, 2].length) (baseStart_8079608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079608 prefixEnd_8079608 := by exact prefixLift 8079608
  have htrace : WordTrace (prefixWord ++ tailWord_8079608) baseStart_8079608 baseEnd_8079608 := by
    simpa [prefixWord, tailWord_8079608, baseEnd_8079608] using wordTrace_append hprefix tailTrace_8079608
  have hstable : (prefixWord ++ tailWord_8079608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079608).length < 2 ^ (prefixWord ++ tailWord_8079608).sum := by decide
  have hdescent : baseEnd_8079608 < baseStart_8079608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079611 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 5]
def baseStart_8079611 : Nat := 118140960795 + 8079611 * 2 ^ 59
def prefixEnd_8079611 : Nat := 4983230072969 + 3 ^ 40 * 8079611 * 2
def baseEnd_8079611 : Nat := 4148723944353893218505051

theorem tailTrace_8079611 : CollatzResearch.WordTrace tailWord_8079611 prefixEnd_8079611 4148723944353893218505051 := by
  unfold tailWord_8079611
  simp only [CollatzResearch.WordTrace]
  refine ⟨294687622731956709545438687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196458415154637806363625791 294687622731956709545438687)
  ·
    refine ⟨442031434097935064318158031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294687622731956709545438687 442031434097935064318158031)
    ·
      refine ⟨663047151146902596477237047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442031434097935064318158031 663047151146902596477237047)
      ·
        refine ⟨994570726720353894715855571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663047151146902596477237047 994570726720353894715855571)
        ·
          refine ⟨1491856090080530842073783357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994570726720353894715855571 1491856090080530842073783357)
          ·
            refine ⟨559446033780199065777668759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1491856090080530842073783357 559446033780199065777668759)
            ·
              refine ⟨839169050670298598666503139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559446033780199065777668759 839169050670298598666503139)
              ·
                refine ⟨1258753576005447897999754709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839169050670298598666503139 1258753576005447897999754709)
                ·
                  refine ⟨29502036937627685109369251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1258753576005447897999754709 29502036937627685109369251)
                  ·
                    refine ⟨44253055406441527664053877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29502036937627685109369251 44253055406441527664053877)
                    ·
                      refine ⟨4148723944353893218505051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44253055406441527664053877 4148723944353893218505051)
                      ·
                        rfl

theorem cell23_8079611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 5].length) (baseStart_8079611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079611 prefixEnd_8079611 := by exact prefixLift 8079611
  have htrace : WordTrace (prefixWord ++ tailWord_8079611) baseStart_8079611 baseEnd_8079611 := by
    simpa [prefixWord, tailWord_8079611, baseEnd_8079611] using wordTrace_append hprefix tailTrace_8079611
  have hstable : (prefixWord ++ tailWord_8079611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079611).length < 2 ^ (prefixWord ++ tailWord_8079611).sum := by decide
  have hdescent : baseEnd_8079611 < baseStart_8079611 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079628 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 1, 1, 5]
def baseStart_8079628 : Nat := 118140960795 + 8079628 * 2 ^ 59
def prefixEnd_8079628 : Nat := 4983230072969 + 3 ^ 40 * 8079628 * 2
def baseEnd_8079628 : Nat := 4148732673525019651992473

theorem tailTrace_8079628 : CollatzResearch.WordTrace tailWord_8079628 prefixEnd_8079628 4148732673525019651992473 := by
  unfold tailWord_8079628
  simp only [CollatzResearch.WordTrace]
  refine ⟨147344121386447560724403769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196458828515263414299205025 147344121386447560724403769)
  ·
    refine ⟨110508091039835670543302827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147344121386447560724403769 110508091039835670543302827)
    ·
      refine ⟨165762136559753505814954241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110508091039835670543302827 165762136559753505814954241)
      ·
        refine ⟨124321602419815129361215681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165762136559753505814954241 124321602419815129361215681)
        ·
          refine ⟨93241201814861347020911761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124321602419815129361215681 93241201814861347020911761)
          ·
            refine ⟨69930901361146010265683821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93241201814861347020911761 69930901361146010265683821)
            ·
              refine ⟨26224088010429753849631433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69930901361146010265683821 26224088010429753849631433)
              ·
                refine ⟨19668066007822315387223575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26224088010429753849631433 19668066007822315387223575)
                ·
                  refine ⟨29502099011733473080835363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19668066007822315387223575 29502099011733473080835363)
                  ·
                    refine ⟨44253148517600209621253045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29502099011733473080835363 44253148517600209621253045)
                    ·
                      refine ⟨4148732673525019651992473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44253148517600209621253045 4148732673525019651992473)
                      ·
                        rfl

theorem cell23_8079628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_8079628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079628 prefixEnd_8079628 := by exact prefixLift 8079628
  have htrace : WordTrace (prefixWord ++ tailWord_8079628) baseStart_8079628 baseEnd_8079628 := by
    simpa [prefixWord, tailWord_8079628, baseEnd_8079628] using wordTrace_append hprefix tailTrace_8079628
  have hstable : (prefixWord ++ tailWord_8079628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079628).length < 2 ^ (prefixWord ++ tailWord_8079628).sum := by decide
  have hdescent : baseEnd_8079628 < baseStart_8079628 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079642 : List Nat := [3, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4]
def baseStart_8079642 : Nat := 118140960795 + 8079642 * 2 ^ 59
def prefixEnd_8079642 : Nat := 4983230072969 + 3 ^ 40 * 8079642 * 2
def baseEnd_8079642 : Nat := 4148739862254182597217409

theorem tailTrace_8079642 : CollatzResearch.WordTrace tailWord_8079642 prefixEnd_8079642 4148739862254182597217409 := by
  unfold tailWord_8079642
  simp only [CollatzResearch.WordTrace]
  refine ⟨73672188348711100459954295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196459168929896267893211453 73672188348711100459954295)
  ·
    refine ⟨110508282523066650689931443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73672188348711100459954295 110508282523066650689931443)
    ·
      refine ⟨165762423784599976034897165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110508282523066650689931443 165762423784599976034897165)
      ·
        refine ⟨62160908919224991013086437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165762423784599976034897165 62160908919224991013086437)
        ·
          refine ⟨11655170422354685814953707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62160908919224991013086437 11655170422354685814953707)
          ·
            refine ⟨17482755633532028722430561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11655170422354685814953707 17482755633532028722430561)
            ·
              refine ⟨13112066725149021541822921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17482755633532028722430561 13112066725149021541822921)
              ·
                refine ⟨9834050043861766156367191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13112066725149021541822921 9834050043861766156367191)
                ·
                  refine ⟨14751075065792649234550787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9834050043861766156367191 14751075065792649234550787)
                  ·
                    refine ⟨22126612598688973851826181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14751075065792649234550787 22126612598688973851826181)
                    ·
                      refine ⟨4148739862254182597217409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22126612598688973851826181 4148739862254182597217409)
                      ·
                        rfl

theorem cell23_8079642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_8079642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079642 prefixEnd_8079642 := by exact prefixLift 8079642
  have htrace : WordTrace (prefixWord ++ tailWord_8079642) baseStart_8079642 baseEnd_8079642 := by
    simpa [prefixWord, tailWord_8079642, baseEnd_8079642] using wordTrace_append hprefix tailTrace_8079642
  have hstable : (prefixWord ++ tailWord_8079642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079642).length < 2 ^ (prefixWord ++ tailWord_8079642).sum := by decide
  have hdescent : baseEnd_8079642 < baseStart_8079642 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079648 : List Nat := [2, 1, 1, 5, 2, 2, 1, 9]
def baseStart_8079648 : Nat := 118140960795 + 8079648 * 2 ^ 59
def prefixEnd_8079648 : Nat := 4983230072969 + 3 ^ 40 * 8079648 * 2
def baseEnd_8079648 : Nat := 153657146042152206434903

theorem tailTrace_8079648 : CollatzResearch.WordTrace tailWord_8079648 prefixEnd_8079648 153657146042152206434903 := by
  unfold tailWord_8079648
  simp only [CollatzResearch.WordTrace]
  refine ⟨147344486116411332432267799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196459314821881776576357065 147344486116411332432267799)
  ·
    refine ⟨221016729174616998648401699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147344486116411332432267799 221016729174616998648401699)
    ·
      refine ⟨331525093761925497972602549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221016729174616998648401699 331525093761925497972602549)
      ·
        refine ⟨31080477540180515434931489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 331525093761925497972602549 31080477540180515434931489)
        ·
          refine ⟨23310358155135386576198617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31080477540180515434931489 23310358155135386576198617)
          ·
            refine ⟨17482768616351539932148963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23310358155135386576198617 17482768616351539932148963)
            ·
              refine ⟨26224152924527309898223445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17482768616351539932148963 26224152924527309898223445)
              ·
                refine ⟨153657146042152206434903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26224152924527309898223445 153657146042152206434903)
                ·
                  rfl

theorem cell23_8079648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 9].length) (baseStart_8079648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079648 prefixEnd_8079648 := by exact prefixLift 8079648
  have htrace : WordTrace (prefixWord ++ tailWord_8079648) baseStart_8079648 baseEnd_8079648 := by
    simpa [prefixWord, tailWord_8079648, baseEnd_8079648] using wordTrace_append hprefix tailTrace_8079648
  have hstable : (prefixWord ++ tailWord_8079648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079648).length < 2 ^ (prefixWord ++ tailWord_8079648).sum := by decide
  have hdescent : baseEnd_8079648 < baseStart_8079648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079665 : List Nat := [1, 2, 2, 3, 5, 1, 9]
def baseStart_8079665 : Nat := 118140960795 + 8079665 * 2 ^ 59
def prefixEnd_8079665 : Nat := 4983230072969 + 3 ^ 40 * 8079665 * 2
def baseEnd_8079665 : Nat := 51219156448262172928763

theorem tailTrace_8079665 : CollatzResearch.WordTrace tailWord_8079665 prefixEnd_8079665 51219156448262172928763 := by
  unfold tailWord_8079665
  simp only [CollatzResearch.WordTrace]
  refine ⟨294689592273761076767904449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196459728182507384511936299 294689592273761076767904449)
  ·
    refine ⟨221017194205320807575928337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294689592273761076767904449 221017194205320807575928337)
    ·
      refine ⟨165762895653990605681946253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221017194205320807575928337 165762895653990605681946253)
      ·
        refine ⟨62161085870246477130729845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165762895653990605681946253 62161085870246477130729845)
        ·
          refine ⟨5827601800335607231005923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62161085870246477130729845 5827601800335607231005923)
          ·
            refine ⟨8741402700503410846508885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5827601800335607231005923 8741402700503410846508885)
            ·
              refine ⟨51219156448262172928763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8741402700503410846508885 51219156448262172928763)
              ·
                rfl

theorem cell23_8079665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 9].length) (baseStart_8079665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079665 prefixEnd_8079665 := by exact prefixLift 8079665
  have htrace : WordTrace (prefixWord ++ tailWord_8079665) baseStart_8079665 baseEnd_8079665 := by
    simpa [prefixWord, tailWord_8079665, baseEnd_8079665] using wordTrace_append hprefix tailTrace_8079665
  have hstable : (prefixWord ++ tailWord_8079665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079665).length < 2 ^ (prefixWord ++ tailWord_8079665).sum := by decide
  have hdescent : baseEnd_8079665 < baseStart_8079665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079676 : List Nat := [2, 2, 2, 2, 1, 2, 5, 2, 1, 2, 2]
def baseStart_8079676 : Nat := 118140960795 + 8079676 * 2 ^ 59
def prefixEnd_8079676 : Nat := 4983230072969 + 3 ^ 40 * 8079676 * 2
def baseEnd_8079676 : Nat := 4148757320596435464192253

theorem tailTrace_8079676 : CollatzResearch.WordTrace tailWord_8079676 prefixEnd_8079676 4148757320596435464192253 := by
  unfold tailWord_8079676
  simp only [CollatzResearch.WordTrace]
  refine ⟨147344996738360612823277441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196459995651147483764369921 147344996738360612823277441)
  ·
    refine ⟨110508747553770459617458081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147344996738360612823277441 110508747553770459617458081)
    ·
      refine ⟨82881560665327844713093561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110508747553770459617458081 82881560665327844713093561)
      ·
        refine ⟨62161170498995883534820171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82881560665327844713093561 62161170498995883534820171)
        ·
          refine ⟨93241755748493825302230257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62161170498995883534820171 93241755748493825302230257)
          ·
            refine ⟨69931316811370368976672693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93241755748493825302230257 69931316811370368976672693)
            ·
              refine ⟨6556060951065972091563065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69931316811370368976672693 6556060951065972091563065)
              ·
                refine ⟨4917045713299479068672299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6556060951065972091563065 4917045713299479068672299)
                ·
                  refine ⟨7375568569949218603008449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4917045713299479068672299 7375568569949218603008449)
                  ·
                    refine ⟨5531676427461913952256337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7375568569949218603008449 5531676427461913952256337)
                    ·
                      refine ⟨4148757320596435464192253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5531676427461913952256337 4148757320596435464192253)
                      ·
                        rfl

theorem cell23_8079676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_8079676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079676 prefixEnd_8079676 := by exact prefixLift 8079676
  have htrace : WordTrace (prefixWord ++ tailWord_8079676) baseStart_8079676 baseEnd_8079676 := by
    simpa [prefixWord, tailWord_8079676, baseEnd_8079676] using wordTrace_append hprefix tailTrace_8079676
  have hstable : (prefixWord ++ tailWord_8079676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079676).length < 2 ^ (prefixWord ++ tailWord_8079676).sum := by decide
  have hdescent : baseEnd_8079676 < baseStart_8079676 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079692 : List Nat := [2, 2, 1, 3, 2, 1, 3, 3, 2, 1, 3]
def baseStart_8079692 : Nat := 118140960795 + 8079692 * 2 ^ 59
def prefixEnd_8079692 : Nat := 4983230072969 + 3 ^ 40 * 8079692 * 2
def baseEnd_8079692 : Nat := 4148765536286907401592179

theorem tailTrace_8079692 : CollatzResearch.WordTrace tailWord_8079692 prefixEnd_8079692 4148765536286907401592179 := by
  unfold tailWord_8079692
  simp only [CollatzResearch.WordTrace]
  refine ⟨147345288522331630189568665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196460384696442173586091553 147345288522331630189568665)
  ·
    refine ⟨110508966391748722642176499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147345288522331630189568665 110508966391748722642176499)
    ·
      refine ⟨165763449587623083963264749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110508966391748722642176499 165763449587623083963264749)
      ·
        refine ⟨62161293595358656486224281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165763449587623083963264749 62161293595358656486224281)
        ·
          refine ⟨46620970196518992364668211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62161293595358656486224281 46620970196518992364668211)
          ·
            refine ⟨69931455294778488547002317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46620970196518992364668211 69931455294778488547002317)
            ·
              refine ⟨26224295735541933205125869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69931455294778488547002317 26224295735541933205125869)
              ·
                refine ⟨9834110900828224951922201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26224295735541933205125869 9834110900828224951922201)
                ·
                  refine ⟨7375583175621168713941651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9834110900828224951922201 7375583175621168713941651)
                  ·
                    refine ⟨11063374763431753070912477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7375583175621168713941651 11063374763431753070912477)
                    ·
                      refine ⟨4148765536286907401592179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11063374763431753070912477 4148765536286907401592179)
                      ·
                        rfl

theorem cell23_8079692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_8079692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079692 prefixEnd_8079692 := by exact prefixLift 8079692
  have htrace : WordTrace (prefixWord ++ tailWord_8079692) baseStart_8079692 baseEnd_8079692 := by
    simpa [prefixWord, tailWord_8079692, baseEnd_8079692] using wordTrace_append hprefix tailTrace_8079692
  have hstable : (prefixWord ++ tailWord_8079692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079692).length < 2 ^ (prefixWord ++ tailWord_8079692).sum := by decide
  have hdescent : baseEnd_8079692 < baseStart_8079692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079710 : List Nat := [4, 4, 2, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_8079710 : Nat := 118140960795 + 8079710 * 2 ^ 59
def prefixEnd_8079710 : Nat := 4983230072969 + 3 ^ 40 * 8079710 * 2
def baseEnd_8079710 : Nat := 4148774778938688331167097

theorem tailTrace_8079710 : CollatzResearch.WordTrace tailWord_8079710 prefixEnd_8079710 4148774778938688331167097 := by
  unfold tailWord_8079710
  simp only [CollatzResearch.WordTrace]
  refine ⟨36836404194824756181661573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196460822372398699635528389 36836404194824756181661573)
  ·
    refine ⟨6906825786529641784061545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36836404194824756181661573 6906825786529641784061545)
    ·
      refine ⟨5180119339897231338046159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6906825786529641784061545 5180119339897231338046159)
      ·
        refine ⟨7770179009845847007069239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5180119339897231338046159 7770179009845847007069239)
        ·
          refine ⟨11655268514768770510603859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7770179009845847007069239 11655268514768770510603859)
          ·
            refine ⟨17482902772153155765905789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11655268514768770510603859 17482902772153155765905789)
            ·
              refine ⟨6556088539557433412214671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17482902772153155765905789 6556088539557433412214671)
              ·
                refine ⟨9834132809336150118322007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6556088539557433412214671 9834132809336150118322007)
                ·
                  refine ⟨14751199214004225177483011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9834132809336150118322007 14751199214004225177483011)
                  ·
                    refine ⟨22126798821006337766224517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14751199214004225177483011 22126798821006337766224517)
                    ·
                      refine ⟨4148774778938688331167097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22126798821006337766224517 4148774778938688331167097)
                      ·
                        rfl

theorem cell23_8079710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_8079710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079710 prefixEnd_8079710 := by exact prefixLift 8079710
  have htrace : WordTrace (prefixWord ++ tailWord_8079710) baseStart_8079710 baseEnd_8079710 := by
    simpa [prefixWord, tailWord_8079710, baseEnd_8079710] using wordTrace_append hprefix tailTrace_8079710
  have hstable : (prefixWord ++ tailWord_8079710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079710).length < 2 ^ (prefixWord ++ tailWord_8079710).sum := by decide
  have hdescent : baseEnd_8079710 < baseStart_8079710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079745 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_8079745 : Nat := 118140960795 + 8079745 * 2 ^ 59
def prefixEnd_8079745 : Nat := 4983230072969 + 3 ^ 40 * 8079745 * 2
def baseEnd_8079745 : Nat := 4148792750761595694229435

theorem tailTrace_8079745 : CollatzResearch.WordTrace tailWord_8079745 prefixEnd_8079745 4148792750761595694229435 := by
  unfold tailWord_8079745
  simp only [CollatzResearch.WordTrace]
  refine ⟨294692510113471250430816689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196461673408980833620544459 294692510113471250430816689)
  ·
    refine ⟨221019382585103437823112517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294692510113471250430816689 221019382585103437823112517)
    ·
      refine ⟨41441134234706894591833597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221019382585103437823112517 41441134234706894591833597)
      ·
        refine ⟨15540425338015085471937599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41441134234706894591833597 15540425338015085471937599)
        ·
          refine ⟨23310638007022628207906399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15540425338015085471937599 23310638007022628207906399)
          ·
            refine ⟨34965957010533942311859599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23310638007022628207906399 34965957010533942311859599)
            ·
              refine ⟨52448935515800913467789399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34965957010533942311859599 52448935515800913467789399)
              ·
                refine ⟨78673403273701370201684099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52448935515800913467789399 78673403273701370201684099)
                ·
                  refine ⟨118010104910552055302526149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78673403273701370201684099 118010104910552055302526149)
                  ·
                    refine ⟨22126894670728510369223653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118010104910552055302526149 22126894670728510369223653)
                    ·
                      refine ⟨4148792750761595694229435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22126894670728510369223653 4148792750761595694229435)
                      ·
                        rfl

theorem cell23_8079745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_8079745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079745 prefixEnd_8079745 := by exact prefixLift 8079745
  have htrace : WordTrace (prefixWord ++ tailWord_8079745) baseStart_8079745 baseEnd_8079745 := by
    simpa [prefixWord, tailWord_8079745, baseEnd_8079745] using wordTrace_append hprefix tailTrace_8079745
  have hstable : (prefixWord ++ tailWord_8079745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079745).length < 2 ^ (prefixWord ++ tailWord_8079745).sum := by decide
  have hdescent : baseEnd_8079745 < baseStart_8079745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079805 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_8079805 : Nat := 118140960795 + 8079805 * 2 ^ 59
def prefixEnd_8079805 : Nat := 4983230072969 + 3 ^ 40 * 8079805 * 2
def baseEnd_8079805 : Nat := 4148823559600865459479159

theorem tailTrace_8079805 : CollatzResearch.WordTrace tailWord_8079805 prefixEnd_8079805 4148823559600865459479159 := by
  unfold tailWord_8079805
  simp only [CollatzResearch.WordTrace]
  refine ⟨294694698493253880678000869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196463132328835920452000579 294694698493253880678000869)
  ·
    refine ⟨55255255967485102627125163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294694698493253880678000869 55255255967485102627125163)
    ·
      refine ⟨82882883951227653940687745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55255255967485102627125163 82882883951227653940687745)
      ·
        refine ⟨62162162963420740455515809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82882883951227653940687745 62162162963420740455515809)
        ·
          refine ⟨46621622222565555341636857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62162162963420740455515809 46621622222565555341636857)
          ·
            refine ⟨34966216666924166506227643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46621622222565555341636857 34966216666924166506227643)
            ·
              refine ⟨52449325000386249759341465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34966216666924166506227643 52449325000386249759341465)
              ·
                refine ⟨39336993750289687319506099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52449325000386249759341465 39336993750289687319506099)
                ·
                  refine ⟨59005490625434530979259149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39336993750289687319506099 59005490625434530979259149)
                  ·
                    refine ⟨22127058984537949117222181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59005490625434530979259149 22127058984537949117222181)
                    ·
                      refine ⟨4148823559600865459479159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22127058984537949117222181 4148823559600865459479159)
                      ·
                        rfl

theorem cell23_8079805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_8079805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079805 prefixEnd_8079805 := by exact prefixLift 8079805
  have htrace : WordTrace (prefixWord ++ tailWord_8079805) baseStart_8079805 baseEnd_8079805 := by
    simpa [prefixWord, tailWord_8079805, baseEnd_8079805] using wordTrace_append hprefix tailTrace_8079805
  have hstable : (prefixWord ++ tailWord_8079805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079805).length < 2 ^ (prefixWord ++ tailWord_8079805).sum := by decide
  have hdescent : baseEnd_8079805 < baseStart_8079805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079825 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 6, 2, 3]
def baseStart_8079825 : Nat := 118140960795 + 8079825 * 2 ^ 59
def prefixEnd_8079825 : Nat := 4983230072969 + 3 ^ 40 * 8079825 * 2
def baseEnd_8079825 : Nat := 4148833829213955381229067

theorem tailTrace_8079825 : CollatzResearch.WordTrace tailWord_8079825 prefixEnd_8079825 4148833829213955381229067 := by
  unfold tailWord_8079825
  simp only [CollatzResearch.WordTrace]
  refine ⟨294695427953181424093728929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196463618635454282729152619 294695427953181424093728929)
  ·
    refine ⟨221021570964886068070296697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294695427953181424093728929 221021570964886068070296697)
    ·
      refine ⟨165766178223664551052722523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221021570964886068070296697 165766178223664551052722523)
      ·
        refine ⟨248649267335496826579083785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165766178223664551052722523 248649267335496826579083785)
        ·
          refine ⟨186486950501622619934312839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248649267335496826579083785 186486950501622619934312839)
          ·
            refine ⟨279730425752433929901469259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186486950501622619934312839 279730425752433929901469259)
            ·
              refine ⟨419595638628650894852203889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279730425752433929901469259 419595638628650894852203889)
              ·
                refine ⟨314696728971488171139152917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419595638628650894852203889 314696728971488171139152917)
                ·
                  refine ⟨14751409170538508022147793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 314696728971488171139152917 14751409170538508022147793)
                  ·
                    refine ⟨11063556877903881016610845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14751409170538508022147793 11063556877903881016610845)
                    ·
                      refine ⟨4148833829213955381229067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11063556877903881016610845 4148833829213955381229067)
                      ·
                        rfl

theorem cell23_8079825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_8079825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079825 prefixEnd_8079825 := by exact prefixLift 8079825
  have htrace : WordTrace (prefixWord ++ tailWord_8079825) baseStart_8079825 baseEnd_8079825 := by
    simpa [prefixWord, tailWord_8079825, baseEnd_8079825] using wordTrace_append hprefix tailTrace_8079825
  have hstable : (prefixWord ++ tailWord_8079825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079825).length < 2 ^ (prefixWord ++ tailWord_8079825).sum := by decide
  have hdescent : baseEnd_8079825 < baseStart_8079825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079862 : List Nat := [5, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_8079862 : Nat := 118140960795 + 8079862 * 2 ^ 59
def prefixEnd_8079862 : Nat := 4983230072969 + 3 ^ 40 * 8079862 * 2
def baseEnd_8079862 : Nat := 460983647555352415162933

theorem tailTrace_8079862 : CollatzResearch.WordTrace tailWord_8079862 prefixEnd_8079862 460983647555352415162933 := by
  unfold tailWord_8079862
  simp only [CollatzResearch.WordTrace]
  refine ⟨18418548590877961213301615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196464518302698252941883893 18418548590877961213301615)
  ·
    refine ⟨27627822886316941819952423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18418548590877961213301615 27627822886316941819952423)
    ·
      refine ⟨41441734329475412729928635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27627822886316941819952423 41441734329475412729928635)
      ·
        refine ⟨62162601494213119094892953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41441734329475412729928635 62162601494213119094892953)
        ·
          refine ⟨46621951120659839321169715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62162601494213119094892953 46621951120659839321169715)
          ·
            refine ⟨69932926680989758981754573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46621951120659839321169715 69932926680989758981754573)
            ·
              refine ⟨26224847505371159618157965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69932926680989758981754573 26224847505371159618157965)
              ·
                refine ⟨9834317814514184856809237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26224847505371159618157965 9834317814514184856809237)
                ·
                  refine ⟨460983647555352415162933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9834317814514184856809237 460983647555352415162933)
                  ·
                    rfl

theorem cell23_8079862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_8079862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079862 prefixEnd_8079862 := by exact prefixLift 8079862
  have htrace : WordTrace (prefixWord ++ tailWord_8079862) baseStart_8079862 baseEnd_8079862 := by
    simpa [prefixWord, tailWord_8079862, baseEnd_8079862] using wordTrace_append hprefix tailTrace_8079862
  have hstable : (prefixWord ++ tailWord_8079862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079862).length < 2 ^ (prefixWord ++ tailWord_8079862).sum := by decide
  have hdescent : baseEnd_8079862 < baseStart_8079862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079875 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 3, 5]
def baseStart_8079875 : Nat := 118140960795 + 8079875 * 2 ^ 59
def prefixEnd_8079875 : Nat := 4983230072969 + 3 ^ 40 * 8079875 * 2
def baseEnd_8079875 : Nat := 1382953167748893395201279

theorem tailTrace_8079875 : CollatzResearch.WordTrace tailWord_8079875 prefixEnd_8079875 1382953167748893395201279 := by
  unfold tailWord_8079875
  simp only [CollatzResearch.WordTrace]
  refine ⟨294697251603000282633049079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196464834402000188422032719 294697251603000282633049079)
  ·
    refine ⟨442045877404500423949573619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294697251603000282633049079 442045877404500423949573619)
    ·
      refine ⟨663068816106750635924360429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442045877404500423949573619 663068816106750635924360429)
      ·
        refine ⟨248650806040031488471635161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 663068816106750635924360429 248650806040031488471635161)
        ·
          refine ⟨186488104530023616353726371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248650806040031488471635161 186488104530023616353726371)
          ·
            refine ⟨279732156795035424530589557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186488104530023616353726371 279732156795035424530589557)
            ·
              refine ⟨26224889699534571049742771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279732156795035424530589557 26224889699534571049742771)
              ·
                refine ⟨39337334549301856574614157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26224889699534571049742771 39337334549301856574614157)
                ·
                  refine ⟨14751500455988196215480309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39337334549301856574614157 14751500455988196215480309)
                  ·
                    refine ⟨1382953167748893395201279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14751500455988196215480309 1382953167748893395201279)
                    ·
                      rfl

theorem cell23_8079875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 5].length) (baseStart_8079875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079875 prefixEnd_8079875 := by exact prefixLift 8079875
  have htrace : WordTrace (prefixWord ++ tailWord_8079875) baseStart_8079875 baseEnd_8079875 := by
    simpa [prefixWord, tailWord_8079875, baseEnd_8079875] using wordTrace_append hprefix tailTrace_8079875
  have hstable : (prefixWord ++ tailWord_8079875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079875).length < 2 ^ (prefixWord ++ tailWord_8079875).sum := by decide
  have hdescent : baseEnd_8079875 < baseStart_8079875 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079905 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 3, 6]
def baseStart_8079905 : Nat := 118140960795 + 8079905 * 2 ^ 59
def prefixEnd_8079905 : Nat := 4983230072969 + 3 ^ 40 * 8079905 * 2
def baseEnd_8079905 : Nat := 1382958302555438356076233

theorem tailTrace_8079905 : CollatzResearch.WordTrace tailWord_8079905 prefixEnd_8079905 1382958302555438356076233 := by
  unfold tailWord_8079905
  simp only [CollatzResearch.WordTrace]
  refine ⟨294698345792891597756641169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196465563861927731837760779 294698345792891597756641169)
  ·
    refine ⟨221023759344668698317480877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294698345792891597756641169 221023759344668698317480877)
    ·
      refine ⟨82883909754250761869055329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221023759344668698317480877 82883909754250761869055329)
      ·
        refine ⟨62162932315688071401791497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82883909754250761869055329 62162932315688071401791497)
        ·
          refine ⟨46622199236766053551343623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62162932315688071401791497 46622199236766053551343623)
          ·
            refine ⟨69933298855149080327015435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46622199236766053551343623 69933298855149080327015435)
            ·
              refine ⟨104899948282723620490523153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69933298855149080327015435 104899948282723620490523153)
              ·
                refine ⟨78674961212042715367892365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104899948282723620490523153 78674961212042715367892365)
                ·
                  refine ⟨29503110454516018262959637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78674961212042715367892365 29503110454516018262959637)
                  ·
                    refine ⟨1382958302555438356076233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29503110454516018262959637 1382958302555438356076233)
                    ·
                      rfl

theorem cell23_8079905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_8079905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079905 prefixEnd_8079905 := by exact prefixLift 8079905
  have htrace : WordTrace (prefixWord ++ tailWord_8079905) baseStart_8079905 baseEnd_8079905 := by
    simpa [prefixWord, tailWord_8079905, baseEnd_8079905] using wordTrace_append hprefix tailTrace_8079905
  have hstable : (prefixWord ++ tailWord_8079905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079905).length < 2 ^ (prefixWord ++ tailWord_8079905).sum := by decide
  have hdescent : baseEnd_8079905 < baseStart_8079905 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079915 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 5]
def baseStart_8079915 : Nat := 118140960795 + 8079915 * 2 ^ 59
def prefixEnd_8079915 : Nat := 4983230072969 + 3 ^ 40 * 8079915 * 2
def baseEnd_8079915 : Nat := 4148880042472860029103653

theorem tailTrace_8079915 : CollatzResearch.WordTrace tailWord_8079915 prefixEnd_8079915 4148880042472860029103653 := by
  unfold tailWord_8079915
  simp only [CollatzResearch.WordTrace]
  refine ⟨294698710522855369464505199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196465807015236912976336799 294698710522855369464505199)
  ·
    refine ⟨442048065784283054196757799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294698710522855369464505199 442048065784283054196757799)
    ·
      refine ⟨663072098676424581295136699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442048065784283054196757799 663072098676424581295136699)
      ·
        refine ⟨994608148014636871942705049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663072098676424581295136699 994608148014636871942705049)
        ·
          refine ⟨745956111010977653957028787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 994608148014636871942705049 745956111010977653957028787)
          ·
            refine ⟨1118934166516466480935543181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745956111010977653957028787 1118934166516466480935543181)
            ·
              refine ⟨419600312443674930350828693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1118934166516466480935543181 419600312443674930350828693)
              ·
                refine ⟨19668764645797262360195095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 419600312443674930350828693 19668764645797262360195095)
                ·
                  refine ⟨29503146968695893540292643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19668764645797262360195095 29503146968695893540292643)
                  ·
                    refine ⟨44254720453043840310438965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29503146968695893540292643 44254720453043840310438965)
                    ·
                      refine ⟨4148880042472860029103653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44254720453043840310438965 4148880042472860029103653)
                      ·
                        rfl

theorem cell23_8079915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 5].length) (baseStart_8079915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079915 prefixEnd_8079915 := by exact prefixLift 8079915
  have htrace : WordTrace (prefixWord ++ tailWord_8079915) baseStart_8079915 baseEnd_8079915 := by
    simpa [prefixWord, tailWord_8079915, baseEnd_8079915] using wordTrace_append hprefix tailTrace_8079915
  have hstable : (prefixWord ++ tailWord_8079915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079915).length < 2 ^ (prefixWord ++ tailWord_8079915).sum := by decide
  have hdescent : baseEnd_8079915 < baseStart_8079915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079946 : List Nat := [3, 1, 2, 1, 1, 6, 2, 1, 1, 1, 4]
def baseStart_8079946 : Nat := 118140960795 + 8079946 * 2 ^ 59
def prefixEnd_8079946 : Nat := 4983230072969 + 3 ^ 40 * 8079946 * 2
def baseEnd_8079946 : Nat := 4148895960373149407816011

theorem tailTrace_8079946 : CollatzResearch.WordTrace tailWord_8079946 prefixEnd_8079946 4148895960373149407816011 := by
  unfold tailWord_8079946
  simp only [CollatzResearch.WordTrace]
  refine ⟨73674960296435765439720923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196466560790495374505922461 73674960296435765439720923)
  ·
    refine ⟨110512440444653648159581385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73674960296435765439720923 110512440444653648159581385)
    ·
      refine ⟨82884330333490236119686039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110512440444653648159581385 82884330333490236119686039)
      ·
        refine ⟨124326495500235354179529059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82884330333490236119686039 124326495500235354179529059)
        ·
          refine ⟨186489743250353031269293589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124326495500235354179529059 186489743250353031269293589)
          ·
            refine ⟨8741706714860298340748137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 186489743250353031269293589 8741706714860298340748137)
            ·
              refine ⟨6556280036145223755561103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8741706714860298340748137 6556280036145223755561103)
              ·
                refine ⟨9834420054217835633341655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6556280036145223755561103 9834420054217835633341655)
                ·
                  refine ⟨14751630081326753450012483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9834420054217835633341655 14751630081326753450012483)
                  ·
                    refine ⟨22127445121990130175018725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14751630081326753450012483 22127445121990130175018725)
                    ·
                      refine ⟨4148895960373149407816011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22127445121990130175018725 4148895960373149407816011)
                      ·
                        rfl

theorem cell23_8079946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_8079946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079946 prefixEnd_8079946 := by exact prefixLift 8079946
  have htrace : WordTrace (prefixWord ++ tailWord_8079946) baseStart_8079946 baseEnd_8079946 := by
    simpa [prefixWord, tailWord_8079946, baseEnd_8079946] using wordTrace_append hprefix tailTrace_8079946
  have hstable : (prefixWord ++ tailWord_8079946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079946).length < 2 ^ (prefixWord ++ tailWord_8079946).sum := by decide
  have hdescent : baseEnd_8079946 < baseStart_8079946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079956 : List Nat := [2, 4, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_8079956 : Nat := 118140960795 + 8079956 * 2 ^ 59
def prefixEnd_8079956 : Nat := 4983230072969 + 3 ^ 40 * 8079956 * 2
def baseEnd_8079956 : Nat := 1382967031726564789563655

theorem tailTrace_8079956 : CollatzResearch.WordTrace tailWord_8079956 prefixEnd_8079956 1382967031726564789563655 := by
  unfold tailWord_8079956
  simp only [CollatzResearch.WordTrace]
  refine ⟨147350102957853416733373861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196466803943804555644498481 147350102957853416733373861)
  ·
    refine ⟨27628144304597515637507599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147350102957853416733373861 27628144304597515637507599)
    ·
      refine ⟨41442216456896273456261399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27628144304597515637507599 41442216456896273456261399)
      ·
        refine ⟨62163324685344410184392099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41442216456896273456261399 62163324685344410184392099)
        ·
          refine ⟨93244987028016615276588149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62163324685344410184392099 93244987028016615276588149)
          ·
            refine ⟨8741717533876557682180139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93244987028016615276588149 8741717533876557682180139)
            ·
              refine ⟨13112576300814836523270209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8741717533876557682180139 13112576300814836523270209)
              ·
                refine ⟨9834432225611127392452657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13112576300814836523270209 9834432225611127392452657)
                ·
                  refine ⟨7375824169208345544339493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9834432225611127392452657 7375824169208345544339493)
                  ·
                    refine ⟨1382967031726564789563655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7375824169208345544339493 1382967031726564789563655)
                    ·
                      rfl

theorem cell23_8079956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_8079956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079956 prefixEnd_8079956 := by exact prefixLift 8079956
  have htrace : WordTrace (prefixWord ++ tailWord_8079956) baseStart_8079956 baseEnd_8079956 := by
    simpa [prefixWord, tailWord_8079956, baseEnd_8079956] using wordTrace_append hprefix tailTrace_8079956
  have hstable : (prefixWord ++ tailWord_8079956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079956).length < 2 ^ (prefixWord ++ tailWord_8079956).sum := by decide
  have hdescent : baseEnd_8079956 < baseStart_8079956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079976 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_8079976 : Nat := 118140960795 + 8079976 * 2 ^ 59
def prefixEnd_8079976 : Nat := 4983230072969 + 3 ^ 40 * 8079976 * 2
def baseEnd_8079976 : Nat := 4148911364792784290440873

theorem tailTrace_8079976 : CollatzResearch.WordTrace tailWord_8079976 prefixEnd_8079976 4148911364792784290440873 := by
  unfold tailWord_8079976
  simp only [CollatzResearch.WordTrace]
  refine ⟨147350467687817188441237891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196467290250422917921650521 147350467687817188441237891)
  ·
    refine ⟨221025701531725782661856837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147350467687817188441237891 221025701531725782661856837)
    ·
      refine ⟨41442319037198584249098157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221025701531725782661856837 41442319037198584249098157)
      ·
        refine ⟨15540869638949469093411809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41442319037198584249098157 15540869638949469093411809)
        ·
          refine ⟨11655652229212101820058857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15540869638949469093411809 11655652229212101820058857)
          ·
            refine ⟨8741739171909076365044143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11655652229212101820058857 8741739171909076365044143)
            ·
              refine ⟨13112608757863614547566215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8741739171909076365044143 13112608757863614547566215)
              ·
                refine ⟨19668913136795421821349323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13112608757863614547566215 19668913136795421821349323)
                ·
                  refine ⟨29503369705193132732023985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19668913136795421821349323 29503369705193132732023985)
                  ·
                    refine ⟨22127527278894849549017989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29503369705193132732023985 22127527278894849549017989)
                    ·
                      refine ⟨4148911364792784290440873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22127527278894849549017989 4148911364792784290440873)
                      ·
                        rfl

theorem cell23_8079976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_8079976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079976 prefixEnd_8079976 := by exact prefixLift 8079976
  have htrace : WordTrace (prefixWord ++ tailWord_8079976) baseStart_8079976 baseEnd_8079976 := by
    simpa [prefixWord, tailWord_8079976, baseEnd_8079976] using wordTrace_append hprefix tailTrace_8079976
  have hstable : (prefixWord ++ tailWord_8079976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079976).length < 2 ^ (prefixWord ++ tailWord_8079976).sum := by decide
  have hdescent : baseEnd_8079976 < baseStart_8079976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079986 : List Nat := [3, 2, 1, 2, 5, 1, 2, 7]
def baseStart_8079986 : Nat := 118140960795 + 8079986 * 2 ^ 59
def prefixEnd_8079986 : Nat := 4983230072969 + 3 ^ 40 * 8079986 * 2
def baseEnd_8079986 : Nat := 153663574059234416715401

theorem tailTrace_8079986 : CollatzResearch.WordTrace tailWord_8079986 prefixEnd_8079986 153663574059234416715401 := by
  unfold tailWord_8079986
  simp only [CollatzResearch.WordTrace]
  refine ⟨73675325026399537147584953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196467533403732099060226541 73675325026399537147584953)
  ·
    refine ⟨55256493769799652860688715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73675325026399537147584953 55256493769799652860688715)
    ·
      refine ⟨82884740654699479291033073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55256493769799652860688715 82884740654699479291033073)
      ·
        refine ⟨62163555491024609468274805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82884740654699479291033073 62163555491024609468274805)
        ·
          refine ⟨5827833327283557137650763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62163555491024609468274805 5827833327283557137650763)
          ·
            refine ⟨8741749990925335706476145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5827833327283557137650763 8741749990925335706476145)
            ·
              refine ⟨6556312493194001779857109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8741749990925335706476145 6556312493194001779857109)
              ·
                refine ⟨153663574059234416715401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6556312493194001779857109 153663574059234416715401)
                ·
                  rfl

theorem cell23_8079986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 7].length) (baseStart_8079986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079986 prefixEnd_8079986 := by exact prefixLift 8079986
  have htrace : WordTrace (prefixWord ++ tailWord_8079986) baseStart_8079986 baseEnd_8079986 := by
    simpa [prefixWord, tailWord_8079986, baseEnd_8079986] using wordTrace_append hprefix tailTrace_8079986
  have hstable : (prefixWord ++ tailWord_8079986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079986).length < 2 ^ (prefixWord ++ tailWord_8079986).sum := by decide
  have hdescent : baseEnd_8079986 < baseStart_8079986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079995 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 4, 6]
def baseStart_8079995 : Nat := 118140960795 + 8079995 * 2 ^ 59
def prefixEnd_8079995 : Nat := 4983230072969 + 3 ^ 40 * 8079995 * 2
def baseEnd_8079995 : Nat := 1382973706975073238701095

theorem tailTrace_8079995 : CollatzResearch.WordTrace tailWord_8079995 prefixEnd_8079995 1382973706975073238701095 := by
  unfold tailWord_8079995
  simp only [CollatzResearch.WordTrace]
  refine ⟨294701628362565543127417439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196467752241710362084944959 294701628362565543127417439)
  ·
    refine ⟨442052442543848314691126159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294701628362565543127417439 442052442543848314691126159)
    ·
      refine ⟨663078663815772472036689239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442052442543848314691126159 663078663815772472036689239)
      ·
        refine ⟨994617995723658708055033859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663078663815772472036689239 994617995723658708055033859)
        ·
          refine ⟨1491926993585488062082550789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994617995723658708055033859 1491926993585488062082550789)
          ·
            refine ⟨279736311297279011640478273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1491926993585488062082550789 279736311297279011640478273)
            ·
              refine ⟨209802233472959258730358705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279736311297279011640478273 209802233472959258730358705)
              ·
                refine ⟨157351675104719444047769029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209802233472959258730358705 157351675104719444047769029)
                ·
                  refine ⟨29503439082134895758956693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157351675104719444047769029 29503439082134895758956693)
                  ·
                    refine ⟨1382973706975073238701095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29503439082134895758956693 1382973706975073238701095)
                    ·
                      rfl

theorem cell23_8079995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 6].length) (baseStart_8079995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079995 prefixEnd_8079995 := by exact prefixLift 8079995
  have htrace : WordTrace (prefixWord ++ tailWord_8079995) baseStart_8079995 baseEnd_8079995 := by
    simpa [prefixWord, tailWord_8079995, baseEnd_8079995] using wordTrace_append hprefix tailTrace_8079995
  have hstable : (prefixWord ++ tailWord_8079995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079995).length < 2 ^ (prefixWord ++ tailWord_8079995).sum := by decide
  have hdescent : baseEnd_8079995 < baseStart_8079995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8079997 : List Nat := [1, 4, 1, 1, 6, 1, 1, 3, 1, 2, 2]
def baseStart_8079997 : Nat := 118140960795 + 8079997 * 2 ^ 59
def prefixEnd_8079997 : Nat := 4983230072969 + 3 ^ 40 * 8079997 * 2
def baseEnd_8079997 : Nat := 4148922147886528708278277

theorem tailTrace_8079997 : CollatzResearch.WordTrace tailWord_8079997 prefixEnd_8079997 4148922147886528708278277 := by
  unfold tailWord_8079997
  simp only [CollatzResearch.WordTrace]
  refine ⟨294701701308558297468990245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196467800872372198312660163 294701701308558297468990245)
  ·
    refine ⟨55256568995354680775435671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294701701308558297468990245 55256568995354680775435671)
    ·
      refine ⟨82884853493032021163153507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55256568995354680775435671 82884853493032021163153507)
      ·
        refine ⟨124327280239548031744730261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82884853493032021163153507 124327280239548031744730261)
        ·
          refine ⟨5827841261228813988034231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 124327280239548031744730261 5827841261228813988034231)
          ·
            refine ⟨8741761891843220982051347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5827841261228813988034231 8741761891843220982051347)
            ·
              refine ⟨13112642837764831473077021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8741761891843220982051347 13112642837764831473077021)
              ·
                refine ⟨4917241064161811802403883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13112642837764831473077021 4917241064161811802403883)
                ·
                  refine ⟨7375861596242717703605825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4917241064161811802403883 7375861596242717703605825)
                  ·
                    refine ⟨5531896197182038277704369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7375861596242717703605825 5531896197182038277704369)
                    ·
                      refine ⟨4148922147886528708278277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5531896197182038277704369 4148922147886528708278277)
                      ·
                        rfl

theorem cell23_8079997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_8079997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8079997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8079997 prefixEnd_8079997 := by exact prefixLift 8079997
  have htrace : WordTrace (prefixWord ++ tailWord_8079997) baseStart_8079997 baseEnd_8079997 := by
    simpa [prefixWord, tailWord_8079997, baseEnd_8079997] using wordTrace_append hprefix tailTrace_8079997
  have hstable : (prefixWord ++ tailWord_8079997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8079997).length < 2 ^ (prefixWord ++ tailWord_8079997).sum := by decide
  have hdescent : baseEnd_8079997 < baseStart_8079997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8079997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080076 : List Nat := [2, 2, 1, 5, 1, 2, 1, 4, 5]
def baseStart_8080076 : Nat := 118140960795 + 8080076 * 2 ^ 59
def prefixEnd_8080076 : Nat := 4983230072969 + 3 ^ 40 * 8080076 * 2
def baseEnd_8080076 : Nat := 460995856984248211021157

theorem tailTrace_8080076 : CollatzResearch.WordTrace tailWord_8080076 prefixEnd_8080076 460995856984248211021157 := by
  unfold tailWord_8080076
  simp only [CollatzResearch.WordTrace]
  refine ⟨147352291337636046980558041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196469721783514729307410721 147352291337636046980558041)
  ·
    refine ⟨110514218503227035235418531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147352291337636046980558041 110514218503227035235418531)
    ·
      refine ⟨165771327754840552853127797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110514218503227035235418531 165771327754840552853127797)
      ·
        refine ⟨15541061977016301829980731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165771327754840552853127797 15541061977016301829980731)
        ·
          refine ⟨23311592965524452744971097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15541061977016301829980731 23311592965524452744971097)
          ·
            refine ⟨17483694724143339558728323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23311592965524452744971097 17483694724143339558728323)
            ·
              refine ⟨26225542086215009338092485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17483694724143339558728323 26225542086215009338092485)
              ·
                refine ⟨4917289141165314250892341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26225542086215009338092485 4917289141165314250892341)
                ·
                  refine ⟨460995856984248211021157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4917289141165314250892341 460995856984248211021157)
                  ·
                    rfl

theorem cell23_8080076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 5].length) (baseStart_8080076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080076 prefixEnd_8080076 := by exact prefixLift 8080076
  have htrace : WordTrace (prefixWord ++ tailWord_8080076) baseStart_8080076 baseEnd_8080076 := by
    simpa [prefixWord, tailWord_8080076, baseEnd_8080076] using wordTrace_append hprefix tailTrace_8080076
  have hstable : (prefixWord ++ tailWord_8080076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080076).length < 2 ^ (prefixWord ++ tailWord_8080076).sum := by decide
  have hdescent : baseEnd_8080076 < baseStart_8080076 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080109 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_8080109 : Nat := 118140960795 + 8080109 * 2 ^ 59
def prefixEnd_8080109 : Nat := 4983230072969 + 3 ^ 40 * 8080109 * 2
def baseEnd_8080109 : Nat := 4148979657719832270077761

theorem tailTrace_8080109 : CollatzResearch.WordTrace tailWord_8080109 prefixEnd_8080109 4148979657719832270077761 := by
  unfold tailWord_8080109
  simp only [CollatzResearch.WordTrace]
  refine ⟨294705786284152540597067381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196470524189435027064711587 294705786284152540597067381)
  ·
    refine ⟨27628667464139300680975067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294705786284152540597067381 27628667464139300680975067)
    ·
      refine ⟨41443001196208951021462601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27628667464139300680975067 41443001196208951021462601)
      ·
        refine ⟨31082250897156713266096951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41443001196208951021462601 31082250897156713266096951)
        ·
          refine ⟨46623376345735069899145427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31082250897156713266096951 46623376345735069899145427)
          ·
            refine ⟨69935064518602604848718141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46623376345735069899145427 69935064518602604848718141)
            ·
              refine ⟨26225649194475976818269303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69935064518602604848718141 26225649194475976818269303)
              ·
                refine ⟨39338473791713965227403955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26225649194475976818269303 39338473791713965227403955)
                ·
                  refine ⟨59007710687570947841105933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39338473791713965227403955 59007710687570947841105933)
                  ·
                    refine ⟨22127891507839105440414725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59007710687570947841105933 22127891507839105440414725)
                    ·
                      refine ⟨4148979657719832270077761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22127891507839105440414725 4148979657719832270077761)
                      ·
                        rfl

theorem cell23_8080109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_8080109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080109 prefixEnd_8080109 := by exact prefixLift 8080109
  have htrace : WordTrace (prefixWord ++ tailWord_8080109) baseStart_8080109 baseEnd_8080109 := by
    simpa [prefixWord, tailWord_8080109, baseEnd_8080109] using wordTrace_append hprefix tailTrace_8080109
  have hstable : (prefixWord ++ tailWord_8080109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080109).length < 2 ^ (prefixWord ++ tailWord_8080109).sum := by decide
  have hdescent : baseEnd_8080109 < baseStart_8080109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080122 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_8080122 : Nat := 118140960795 + 8080122 * 2 ^ 59
def prefixEnd_8080122 : Nat := 4983230072969 + 3 ^ 40 * 8080122 * 2
def baseEnd_8080122 : Nat := 4148986332968340719215201

theorem tailTrace_8080122 : CollatzResearch.WordTrace tailWord_8080122 prefixEnd_8080122 4148986332968340719215201 := by
  unfold tailWord_8080122
  simp only [CollatzResearch.WordTrace]
  refine ⟨73676565108276360954322655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196470840288736962544860413 73676565108276360954322655)
  ·
    refine ⟨110514847662414541431483983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73676565108276360954322655 110514847662414541431483983)
    ·
      refine ⟨165772271493621812147225975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110514847662414541431483983 165772271493621812147225975)
      ·
        refine ⟨248658407240432718220838963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165772271493621812147225975 248658407240432718220838963)
        ·
          refine ⟨372987610860649077331258445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248658407240432718220838963 372987610860649077331258445)
          ·
            refine ⟨139870354072743403999221917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372987610860649077331258445 139870354072743403999221917)
            ·
              refine ⟨52451382777278776499708219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139870354072743403999221917 52451382777278776499708219)
              ·
                refine ⟨78677074165918164749562329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52451382777278776499708219 78677074165918164749562329)
                ·
                  refine ⟨59007805624438623562171747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78677074165918164749562329 59007805624438623562171747)
                  ·
                    refine ⟨88511708436657935343257621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59007805624438623562171747 88511708436657935343257621)
                    ·
                      refine ⟨4148986332968340719215201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88511708436657935343257621 4148986332968340719215201)
                      ·
                        rfl

theorem cell23_8080122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_8080122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080122 prefixEnd_8080122 := by exact prefixLift 8080122
  have htrace : WordTrace (prefixWord ++ tailWord_8080122) baseStart_8080122 baseEnd_8080122 := by
    simpa [prefixWord, tailWord_8080122, baseEnd_8080122] using wordTrace_append hprefix tailTrace_8080122
  have hstable : (prefixWord ++ tailWord_8080122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080122).length < 2 ^ (prefixWord ++ tailWord_8080122).sum := by decide
  have hdescent : baseEnd_8080122 < baseStart_8080122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080129 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_8080129 : Nat := 118140960795 + 8080129 * 2 ^ 59
def prefixEnd_8080129 : Nat := 4983230072969 + 3 ^ 40 * 8080129 * 2
def baseEnd_8080129 : Nat := 4148989927332922191827669

theorem tailTrace_8080129 : CollatzResearch.WordTrace tailWord_8080129 prefixEnd_8080129 4148989927332922191827669 := by
  unfold tailWord_8080129
  simp only [CollatzResearch.WordTrace]
  refine ⟨294706515744080084012795441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196471010496053389341863627 294706515744080084012795441)
  ·
    refine ⟨221029886808060063009596581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294706515744080084012795441 221029886808060063009596581)
    ·
      refine ⟨41443103776511261814299359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221029886808060063009596581 41443103776511261814299359)
      ·
        refine ⟨62164655664766892721449039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41443103776511261814299359 62164655664766892721449039)
        ·
          refine ⟨93246983497150339082173559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62164655664766892721449039 93246983497150339082173559)
          ·
            refine ⟨139870475245725508623260339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93246983497150339082173559 139870475245725508623260339)
            ·
              refine ⟨209805712868588262934890509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139870475245725508623260339 209805712868588262934890509)
              ·
                refine ⟨78677142325720598600583941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209805712868588262934890509 78677142325720598600583941)
                ·
                  refine ⟨14751964186072612237609489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78677142325720598600583941 14751964186072612237609489)
                  ·
                    refine ⟨11063973139554459178207117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14751964186072612237609489 11063973139554459178207117)
                    ·
                      refine ⟨4148989927332922191827669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11063973139554459178207117 4148989927332922191827669)
                      ·
                        rfl

theorem cell23_8080129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_8080129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080129 prefixEnd_8080129 := by exact prefixLift 8080129
  have htrace : WordTrace (prefixWord ++ tailWord_8080129) baseStart_8080129 baseEnd_8080129 := by
    simpa [prefixWord, tailWord_8080129, baseEnd_8080129] using wordTrace_append hprefix tailTrace_8080129
  have hstable : (prefixWord ++ tailWord_8080129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080129).length < 2 ^ (prefixWord ++ tailWord_8080129).sum := by decide
  have hdescent : baseEnd_8080129 < baseStart_8080129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080136 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 3, 4]
def baseStart_8080136 : Nat := 118140960795 + 8080136 * 2 ^ 59
def prefixEnd_8080136 : Nat := 4983230072969 + 3 ^ 40 * 8080136 * 2
def baseEnd_8080136 : Nat := 1382997840565834554813379

theorem tailTrace_8080136 : CollatzResearch.WordTrace tailWord_8080136 prefixEnd_8080136 1382997840565834554813379 := by
  unfold tailWord_8080136
  simp only [CollatzResearch.WordTrace]
  refine ⟨147353385527527362104150131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196471180703369816138866841 147353385527527362104150131)
  ·
    refine ⟨221030078291291043156225197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147353385527527362104150131 221030078291291043156225197)
    ·
      refine ⟨82886279359234141183584449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221030078291291043156225197 82886279359234141183584449)
      ·
        refine ⟨62164709519425605887688337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82886279359234141183584449 62164709519425605887688337)
        ·
          refine ⟨46623532139569204415766253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62164709519425605887688337 46623532139569204415766253)
          ·
            refine ⟨17483824552338451655912345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46623532139569204415766253 17483824552338451655912345)
            ·
              refine ⟨13112868414253838741934259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17483824552338451655912345 13112868414253838741934259)
              ·
                refine ⟨19669302621380758112901389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13112868414253838741934259 19669302621380758112901389)
                ·
                  refine ⟨7375988483017784292338021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19669302621380758112901389 7375988483017784292338021)
                  ·
                    refine ⟨1382997840565834554813379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7375988483017784292338021 1382997840565834554813379)
                    ·
                      rfl

theorem cell23_8080136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_8080136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080136 prefixEnd_8080136 := by exact prefixLift 8080136
  have htrace : WordTrace (prefixWord ++ tailWord_8080136) baseStart_8080136 baseEnd_8080136 := by
    simpa [prefixWord, tailWord_8080136, baseEnd_8080136] using wordTrace_append hprefix tailTrace_8080136
  have hstable : (prefixWord ++ tailWord_8080136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080136).length < 2 ^ (prefixWord ++ tailWord_8080136).sum := by decide
  have hdescent : baseEnd_8080136 < baseStart_8080136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080152 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_8080152 : Nat := 118140960795 + 8080152 * 2 ^ 59
def prefixEnd_8080152 : Nat := 4983230072969 + 3 ^ 40 * 8080152 * 2
def baseEnd_8080152 : Nat := 4149001737387975601840063

theorem tailTrace_8080152 : CollatzResearch.WordTrace tailWord_8080152 prefixEnd_8080152 4149001737387975601840063 := by
  unfold tailWord_8080152
  simp only [CollatzResearch.WordTrace]
  refine ⟨147353677311498379470441355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196471569748664505960588473 147353677311498379470441355)
  ·
    refine ⟨221030515967247569205662033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147353677311498379470441355 221030515967247569205662033)
    ·
      refine ⟨165772886975435676904246525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221030515967247569205662033 165772886975435676904246525)
      ·
        refine ⟨62164832615788378839092447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165772886975435676904246525 62164832615788378839092447)
        ·
          refine ⟨93247248923682568258638671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62164832615788378839092447 93247248923682568258638671)
          ·
            refine ⟨139870873385523852387958007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93247248923682568258638671 139870873385523852387958007)
            ·
              refine ⟨209806310078285778581937011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139870873385523852387958007 209806310078285778581937011)
              ·
                refine ⟨314709465117428667872905517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209806310078285778581937011 314709465117428667872905517)
                ·
                  refine ⟨118016049419035750452339569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314709465117428667872905517 118016049419035750452339569)
                  ·
                    refine ⟨88512037064276812839254677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118016049419035750452339569 88512037064276812839254677)
                    ·
                      refine ⟨4149001737387975601840063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88512037064276812839254677 4149001737387975601840063)
                      ·
                        rfl

theorem cell23_8080152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_8080152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080152 prefixEnd_8080152 := by exact prefixLift 8080152
  have htrace : WordTrace (prefixWord ++ tailWord_8080152) baseStart_8080152 baseEnd_8080152 := by
    simpa [prefixWord, tailWord_8080152, baseEnd_8080152] using wordTrace_append hprefix tailTrace_8080152
  have hstable : (prefixWord ++ tailWord_8080152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080152).length < 2 ^ (prefixWord ++ tailWord_8080152).sum := by decide
  have hdescent : baseEnd_8080152 < baseStart_8080152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080199 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_8080199 : Nat := 118140960795 + 8080199 * 2 ^ 59
def prefixEnd_8080199 : Nat := 4983230072969 + 3 ^ 40 * 8080199 * 2
def baseEnd_8080199 : Nat := 4149025870978736917952347

theorem tailTrace_8080199 : CollatzResearch.WordTrace tailWord_8080199 prefixEnd_8080199 4149025870978736917952347 := by
  unfold tailWord_8080199
  simp only [CollatzResearch.WordTrace]
  refine ⟨294709068853826485967843651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196472712569217657311895767 294709068853826485967843651)
  ·
    refine ⟨442063603280739728951765477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294709068853826485967843651 442063603280739728951765477)
    ·
      refine ⟨82886925615138699178456027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442063603280739728951765477 82886925615138699178456027)
      ·
        refine ⟨124330388422708048767684041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82886925615138699178456027 124330388422708048767684041)
        ·
          refine ⟨93247791317031036575763031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124330388422708048767684041 93247791317031036575763031)
          ·
            refine ⟨139871686975546554863644547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93247791317031036575763031 139871686975546554863644547)
            ·
              refine ⟨209807530463319832295466821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139871686975546554863644547 209807530463319832295466821)
              ·
                refine ⟨39338911961872468555400029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209807530463319832295466821 39338911961872468555400029)
                ·
                  refine ⟨14752091985702175708275011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39338911961872468555400029 14752091985702175708275011)
                  ·
                    refine ⟨22128137978553263562412517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14752091985702175708275011 22128137978553263562412517)
                    ·
                      refine ⟨4149025870978736917952347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22128137978553263562412517 4149025870978736917952347)
                      ·
                        rfl

theorem cell23_8080199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_8080199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080199 prefixEnd_8080199 := by exact prefixLift 8080199
  have htrace : WordTrace (prefixWord ++ tailWord_8080199) baseStart_8080199 baseEnd_8080199 := by
    simpa [prefixWord, tailWord_8080199, baseEnd_8080199] using wordTrace_append hprefix tailTrace_8080199
  have hstable : (prefixWord ++ tailWord_8080199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080199).length < 2 ^ (prefixWord ++ tailWord_8080199).sum := by decide
  have hdescent : baseEnd_8080199 < baseStart_8080199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080220 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_8080220 : Nat := 118140960795 + 8080220 * 2 ^ 59
def prefixEnd_8080220 : Nat := 4983230072969 + 3 ^ 40 * 8080220 * 2
def baseEnd_8080220 : Nat := 4149036654072481335789751

theorem tailTrace_8080220 : CollatzResearch.WordTrace tailWord_8080220 prefixEnd_8080220 4149036654072481335789751 := by
  unfold tailWord_8080220
  simp only [CollatzResearch.WordTrace]
  refine ⟨147354917393375203277179057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196473223191166937702905409 147354917393375203277179057)
  ·
    refine ⟨110516188045031402457884293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147354917393375203277179057 110516188045031402457884293)
    ·
      refine ⟨20721785258443387960853305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110516188045031402457884293 20721785258443387960853305)
      ·
        refine ⟨15541338943832540970639979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20721785258443387960853305 15541338943832540970639979)
        ·
          refine ⟨23312008415748811455959969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15541338943832540970639979 23312008415748811455959969)
          ·
            refine ⟨17484006311811608591969977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23312008415748811455959969 17484006311811608591969977)
            ·
              refine ⟨13113004733858706443977483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17484006311811608591969977 13113004733858706443977483)
              ·
                refine ⟨19669507100788059665966225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13113004733858706443977483 19669507100788059665966225)
                ·
                  refine ⟨14752130325591044749474669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19669507100788059665966225 14752130325591044749474669)
                  ·
                    refine ⟨5532048872096641781053001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14752130325591044749474669 5532048872096641781053001)
                    ·
                      refine ⟨4149036654072481335789751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532048872096641781053001 4149036654072481335789751)
                      ·
                        rfl

theorem cell23_8080220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_8080220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080220 prefixEnd_8080220 := by exact prefixLift 8080220
  have htrace : WordTrace (prefixWord ++ tailWord_8080220) baseStart_8080220 baseEnd_8080220 := by
    simpa [prefixWord, tailWord_8080220, baseEnd_8080220] using wordTrace_append hprefix tailTrace_8080220
  have hstable : (prefixWord ++ tailWord_8080220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080220).length < 2 ^ (prefixWord ++ tailWord_8080220).sum := by decide
  have hdescent : baseEnd_8080220 < baseStart_8080220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080229 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_8080229 : Nat := 118140960795 + 8080229 * 2 ^ 59
def prefixEnd_8080229 : Nat := 4983230072969 + 3 ^ 40 * 8080229 * 2
def baseEnd_8080229 : Nat := 4149041275398371800577209

theorem tailTrace_8080229 : CollatzResearch.WordTrace tailWord_8080229 prefixEnd_8080229 4149041275398371800577209 := by
  unfold tailWord_8080229
  simp only [CollatzResearch.WordTrace]
  refine ⟨294710163043717801091435741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196473442029145200727623827 294710163043717801091435741)
  ·
    refine ⟨110516311141394175409288403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294710163043717801091435741 110516311141394175409288403)
    ·
      refine ⟨165774466712091263113932605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110516311141394175409288403 165774466712091263113932605)
      ·
        refine ⟨62165425017034223667724727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165774466712091263113932605 62165425017034223667724727)
        ·
          refine ⟨93248137525551335501587091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62165425017034223667724727 93248137525551335501587091)
          ·
            refine ⟨139872206288327003252380637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93248137525551335501587091 139872206288327003252380637)
            ·
              refine ⟨52452077358122626219642739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139872206288327003252380637 52452077358122626219642739)
              ·
                refine ⟨78678116037183939329464109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52452077358122626219642739 78678116037183939329464109)
                ·
                  refine ⟨29504293513943977248549041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78678116037183939329464109 29504293513943977248549041)
                  ·
                    refine ⟨22128220135457982936411781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29504293513943977248549041 22128220135457982936411781)
                    ·
                      refine ⟨4149041275398371800577209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22128220135457982936411781 4149041275398371800577209)
                      ·
                        rfl

theorem cell23_8080229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_8080229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080229 prefixEnd_8080229 := by exact prefixLift 8080229
  have htrace : WordTrace (prefixWord ++ tailWord_8080229) baseStart_8080229 baseEnd_8080229 := by
    simpa [prefixWord, tailWord_8080229, baseEnd_8080229] using wordTrace_append hprefix tailTrace_8080229
  have hstable : (prefixWord ++ tailWord_8080229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080229).length < 2 ^ (prefixWord ++ tailWord_8080229).sum := by decide
  have hdescent : baseEnd_8080229 < baseStart_8080229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080279 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_8080279 : Nat := 118140960795 + 8080279 * 2 ^ 59
def prefixEnd_8080279 : Nat := 4983230072969 + 3 ^ 40 * 8080279 * 2
def baseEnd_8080279 : Nat := 4149066949431096604951979

theorem tailTrace_8080279 : CollatzResearch.WordTrace tailWord_8080279 prefixEnd_8080279 4149066949431096604951979 := by
  unfold tailWord_8080279
  simp only [CollatzResearch.WordTrace]
  refine ⟨294711986693536659630755891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196474657795691106420503927 294711986693536659630755891)
  ·
    refine ⟨442067980040304989446133837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294711986693536659630755891 442067980040304989446133837)
    ·
      refine ⟨165775492515114371042300189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442067980040304989446133837 165775492515114371042300189)
      ·
        refine ⟨62165809693167889140862571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165775492515114371042300189 62165809693167889140862571)
        ·
          refine ⟨93248714539751833711293857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62165809693167889140862571 93248714539751833711293857)
          ·
            refine ⟨69936535904813875283470393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93248714539751833711293857 69936535904813875283470393)
            ·
              refine ⟨52452401928610406462602795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69936535904813875283470393 52452401928610406462602795)
              ·
                refine ⟨78678602892915609693904193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52452401928610406462602795 78678602892915609693904193)
                ·
                  refine ⟨59008952169686707270428145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78678602892915609693904193 59008952169686707270428145)
                  ·
                    refine ⟨44256714127265030452821109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59008952169686707270428145 44256714127265030452821109)
                    ·
                      refine ⟨4149066949431096604951979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44256714127265030452821109 4149066949431096604951979)
                      ·
                        rfl

theorem cell23_8080279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_8080279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080279 prefixEnd_8080279 := by exact prefixLift 8080279
  have htrace : WordTrace (prefixWord ++ tailWord_8080279) baseStart_8080279 baseEnd_8080279 := by
    simpa [prefixWord, tailWord_8080279, baseEnd_8080279] using wordTrace_append hprefix tailTrace_8080279
  have hstable : (prefixWord ++ tailWord_8080279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080279).length < 2 ^ (prefixWord ++ tailWord_8080279).sum := by decide
  have hdescent : baseEnd_8080279 < baseStart_8080279 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080284 : List Nat := [2, 2, 3, 3, 2, 1, 2, 3, 1, 2, 2]
def baseStart_8080284 : Nat := 118140960795 + 8080284 * 2 ^ 59
def prefixEnd_8080284 : Nat := 4983230072969 + 3 ^ 40 * 8080284 * 2
def baseEnd_8080284 : Nat := 4149069516834369085389457

theorem tailTrace_8080284 : CollatzResearch.WordTrace tailWord_8080284 prefixEnd_8080284 4149069516834369085389457 := by
  unfold tailWord_8080284
  simp only [CollatzResearch.WordTrace]
  refine ⟨147356084529259272742343953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196474779372345696989791937 147356084529259272742343953)
  ·
    refine ⟨110517063396944454556757965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147356084529259272742343953 110517063396944454556757965)
    ·
      refine ⟨41443898773854170458784237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110517063396944454556757965 41443898773854170458784237)
      ·
        refine ⟨15541462040195313922044089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41443898773854170458784237 15541462040195313922044089)
        ·
          refine ⟨11656096530146485441533067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15541462040195313922044089 11656096530146485441533067)
          ·
            refine ⟨17484144795219728162299601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11656096530146485441533067 17484144795219728162299601)
            ·
              refine ⟨13113108596414796121724701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17484144795219728162299601 13113108596414796121724701)
              ·
                refine ⟨4917415723655548545646763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13113108596414796121724701 4917415723655548545646763)
                ·
                  refine ⟨7376123585483322818470145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4917415723655548545646763 7376123585483322818470145)
                  ·
                    refine ⟨5532092689112492113852609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7376123585483322818470145 5532092689112492113852609)
                    ·
                      refine ⟨4149069516834369085389457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532092689112492113852609 4149069516834369085389457)
                      ·
                        rfl

theorem cell23_8080284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_8080284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080284 prefixEnd_8080284 := by exact prefixLift 8080284
  have htrace : WordTrace (prefixWord ++ tailWord_8080284) baseStart_8080284 baseEnd_8080284 := by
    simpa [prefixWord, tailWord_8080284, baseEnd_8080284] using wordTrace_append hprefix tailTrace_8080284
  have hstable : (prefixWord ++ tailWord_8080284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080284).length < 2 ^ (prefixWord ++ tailWord_8080284).sum := by decide
  have hdescent : baseEnd_8080284 < baseStart_8080284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080306 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2]
def baseStart_8080306 : Nat := 118140960795 + 8080306 * 2 ^ 59
def prefixEnd_8080306 : Nat := 4983230072969 + 3 ^ 40 * 8080306 * 2
def baseEnd_8080306 : Nat := 4149080813408767999314355

theorem tailTrace_8080306 : CollatzResearch.WordTrace tailWord_8080306 prefixEnd_8080306 4149080813408767999314355 := by
  unfold tailWord_8080306
  simp only [CollatzResearch.WordTrace]
  refine ⟨73678242866109710810497193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196475314309625895494659181 73678242866109710810497193)
  ·
    refine ⟨55258682149582283107872895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73678242866109710810497193 55258682149582283107872895)
    ·
      refine ⟨82888023224373424661809343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55258682149582283107872895 82888023224373424661809343)
      ·
        refine ⟨124332034836560136992714015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82888023224373424661809343 124332034836560136992714015)
        ·
          refine ⟨186498052254840205489071023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124332034836560136992714015 186498052254840205489071023)
          ·
            refine ⟨279747078382260308233606535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186498052254840205489071023 279747078382260308233606535)
            ·
              refine ⟨419620617573390462350409803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279747078382260308233606535 419620617573390462350409803)
              ·
                refine ⟨629430926360085693525614705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419620617573390462350409803 629430926360085693525614705)
                ·
                  refine ⟨472073194770064270144211029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629430926360085693525614705 472073194770064270144211029)
                  ·
                    refine ⟨5532107751211690665752473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 472073194770064270144211029 5532107751211690665752473)
                    ·
                      refine ⟨4149080813408767999314355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532107751211690665752473 4149080813408767999314355)
                      ·
                        rfl

theorem cell23_8080306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_8080306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080306 prefixEnd_8080306 := by exact prefixLift 8080306
  have htrace : WordTrace (prefixWord ++ tailWord_8080306) baseStart_8080306 baseEnd_8080306 := by
    simpa [prefixWord, tailWord_8080306, baseEnd_8080306] using wordTrace_append hprefix tailTrace_8080306
  have hstable : (prefixWord ++ tailWord_8080306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080306).length < 2 ^ (prefixWord ++ tailWord_8080306).sum := by decide
  have hdescent : baseEnd_8080306 < baseStart_8080306 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080317 : List Nat := [1, 4, 1, 2, 4, 1, 3, 1, 2, 1, 3]
def baseStart_8080317 : Nat := 118140960795 + 8080317 * 2 ^ 59
def prefixEnd_8080317 : Nat := 4983230072969 + 3 ^ 40 * 8080317 * 2
def baseEnd_8080317 : Nat := 4149086461695967456276805

theorem tailTrace_8080317 : CollatzResearch.WordTrace tailWord_8080317 prefixEnd_8080317 4149086461695967456276805 := by
  unfold tailWord_8080317
  simp only [CollatzResearch.WordTrace]
  refine ⟨294713372667398992120639205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196475581778265994747092803 294713372667398992120639205)
  ·
    refine ⟨55258757375137311022619851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294713372667398992120639205 55258757375137311022619851)
    ·
      refine ⟨82888136062705966533929777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55258757375137311022619851 82888136062705966533929777)
      ·
        refine ⟨62166102047029474900447333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82888136062705966533929777 62166102047029474900447333)
        ·
          refine ⟨11656144133818026543833875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62166102047029474900447333 11656144133818026543833875)
          ·
            refine ⟨17484216200727039815750813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11656144133818026543833875 17484216200727039815750813)
            ·
              refine ⟨6556581075272639930906555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17484216200727039815750813 6556581075272639930906555)
              ·
                refine ⟨9834871612908959896359833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6556581075272639930906555 9834871612908959896359833)
                ·
                  refine ⟨7376153709681719922269875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9834871612908959896359833 7376153709681719922269875)
                  ·
                    refine ⟨11064230564522579883404813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7376153709681719922269875 11064230564522579883404813)
                    ·
                      refine ⟨4149086461695967456276805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11064230564522579883404813 4149086461695967456276805)
                      ·
                        rfl

theorem cell23_8080317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_8080317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080317 prefixEnd_8080317 := by exact prefixLift 8080317
  have htrace : WordTrace (prefixWord ++ tailWord_8080317) baseStart_8080317 baseEnd_8080317 := by
    simpa [prefixWord, tailWord_8080317, baseEnd_8080317] using wordTrace_append hprefix tailTrace_8080317
  have hstable : (prefixWord ++ tailWord_8080317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080317).length < 2 ^ (prefixWord ++ tailWord_8080317).sum := by decide
  have hdescent : baseEnd_8080317 < baseStart_8080317 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080319 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 4]
def baseStart_8080319 : Nat := 118140960795 + 8080319 * 2 ^ 59
def prefixEnd_8080319 : Nat := 4983230072969 + 3 ^ 40 * 8080319 * 2
def baseEnd_8080319 : Nat := 4149087488657276448451795

theorem tailTrace_8080319 : CollatzResearch.WordTrace tailWord_8080319 prefixEnd_8080319 4149087488657276448451795 := by
  unfold tailWord_8080319
  simp only [CollatzResearch.WordTrace]
  refine ⟨294713445613391746462212011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196475630408927830974808007 294713445613391746462212011)
  ·
    refine ⟨442070168420087619693318017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294713445613391746462212011 442070168420087619693318017)
    ·
      refine ⟨331552626315065714769988513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442070168420087619693318017 331552626315065714769988513)
      ·
        refine ⟨248664469736299286077491385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331552626315065714769988513 248664469736299286077491385)
        ·
          refine ⟨186498352302224464558118539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248664469736299286077491385 186498352302224464558118539)
          ·
            refine ⟨279747528453336696837177809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186498352302224464558118539 279747528453336696837177809)
            ·
              refine ⟨209810646340002522627883357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279747528453336696837177809 209810646340002522627883357)
              ·
                refine ⟨78678992377500945985456259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209810646340002522627883357 78678992377500945985456259)
                ·
                  refine ⟨118018488566251418978184389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78678992377500945985456259 118018488566251418978184389)
                  ·
                    refine ⟨22128466606172141058409573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118018488566251418978184389 22128466606172141058409573)
                    ·
                      refine ⟨4149087488657276448451795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22128466606172141058409573 4149087488657276448451795)
                      ·
                        rfl

theorem cell23_8080319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_8080319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080319 prefixEnd_8080319 := by exact prefixLift 8080319
  have htrace : WordTrace (prefixWord ++ tailWord_8080319) baseStart_8080319 baseEnd_8080319 := by
    simpa [prefixWord, tailWord_8080319, baseEnd_8080319] using wordTrace_append hprefix tailTrace_8080319
  have hstable : (prefixWord ++ tailWord_8080319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080319).length < 2 ^ (prefixWord ++ tailWord_8080319).sum := by decide
  have hdescent : baseEnd_8080319 < baseStart_8080319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080340 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_8080340 : Nat := 118140960795 + 8080340 * 2 ^ 59
def prefixEnd_8080340 : Nat := 4983230072969 + 3 ^ 40 * 8080340 * 2
def baseEnd_8080340 : Nat := 4149098271751020866289199

theorem tailTrace_8080340 : CollatzResearch.WordTrace tailWord_8080340 prefixEnd_8080340 4149098271751020866289199 := by
  unfold tailWord_8080340
  simp only [CollatzResearch.WordTrace]
  refine ⟨147357105773157833524363237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196476141030877111365817649 147357105773157833524363237)
  ·
    refine ⟨27629457332467093785818107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147357105773157833524363237 27629457332467093785818107)
    ·
      refine ⟨41444185998700640678727161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27629457332467093785818107 41444185998700640678727161)
      ·
        refine ⟨31083139499025480509045371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41444185998700640678727161 31083139499025480509045371)
        ·
          refine ⟨46624709248538220763568057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31083139499025480509045371 46624709248538220763568057)
          ·
            refine ⟨34968531936403665572676043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46624709248538220763568057 34968531936403665572676043)
            ·
              refine ⟨52452797904605498359014065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34968531936403665572676043 52452797904605498359014065)
              ·
                refine ⟨39339598428454123769260549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52452797904605498359014065 39339598428454123769260549)
                ·
                  refine ⟨7376174705335148206736353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39339598428454123769260549 7376174705335148206736353)
                  ·
                    refine ⟨5532131029001361155052265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7376174705335148206736353 5532131029001361155052265)
                    ·
                      refine ⟨4149098271751020866289199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532131029001361155052265 4149098271751020866289199)
                      ·
                        rfl

theorem cell23_8080340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_8080340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080340 prefixEnd_8080340 := by exact prefixLift 8080340
  have htrace : WordTrace (prefixWord ++ tailWord_8080340) baseStart_8080340 baseEnd_8080340 := by
    simpa [prefixWord, tailWord_8080340, baseEnd_8080340] using wordTrace_append hprefix tailTrace_8080340
  have hstable : (prefixWord ++ tailWord_8080340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080340).length < 2 ^ (prefixWord ++ tailWord_8080340).sum := by decide
  have hdescent : baseEnd_8080340 < baseStart_8080340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080356 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_8080356 : Nat := 118140960795 + 8080356 * 2 ^ 59
def prefixEnd_8080356 : Nat := 4983230072969 + 3 ^ 40 * 8080356 * 2
def baseEnd_8080356 : Nat := 4149106487441492803689125

theorem tailTrace_8080356 : CollatzResearch.WordTrace tailWord_8080356 prefixEnd_8080356 4149106487441492803689125 := by
  unfold tailWord_8080356
  simp only [CollatzResearch.WordTrace]
  refine ⟨147357397557128850890654461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196476530076171801187539281 147357397557128850890654461)
  ·
    refine ⟨55259024083923319083995423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147357397557128850890654461 55259024083923319083995423)
    ·
      refine ⟨82888536125884978625993135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55259024083923319083995423 82888536125884978625993135)
      ·
        refine ⟨124332804188827467938989703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82888536125884978625993135 124332804188827467938989703)
        ·
          refine ⟨186499206283241201908484555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124332804188827467938989703 186499206283241201908484555)
          ·
            refine ⟨279748809424861802862726833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186499206283241201908484555 279748809424861802862726833)
            ·
              refine ⟨209811607068646352147045125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279748809424861802862726833 209811607068646352147045125)
              ·
                refine ⟨39339676325371191027570961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209811607068646352147045125 39339676325371191027570961)
                ·
                  refine ⟨29504757244028393270678221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39339676325371191027570961 29504757244028393270678221)
                  ·
                    refine ⟨11064283966510647476504333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29504757244028393270678221 11064283966510647476504333)
                    ·
                      refine ⟨4149106487441492803689125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11064283966510647476504333 4149106487441492803689125)
                      ·
                        rfl

theorem cell23_8080356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_8080356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080356 prefixEnd_8080356 := by exact prefixLift 8080356
  have htrace : WordTrace (prefixWord ++ tailWord_8080356) baseStart_8080356 baseEnd_8080356 := by
    simpa [prefixWord, tailWord_8080356, baseEnd_8080356] using wordTrace_append hprefix tailTrace_8080356
  have hstable : (prefixWord ++ tailWord_8080356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080356).length < 2 ^ (prefixWord ++ tailWord_8080356).sum := by decide
  have hdescent : baseEnd_8080356 < baseStart_8080356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080374 : List Nat := [5, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_8080374 : Nat := 118140960795 + 8080374 * 2 ^ 59
def prefixEnd_8080374 : Nat := 4983230072969 + 3 ^ 40 * 8080374 * 2
def baseEnd_8080374 : Nat := 4149115730093273733264043

theorem tailTrace_8080374 : CollatzResearch.WordTrace tailWord_8080374 prefixEnd_8080374 4149115730093273733264043 := by
  unfold tailWord_8080374
  simp only [CollatzResearch.WordTrace]
  refine ⟨18419715726762030678466511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196476967752128327236976117 18419715726762030678466511)
  ·
    refine ⟨27629573590143046017699767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18419715726762030678466511 27629573590143046017699767)
    ·
      refine ⟨41444360385214569026549651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27629573590143046017699767 41444360385214569026549651)
      ·
        refine ⟨62166540577821853539824477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41444360385214569026549651 62166540577821853539824477)
        ·
          refine ⟨23312452716683195077434179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62166540577821853539824477 23312452716683195077434179)
          ·
            refine ⟨34968679075024792616151269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23312452716683195077434179 34968679075024792616151269)
            ·
              refine ⟨6556627326567148615528363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34968679075024792616151269 6556627326567148615528363)
              ·
                refine ⟨9834940989850722923292545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6556627326567148615528363 9834940989850722923292545)
                ·
                  refine ⟨7376205742388042192469409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9834940989850722923292545 7376205742388042192469409)
                  ·
                    refine ⟨5532154306791031644352057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7376205742388042192469409 5532154306791031644352057)
                    ·
                      refine ⟨4149115730093273733264043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532154306791031644352057 4149115730093273733264043)
                      ·
                        rfl

theorem cell23_8080374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_8080374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080374 prefixEnd_8080374 := by exact prefixLift 8080374
  have htrace : WordTrace (prefixWord ++ tailWord_8080374) baseStart_8080374 baseEnd_8080374 := by
    simpa [prefixWord, tailWord_8080374, baseEnd_8080374] using wordTrace_append hprefix tailTrace_8080374
  have hstable : (prefixWord ++ tailWord_8080374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080374).length < 2 ^ (prefixWord ++ tailWord_8080374).sum := by decide
  have hdescent : baseEnd_8080374 < baseStart_8080374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080430 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_8080430 : Nat := 118140960795 + 8080430 * 2 ^ 59
def prefixEnd_8080430 : Nat := 4983230072969 + 3 ^ 40 * 8080430 * 2
def baseEnd_8080430 : Nat := 4149144485009925514163785

theorem tailTrace_8080430 : CollatzResearch.WordTrace tailWord_8080430 prefixEnd_8080430 4149144485009925514163785 := by
  unfold tailWord_8080430
  simp only [CollatzResearch.WordTrace]
  refine ⟨36839686764498701552437843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196478329410659741613001829 36839686764498701552437843)
  ·
    refine ⟨55259530146748052328656765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36839686764498701552437843 55259530146748052328656765)
    ·
      refine ⟨20722323805030519623246287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55259530146748052328656765 20722323805030519623246287)
      ·
        refine ⟨31083485707545779434869431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20722323805030519623246287 31083485707545779434869431)
        ·
          refine ⟨46625228561318669152304147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31083485707545779434869431 46625228561318669152304147)
          ·
            refine ⟨69937842841978003728456221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46625228561318669152304147 69937842841978003728456221)
            ·
              refine ⟨26226691065741751398171083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69937842841978003728456221 26226691065741751398171083)
              ·
                refine ⟨39340036598612627097256625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26226691065741751398171083 39340036598612627097256625)
                ·
                  refine ⟨29505027448959470322942469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39340036598612627097256625 29505027448959470322942469)
                  ·
                    refine ⟨5532192646679900685551713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29505027448959470322942469 5532192646679900685551713)
                    ·
                      refine ⟨4149144485009925514163785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532192646679900685551713 4149144485009925514163785)
                      ·
                        rfl

theorem cell23_8080430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_8080430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080430 prefixEnd_8080430 := by exact prefixLift 8080430
  have htrace : WordTrace (prefixWord ++ tailWord_8080430) baseStart_8080430 baseEnd_8080430 := by
    simpa [prefixWord, tailWord_8080430, baseEnd_8080430] using wordTrace_append hprefix tailTrace_8080430
  have hstable : (prefixWord ++ tailWord_8080430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080430).length < 2 ^ (prefixWord ++ tailWord_8080430).sum := by decide
  have hdescent : baseEnd_8080430 < baseStart_8080430 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080480 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 3, 1, 3]
def baseStart_8080480 : Nat := 118140960795 + 8080480 * 2 ^ 59
def prefixEnd_8080480 : Nat := 4983230072969 + 3 ^ 40 * 8080480 * 2
def baseEnd_8080480 : Nat := 4149170159042650318538555

theorem tailTrace_8080480 : CollatzResearch.WordTrace tailWord_8080480 prefixEnd_8080480 4149170159042650318538555 := by
  unfold tailWord_8080480
  simp only [CollatzResearch.WordTrace]
  refine ⟨147359658882904235479411447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196479545177205647305881929 147359658882904235479411447)
  ·
    refine ⟨221039488324356353219117171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147359658882904235479411447 221039488324356353219117171)
    ·
      refine ⟨331559232486534529828675757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221039488324356353219117171 331559232486534529828675757)
      ·
        refine ⟨124334712182450448685753409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331559232486534529828675757 124334712182450448685753409)
        ·
          refine ⟨93251034136837836514315057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124334712182450448685753409 93251034136837836514315057)
          ·
            refine ⟨69938275602628377385736293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93251034136837836514315057 69938275602628377385736293)
            ·
              refine ⟨13113426675492820759825555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69938275602628377385736293 13113426675492820759825555)
              ·
                refine ⟨19670140013239231139738333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13113426675492820759825555 19670140013239231139738333)
                ·
                  refine ⟨7376302504964711677401875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19670140013239231139738333 7376302504964711677401875)
                  ·
                    refine ⟨11064453757447067516102813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7376302504964711677401875 11064453757447067516102813)
                    ·
                      refine ⟨4149170159042650318538555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11064453757447067516102813 4149170159042650318538555)
                      ·
                        rfl

theorem cell23_8080480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_8080480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080480 prefixEnd_8080480 := by exact prefixLift 8080480
  have htrace : WordTrace (prefixWord ++ tailWord_8080480) baseStart_8080480 baseEnd_8080480 := by
    simpa [prefixWord, tailWord_8080480, baseEnd_8080480] using wordTrace_append hprefix tailTrace_8080480
  have hstable : (prefixWord ++ tailWord_8080480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080480).length < 2 ^ (prefixWord ++ tailWord_8080480).sum := by decide
  have hdescent : baseEnd_8080480 < baseStart_8080480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080490 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_8080490 : Nat := 118140960795 + 8080490 * 2 ^ 59
def prefixEnd_8080490 : Nat := 4983230072969 + 3 ^ 40 * 8080490 * 2
def baseEnd_8080490 : Nat := 4149175293849195279413509

theorem tailTrace_8080490 : CollatzResearch.WordTrace tailWord_8080490 prefixEnd_8080490 4149175293849195279413509 := by
  unfold tailWord_8080490
  simp only [CollatzResearch.WordTrace]
  refine ⟨73679920623943060666671731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196479788330514828444457949 73679920623943060666671731)
  ·
    refine ⟨110519880935914591000007597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73679920623943060666671731 110519880935914591000007597)
    ·
      refine ⟨41444955350967971625002849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110519880935914591000007597 41444955350967971625002849)
      ·
        refine ⟨31083716513225978718752137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41444955350967971625002849 31083716513225978718752137)
        ·
          refine ⟨23312787384919484039064103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31083716513225978718752137 23312787384919484039064103)
          ·
            refine ⟨34969181077379226058596155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23312787384919484039064103 34969181077379226058596155)
            ·
              refine ⟨52453771616068839087894233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34969181077379226058596155 52453771616068839087894233)
              ·
                refine ⟨39340328712051629315920675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52453771616068839087894233 39340328712051629315920675)
                ·
                  refine ⟨59010493068077443973881013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39340328712051629315920675 59010493068077443973881013)
                  ·
                    refine ⟨5532233725132260372551345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59010493068077443973881013 5532233725132260372551345)
                    ·
                      refine ⟨4149175293849195279413509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532233725132260372551345 4149175293849195279413509)
                      ·
                        rfl

theorem cell23_8080490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_8080490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080490 prefixEnd_8080490 := by exact prefixLift 8080490
  have htrace : WordTrace (prefixWord ++ tailWord_8080490) baseStart_8080490 baseEnd_8080490 := by
    simpa [prefixWord, tailWord_8080490, baseEnd_8080490] using wordTrace_append hprefix tailTrace_8080490
  have hstable : (prefixWord ++ tailWord_8080490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080490).length < 2 ^ (prefixWord ++ tailWord_8080490).sum := by decide
  have hdescent : baseEnd_8080490 < baseStart_8080490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080503 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 2, 6, 2]
def baseStart_8080503 : Nat := 118140960795 + 8080503 * 2 ^ 59
def prefixEnd_8080503 : Nat := 4983230072969 + 3 ^ 40 * 8080503 * 2
def baseEnd_8080503 : Nat := 4149181969097703728550949

theorem tailTrace_8080503 : CollatzResearch.WordTrace tailWord_8080503 prefixEnd_8080503 4149181969097703728550949 := by
  unfold tailWord_8080503
  simp only [CollatzResearch.WordTrace]
  refine ⟨294720156644725145886910163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196480104429816763924606775 294720156644725145886910163)
  ·
    refine ⟨442080234967087718830365245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294720156644725145886910163 442080234967087718830365245)
    ·
      refine ⟨165780088112657894561386967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442080234967087718830365245 165780088112657894561386967)
      ·
        refine ⟨248670132168986841842080451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165780088112657894561386967 248670132168986841842080451)
        ·
          refine ⟨373005198253480262763120677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248670132168986841842080451 373005198253480262763120677)
          ·
            refine ⟨69938474672527549268085127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373005198253480262763120677 69938474672527549268085127)
            ·
              refine ⟨104907712008791323902127691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69938474672527549268085127 104907712008791323902127691)
              ·
                refine ⟨157361568013186985853191537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104907712008791323902127691 157361568013186985853191537)
                ·
                  refine ⟨118021176009890239389893653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157361568013186985853191537 118021176009890239389893653)
                  ·
                    refine ⟨5532242625463604971401265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118021176009890239389893653 5532242625463604971401265)
                    ·
                      refine ⟨4149181969097703728550949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532242625463604971401265 4149181969097703728550949)
                      ·
                        rfl

theorem cell23_8080503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 6, 2].length) (baseStart_8080503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080503 prefixEnd_8080503 := by exact prefixLift 8080503
  have htrace : WordTrace (prefixWord ++ tailWord_8080503) baseStart_8080503 baseEnd_8080503 := by
    simpa [prefixWord, tailWord_8080503, baseEnd_8080503] using wordTrace_append hprefix tailTrace_8080503
  have hstable : (prefixWord ++ tailWord_8080503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080503).length < 2 ^ (prefixWord ++ tailWord_8080503).sum := by decide
  have hdescent : baseEnd_8080503 < baseStart_8080503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080530 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_8080530 : Nat := 118140960795 + 8080530 * 2 ^ 59
def prefixEnd_8080530 : Nat := 4983230072969 + 3 ^ 40 * 8080530 * 2
def baseEnd_8080530 : Nat := 1383065277691791707637775

theorem tailTrace_8080530 : CollatzResearch.WordTrace tailWord_8080530 prefixEnd_8080530 1383065277691791707637775 := by
  unfold tailWord_8080530
  simp only [CollatzResearch.WordTrace]
  refine ⟨73680285353906832374535761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196480760943751552998762029 73680285353906832374535761)
  ·
    refine ⟨55260214015430124280901821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73680285353906832374535761 55260214015430124280901821)
    ·
      refine ⟨20722580255786296605338183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55260214015430124280901821 20722580255786296605338183)
      ·
        refine ⟨31083870383679444908007275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20722580255786296605338183 31083870383679444908007275)
        ·
          refine ⟨46625805575519167362010913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31083870383679444908007275 46625805575519167362010913)
          ·
            refine ⟨34969354181639375521508185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46625805575519167362010913 34969354181639375521508185)
            ·
              refine ⟨26227015636229531641131139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34969354181639375521508185 26227015636229531641131139)
              ·
                refine ⟨39340523454344297461696709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26227015636229531641131139 39340523454344297461696709)
                ·
                  refine ⟨7376348147689555774068133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39340523454344297461696709 7376348147689555774068133)
                  ·
                    refine ⟨1383065277691791707637775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7376348147689555774068133 1383065277691791707637775)
                    ·
                      rfl

theorem cell23_8080530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_8080530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080530 prefixEnd_8080530 := by exact prefixLift 8080530
  have htrace : WordTrace (prefixWord ++ tailWord_8080530) baseStart_8080530 baseEnd_8080530 := by
    simpa [prefixWord, tailWord_8080530, baseEnd_8080530] using wordTrace_append hprefix tailTrace_8080530
  have hstable : (prefixWord ++ tailWord_8080530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080530).length < 2 ^ (prefixWord ++ tailWord_8080530).sum := by decide
  have hdescent : baseEnd_8080530 < baseStart_8080530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080554 : List Nat := [3, 1, 5, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_8080554 : Nat := 118140960795 + 8080554 * 2 ^ 59
def prefixEnd_8080554 : Nat := 4983230072969 + 3 ^ 40 * 8080554 * 2
def baseEnd_8080554 : Nat := 4149208156611083029013215

theorem tailTrace_8080554 : CollatzResearch.WordTrace tailWord_8080554 prefixEnd_8080554 4149208156611083029013215 := by
  unfold tailWord_8080554
  simp only [CollatzResearch.WordTrace]
  refine ⟨73680504191885095399254179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196481344511693587731344477 73680504191885095399254179)
  ·
    refine ⟨110520756287827643098881269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73680504191885095399254179 110520756287827643098881269)
    ·
      refine ⟨10361320901983841540520119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110520756287827643098881269 10361320901983841540520119)
      ·
        refine ⟨15541981352975762310780179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10361320901983841540520119 15541981352975762310780179)
        ·
          refine ⟨23312972029463643466170269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15541981352975762310780179 23312972029463643466170269)
          ·
            refine ⟨8742364511048866299813851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23312972029463643466170269 8742364511048866299813851)
            ·
              refine ⟨13113546766573299449720777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8742364511048866299813851 13113546766573299449720777)
              ·
                refine ⟨9835160074929974587290583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13113546766573299449720777 9835160074929974587290583)
                ·
                  refine ⟨14752740112394961880935875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9835160074929974587290583 14752740112394961880935875)
                  ·
                    refine ⟨22129110168592442821403813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14752740112394961880935875 22129110168592442821403813)
                    ·
                      refine ⟨4149208156611083029013215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22129110168592442821403813 4149208156611083029013215)
                      ·
                        rfl

theorem cell23_8080554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_8080554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080554 prefixEnd_8080554 := by exact prefixLift 8080554
  have htrace : WordTrace (prefixWord ++ tailWord_8080554) baseStart_8080554 baseEnd_8080554 := by
    simpa [prefixWord, tailWord_8080554, baseEnd_8080554] using wordTrace_append hprefix tailTrace_8080554
  have hstable : (prefixWord ++ tailWord_8080554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080554).length < 2 ^ (prefixWord ++ tailWord_8080554).sum := by decide
  have hdescent : baseEnd_8080554 < baseStart_8080554 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080556 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 4, 7]
def baseStart_8080556 : Nat := 118140960795 + 8080556 * 2 ^ 59
def prefixEnd_8080556 : Nat := 4983230072969 + 3 ^ 40 * 8080556 * 2
def baseEnd_8080556 : Nat := 1383069727857464007062735

theorem tailTrace_8080556 : CollatzResearch.WordTrace tailWord_8080556 prefixEnd_8080556 1383069727857464007062735 := by
  unfold tailWord_8080556
  simp only [CollatzResearch.WordTrace]
  refine ⟨147361044856766567969294761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196481393142355423959059681 147361044856766567969294761)
  ·
    refine ⟨110520783642574925976971071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147361044856766567969294761 110520783642574925976971071)
    ·
      refine ⟨165781175463862388965456607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110520783642574925976971071 165781175463862388965456607)
      ·
        refine ⟨248671763195793583448184911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165781175463862388965456607 248671763195793583448184911)
        ·
          refine ⟨373007644793690375172277367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248671763195793583448184911 373007644793690375172277367)
          ·
            refine ⟨559511467190535562758416051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373007644793690375172277367 559511467190535562758416051)
            ·
              refine ⟨839267200785803344137624077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559511467190535562758416051 839267200785803344137624077)
              ·
                refine ⟨314725200294676254051609029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 839267200785803344137624077 314725200294676254051609029)
                ·
                  refine ⟨59010975055251797634676693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314725200294676254051609029 59010975055251797634676693)
                  ·
                    refine ⟨1383069727857464007062735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59010975055251797634676693 1383069727857464007062735)
                    ·
                      rfl

theorem cell23_8080556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_8080556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080556 prefixEnd_8080556 := by exact prefixLift 8080556
  have htrace : WordTrace (prefixWord ++ tailWord_8080556) baseStart_8080556 baseEnd_8080556 := by
    simpa [prefixWord, tailWord_8080556, baseEnd_8080556] using wordTrace_append hprefix tailTrace_8080556
  have hstable : (prefixWord ++ tailWord_8080556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080556).length < 2 ^ (prefixWord ++ tailWord_8080556).sum := by decide
  have hdescent : baseEnd_8080556 < baseStart_8080556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080557 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_8080557 : Nat := 118140960795 + 8080557 * 2 ^ 59
def prefixEnd_8080557 : Nat := 4983230072969 + 3 ^ 40 * 8080557 * 2
def baseEnd_8080557 : Nat := 4149209697053046517275701

theorem tailTrace_8080557 : CollatzResearch.WordTrace tailWord_8080557 prefixEnd_8080557 4149209697053046517275701 := by
  unfold tailWord_8080557
  simp only [CollatzResearch.WordTrace]
  refine ⟨294722126186529513109375925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196481417457686342072917283 294722126186529513109375925)
  ·
    refine ⟨27630199329987141854003993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294722126186529513109375925 27630199329987141854003993)
    ·
      refine ⟨20722649497490356390502995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27630199329987141854003993 20722649497490356390502995)
      ·
        refine ⟨31083974246235534585754493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20722649497490356390502995 31083974246235534585754493)
        ·
          refine ⟨11656490342338325469657935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31083974246235534585754493 11656490342338325469657935)
          ·
            refine ⟨17484735513507488204486903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11656490342338325469657935 17484735513507488204486903)
            ·
              refine ⟨26227103270261232306730355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17484735513507488204486903 26227103270261232306730355)
              ·
                refine ⟨39340654905391848460095533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26227103270261232306730355 39340654905391848460095533)
                ·
                  refine ⟨14752745589521943172535825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39340654905391848460095533 14752745589521943172535825)
                  ·
                    refine ⟨11064559192141457379401869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14752745589521943172535825 11064559192141457379401869)
                    ·
                      refine ⟨4149209697053046517275701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11064559192141457379401869 4149209697053046517275701)
                      ·
                        rfl

theorem cell23_8080557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_8080557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080557 prefixEnd_8080557 := by exact prefixLift 8080557
  have htrace : WordTrace (prefixWord ++ tailWord_8080557) baseStart_8080557 baseEnd_8080557 := by
    simpa [prefixWord, tailWord_8080557, baseEnd_8080557] using wordTrace_append hprefix tailTrace_8080557
  have hstable : (prefixWord ++ tailWord_8080557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080557).length < 2 ^ (prefixWord ++ tailWord_8080557).sum := by decide
  have hdescent : baseEnd_8080557 < baseStart_8080557 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080574 : List Nat := [4, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_8080574 : Nat := 118140960795 + 8080574 * 2 ^ 59
def prefixEnd_8080574 : Nat := 4983230072969 + 3 ^ 40 * 8080574 * 2
def baseEnd_8080574 : Nat := 4149218426224172950763123

theorem tailTrace_8080574 : CollatzResearch.WordTrace tailWord_8080574 prefixEnd_8080574 4149218426224172950763123 := by
  unfold tailWord_8080574
  simp only [CollatzResearch.WordTrace]
  refine ⟨36840343278433490626593097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196481830818311950008496517 36840343278433490626593097)
  ·
    refine ⟨27630257458825117969944823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36840343278433490626593097 27630257458825117969944823)
    ·
      refine ⟨41445386188237676954917235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27630257458825117969944823 41445386188237676954917235)
      ·
        refine ⟨62168079282356515432375853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41445386188237676954917235 62168079282356515432375853)
        ·
          refine ⟨23313029730883693287140945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62168079282356515432375853 23313029730883693287140945)
          ·
            refine ⟨17484772298162769965355709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23313029730883693287140945 17484772298162769965355709)
            ·
              refine ⟨6556789611811038737008391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17484772298162769965355709 6556789611811038737008391)
              ·
                refine ⟨9835184417716558105512587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6556789611811038737008391 9835184417716558105512587)
                ·
                  refine ⟨14752776626574837158268881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9835184417716558105512587 14752776626574837158268881)
                  ·
                    refine ⟨11064582469931127868701661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14752776626574837158268881 11064582469931127868701661)
                    ·
                      refine ⟨4149218426224172950763123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11064582469931127868701661 4149218426224172950763123)
                      ·
                        rfl

theorem cell23_8080574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_8080574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080574 prefixEnd_8080574 := by exact prefixLift 8080574
  have htrace : WordTrace (prefixWord ++ tailWord_8080574) baseStart_8080574 baseEnd_8080574 := by
    simpa [prefixWord, tailWord_8080574, baseEnd_8080574] using wordTrace_append hprefix tailTrace_8080574
  have hstable : (prefixWord ++ tailWord_8080574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080574).length < 2 ^ (prefixWord ++ tailWord_8080574).sum := by decide
  have hdescent : baseEnd_8080574 < baseStart_8080574 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080582 : List Nat := [6, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_8080582 : Nat := 118140960795 + 8080582 * 2 ^ 59
def prefixEnd_8080582 : Nat := 4983230072969 + 3 ^ 40 * 8080582 * 2
def baseEnd_8080582 : Nat := 4149222534069408919463087

theorem tailTrace_8080582 : CollatzResearch.WordTrace tailWord_8080582 prefixEnd_8080582 4149222534069408919463087 := by
  unfold tailWord_8080582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9210094937857466949344875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196482025340959294919357333 9210094937857466949344875)
  ·
    refine ⟨13815142406786200424017313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9210094937857466949344875 13815142406786200424017313)
    ·
      refine ⟨10361356805089650318012985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13815142406786200424017313 10361356805089650318012985)
      ·
        refine ⟨7771017603817237738509739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10361356805089650318012985 7771017603817237738509739)
        ·
          refine ⟨11656526405725856607764609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7771017603817237738509739 11656526405725856607764609)
          ·
            refine ⟨8742394804294392455823457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11656526405725856607764609 8742394804294392455823457)
            ·
              refine ⟨6556796103220794341867593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8742394804294392455823457 6556796103220794341867593)
              ·
                refine ⟨4917597077415595756400695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6556796103220794341867593 4917597077415595756400695)
                ·
                  refine ⟨7376395616123393634601043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4917597077415595756400695 7376395616123393634601043)
                  ·
                    refine ⟨11064593424185090451901565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7376395616123393634601043 11064593424185090451901565)
                    ·
                      refine ⟨4149222534069408919463087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11064593424185090451901565 4149222534069408919463087)
                      ·
                        rfl

theorem cell23_8080582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_8080582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080582 prefixEnd_8080582 := by exact prefixLift 8080582
  have htrace : WordTrace (prefixWord ++ tailWord_8080582) baseStart_8080582 baseEnd_8080582 := by
    simpa [prefixWord, tailWord_8080582, baseEnd_8080582] using wordTrace_append hprefix tailTrace_8080582
  have hstable : (prefixWord ++ tailWord_8080582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080582).length < 2 ^ (prefixWord ++ tailWord_8080582).sum := by decide
  have hdescent : baseEnd_8080582 < baseStart_8080582 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080597 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 3, 3, 2]
def baseStart_8080597 : Nat := 118140960795 + 8080597 * 2 ^ 59
def prefixEnd_8080597 : Nat := 4983230072969 + 3 ^ 40 * 8080597 * 2
def baseEnd_8080597 : Nat := 4149230236279226360775517

theorem tailTrace_8080597 : CollatzResearch.WordTrace tailWord_8080597 prefixEnd_8080597 4149230236279226360775517 := by
  unfold tailWord_8080597
  simp only [CollatzResearch.WordTrace]
  refine ⟨294723585106384599940832045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196482390070923066627221363 294723585106384599940832045)
  ·
    refine ⟨110521344414894224977812017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294723585106384599940832045 110521344414894224977812017)
    ·
      refine ⟨82891008311170668733359013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110521344414894224977812017 82891008311170668733359013)
      ·
        refine ⟨15542064058344500387504815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82891008311170668733359013 15542064058344500387504815)
        ·
          refine ⟨23313096087516750581257223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15542064058344500387504815 23313096087516750581257223)
          ·
            refine ⟨34969644131275125871885835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23313096087516750581257223 34969644131275125871885835)
            ·
              refine ⟨52454466196912688807828753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34969644131275125871885835 52454466196912688807828753)
              ·
                refine ⟨39340849647684516605871565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52454466196912688807828753 39340849647684516605871565)
                ·
                  refine ⟨14752818617881693727201837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39340849647684516605871565 14752818617881693727201837)
                  ·
                    refine ⟨5532306981705635147700689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14752818617881693727201837 5532306981705635147700689)
                    ·
                      refine ⟨4149230236279226360775517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532306981705635147700689 4149230236279226360775517)
                      ·
                        rfl

theorem cell23_8080597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_8080597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080597 prefixEnd_8080597 := by exact prefixLift 8080597
  have htrace : WordTrace (prefixWord ++ tailWord_8080597) baseStart_8080597 baseEnd_8080597 := by
    simpa [prefixWord, tailWord_8080597, baseEnd_8080597] using wordTrace_append hprefix tailTrace_8080597
  have hstable : (prefixWord ++ tailWord_8080597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080597).length < 2 ^ (prefixWord ++ tailWord_8080597).sum := by decide
  have hdescent : baseEnd_8080597 < baseStart_8080597 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080644 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_8080644 : Nat := 118140960795 + 8080644 * 2 ^ 59
def prefixEnd_8080644 : Nat := 4983230072969 + 3 ^ 40 * 8080644 * 2
def baseEnd_8080644 : Nat := 4149254369869987676887801

theorem tailTrace_8080644 : CollatzResearch.WordTrace tailWord_8080644 prefixEnd_8080644 4149254369869987676887801 := by
  unfold tailWord_8080644
  simp only [CollatzResearch.WordTrace]
  refine ⟨147362649668607163483896493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196483532891476217978528657 147362649668607163483896493)
  ·
    refine ⟨55260993625727686306461185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147362649668607163483896493 55260993625727686306461185)
    ·
      refine ⟨41445745219295764729845889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55260993625727686306461185 41445745219295764729845889)
      ·
        refine ⟨31084308914471823547384417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41445745219295764729845889 31084308914471823547384417)
        ·
          refine ⟨23313231685853867660538313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31084308914471823547384417 23313231685853867660538313)
          ·
            refine ⟨17484923764390400745403735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23313231685853867660538313 17484923764390400745403735)
            ·
              refine ⟨26227385646585601118105603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17484923764390400745403735 26227385646585601118105603)
              ·
                refine ⟨39341078469878401677158405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26227385646585601118105603 39341078469878401677158405)
                ·
                  refine ⟨7376452213102200314467201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39341078469878401677158405 7376452213102200314467201)
                  ·
                    refine ⟨5532339159826650235850401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7376452213102200314467201 5532339159826650235850401)
                    ·
                      refine ⟨4149254369869987676887801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532339159826650235850401 4149254369869987676887801)
                      ·
                        rfl

theorem cell23_8080644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_8080644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080644 prefixEnd_8080644 := by exact prefixLift 8080644
  have htrace : WordTrace (prefixWord ++ tailWord_8080644) baseStart_8080644 baseEnd_8080644 := by
    simpa [prefixWord, tailWord_8080644, baseEnd_8080644] using wordTrace_append hprefix tailTrace_8080644
  have hstable : (prefixWord ++ tailWord_8080644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080644).length < 2 ^ (prefixWord ++ tailWord_8080644).sum := by decide
  have hdescent : baseEnd_8080644 < baseStart_8080644 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080663 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 3, 7]
def baseStart_8080663 : Nat := 118140960795 + 8080663 * 2 ^ 59
def prefixEnd_8080663 : Nat := 4983230072969 + 3 ^ 40 * 8080663 * 2
def baseEnd_8080663 : Nat := 1383088042000807700850071

theorem tailTrace_8080663 : CollatzResearch.WordTrace tailWord_8080663 prefixEnd_8080663 1383088042000807700850071 := by
  unfold tailWord_8080663
  simp only [CollatzResearch.WordTrace]
  refine ⟨294725992324145493212734643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196483994882763662141823095 294725992324145493212734643)
  ·
    refine ⟨442088988486218239819101965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294725992324145493212734643 442088988486218239819101965)
    ·
      refine ⟨165783370682331839932163237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442088988486218239819101965 165783370682331839932163237)
      ·
        refine ⟨31084382002937219987280607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165783370682331839932163237 31084382002937219987280607)
        ·
          refine ⟨46626573004405829980920911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31084382002937219987280607 46626573004405829980920911)
          ·
            refine ⟨69939859506608744971381367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46626573004405829980920911 69939859506608744971381367)
            ·
              refine ⟨104909789259913117457072051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69939859506608744971381367 104909789259913117457072051)
              ·
                refine ⟨157364683889869676185608077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104909789259913117457072051 157364683889869676185608077)
                ·
                  refine ⟨59011756458701128569603029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157364683889869676185608077 59011756458701128569603029)
                  ·
                    refine ⟨1383088042000807700850071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59011756458701128569603029 1383088042000807700850071)
                    ·
                      rfl

theorem cell23_8080663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_8080663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080663 prefixEnd_8080663 := by exact prefixLift 8080663
  have htrace : WordTrace (prefixWord ++ tailWord_8080663) baseStart_8080663 baseEnd_8080663 := by
    simpa [prefixWord, tailWord_8080663, baseEnd_8080663] using wordTrace_append hprefix tailTrace_8080663
  have hstable : (prefixWord ++ tailWord_8080663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080663).length < 2 ^ (prefixWord ++ tailWord_8080663).sum := by decide
  have hdescent : baseEnd_8080663 < baseStart_8080663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080673 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_8080673 : Nat := 118140960795 + 8080673 * 2 ^ 59
def prefixEnd_8080673 : Nat := 4983230072969 + 3 ^ 40 * 8080673 * 2
def baseEnd_8080673 : Nat := 4149269260808968063425167

theorem tailTrace_8080673 : CollatzResearch.WordTrace tailWord_8080673 prefixEnd_8080673 4149269260808968063425167 := by
  unfold tailWord_8080673
  simp only [CollatzResearch.WordTrace]
  refine ⟨294726357054109264920598673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196484238036072843280399115 294726357054109264920598673)
  ·
    refine ⟨221044767790581948690449005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294726357054109264920598673 221044767790581948690449005)
    ·
      refine ⟨82891787921468230758918377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221044767790581948690449005 82891787921468230758918377)
      ·
        refine ⟨62168840941101173069188783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82891787921468230758918377 62168840941101173069188783)
        ·
          refine ⟨93253261411651759603783175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62168840941101173069188783 93253261411651759603783175)
          ·
            refine ⟨139879892117477639405674763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93253261411651759603783175 139879892117477639405674763)
            ·
              refine ⟨209819838176216459108512145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139879892117477639405674763 209819838176216459108512145)
              ·
                refine ⟨157364878632162344331384109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209819838176216459108512145 157364878632162344331384109)
                ·
                  refine ⟨59011829487060879124269041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157364878632162344331384109 59011829487060879124269041)
                  ·
                    refine ⟨44258872115295659343201781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59011829487060879124269041 44258872115295659343201781)
                    ·
                      refine ⟨4149269260808968063425167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44258872115295659343201781 4149269260808968063425167)
                      ·
                        rfl

theorem cell23_8080673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_8080673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080673 prefixEnd_8080673 := by exact prefixLift 8080673
  have htrace : WordTrace (prefixWord ++ tailWord_8080673) baseStart_8080673 baseEnd_8080673 := by
    simpa [prefixWord, tailWord_8080673, baseEnd_8080673] using wordTrace_append hprefix tailTrace_8080673
  have hstable : (prefixWord ++ tailWord_8080673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080673).length < 2 ^ (prefixWord ++ tailWord_8080673).sum := by decide
  have hdescent : baseEnd_8080673 < baseStart_8080673 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080680 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 1, 7]
def baseStart_8080680 : Nat := 118140960795 + 8080680 * 2 ^ 59
def prefixEnd_8080680 : Nat := 4983230072969 + 3 ^ 40 * 8080680 * 2
def baseEnd_8080680 : Nat := 1383090951724516512012545

theorem tailTrace_8080680 : CollatzResearch.WordTrace tailWord_8080680 prefixEnd_8080680 1383090951724516512012545 := by
  unfold tailWord_8080680
  simp only [CollatzResearch.WordTrace]
  refine ⟨147363306182541952558051747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196484408243389270077402329 147363306182541952558051747)
  ·
    refine ⟨221044959273812928837077621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147363306182541952558051747 221044959273812928837077621)
    ·
      refine ⟨20722964931919962078476027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221044959273812928837077621 20722964931919962078476027)
      ·
        refine ⟨31084447397879943117714041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20722964931919962078476027 31084447397879943117714041)
        ·
          refine ⟨23313335548409957338285531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31084447397879943117714041 23313335548409957338285531)
          ·
            refine ⟨34970003322614936007428297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23313335548409957338285531 34970003322614936007428297)
            ·
              refine ⟨26227502491961202005571223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34970003322614936007428297 26227502491961202005571223)
              ·
                refine ⟨39341253737941803008356835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26227502491961202005571223 39341253737941803008356835)
                ·
                  refine ⟨59011880606912704512535253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39341253737941803008356835 59011880606912704512535253)
                  ·
                    refine ⟨1383090951724516512012545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59011880606912704512535253 1383090951724516512012545)
                    ·
                      rfl

theorem cell23_8080680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_8080680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080680 prefixEnd_8080680 := by exact prefixLift 8080680
  have htrace : WordTrace (prefixWord ++ tailWord_8080680) baseStart_8080680 baseEnd_8080680 := by
    simpa [prefixWord, tailWord_8080680, baseEnd_8080680] using wordTrace_append hprefix tailTrace_8080680
  have hstable : (prefixWord ++ tailWord_8080680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080680).length < 2 ^ (prefixWord ++ tailWord_8080680).sum := by decide
  have hdescent : baseEnd_8080680 < baseStart_8080680 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080697 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 2, 5]
def baseStart_8080697 : Nat := 118140960795 + 8080697 * 2 ^ 59
def prefixEnd_8080697 : Nat := 4983230072969 + 3 ^ 40 * 8080697 * 2
def baseEnd_8080697 : Nat := 1383093861448225323175019

theorem tailTrace_8080697 : CollatzResearch.WordTrace tailWord_8080697 prefixEnd_8080697 1383093861448225323175019 := by
  unfold tailWord_8080697
  simp only [CollatzResearch.WordTrace]
  refine ⟨294727232406022317019472345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196484821604014878012981563 294727232406022317019472345)
  ·
    refine ⟨221045424304516737764604259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294727232406022317019472345 221045424304516737764604259)
    ·
      refine ⟨331568136456775106646906389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221045424304516737764604259 331568136456775106646906389)
      ·
        refine ⟨15542256396411333124073737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 331568136456775106646906389 15542256396411333124073737)
        ·
          refine ⟨11656692297308499843055303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15542256396411333124073737 11656692297308499843055303)
          ·
            refine ⟨17485038445962749764582955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11656692297308499843055303 17485038445962749764582955)
            ·
              refine ⟨26227557668944124646874433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17485038445962749764582955 26227557668944124646874433)
              ·
                refine ⟨19670668251708093485155825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26227557668944124646874433 19670668251708093485155825)
                ·
                  refine ⟨14753001188781070113866869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19670668251708093485155825 14753001188781070113866869)
                  ·
                    refine ⟨1383093861448225323175019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14753001188781070113866869 1383093861448225323175019)
                    ·
                      rfl

theorem cell23_8080697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 5].length) (baseStart_8080697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080697 prefixEnd_8080697 := by exact prefixLift 8080697
  have htrace : WordTrace (prefixWord ++ tailWord_8080697) baseStart_8080697 baseEnd_8080697 := by
    simpa [prefixWord, tailWord_8080697, baseEnd_8080697] using wordTrace_append hprefix tailTrace_8080697
  have hstable : (prefixWord ++ tailWord_8080697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080697).length < 2 ^ (prefixWord ++ tailWord_8080697).sum := by decide
  have hdescent : baseEnd_8080697 < baseStart_8080697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080700 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_8080700 : Nat := 118140960795 + 8080700 * 2 ^ 59
def prefixEnd_8080700 : Nat := 4983230072969 + 3 ^ 40 * 8080700 * 2
def baseEnd_8080700 : Nat := 4149283124786639457787543

theorem tailTrace_8080700 : CollatzResearch.WordTrace tailWord_8080700 prefixEnd_8080700 4149283124786639457787543 := by
  unfold tailWord_8080700
  simp only [CollatzResearch.WordTrace]
  refine ⟨147363670912505724265915777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196484894550007632354554369 147363670912505724265915777)
  ·
    refine ⟨110522753184379293199436833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147363670912505724265915777 110522753184379293199436833)
    ·
      refine ⟨82892064888284469899577625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110522753184379293199436833 82892064888284469899577625)
      ·
        refine ⟨62169048666213352424683219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82892064888284469899577625 62169048666213352424683219)
        ·
          refine ⟨93253572999320028637024829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62169048666213352424683219 93253572999320028637024829)
          ·
            refine ⟨34970089874745010738884311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93253572999320028637024829 34970089874745010738884311)
            ·
              refine ⟨52455134812117516108326467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34970089874745010738884311 52455134812117516108326467)
              ·
                refine ⟨78682702218176274162489701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52455134812117516108326467 78682702218176274162489701)
                ·
                  refine ⟨14753006665908051405466819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78682702218176274162489701 14753006665908051405466819)
                  ·
                    refine ⟨22129509998862077108200229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14753006665908051405466819 22129509998862077108200229)
                    ·
                      refine ⟨4149283124786639457787543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22129509998862077108200229 4149283124786639457787543)
                      ·
                        rfl

theorem cell23_8080700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_8080700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080700 prefixEnd_8080700 := by exact prefixLift 8080700
  have htrace : WordTrace (prefixWord ++ tailWord_8080700) baseStart_8080700 baseEnd_8080700 := by
    simpa [prefixWord, tailWord_8080700, baseEnd_8080700] using wordTrace_append hprefix tailTrace_8080700
  have hstable : (prefixWord ++ tailWord_8080700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080700).length < 2 ^ (prefixWord ++ tailWord_8080700).sum := by decide
  have hdescent : baseEnd_8080700 < baseStart_8080700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080701 : List Nat := [1, 4, 1, 5, 1, 1, 3, 2, 5]
def baseStart_8080701 : Nat := 118140960795 + 8080701 * 2 ^ 59
def prefixEnd_8080701 : Nat := 4983230072969 + 3 ^ 40 * 8080701 * 2
def baseEnd_8080701 : Nat := 461031515363032661541671

theorem tailTrace_8080701 : CollatzResearch.WordTrace tailWord_8080701 prefixEnd_8080701 461031515363032661541671 := by
  unfold tailWord_8080701
  simp only [CollatzResearch.WordTrace]
  refine ⟨294727378298007825702617957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196484918865338550468411971 294727378298007825702617957)
  ·
    refine ⟨55261383430876467319240867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294727378298007825702617957 55261383430876467319240867)
    ·
      refine ⟨82892075146314700978861301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55261383430876467319240867 82892075146314700978861301)
      ·
        refine ⟨7771132044967003216768247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82892075146314700978861301 7771132044967003216768247)
        ·
          refine ⟨11656698067450504825152371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7771132044967003216768247 11656698067450504825152371)
          ·
            refine ⟨17485047101175757237728557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11656698067450504825152371 17485047101175757237728557)
            ·
              refine ⟨6556892662940908964148209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17485047101175757237728557 6556892662940908964148209)
              ·
                refine ⟨4917669497205681723111157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6556892662940908964148209 4917669497205681723111157)
                ·
                  refine ⟨461031515363032661541671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4917669497205681723111157 461031515363032661541671)
                  ·
                    rfl

theorem cell23_8080701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_8080701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080701 prefixEnd_8080701 := by exact prefixLift 8080701
  have htrace : WordTrace (prefixWord ++ tailWord_8080701) baseStart_8080701 baseEnd_8080701 := by
    simpa [prefixWord, tailWord_8080701, baseEnd_8080701] using wordTrace_append hprefix tailTrace_8080701
  have hstable : (prefixWord ++ tailWord_8080701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080701).length < 2 ^ (prefixWord ++ tailWord_8080701).sum := by decide
  have hdescent : baseEnd_8080701 < baseStart_8080701 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080713 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 6]
def baseStart_8080713 : Nat := 118140960795 + 8080713 * 2 ^ 59
def prefixEnd_8080713 : Nat := 4983230072969 + 3 ^ 40 * 8080713 * 2
def baseEnd_8080713 : Nat := 4149289800035147906924983

theorem tailTrace_8080713 : CollatzResearch.WordTrace tailWord_8080713 prefixEnd_8080713 4149289800035147906924983 := by
  unfold tailWord_8080713
  simp only [CollatzResearch.WordTrace]
  refine ⟨294727815973964351752054793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196485210649309567834703195 294727815973964351752054793)
  ·
    refine ⟨221045861980473263814041095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294727815973964351752054793 221045861980473263814041095)
    ·
      refine ⟨331568792970709895721061643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221045861980473263814041095 331568792970709895721061643)
      ·
        refine ⟨497353189456064843581592465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331568792970709895721061643 497353189456064843581592465)
        ·
          refine ⟨373014892092048632686194349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497353189456064843581592465 373014892092048632686194349)
          ·
            refine ⟨139880584534518237257322881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373014892092048632686194349 139880584534518237257322881)
            ·
              refine ⟨104910438400888677942992161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139880584534518237257322881 104910438400888677942992161)
              ·
                refine ⟨78682828800666508457244121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104910438400888677942992161 78682828800666508457244121)
                ·
                  refine ⟨59012121600499881342933091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78682828800666508457244121 59012121600499881342933091)
                  ·
                    refine ⟨88518182400749822014399637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59012121600499881342933091 88518182400749822014399637)
                    ·
                      refine ⟨4149289800035147906924983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88518182400749822014399637 4149289800035147906924983)
                      ·
                        rfl

theorem cell23_8080713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_8080713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080713 prefixEnd_8080713 := by exact prefixLift 8080713
  have htrace : WordTrace (prefixWord ++ tailWord_8080713) baseStart_8080713 baseEnd_8080713 := by
    simpa [prefixWord, tailWord_8080713, baseEnd_8080713] using wordTrace_append hprefix tailTrace_8080713
  have hstable : (prefixWord ++ tailWord_8080713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080713).length < 2 ^ (prefixWord ++ tailWord_8080713).sum := by decide
  have hdescent : baseEnd_8080713 < baseStart_8080713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080720 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 3]
def baseStart_8080720 : Nat := 118140960795 + 8080720 * 2 ^ 59
def prefixEnd_8080720 : Nat := 4983230072969 + 3 ^ 40 * 8080720 * 2
def baseEnd_8080720 : Nat := 4149293394399729379537451

theorem tailTrace_8080720 : CollatzResearch.WordTrace tailWord_8080720 prefixEnd_8080720 4149293394399729379537451 := by
  unfold tailWord_8080720
  simp only [CollatzResearch.WordTrace]
  refine ⟨147364035642469495973779807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196485380856625994631706409 147364035642469495973779807)
  ·
    refine ⟨221046053463704243960669711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147364035642469495973779807 221046053463704243960669711)
    ·
      refine ⟨331569080195556365941004567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221046053463704243960669711 331569080195556365941004567)
      ·
        refine ⟨497353620293334548911506851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331569080195556365941004567 497353620293334548911506851)
        ·
          refine ⟨746030430440001823367260277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497353620293334548911506851 746030430440001823367260277)
          ·
            refine ⟨69940352853750170940680651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 746030430440001823367260277 69940352853750170940680651)
            ·
              refine ⟨104910529280625256411020977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69940352853750170940680651 104910529280625256411020977)
              ·
                refine ⟨78682896960468942308265733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104910529280625256411020977 78682896960468942308265733)
                ·
                  refine ⟨14753043180087926682799825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78682896960468942308265733 14753043180087926682799825)
                  ·
                    refine ⟨11064782385065945012099869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14753043180087926682799825 11064782385065945012099869)
                    ·
                      refine ⟨4149293394399729379537451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11064782385065945012099869 4149293394399729379537451)
                      ·
                        rfl

theorem cell23_8080720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 3].length) (baseStart_8080720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080720 prefixEnd_8080720 := by exact prefixLift 8080720
  have htrace : WordTrace (prefixWord ++ tailWord_8080720) baseStart_8080720 baseEnd_8080720 := by
    simpa [prefixWord, tailWord_8080720, baseEnd_8080720] using wordTrace_append hprefix tailTrace_8080720
  have hstable : (prefixWord ++ tailWord_8080720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080720).length < 2 ^ (prefixWord ++ tailWord_8080720).sum := by decide
  have hdescent : baseEnd_8080720 < baseStart_8080720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080800 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 1, 6]
def baseStart_8080800 : Nat := 118140960795 + 8080800 * 2 ^ 59
def prefixEnd_8080800 : Nat := 4983230072969 + 3 ^ 40 * 8080800 * 2
def baseEnd_8080800 : Nat := 1383111490950696355512361

theorem tailTrace_8080800 : CollatzResearch.WordTrace tailWord_8080800 prefixEnd_8080800 1383111490950696355512361 := by
  unfold tailWord_8080800
  simp only [CollatzResearch.WordTrace]
  refine ⟨147365494562324582805235927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196487326083099443740314569 147365494562324582805235927)
  ·
    refine ⟨221048241843486874207853891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147365494562324582805235927 221048241843486874207853891)
    ·
      refine ⟨331572362765230311311780837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221048241843486874207853891 331572362765230311311780837)
      ·
        refine ⟨62169818018480683370958907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331572362765230311311780837 62169818018480683370958907)
        ·
          refine ⟨93254727027721025056438361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62169818018480683370958907 93254727027721025056438361)
          ·
            refine ⟨69941045270790768792328771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93254727027721025056438361 69941045270790768792328771)
            ·
              refine ⟨104911567906186153188493157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69941045270790768792328771 104911567906186153188493157)
              ·
                refine ⟨19670918982409903722842467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104911567906186153188493157 19670918982409903722842467)
                ·
                  refine ⟨29506378473614855584263701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19670918982409903722842467 29506378473614855584263701)
                  ·
                    refine ⟨1383111490950696355512361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29506378473614855584263701 1383111490950696355512361)
                    ·
                      rfl

theorem cell23_8080800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 1, 6].length) (baseStart_8080800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080800 prefixEnd_8080800 := by exact prefixLift 8080800
  have htrace : WordTrace (prefixWord ++ tailWord_8080800) baseStart_8080800 baseEnd_8080800 := by
    simpa [prefixWord, tailWord_8080800, baseEnd_8080800] using wordTrace_append hprefix tailTrace_8080800
  have hstable : (prefixWord ++ tailWord_8080800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080800).length < 2 ^ (prefixWord ++ tailWord_8080800).sum := by decide
  have hdescent : baseEnd_8080800 < baseStart_8080800 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080817 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 4, 4]
def baseStart_8080817 : Nat := 118140960795 + 8080817 * 2 ^ 59
def prefixEnd_8080817 : Nat := 4983230072969 + 3 ^ 40 * 8080817 * 2
def baseEnd_8080817 : Nat := 1383114400674405166674835

theorem tailTrace_8080817 : CollatzResearch.WordTrace tailWord_8080817 prefixEnd_8080817 1383114400674405166674835 := by
  unfold tailWord_8080817
  simp only [CollatzResearch.WordTrace]
  refine ⟨294731609165587577513840705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196487739443725051675893803 294731609165587577513840705)
  ·
    refine ⟨221048706874190683135380529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294731609165587577513840705 221048706874190683135380529)
    ·
      refine ⟨165786530155643012351535397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221048706874190683135380529 165786530155643012351535397)
      ·
        refine ⟨31084974404183064815912887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165786530155643012351535397 31084974404183064815912887)
        ·
          refine ⟨46627461606274597223869331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31084974404183064815912887 46627461606274597223869331)
          ·
            refine ⟨69941192409411895835803997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46627461606274597223869331 69941192409411895835803997)
            ·
              refine ⟨26227947153529460938426499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69941192409411895835803997 26227947153529460938426499)
              ·
                refine ⟨39341920730294191407639749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26227947153529460938426499 39341920730294191407639749)
                ·
                  refine ⟨7376610136930160888932453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39341920730294191407639749 7376610136930160888932453)
                  ·
                    refine ⟨1383114400674405166674835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7376610136930160888932453 1383114400674405166674835)
                    ·
                      rfl

theorem cell23_8080817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_8080817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080817 prefixEnd_8080817 := by exact prefixLift 8080817
  have htrace : WordTrace (prefixWord ++ tailWord_8080817) baseStart_8080817 baseEnd_8080817 := by
    simpa [prefixWord, tailWord_8080817, baseEnd_8080817] using wordTrace_append hprefix tailTrace_8080817
  have hstable : (prefixWord ++ tailWord_8080817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080817).length < 2 ^ (prefixWord ++ tailWord_8080817).sum := by decide
  have hdescent : baseEnd_8080817 < baseStart_8080817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080824 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 3, 2, 2]
def baseStart_8080824 : Nat := 118140960795 + 8080824 * 2 ^ 59
def prefixEnd_8080824 : Nat := 4983230072969 + 3 ^ 40 * 8080824 * 2
def baseEnd_8080824 : Nat := 4149346796387796972636973

theorem tailTrace_8080824 : CollatzResearch.WordTrace tailWord_8080824 prefixEnd_8080824 4149346796387796972636973 := by
  unfold tailWord_8080824
  simp only [CollatzResearch.WordTrace]
  refine ⟨147365932238281108854672763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196487909651041478472897017 147365932238281108854672763)
  ·
    refine ⟨221048898357421663282009145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147365932238281108854672763 221048898357421663282009145)
    ·
      refine ⟨165786673768066247461506859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221048898357421663282009145 165786673768066247461506859)
      ·
        refine ⟨248680010652099371192260289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165786673768066247461506859 248680010652099371192260289)
        ·
          refine ⟨186510007989074528394195217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248680010652099371192260289 186510007989074528394195217)
          ·
            refine ⟨139882505991805896295646413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186510007989074528394195217 139882505991805896295646413)
            ·
              refine ⟨52455939746927211110867405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139882505991805896295646413 52455939746927211110867405)
              ·
                refine ⟨19670977405097704166575277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52455939746927211110867405 19670977405097704166575277)
                ·
                  refine ⟨7376616526911639062465729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19670977405097704166575277 7376616526911639062465729)
                  ·
                    refine ⟨5532462395183729296849297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7376616526911639062465729 5532462395183729296849297)
                    ·
                      refine ⟨4149346796387796972636973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532462395183729296849297 4149346796387796972636973)
                      ·
                        rfl

theorem cell23_8080824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 3, 2, 2].length) (baseStart_8080824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080824 prefixEnd_8080824 := by exact prefixLift 8080824
  have htrace : WordTrace (prefixWord ++ tailWord_8080824) baseStart_8080824 baseEnd_8080824 := by
    simpa [prefixWord, tailWord_8080824, baseEnd_8080824] using wordTrace_append hprefix tailTrace_8080824
  have hstable : (prefixWord ++ tailWord_8080824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080824).length < 2 ^ (prefixWord ++ tailWord_8080824).sum := by decide
  have hdescent : baseEnd_8080824 < baseStart_8080824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080830 : List Nat := [4, 2, 1, 1, 1, 1, 1, 12]
def baseStart_8080830 : Nat := 118140960795 + 8080830 * 2 ^ 59
def prefixEnd_8080830 : Nat := 4983230072969 + 3 ^ 40 * 8080830 * 2
def baseEnd_8080830 : Nat := 153679625084137924043035

theorem tailTrace_8080830 : CollatzResearch.WordTrace tailWord_8080830 prefixEnd_8080830 153679625084137924043035 := by
  unfold tailWord_8080830
  simp only [CollatzResearch.WordTrace]
  refine ⟨36841510414317560091757993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196488055543026987156042629 36841510414317560091757993)
  ·
    refine ⟨27631132810738170068818495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36841510414317560091757993 27631132810738170068818495)
    ·
      refine ⟨41446699216107255103227743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27631132810738170068818495 41446699216107255103227743)
      ·
        refine ⟨62170048824160882654841615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41446699216107255103227743 62170048824160882654841615)
        ·
          refine ⟨93255073236241323982262423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62170048824160882654841615 93255073236241323982262423)
          ·
            refine ⟨139882609854361985973393635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93255073236241323982262423 139882609854361985973393635)
            ·
              refine ⟨209823914781542978960090453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139882609854361985973393635 209823914781542978960090453)
              ·
                refine ⟨153679625084137924043035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 209823914781542978960090453 153679625084137924043035)
                ·
                  rfl

theorem cell23_8080830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_8080830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080830 prefixEnd_8080830 := by exact prefixLift 8080830
  have htrace : WordTrace (prefixWord ++ tailWord_8080830) baseStart_8080830 baseEnd_8080830 := by
    simpa [prefixWord, tailWord_8080830, baseEnd_8080830] using wordTrace_append hprefix tailTrace_8080830
  have hstable : (prefixWord ++ tailWord_8080830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080830).length < 2 ^ (prefixWord ++ tailWord_8080830).sum := by decide
  have hdescent : baseEnd_8080830 < baseStart_8080830 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080844 : List Nat := [2, 2, 1, 4, 2, 1, 1, 4, 1, 2, 3]
def baseStart_8080844 : Nat := 118140960795 + 8080844 * 2 ^ 59
def prefixEnd_8080844 : Nat := 4983230072969 + 3 ^ 40 * 8080844 * 2
def baseEnd_8080844 : Nat := 4149357066000886894386881

theorem tailTrace_8080844 : CollatzResearch.WordTrace tailWord_8080844 prefixEnd_8080844 4149357066000886894386881 := by
  unfold tailWord_8080844
  simp only [CollatzResearch.WordTrace]
  refine ⟨147366296968244880562536793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196488395957659840750049057 147366296968244880562536793)
  ·
    refine ⟨110524722726183660421902595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147366296968244880562536793 110524722726183660421902595)
    ·
      refine ⟨165787084089275490632853893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110524722726183660421902595 165787084089275490632853893)
      ·
        refine ⟨31085078266739154493660105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165787084089275490632853893 31085078266739154493660105)
        ·
          refine ⟨23313808700054365870245079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31085078266739154493660105 23313808700054365870245079)
          ·
            refine ⟨34970713050081548805367619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23313808700054365870245079 34970713050081548805367619)
            ·
              refine ⟨52456069575122323208051429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34970713050081548805367619 52456069575122323208051429)
              ·
                refine ⟨9835513045335435601509643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52456069575122323208051429 9835513045335435601509643)
                ·
                  refine ⟨14753269568003153402264465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9835513045335435601509643 14753269568003153402264465)
                  ·
                    refine ⟨11064952176002365051698349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14753269568003153402264465 11064952176002365051698349)
                    ·
                      refine ⟨4149357066000886894386881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11064952176002365051698349 4149357066000886894386881)
                      ·
                        rfl

theorem cell23_8080844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_8080844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080844 prefixEnd_8080844 := by exact prefixLift 8080844
  have htrace : WordTrace (prefixWord ++ tailWord_8080844) baseStart_8080844 baseEnd_8080844 := by
    simpa [prefixWord, tailWord_8080844, baseEnd_8080844] using wordTrace_append hprefix tailTrace_8080844
  have hstable : (prefixWord ++ tailWord_8080844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080844).length < 2 ^ (prefixWord ++ tailWord_8080844).sum := by decide
  have hdescent : baseEnd_8080844 < baseStart_8080844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080858 : List Nat := [3, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2]
def baseStart_8080858 : Nat := 118140960795 + 8080858 * 2 ^ 59
def prefixEnd_8080858 : Nat := 4983230072969 + 3 ^ 40 * 8080858 * 2
def baseEnd_8080858 : Nat := 4149364254730049839611817

theorem tailTrace_8080858 : CollatzResearch.WordTrace tailWord_8080858 prefixEnd_8080858 4149364254730049839611817 := by
  unfold tailWord_8080858
  simp only [CollatzResearch.WordTrace]
  refine ⟨73683276139609760379020807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196488736372292694344055485 73683276139609760379020807)
  ·
    refine ⟨110524914209414640568531211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73683276139609760379020807 110524914209414640568531211)
    ·
      refine ⟨165787371314121960852796817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110524914209414640568531211 165787371314121960852796817)
      ·
        refine ⟨124340528485591470639597613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165787371314121960852796817 124340528485591470639597613)
        ·
          refine ⟨46627698182096801489849105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124340528485591470639597613 46627698182096801489849105)
          ·
            refine ⟨34970773636572601117386829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46627698182096801489849105 34970773636572601117386829)
            ·
              refine ⟨13114040113714725419020061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34970773636572601117386829 13114040113714725419020061)
              ·
                refine ⟨4917765042643022032132523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13114040113714725419020061 4917765042643022032132523)
                ·
                  refine ⟨7376647563964533048198785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4917765042643022032132523 7376647563964533048198785)
                  ·
                    refine ⟨5532485672973399786149089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7376647563964533048198785 5532485672973399786149089)
                    ·
                      refine ⟨4149364254730049839611817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532485672973399786149089 4149364254730049839611817)
                      ·
                        rfl

theorem cell23_8080858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_8080858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080858 prefixEnd_8080858 := by exact prefixLift 8080858
  have htrace : WordTrace (prefixWord ++ tailWord_8080858) baseStart_8080858 baseEnd_8080858 := by
    simpa [prefixWord, tailWord_8080858, baseEnd_8080858] using wordTrace_append hprefix tailTrace_8080858
  have hstable : (prefixWord ++ tailWord_8080858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080858).length < 2 ^ (prefixWord ++ tailWord_8080858).sum := by decide
  have hdescent : baseEnd_8080858 < baseStart_8080858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080890 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 1, 8]
def baseStart_8080890 : Nat := 118140960795 + 8080890 * 2 ^ 59
def prefixEnd_8080890 : Nat := 4983230072969 + 3 ^ 40 * 8080890 * 2
def baseEnd_8080890 : Nat := 1383126895370331238137223

theorem tailTrace_8080890 : CollatzResearch.WordTrace tailWord_8080890 prefixEnd_8080890 1383126895370331238137223 := by
  unfold tailWord_8080890
  simp only [CollatzResearch.WordTrace]
  refine ⟨73683567923580777745312031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196489514462882073987498749 73683567923580777745312031)
  ·
    refine ⟨110525351885371166617968047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73683567923580777745312031 110525351885371166617968047)
    ·
      refine ⟨165788027828056749926952071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110525351885371166617968047 165788027828056749926952071)
      ·
        refine ⟨248682041742085124890428107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165788027828056749926952071 248682041742085124890428107)
        ·
          refine ⟨373023062613127687335642161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248682041742085124890428107 373023062613127687335642161)
          ·
            refine ⟨279767296959845765501731621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373023062613127687335642161 279767296959845765501731621)
            ·
              refine ⟨52456368179971081031574679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279767296959845765501731621 52456368179971081031574679)
              ·
                refine ⟨78684552269956621547362019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52456368179971081031574679 78684552269956621547362019)
                ·
                  refine ⟨118026828404934932321043029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78684552269956621547362019 118026828404934932321043029)
                  ·
                    refine ⟨1383126895370331238137223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118026828404934932321043029 1383126895370331238137223)
                    ·
                      rfl

theorem cell23_8080890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_8080890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080890 prefixEnd_8080890 := by exact prefixLift 8080890
  have htrace : WordTrace (prefixWord ++ tailWord_8080890) baseStart_8080890 baseEnd_8080890 := by
    simpa [prefixWord, tailWord_8080890, baseEnd_8080890] using wordTrace_append hprefix tailTrace_8080890
  have hstable : (prefixWord ++ tailWord_8080890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080890).length < 2 ^ (prefixWord ++ tailWord_8080890).sum := by decide
  have hdescent : baseEnd_8080890 < baseStart_8080890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080917 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_8080917 : Nat := 118140960795 + 8080917 * 2 ^ 59
def prefixEnd_8080917 : Nat := 4983230072969 + 3 ^ 40 * 8080917 * 2
def baseEnd_8080917 : Nat := 4149394550088665108774045

theorem tailTrace_8080917 : CollatzResearch.WordTrace tailWord_8080917 prefixEnd_8080917 4149394550088665108774045 := by
  unfold tailWord_8080917
  simp only [CollatzResearch.WordTrace]
  refine ⟨294735256465225294592481005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196490170976816863061654003 294735256465225294592481005)
  ·
    refine ⟨110525721174459485472180377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294735256465225294592481005 110525721174459485472180377)
    ·
      refine ⟨82894290880844614104135283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110525721174459485472180377 82894290880844614104135283)
      ·
        refine ⟨124341436321266921156202925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82894290880844614104135283 124341436321266921156202925)
        ·
          refine ⟨46628038620475095433576097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124341436321266921156202925 46628038620475095433576097)
          ·
            refine ⟨34971028965356321575182073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46628038620475095433576097 34971028965356321575182073)
            ·
              refine ⟨26228271724017241181386555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34971028965356321575182073 26228271724017241181386555)
              ·
                refine ⟨39342407586025861772079833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26228271724017241181386555 39342407586025861772079833)
                ·
                  refine ⟨29506805689519396329059875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39342407586025861772079833 29506805689519396329059875)
                  ·
                    refine ⟨44260208534279094493589813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29506805689519396329059875 44260208534279094493589813)
                    ·
                      refine ⟨4149394550088665108774045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44260208534279094493589813 4149394550088665108774045)
                      ·
                        rfl

theorem cell23_8080917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_8080917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080917 prefixEnd_8080917 := by exact prefixLift 8080917
  have htrace : WordTrace (prefixWord ++ tailWord_8080917) baseStart_8080917 baseEnd_8080917 := by
    simpa [prefixWord, tailWord_8080917, baseEnd_8080917] using wordTrace_append hprefix tailTrace_8080917
  have hstable : (prefixWord ++ tailWord_8080917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080917).length < 2 ^ (prefixWord ++ tailWord_8080917).sum := by decide
  have hdescent : baseEnd_8080917 < baseStart_8080917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080940 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_8080940 : Nat := 118140960795 + 8080940 * 2 ^ 59
def prefixEnd_8080940 : Nat := 4983230072969 + 3 ^ 40 * 8080940 * 2
def baseEnd_8080940 : Nat := 4149406360143718518786439

theorem tailTrace_8080940 : CollatzResearch.WordTrace tailWord_8080940 prefixEnd_8080940 4149406360143718518786439 := by
  unfold tailWord_8080940
  simp only [CollatzResearch.WordTrace]
  refine ⟨147368047672070984760284137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196490730229427979680378849 147368047672070984760284137)
  ·
    refine ⟨110526035754053238570213103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147368047672070984760284137 110526035754053238570213103)
    ·
      refine ⟨165789053631079857855319655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110526035754053238570213103 165789053631079857855319655)
      ·
        refine ⟨248683580446619786782979483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165789053631079857855319655 248683580446619786782979483)
        ·
          refine ⟨373025370669929680174469225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248683580446619786782979483 373025370669929680174469225)
          ·
            refine ⟨279769028002447260130851919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373025370669929680174469225 279769028002447260130851919)
            ·
              refine ⟨419653542003670890196277879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279769028002447260130851919 419653542003670890196277879)
              ·
                refine ⟨629480313005506335294416819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419653542003670890196277879 629480313005506335294416819)
                ·
                  refine ⟨944220469508259502941625229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629480313005506335294416819 944220469508259502941625229)
                  ·
                    refine ⟨354082676065597313603109461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 944220469508259502941625229 354082676065597313603109461)
                    ·
                      refine ⟨4149406360143718518786439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 354082676065597313603109461 4149406360143718518786439)
                      ·
                        rfl

theorem cell23_8080940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_8080940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080940 prefixEnd_8080940 := by exact prefixLift 8080940
  have htrace : WordTrace (prefixWord ++ tailWord_8080940) baseStart_8080940 baseEnd_8080940 := by
    simpa [prefixWord, tailWord_8080940, baseEnd_8080940] using wordTrace_append hprefix tailTrace_8080940
  have hstable : (prefixWord ++ tailWord_8080940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080940).length < 2 ^ (prefixWord ++ tailWord_8080940).sum := by decide
  have hdescent : baseEnd_8080940 < baseStart_8080940 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080947 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 3]
def baseStart_8080947 : Nat := 118140960795 + 8080947 * 2 ^ 59
def prefixEnd_8080947 : Nat := 4983230072969 + 3 ^ 40 * 8080947 * 2
def baseEnd_8080947 : Nat := 4149409954508299991398907

theorem tailTrace_8080947 : CollatzResearch.WordTrace tailWord_8080947 prefixEnd_8080947 4149409954508299991398907 := by
  unfold tailWord_8080947
  simp only [CollatzResearch.WordTrace]
  refine ⟨294736350655116609716073095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196490900436744406477382063 294736350655116609716073095)
  ·
    refine ⟨442104525982674914574109643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294736350655116609716073095 442104525982674914574109643)
    ·
      refine ⟨663156788974012371861164465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442104525982674914574109643 663156788974012371861164465)
      ·
        refine ⟨497367591730509278895873349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 663156788974012371861164465 497367591730509278895873349)
        ·
          refine ⟨93256423449470489792976253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 497367591730509278895873349 93256423449470489792976253)
          ·
            refine ⟨34971158793551433672366095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93256423449470489792976253 34971158793551433672366095)
            ·
              refine ⟨52456738190327150508549143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34971158793551433672366095 52456738190327150508549143)
              ·
                refine ⟨78685107285490725762823715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52456738190327150508549143 78685107285490725762823715)
                ·
                  refine ⟨118027660928236088644235573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78685107285490725762823715 118027660928236088644235573)
                  ·
                    refine ⟨11065093212022133310397085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118027660928236088644235573 11065093212022133310397085)
                    ·
                      refine ⟨4149409954508299991398907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11065093212022133310397085 4149409954508299991398907)
                      ·
                        rfl

theorem cell23_8080947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 3].length) (baseStart_8080947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080947 prefixEnd_8080947 := by exact prefixLift 8080947
  have htrace : WordTrace (prefixWord ++ tailWord_8080947) baseStart_8080947 baseEnd_8080947 := by
    simpa [prefixWord, tailWord_8080947, baseEnd_8080947] using wordTrace_append hprefix tailTrace_8080947
  have hstable : (prefixWord ++ tailWord_8080947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080947).length < 2 ^ (prefixWord ++ tailWord_8080947).sum := by decide
  have hdescent : baseEnd_8080947 < baseStart_8080947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8080982 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_8080982 : Nat := 118140960795 + 8080982 * 2 ^ 59
def prefixEnd_8080982 : Nat := 4983230072969 + 3 ^ 40 * 8080982 * 2
def baseEnd_8080982 : Nat := 4149427926331207354461247

theorem tailTrace_8080982 : CollatzResearch.WordTrace tailWord_8080982 prefixEnd_8080982 4149427926331207354461247 := by
  unfold tailWord_8080982
  simp only [CollatzResearch.WordTrace]
  refine ⟨18421101700624363168349825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196491751473326540462398133 18421101700624363168349825)
  ·
    refine ⟨13815826275468272376262369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18421101700624363168349825 13815826275468272376262369)
    ·
      refine ⟨10361869706601204282196777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13815826275468272376262369 10361869706601204282196777)
      ·
        refine ⟨7771402279950903211647583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10361869706601204282196777 7771402279950903211647583)
        ·
          refine ⟨11657103419926354817471375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7771402279950903211647583 11657103419926354817471375)
          ·
            refine ⟨17485655129889532226207063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11657103419926354817471375 17485655129889532226207063)
            ·
              refine ⟨26228482694834298339310595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17485655129889532226207063 26228482694834298339310595)
              ·
                refine ⟨39342724042251447508965893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26228482694834298339310595 39342724042251447508965893)
                ·
                  refine ⟨7376760757922146407931105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39342724042251447508965893 7376760757922146407931105)
                  ·
                    refine ⟨5532570568441609805948329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7376760757922146407931105 5532570568441609805948329)
                    ·
                      refine ⟨4149427926331207354461247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532570568441609805948329 4149427926331207354461247)
                      ·
                        rfl

theorem cell23_8080982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_8080982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8080982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8080982 prefixEnd_8080982 := by exact prefixLift 8080982
  have htrace : WordTrace (prefixWord ++ tailWord_8080982) baseStart_8080982 baseEnd_8080982 := by
    simpa [prefixWord, tailWord_8080982, baseEnd_8080982] using wordTrace_append hprefix tailTrace_8080982
  have hstable : (prefixWord ++ tailWord_8080982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8080982).length < 2 ^ (prefixWord ++ tailWord_8080982).sum := by decide
  have hdescent : baseEnd_8080982 < baseStart_8080982 := by decide
  rcases family_descends (prefixWord ++ tailWord_8080982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081017 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 2, 4, 4]
def baseStart_8081017 : Nat := 118140960795 + 8081017 * 2 ^ 59
def prefixEnd_8081017 : Nat := 4983230072969 + 3 ^ 40 * 8081017 * 2
def baseEnd_8081017 : Nat := 4149445898154114717523585

theorem tailTrace_8081017 : CollatzResearch.WordTrace tailWord_8081017 prefixEnd_8081017 4149445898154114717523585 := by
  unfold tailWord_8081017
  simp only [CollatzResearch.WordTrace]
  refine ⟨294738903764863011671121305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196492602509908674447414203 294738903764863011671121305)
  ·
    refine ⟨221054177823647258753340979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294738903764863011671121305 221054177823647258753340979)
    ·
      refine ⟨331581266735470888130011469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221054177823647258753340979 331581266735470888130011469)
      ·
        refine ⟨124342975025801583048754301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331581266735470888130011469 124342975025801583048754301)
        ·
          refine ⟨46628615634675593643282863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124342975025801583048754301 46628615634675593643282863)
          ·
            refine ⟨69942923452013390464924295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46628615634675593643282863 69942923452013390464924295)
            ·
              refine ⟨104914385178020085697386443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69942923452013390464924295 104914385178020085697386443)
              ·
                refine ⟨157371577767030128546079665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104914385178020085697386443 157371577767030128546079665)
                ·
                  refine ⟨118028683325272596409559749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157371577767030128546079665 118028683325272596409559749)
                  ·
                    refine ⟨22130378123488611826792453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118028683325272596409559749 22130378123488611826792453)
                    ·
                      refine ⟨4149445898154114717523585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22130378123488611826792453 4149445898154114717523585)
                      ·
                        rfl

theorem cell23_8081017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_8081017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081017 prefixEnd_8081017 := by exact prefixLift 8081017
  have htrace : WordTrace (prefixWord ++ tailWord_8081017) baseStart_8081017 baseEnd_8081017 := by
    simpa [prefixWord, tailWord_8081017, baseEnd_8081017] using wordTrace_append hprefix tailTrace_8081017
  have hstable : (prefixWord ++ tailWord_8081017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081017).length < 2 ^ (prefixWord ++ tailWord_8081017).sum := by decide
  have hdescent : baseEnd_8081017 < baseStart_8081017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081024 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 3]
def baseStart_8081024 : Nat := 118140960795 + 8081024 * 2 ^ 59
def prefixEnd_8081024 : Nat := 4983230072969 + 3 ^ 40 * 8081024 * 2
def baseEnd_8081024 : Nat := 4149449492518696190136053

theorem tailTrace_8081024 : CollatzResearch.WordTrace tailWord_8081024 prefixEnd_8081024 4149449492518696190136053 := by
  unfold tailWord_8081024
  simp only [CollatzResearch.WordTrace]
  refine ⟨147369579537918825933313063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196492772717225101244417417 147369579537918825933313063)
  ·
    refine ⟨221054369306878238899969595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147369579537918825933313063 221054369306878238899969595)
    ·
      refine ⟨331581553960317358349954393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221054369306878238899969595 331581553960317358349954393)
      ·
        refine ⟨248686165470238018762465795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331581553960317358349954393 248686165470238018762465795)
        ·
          refine ⟨373029248205357028143698693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248686165470238018762465795 373029248205357028143698693)
          ·
            refine ⟨69942984038504442776943505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373029248205357028143698693 69942984038504442776943505)
            ·
              refine ⟨52457238028878332082707629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69942984038504442776943505 52457238028878332082707629)
              ·
                refine ⟨19671464260829374531015361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52457238028878332082707629 19671464260829374531015361)
                ·
                  refine ⟨14753598195622030898261521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19671464260829374531015361 14753598195622030898261521)
                  ·
                    refine ⟨11065198646716523173696141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14753598195622030898261521 11065198646716523173696141)
                    ·
                      refine ⟨4149449492518696190136053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11065198646716523173696141 4149449492518696190136053)
                      ·
                        rfl

theorem cell23_8081024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_8081024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081024 prefixEnd_8081024 := by exact prefixLift 8081024
  have htrace : WordTrace (prefixWord ++ tailWord_8081024) baseStart_8081024 baseEnd_8081024 := by
    simpa [prefixWord, tailWord_8081024, baseEnd_8081024] using wordTrace_append hprefix tailTrace_8081024
  have hstable : (prefixWord ++ tailWord_8081024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081024).length < 2 ^ (prefixWord ++ tailWord_8081024).sum := by decide
  have hdescent : baseEnd_8081024 < baseStart_8081024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081081 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 2, 3, 2]
def baseStart_8081081 : Nat := 118140960795 + 8081081 * 2 ^ 59
def prefixEnd_8081081 : Nat := 4983230072969 + 3 ^ 40 * 8081081 * 2
def baseEnd_8081081 : Nat := 4149478760916002467123291

theorem tailTrace_8081081 : CollatzResearch.WordTrace tailWord_8081081 prefixEnd_8081081 4149478760916002467123291 := by
  unfold tailWord_8081081
  simp only [CollatzResearch.WordTrace]
  refine ⟨294741238036631150601451097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196494158691087433734300731 294741238036631150601451097)
  ·
    refine ⟨221055928527473362951088323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294741238036631150601451097 221055928527473362951088323)
    ·
      refine ⟨331583892791210044426632485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221055928527473362951088323 331583892791210044426632485)
      ·
        refine ⟨62171979898351883329993591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331583892791210044426632485 62171979898351883329993591)
        ·
          refine ⟨93257969847527824994990387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62171979898351883329993591 93257969847527824994990387)
          ·
            refine ⟨139886954771291737492485581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93257969847527824994990387 139886954771291737492485581)
            ·
              refine ⟨52457608039234401559682093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139886954771291737492485581 52457608039234401559682093)
              ·
                refine ⟨19671603014712900584880785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52457608039234401559682093 19671603014712900584880785)
                ·
                  refine ⟨14753702261034675438660589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19671603014712900584880785 14753702261034675438660589)
                  ·
                    refine ⟨5532638347888003289497721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14753702261034675438660589 5532638347888003289497721)
                    ·
                      refine ⟨4149478760916002467123291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532638347888003289497721 4149478760916002467123291)
                      ·
                        rfl

theorem cell23_8081081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_8081081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081081 prefixEnd_8081081 := by exact prefixLift 8081081
  have htrace : WordTrace (prefixWord ++ tailWord_8081081) baseStart_8081081 baseEnd_8081081 := by
    simpa [prefixWord, tailWord_8081081, baseEnd_8081081] using wordTrace_append hprefix tailTrace_8081081
  have hstable : (prefixWord ++ tailWord_8081081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081081).length < 2 ^ (prefixWord ++ tailWord_8081081).sum := by decide
  have hdescent : baseEnd_8081081 < baseStart_8081081 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081088 : List Nat := [2, 1, 1, 2, 4, 1, 2, 5, 1, 1, 3]
def baseStart_8081088 : Nat := 118140960795 + 8081088 * 2 ^ 59
def prefixEnd_8081088 : Nat := 4983230072969 + 3 ^ 40 * 8081088 * 2
def baseEnd_8081088 : Nat := 4149482355280583939735759

theorem tailTrace_8081088 : CollatzResearch.WordTrace tailWord_8081088 prefixEnd_8081088 4149482355280583939735759 := by
  unfold tailWord_8081088
  simp only [CollatzResearch.WordTrace]
  refine ⟨147370746673802895398477959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196494328898403860531303945 147370746673802895398477959)
  ·
    refine ⟨221056120010704343097716939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147370746673802895398477959 221056120010704343097716939)
    ·
      refine ⟨331584180016056514646575409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221056120010704343097716939 331584180016056514646575409)
      ·
        refine ⟨248688135012042385984931557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331584180016056514646575409 248688135012042385984931557)
        ·
          refine ⟨46629025314757947372174667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248688135012042385984931557 46629025314757947372174667)
          ·
            refine ⟨69943537972136921058262001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46629025314757947372174667 69943537972136921058262001)
            ·
              refine ⟨52457653479102690793696501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69943537972136921058262001 52457653479102690793696501)
              ·
                refine ⟨4917905013665877261909047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52457653479102690793696501 4917905013665877261909047)
                ·
                  refine ⟨7376857520498815892863571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4917905013665877261909047 7376857520498815892863571)
                  ·
                    refine ⟨11065286280748223839295357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7376857520498815892863571 11065286280748223839295357)
                    ·
                      refine ⟨4149482355280583939735759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11065286280748223839295357 4149482355280583939735759)
                      ·
                        rfl

theorem cell23_8081088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 1, 1, 3].length) (baseStart_8081088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081088 prefixEnd_8081088 := by exact prefixLift 8081088
  have htrace : WordTrace (prefixWord ++ tailWord_8081088) baseStart_8081088 baseEnd_8081088 := by
    simpa [prefixWord, tailWord_8081088, baseEnd_8081088] using wordTrace_append hprefix tailTrace_8081088
  have hstable : (prefixWord ++ tailWord_8081088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081088).length < 2 ^ (prefixWord ++ tailWord_8081088).sum := by decide
  have hdescent : baseEnd_8081088 < baseStart_8081088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081105 : List Nat := [1, 2, 2, 1, 2, 4, 4, 2, 1, 1, 3]
def baseStart_8081105 : Nat := 118140960795 + 8081105 * 2 ^ 59
def prefixEnd_8081105 : Nat := 4983230072969 + 3 ^ 40 * 8081105 * 2
def baseEnd_8081105 : Nat := 4149491084451710373223181

theorem tailTrace_8081105 : CollatzResearch.WordTrace tailWord_8081105 prefixEnd_8081105 4149491084451710373223181 := by
  unfold tailWord_8081105
  simp only [CollatzResearch.WordTrace]
  refine ⟨294742113388544202700324769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196494742259029468466883179 294742113388544202700324769)
  ·
    refine ⟨221056585041408152025243577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294742113388544202700324769 221056585041408152025243577)
    ·
      refine ⟨165792438781056114018932683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221056585041408152025243577 165792438781056114018932683)
      ·
        refine ⟨248688658171584171028399025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165792438781056114018932683 248688658171584171028399025)
        ·
          refine ⟨186516493628688128271299269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248688658171584171028399025 186516493628688128271299269)
          ·
            refine ⟨34971842555379024050868613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186516493628688128271299269 34971842555379024050868613)
            ·
              refine ⟨6557220479133567009537865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34971842555379024050868613 6557220479133567009537865)
              ·
                refine ⟨4917915359350175257153399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6557220479133567009537865 4917915359350175257153399)
                ·
                  refine ⟨7376873039025262885730099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4917915359350175257153399 7376873039025262885730099)
                  ·
                    refine ⟨11065309558537894328595149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7376873039025262885730099 11065309558537894328595149)
                    ·
                      refine ⟨4149491084451710373223181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11065309558537894328595149 4149491084451710373223181)
                      ·
                        rfl

theorem cell23_8081105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 1, 1, 3].length) (baseStart_8081105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081105 prefixEnd_8081105 := by exact prefixLift 8081105
  have htrace : WordTrace (prefixWord ++ tailWord_8081105) baseStart_8081105 baseEnd_8081105 := by
    simpa [prefixWord, tailWord_8081105, baseEnd_8081105] using wordTrace_append hprefix tailTrace_8081105
  have hstable : (prefixWord ++ tailWord_8081105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081105).length < 2 ^ (prefixWord ++ tailWord_8081105).sum := by decide
  have hdescent : baseEnd_8081105 < baseStart_8081105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081121 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 1, 6]
def baseStart_8081121 : Nat := 118140960795 + 8081121 * 2 ^ 59
def prefixEnd_8081121 : Nat := 4983230072969 + 3 ^ 40 * 8081121 * 2
def baseEnd_8081121 : Nat := 1383166433380727436874369

theorem tailTrace_8081121 : CollatzResearch.WordTrace tailWord_8081121 prefixEnd_8081121 1383166433380727436874369 := by
  unfold tailWord_8081121
  simp only [CollatzResearch.WordTrace]
  refine ⟨294742696956486237432907217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196495131304324158288604811 294742696956486237432907217)
  ·
    refine ⟨221057022717364678074680413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294742696956486237432907217 221057022717364678074680413)
    ·
      refine ⟨82896383519011754278005155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221057022717364678074680413 82896383519011754278005155)
      ·
        refine ⟨124344575278517631417007733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82896383519011754278005155 124344575278517631417007733)
        ·
          refine ⟨11657303932361027945344475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124344575278517631417007733 11657303932361027945344475)
          ·
            refine ⟨17485955898541541918016713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11657303932361027945344475 17485955898541541918016713)
            ·
              refine ⟨13114466923906156438512535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17485955898541541918016713 13114466923906156438512535)
              ·
                refine ⟨19671700385859234657768803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13114466923906156438512535 19671700385859234657768803)
                ·
                  refine ⟨29507550578788851986653205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19671700385859234657768803 29507550578788851986653205)
                  ·
                    refine ⟨1383166433380727436874369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29507550578788851986653205 1383166433380727436874369)
                    ·
                      rfl

theorem cell23_8081121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_8081121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081121 prefixEnd_8081121 := by exact prefixLift 8081121
  have htrace : WordTrace (prefixWord ++ tailWord_8081121) baseStart_8081121 baseEnd_8081121 := by
    simpa [prefixWord, tailWord_8081121, baseEnd_8081121] using wordTrace_append hprefix tailTrace_8081121
  have hstable : (prefixWord ++ tailWord_8081121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081121).length < 2 ^ (prefixWord ++ tailWord_8081121).sum := by decide
  have hdescent : baseEnd_8081121 < baseStart_8081121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081128 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_8081128 : Nat := 118140960795 + 8081128 * 2 ^ 59
def prefixEnd_8081128 : Nat := 4983230072969 + 3 ^ 40 * 8081128 * 2
def baseEnd_8081128 : Nat := 4149502894506763783235575

theorem tailTrace_8081128 : CollatzResearch.WordTrace tailWord_8081128 prefixEnd_8081128 4149502894506763783235575 := by
  unfold tailWord_8081128
  simp only [CollatzResearch.WordTrace]
  refine ⟨147371476133730438814206019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196495301511640585085608025 147371476133730438814206019)
  ·
    refine ⟨221057214200595658221309029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147371476133730438814206019 221057214200595658221309029)
    ·
      refine ⟨41448227662611685916495443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221057214200595658221309029 41448227662611685916495443)
      ·
        refine ⟨62172341493917528874743165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41448227662611685916495443 62172341493917528874743165)
        ·
          refine ⟨23314628060219073328028687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62172341493917528874743165 23314628060219073328028687)
          ·
            refine ⟨34971942090328609992043031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23314628060219073328028687 34971942090328609992043031)
            ·
              refine ⟨52457913135492914988064547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34971942090328609992043031 52457913135492914988064547)
              ·
                refine ⟨78686869703239372482096821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52457913135492914988064547 78686869703239372482096821)
                ·
                  refine ⟨7376894034678691170196577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78686869703239372482096821 7376894034678691170196577)
                  ·
                    refine ⟨5532670526009018377647433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7376894034678691170196577 5532670526009018377647433)
                    ·
                      refine ⟨4149502894506763783235575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532670526009018377647433 4149502894506763783235575)
                      ·
                        rfl

theorem cell23_8081128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_8081128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081128 prefixEnd_8081128 := by exact prefixLift 8081128
  have htrace : WordTrace (prefixWord ++ tailWord_8081128) baseStart_8081128 baseEnd_8081128 := by
    simpa [prefixWord, tailWord_8081128, baseEnd_8081128] using wordTrace_append hprefix tailTrace_8081128
  have hstable : (prefixWord ++ tailWord_8081128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081128).length < 2 ^ (prefixWord ++ tailWord_8081128).sum := by decide
  have hdescent : baseEnd_8081128 < baseStart_8081128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081144 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 3, 3, 3]
def baseStart_8081144 : Nat := 118140960795 + 8081144 * 2 ^ 59
def prefixEnd_8081144 : Nat := 4983230072969 + 3 ^ 40 * 8081144 * 2
def baseEnd_8081144 : Nat := 4149511110197235720635501

theorem tailTrace_8081144 : CollatzResearch.WordTrace tailWord_8081144 prefixEnd_8081144 4149511110197235720635501 := by
  unfold tailWord_8081144
  simp only [CollatzResearch.WordTrace]
  refine ⟨147371767917701456180497243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196495690556935274907329657 147371767917701456180497243)
  ·
    refine ⟨221057651876552184270745865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147371767917701456180497243 221057651876552184270745865)
    ·
      refine ⟨165793238907414138203059399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221057651876552184270745865 165793238907414138203059399)
      ·
        refine ⟨248689858361121207304589099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165793238907414138203059399 248689858361121207304589099)
        ·
          refine ⟨373034787541681810956883649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248689858361121207304589099 373034787541681810956883649)
          ·
            refine ⟨279776090656261358217662737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373034787541681810956883649 279776090656261358217662737)
            ·
              refine ⟨209832067992196018663247053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279776090656261358217662737 209832067992196018663247053)
              ·
                refine ⟨78687025497073506998717645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209832067992196018663247053 78687025497073506998717645)
                ·
                  refine ⟨29507634561402565124519117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78687025497073506998717645 29507634561402565124519117)
                  ·
                    refine ⟨11065362960525961921694669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29507634561402565124519117 11065362960525961921694669)
                    ·
                      refine ⟨4149511110197235720635501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11065362960525961921694669 4149511110197235720635501)
                      ·
                        rfl

theorem cell23_8081144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_8081144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081144 prefixEnd_8081144 := by exact prefixLift 8081144
  have htrace : WordTrace (prefixWord ++ tailWord_8081144) baseStart_8081144 baseEnd_8081144 := by
    simpa [prefixWord, tailWord_8081144, baseEnd_8081144] using wordTrace_append hprefix tailTrace_8081144
  have hstable : (prefixWord ++ tailWord_8081144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081144).length < 2 ^ (prefixWord ++ tailWord_8081144).sum := by decide
  have hdescent : baseEnd_8081144 < baseStart_8081144 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081147 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 1, 9]
def baseStart_8081147 : Nat := 118140960795 + 8081147 * 2 ^ 59
def prefixEnd_8081147 : Nat := 4983230072969 + 3 ^ 40 * 8081147 * 2
def baseEnd_8081147 : Nat := 1383170883546399736299329

theorem tailTrace_8081147 : CollatzResearch.WordTrace tailWord_8081147 prefixEnd_8081147 1383170883546399736299329 := by
  unfold tailWord_8081147
  simp only [CollatzResearch.WordTrace]
  refine ⟨294743645254392043873353695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196495763502928029248902463 294743645254392043873353695)
  ·
    refine ⟨442115467881588065810030543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294743645254392043873353695 442115467881588065810030543)
    ·
      refine ⟨663173201822382098715045815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442115467881588065810030543 663173201822382098715045815)
      ·
        refine ⟨994759802733573148072568723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663173201822382098715045815 994759802733573148072568723)
        ·
          refine ⟨1492139704100359722108853085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994759802733573148072568723 1492139704100359722108853085)
          ·
            refine ⟨559552389037634895790819907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1492139704100359722108853085 559552389037634895790819907)
            ·
              refine ⟨839328583556452343686229861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559552389037634895790819907 839328583556452343686229861)
              ·
                refine ⟨157374109416834814441168099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 839328583556452343686229861 157374109416834814441168099)
                ·
                  refine ⟨236061164125252221661752149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157374109416834814441168099 236061164125252221661752149)
                  ·
                    refine ⟨1383170883546399736299329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 236061164125252221661752149 1383170883546399736299329)
                    ·
                      rfl

theorem cell23_8081147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 9].length) (baseStart_8081147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081147 prefixEnd_8081147 := by exact prefixLift 8081147
  have htrace : WordTrace (prefixWord ++ tailWord_8081147) baseStart_8081147 baseEnd_8081147 := by
    simpa [prefixWord, tailWord_8081147, baseEnd_8081147] using wordTrace_append hprefix tailTrace_8081147
  have hstable : (prefixWord ++ tailWord_8081147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081147).length < 2 ^ (prefixWord ++ tailWord_8081147).sum := by decide
  have hdescent : baseEnd_8081147 < baseStart_8081147 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081171 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 3, 3, 2]
def baseStart_8081171 : Nat := 118140960795 + 8081171 * 2 ^ 59
def prefixEnd_8081171 : Nat := 4983230072969 + 3 ^ 40 * 8081171 * 2
def baseEnd_8081171 : Nat := 4149524974174907114997877

theorem tailTrace_8081171 : CollatzResearch.WordTrace tailWord_8081171 prefixEnd_8081171 4149524974174907114997877 := by
  unfold tailWord_8081171
  simp only [CollatzResearch.WordTrace]
  refine ⟨294744520606305095972227367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196496347070870063981484911 294744520606305095972227367)
  ·
    refine ⟨442116780909457643958341051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294744520606305095972227367 442116780909457643958341051)
    ·
      refine ⟨663175171364186465937511577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442116780909457643958341051 663175171364186465937511577)
      ·
        refine ⟨497381378523139849453133683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 663175171364186465937511577 497381378523139849453133683)
        ·
          refine ⟨746072067784709774179700525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497381378523139849453133683 746072067784709774179700525)
          ·
            refine ⟨279777025419266165317387697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 746072067784709774179700525 279777025419266165317387697)
            ·
              refine ⟨209832769064449623988040773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279777025419266165317387697 209832769064449623988040773)
              ·
                refine ⟨39343644199584304497757645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209832769064449623988040773 39343644199584304497757645)
                ·
                  refine ⟨14753866574844114186659117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39343644199584304497757645 14753866574844114186659117)
                  ·
                    refine ⟨5532699965566542819997169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14753866574844114186659117 5532699965566542819997169)
                    ·
                      refine ⟨4149524974174907114997877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532699965566542819997169 4149524974174907114997877)
                      ·
                        rfl

theorem cell23_8081171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 3, 2].length) (baseStart_8081171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081171 prefixEnd_8081171 := by exact prefixLift 8081171
  have htrace : WordTrace (prefixWord ++ tailWord_8081171) baseStart_8081171 baseEnd_8081171 := by
    simpa [prefixWord, tailWord_8081171, baseEnd_8081171] using wordTrace_append hprefix tailTrace_8081171
  have hstable : (prefixWord ++ tailWord_8081171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081171).length < 2 ^ (prefixWord ++ tailWord_8081171).sum := by decide
  have hdescent : baseEnd_8081171 < baseStart_8081171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081172 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_8081172 : Nat := 118140960795 + 8081172 * 2 ^ 59
def prefixEnd_8081172 : Nat := 4983230072969 + 3 ^ 40 * 8081172 * 2
def baseEnd_8081172 : Nat := 1383175162551853870361791

theorem tailTrace_8081172 : CollatzResearch.WordTrace tailWord_8081172 prefixEnd_8081172 1383175162551853870361791 := by
  unfold tailWord_8081172
  simp only [CollatzResearch.WordTrace]
  refine ⟨147372278539650736571506885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196496371386200982095342513 147372278539650736571506885)
  ·
    refine ⟨27632302226184513107157541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147372278539650736571506885 27632302226184513107157541)
    ·
      refine ⟨5181056667409596207592039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27632302226184513107157541 5181056667409596207592039)
      ·
        refine ⟨7771585001114394311388059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5181056667409596207592039 7771585001114394311388059)
        ·
          refine ⟨11657377501671591467082089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7771585001114394311388059 11657377501671591467082089)
          ·
            refine ⟨8743033126253693600311567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11657377501671591467082089 8743033126253693600311567)
            ·
              refine ⟨13114549689380540400467351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8743033126253693600311567 13114549689380540400467351)
              ·
                refine ⟨19671824534070810600701027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13114549689380540400467351 19671824534070810600701027)
                ·
                  refine ⟨29507736801106215901051541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19671824534070810600701027 29507736801106215901051541)
                  ·
                    refine ⟨1383175162551853870361791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29507736801106215901051541 1383175162551853870361791)
                    ·
                      rfl

theorem cell23_8081172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_8081172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081172 prefixEnd_8081172 := by exact prefixLift 8081172
  have htrace : WordTrace (prefixWord ++ tailWord_8081172) baseStart_8081172 baseEnd_8081172 := by
    simpa [prefixWord, tailWord_8081172, baseEnd_8081172] using wordTrace_append hprefix tailTrace_8081172
  have hstable : (prefixWord ++ tailWord_8081172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081172).length < 2 ^ (prefixWord ++ tailWord_8081172).sum := by decide
  have hdescent : baseEnd_8081172 < baseStart_8081172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081178 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3]
def baseStart_8081178 : Nat := 118140960795 + 8081178 * 2 ^ 59
def prefixEnd_8081178 : Nat := 4983230072969 + 3 ^ 40 * 8081178 * 2
def baseEnd_8081178 : Nat := 4149528568539488587610345

theorem tailTrace_8081178 : CollatzResearch.WordTrace tailWord_8081178 prefixEnd_8081178 4149528568539488587610345 := by
  unfold tailWord_8081178
  simp only [CollatzResearch.WordTrace]
  refine ⟨73686193979319934041933047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196496517278186490778488125 73686193979319934041933047)
  ·
    refine ⟨110529290968979901062899571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73686193979319934041933047 110529290968979901062899571)
    ·
      refine ⟨165793936453469851594349357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110529290968979901062899571 165793936453469851594349357)
      ·
        refine ⟨62172726170051194347881009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165793936453469851594349357 62172726170051194347881009)
        ·
          refine ⟨46629544627538395760910757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62172726170051194347881009 46629544627538395760910757)
          ·
            refine ⟨8743039617663449205170767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46629544627538395760910757 8743039617663449205170767)
            ·
              refine ⟨13114559426495173807756151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8743039617663449205170767 13114559426495173807756151)
              ·
                refine ⟨19671839139742760711634227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13114559426495173807756151 19671839139742760711634227)
                ·
                  refine ⟨29507758709614141067451341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19671839139742760711634227 29507758709614141067451341)
                  ·
                    refine ⟨11065409516105302900294253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29507758709614141067451341 11065409516105302900294253)
                    ·
                      refine ⟨4149528568539488587610345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11065409516105302900294253 4149528568539488587610345)
                      ·
                        rfl

theorem cell23_8081178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_8081178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081178 prefixEnd_8081178 := by exact prefixLift 8081178
  have htrace : WordTrace (prefixWord ++ tailWord_8081178) baseStart_8081178 baseEnd_8081178 := by
    simpa [prefixWord, tailWord_8081178, baseEnd_8081178] using wordTrace_append hprefix tailTrace_8081178
  have hstable : (prefixWord ++ tailWord_8081178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081178).length < 2 ^ (prefixWord ++ tailWord_8081178).sum := by decide
  have hdescent : baseEnd_8081178 < baseStart_8081178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081229 : List Nat := [1, 6, 1, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_8081229 : Nat := 118140960795 + 8081229 * 2 ^ 59
def prefixEnd_8081229 : Nat := 4983230072969 + 3 ^ 40 * 8081229 * 2
def baseEnd_8081229 : Nat := 4149554756052867888072611

theorem tailTrace_8081229 : CollatzResearch.WordTrace tailWord_8081229 prefixEnd_8081229 4149554756052867888072611 := by
  unfold tailWord_8081229
  simp only [CollatzResearch.WordTrace]
  refine ⟨294746636040094971877838741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196497757360063314585225827 294746636040094971877838741)
  ·
    refine ⟨13816248564379451806773691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 294746636040094971877838741 13816248564379451806773691)
    ·
      refine ⟨20724372846569177710160537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13816248564379451806773691 20724372846569177710160537)
      ·
        refine ⟨15543279634926883282620403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20724372846569177710160537 15543279634926883282620403)
        ·
          refine ⟨23314919452390324923930605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15543279634926883282620403 23314919452390324923930605)
          ·
            refine ⟨8743094794646371846473977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23314919452390324923930605 8743094794646371846473977)
            ·
              refine ⟨6557321095984778884855483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8743094794646371846473977 6557321095984778884855483)
              ·
                refine ⟨9835981643977168327283225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6557321095984778884855483 9835981643977168327283225)
                ·
                  refine ⟨7376986232982876245462419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9835981643977168327283225 7376986232982876245462419)
                  ·
                    refine ⟨11065479349474314368193629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7376986232982876245462419 11065479349474314368193629)
                    ·
                      refine ⟨4149554756052867888072611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11065479349474314368193629 4149554756052867888072611)
                      ·
                        rfl

theorem cell23_8081229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_8081229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081229 prefixEnd_8081229 := by exact prefixLift 8081229
  have htrace : WordTrace (prefixWord ++ tailWord_8081229) baseStart_8081229 baseEnd_8081229 := by
    simpa [prefixWord, tailWord_8081229, baseEnd_8081229] using wordTrace_append hprefix tailTrace_8081229
  have hstable : (prefixWord ++ tailWord_8081229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081229).length < 2 ^ (prefixWord ++ tailWord_8081229).sum := by decide
  have hdescent : baseEnd_8081229 < baseStart_8081229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081308 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_8081308 : Nat := 118140960795 + 8081308 * 2 ^ 59
def prefixEnd_8081308 : Nat := 4983230072969 + 3 ^ 40 * 8081308 * 2
def baseEnd_8081308 : Nat := 4149595321024573078984747

theorem tailTrace_8081308 : CollatzResearch.WordTrace tailWord_8081308 prefixEnd_8081308 4149595321024573078984747 := by
  unfold tailWord_8081308
  simp only [CollatzResearch.WordTrace]
  refine ⟨147374758703404384184982289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196499678271205845579976385 147374758703404384184982289)
  ·
    refine ⟨110531069027553288138736717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147374758703404384184982289 110531069027553288138736717)
    ·
      refine ⟨41449150885332483052026269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110531069027553288138736717 41449150885332483052026269)
      ·
        refine ⟨15543431581999681144509851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41449150885332483052026269 15543431581999681144509851)
        ·
          refine ⟨23315147372999521716764777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15543431581999681144509851 23315147372999521716764777)
          ·
            refine ⟨17486360529749641287573583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23315147372999521716764777 17486360529749641287573583)
            ·
              refine ⟨26229540794624461931360375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17486360529749641287573583 26229540794624461931360375)
              ·
                refine ⟨39344311191936692897040563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26229540794624461931360375 39344311191936692897040563)
                ·
                  refine ⟨59016466787905039345560845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39344311191936692897040563 59016466787905039345560845)
                  ·
                    refine ⟨22131175045464389754585317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59016466787905039345560845 22131175045464389754585317)
                    ·
                      refine ⟨4149595321024573078984747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22131175045464389754585317 4149595321024573078984747)
                      ·
                        rfl

theorem cell23_8081308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_8081308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081308 prefixEnd_8081308 := by exact prefixLift 8081308
  have htrace : WordTrace (prefixWord ++ tailWord_8081308) baseStart_8081308 baseEnd_8081308 := by
    simpa [prefixWord, tailWord_8081308, baseEnd_8081308] using wordTrace_append hprefix tailTrace_8081308
  have hstable : (prefixWord ++ tailWord_8081308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081308).length < 2 ^ (prefixWord ++ tailWord_8081308).sum := by decide
  have hdescent : baseEnd_8081308 < baseStart_8081308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081368 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 1, 5, 2]
def baseStart_8081368 : Nat := 118140960795 + 8081368 * 2 ^ 59
def prefixEnd_8081368 : Nat := 4983230072969 + 3 ^ 40 * 8081368 * 2
def baseEnd_8081368 : Nat := 4149626129863842844234471

theorem tailTrace_8081368 : CollatzResearch.WordTrace tailWord_8081368 prefixEnd_8081368 4149626129863842844234471 := by
  unfold tailWord_8081368
  simp only [CollatzResearch.WordTrace]
  refine ⟨147375852893295699308574379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196501137191060932411432505 147375852893295699308574379)
  ·
    refine ⟨221063779339943548962861569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147375852893295699308574379 221063779339943548962861569)
    ·
      refine ⟨165797834504957661722146177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221063779339943548962861569 165797834504957661722146177)
      ·
        refine ⟨124348375878718246291609633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165797834504957661722146177 124348375878718246291609633)
        ·
          refine ⟨93261281909038684718707225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124348375878718246291609633 93261281909038684718707225)
          ·
            refine ⟨69945961431779013539030419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93261281909038684718707225 69945961431779013539030419)
            ·
              refine ⟨104918942147668520308545629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69945961431779013539030419 104918942147668520308545629)
              ·
                refine ⟨39344603305375695115704611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104918942147668520308545629 39344603305375695115704611)
                ·
                  refine ⟨59016904958063542673556917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39344603305375695115704611 59016904958063542673556917)
                  ·
                    refine ⟨5532834839818457125645961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59016904958063542673556917 5532834839818457125645961)
                    ·
                      refine ⟨4149626129863842844234471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532834839818457125645961 4149626129863842844234471)
                      ·
                        rfl

theorem cell23_8081368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_8081368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081368 prefixEnd_8081368 := by exact prefixLift 8081368
  have htrace : WordTrace (prefixWord ++ tailWord_8081368) baseStart_8081368 baseEnd_8081368 := by
    simpa [prefixWord, tailWord_8081368, baseEnd_8081368] using wordTrace_append hprefix tailTrace_8081368
  have hstable : (prefixWord ++ tailWord_8081368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081368).length < 2 ^ (prefixWord ++ tailWord_8081368).sum := by decide
  have hdescent : baseEnd_8081368 < baseStart_8081368 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081369 : List Nat := [1, 2, 1, 2, 7, 1, 1, 3, 1, 4]
def baseStart_8081369 : Nat := 118140960795 + 8081369 * 2 ^ 59
def prefixEnd_8081369 : Nat := 4983230072969 + 3 ^ 40 * 8081369 * 2
def baseEnd_8081369 : Nat := 1383208881114832446773989

theorem tailTrace_8081369 : CollatzResearch.WordTrace tailWord_8081369 prefixEnd_8081369 1383208881114832446773989 := by
  unfold tailWord_8081369
  simp only [CollatzResearch.WordTrace]
  refine ⟨294751742259587775787935161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196501161506391850525290107 294751742259587775787935161)
  ·
    refine ⟨221063806694690831840951371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294751742259587775787935161 221063806694690831840951371)
    ·
      refine ⟨331595710042036247761427057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221063806694690831840951371 331595710042036247761427057)
      ·
        refine ⟨248696782531527185821070293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331595710042036247761427057 248696782531527185821070293)
        ·
          refine ⟨5828830840582668417681335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 248696782531527185821070293 5828830840582668417681335)
          ·
            refine ⟨8743246260874002626522003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5828830840582668417681335 8743246260874002626522003)
            ·
              refine ⟨13114869391311003939783005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8743246260874002626522003 13114869391311003939783005)
              ·
                refine ⟨4918076021741626477418627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13114869391311003939783005 4918076021741626477418627)
                ·
                  refine ⟨7377114032612439716127941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918076021741626477418627 7377114032612439716127941)
                  ·
                    refine ⟨1383208881114832446773989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7377114032612439716127941 1383208881114832446773989)
                    ·
                      rfl

theorem cell23_8081369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 1, 4].length) (baseStart_8081369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081369 prefixEnd_8081369 := by exact prefixLift 8081369
  have htrace : WordTrace (prefixWord ++ tailWord_8081369) baseStart_8081369 baseEnd_8081369 := by
    simpa [prefixWord, tailWord_8081369, baseEnd_8081369] using wordTrace_append hprefix tailTrace_8081369
  have hstable : (prefixWord ++ tailWord_8081369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081369).length < 2 ^ (prefixWord ++ tailWord_8081369).sum := by decide
  have hdescent : baseEnd_8081369 < baseStart_8081369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081411 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 4]
def baseStart_8081411 : Nat := 118140960795 + 8081411 * 2 ^ 59
def prefixEnd_8081411 : Nat := 4983230072969 + 3 ^ 40 * 8081411 * 2
def baseEnd_8081411 : Nat := 4149648209531986175996773

theorem tailTrace_8081411 : CollatzResearch.WordTrace tailWord_8081411 prefixEnd_8081411 4149648209531986175996773 := by
  unfold tailWord_8081411
  simp only [CollatzResearch.WordTrace]
  refine ⟨294753274125435616960964087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196502182750290411307309391 294753274125435616960964087)
  ·
    refine ⟨442129911188153425441446131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294753274125435616960964087 442129911188153425441446131)
    ·
      refine ⟨663194866782230138162169197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442129911188153425441446131 663194866782230138162169197)
      ·
        refine ⟨248698075043336301810813449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 663194866782230138162169197 248698075043336301810813449)
        ·
          refine ⟨186523556282502226358110087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248698075043336301810813449 186523556282502226358110087)
          ·
            refine ⟨279785334423753339537165131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186523556282502226358110087 279785334423753339537165131)
            ·
              refine ⟨419678001635630009305747697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279785334423753339537165131 419678001635630009305747697)
              ·
                refine ⟨314758501226722506979310773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419678001635630009305747697 314758501226722506979310773)
                ·
                  refine ⟨29508609490005235029310385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 314758501226722506979310773 29508609490005235029310385)
                  ·
                    refine ⟨22131457117503926271982789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29508609490005235029310385 22131457117503926271982789)
                    ·
                      refine ⟨4149648209531986175996773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22131457117503926271982789 4149648209531986175996773)
                      ·
                        rfl

theorem cell23_8081411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_8081411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081411 prefixEnd_8081411 := by exact prefixLift 8081411
  have htrace : WordTrace (prefixWord ++ tailWord_8081411) baseStart_8081411 baseEnd_8081411 := by
    simpa [prefixWord, tailWord_8081411, baseEnd_8081411] using wordTrace_append hprefix tailTrace_8081411
  have hstable : (prefixWord ++ tailWord_8081411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081411).length < 2 ^ (prefixWord ++ tailWord_8081411).sum := by decide
  have hdescent : baseEnd_8081411 < baseStart_8081411 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081415 : List Nat := [1, 1, 4, 3, 1, 2, 3, 2, 1, 1, 4]
def baseStart_8081415 : Nat := 118140960795 + 8081415 * 2 ^ 59
def prefixEnd_8081415 : Nat := 4983230072969 + 3 ^ 40 * 8081415 * 2
def baseEnd_8081415 : Nat := 4149650263454604160346755

theorem tailTrace_8081415 : CollatzResearch.WordTrace tailWord_8081415 prefixEnd_8081415 4149650263454604160346755 := by
  unfold tailWord_8081415
  simp only [CollatzResearch.WordTrace]
  refine ⟨294753420017421125644109699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196502280011614083762739799 294753420017421125644109699)
  ·
    refine ⟨442130130026131688466164549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294753420017421125644109699 442130130026131688466164549)
    ·
      refine ⟨82899399379899691587405853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442130130026131688466164549 82899399379899691587405853)
      ·
        refine ⟨31087274767462384345277195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82899399379899691587405853 31087274767462384345277195)
        ·
          refine ⟨46630912151193576517915793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31087274767462384345277195 46630912151193576517915793)
          ·
            refine ⟨34973184113395182388436845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46630912151193576517915793 34973184113395182388436845)
            ·
              refine ⟨13114944042523193395663817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34973184113395182388436845 13114944042523193395663817)
              ·
                refine ⟨9836208031892395046747863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13114944042523193395663817 9836208031892395046747863)
                ·
                  refine ⟨14754312047838592570121795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9836208031892395046747863 14754312047838592570121795)
                  ·
                    refine ⟨22131468071757888855182693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14754312047838592570121795 22131468071757888855182693)
                    ·
                      refine ⟨4149650263454604160346755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22131468071757888855182693 4149650263454604160346755)
                      ·
                        rfl

theorem cell23_8081415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_8081415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081415 prefixEnd_8081415 := by exact prefixLift 8081415
  have htrace : WordTrace (prefixWord ++ tailWord_8081415) baseStart_8081415 baseEnd_8081415 := by
    simpa [prefixWord, tailWord_8081415, baseEnd_8081415] using wordTrace_append hprefix tailTrace_8081415
  have hstable : (prefixWord ++ tailWord_8081415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081415).length < 2 ^ (prefixWord ++ tailWord_8081415).sum := by decide
  have hdescent : baseEnd_8081415 < baseStart_8081415 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081481 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 1, 8]
def baseStart_8081481 : Nat := 118140960795 + 8081481 * 2 ^ 59
def prefixEnd_8081481 : Nat := 4983230072969 + 3 ^ 40 * 8081481 * 2
def baseEnd_8081481 : Nat := 1383228051059266967373817

theorem tailTrace_8081481 : CollatzResearch.WordTrace tailWord_8081481 prefixEnd_8081481 1383228051059266967373817 := by
  unfold tailWord_8081481
  simp only [CollatzResearch.WordTrace]
  refine ⟨294755827235182018916012297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196503884823454679277341531 294755827235182018916012297)
  ·
    refine ⟨221066870426386514187009223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294755827235182018916012297 221066870426386514187009223)
    ·
      refine ⟨331600305639579771280513835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221066870426386514187009223 331600305639579771280513835)
      ·
        refine ⟨497400458459369656920770753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331600305639579771280513835 497400458459369656920770753)
        ·
          refine ⟨373050343844527242690578065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497400458459369656920770753 373050343844527242690578065)
          ·
            refine ⟨279787757883395432017933549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373050343844527242690578065 279787757883395432017933549)
            ·
              refine ⟨104920409206273287006725081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279787757883395432017933549 104920409206273287006725081)
              ·
                refine ⟨78690306904704965255043811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104920409206273287006725081 78690306904704965255043811)
                ·
                  refine ⟨118035460357057447882565717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78690306904704965255043811 118035460357057447882565717)
                  ·
                    refine ⟨1383228051059266967373817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118035460357057447882565717 1383228051059266967373817)
                    ·
                      rfl

theorem cell23_8081481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_8081481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081481 prefixEnd_8081481 := by exact prefixLift 8081481
  have htrace : WordTrace (prefixWord ++ tailWord_8081481) baseStart_8081481 baseEnd_8081481 := by
    simpa [prefixWord, tailWord_8081481, baseEnd_8081481] using wordTrace_append hprefix tailTrace_8081481
  have hstable : (prefixWord ++ tailWord_8081481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081481).length < 2 ^ (prefixWord ++ tailWord_8081481).sum := by decide
  have hdescent : baseEnd_8081481 < baseStart_8081481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081508 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_8081508 : Nat := 118140960795 + 8081508 * 2 ^ 59
def prefixEnd_8081508 : Nat := 4983230072969 + 3 ^ 40 * 8081508 * 2
def baseEnd_8081508 : Nat := 4149698017155472296483827

theorem tailTrace_8081508 : CollatzResearch.WordTrace tailWord_8081508 prefixEnd_8081508 4149698017155472296483827 := by
  unfold tailWord_8081508
  simp only [CollatzResearch.WordTrace]
  refine ⟨147378406003042101263622589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196504541337389468351496785 147378406003042101263622589)
  ·
    refine ⟨55266902251140787973858471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147378406003042101263622589 55266902251140787973858471)
    ·
      refine ⟨82900353376711181960787707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55266902251140787973858471 82900353376711181960787707)
      ·
        refine ⟨124350530065066772941181561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82900353376711181960787707 124350530065066772941181561)
        ·
          refine ⟨93262897548800079705886171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124350530065066772941181561 93262897548800079705886171)
          ·
            refine ⟨139894346323200119558829257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93262897548800079705886171 139894346323200119558829257)
            ·
              refine ⟨104920759742400089669121943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139894346323200119558829257 104920759742400089669121943)
              ·
                refine ⟨157381139613600134503682915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104920759742400089669121943 157381139613600134503682915)
                ·
                  refine ⟨236071709420400201755524373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157381139613600134503682915 236071709420400201755524373)
                  ·
                    refine ⟨11065861379081259457290205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 236071709420400201755524373 11065861379081259457290205)
                    ·
                      refine ⟨4149698017155472296483827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11065861379081259457290205 4149698017155472296483827)
                      ·
                        rfl

theorem cell23_8081508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_8081508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081508 prefixEnd_8081508 := by exact prefixLift 8081508
  have htrace : WordTrace (prefixWord ++ tailWord_8081508) baseStart_8081508 baseEnd_8081508 := by
    simpa [prefixWord, tailWord_8081508, baseEnd_8081508] using wordTrace_append hprefix tailTrace_8081508
  have hstable : (prefixWord ++ tailWord_8081508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081508).length < 2 ^ (prefixWord ++ tailWord_8081508).sum := by decide
  have hdescent : baseEnd_8081508 < baseStart_8081508 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081522 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 1, 4, 2]
def baseStart_8081522 : Nat := 118140960795 + 8081522 * 2 ^ 59
def prefixEnd_8081522 : Nat := 4983230072969 + 3 ^ 40 * 8081522 * 2
def baseEnd_8081522 : Nat := 4149705205884635241708763

theorem tailTrace_8081522 : CollatzResearch.WordTrace tailWord_8081522 prefixEnd_8081522 4149705205884635241708763 := by
  unfold tailWord_8081522
  simp only [CollatzResearch.WordTrace]
  refine ⟨73689330657008370729563705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196504881752022321945503213 73689330657008370729563705)
  ·
    refine ⟨55266997992756278047172779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73689330657008370729563705 55266997992756278047172779)
    ·
      refine ⟨82900496989134417070759169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55266997992756278047172779 82900496989134417070759169)
      ·
        refine ⟨62175372741850812803069377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82900496989134417070759169 62175372741850812803069377)
        ·
          refine ⟨46631529556388109602302033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62175372741850812803069377 46631529556388109602302033)
          ·
            refine ⟨34973647167291082201726525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46631529556388109602302033 34973647167291082201726525)
            ·
              refine ⟨13115117687734155825647447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34973647167291082201726525 13115117687734155825647447)
              ·
                refine ⟨19672676531601233738471171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13115117687734155825647447 19672676531601233738471171)
                ·
                  refine ⟨29509014797401850607706757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19672676531601233738471171 29509014797401850607706757)
                  ·
                    refine ⟨5532940274512846988945017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29509014797401850607706757 5532940274512846988945017)
                    ·
                      refine ⟨4149705205884635241708763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5532940274512846988945017 4149705205884635241708763)
                      ·
                        rfl

theorem cell23_8081522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_8081522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081522 prefixEnd_8081522 := by exact prefixLift 8081522
  have htrace : WordTrace (prefixWord ++ tailWord_8081522) baseStart_8081522 baseEnd_8081522 := by
    simpa [prefixWord, tailWord_8081522, baseEnd_8081522] using wordTrace_append hprefix tailTrace_8081522
  have hstable : (prefixWord ++ tailWord_8081522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081522).length < 2 ^ (prefixWord ++ tailWord_8081522).sum := by decide
  have hdescent : baseEnd_8081522 < baseStart_8081522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081562 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 7]
def baseStart_8081562 : Nat := 118140960795 + 8081562 * 2 ^ 59
def prefixEnd_8081562 : Nat := 4983230072969 + 3 ^ 40 * 8081562 * 2
def baseEnd_8081562 : Nat := 461080638345646120578731

theorem tailTrace_8081562 : CollatzResearch.WordTrace tailWord_8081562 prefixEnd_8081562 461080638345646120578731 := by
  unfold tailWord_8081562
  simp only [CollatzResearch.WordTrace]
  refine ⟨73689695386972142437427735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196505854365259046499807293 73689695386972142437427735)
  ·
    refine ⟨110534543080458213656141603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73689695386972142437427735 110534543080458213656141603)
    ·
      refine ⟨165801814620687320484212405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110534543080458213656141603 165801814620687320484212405)
      ·
        refine ⟨15543920120689436295394913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165801814620687320484212405 15543920120689436295394913)
        ·
          refine ⟨11657940090517077221546185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15543920120689436295394913 11657940090517077221546185)
          ·
            refine ⟨8743455067887807916159639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11657940090517077221546185 8743455067887807916159639)
            ·
              refine ⟨13115182601831711874239459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8743455067887807916159639 13115182601831711874239459)
              ·
                refine ⟨19672773902747567811359189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13115182601831711874239459 19672773902747567811359189)
                ·
                  refine ⟨461080638345646120578731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19672773902747567811359189 461080638345646120578731)
                  ·
                    rfl

theorem cell23_8081562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 7].length) (baseStart_8081562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081562 prefixEnd_8081562 := by exact prefixLift 8081562
  have htrace : WordTrace (prefixWord ++ tailWord_8081562) baseStart_8081562 baseEnd_8081562 := by
    simpa [prefixWord, tailWord_8081562, baseEnd_8081562] using wordTrace_append hprefix tailTrace_8081562
  have hstable : (prefixWord ++ tailWord_8081562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081562).length < 2 ^ (prefixWord ++ tailWord_8081562).sum := by decide
  have hdescent : baseEnd_8081562 < baseStart_8081562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081568 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 7]
def baseStart_8081568 : Nat := 118140960795 + 8081568 * 2 ^ 59
def prefixEnd_8081568 : Nat := 4983230072969 + 3 ^ 40 * 8081568 * 2
def baseEnd_8081568 : Nat := 4149728825994742061733551

theorem tailTrace_8081568 : CollatzResearch.WordTrace tailWord_8081568 prefixEnd_8081568 4149728825994742061733551 := by
  unfold tailWord_8081568
  simp only [CollatzResearch.WordTrace]
  refine ⟨147379500192933416387214679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196506000257244555182952905 147379500192933416387214679)
  ·
    refine ⟨221069250289400124580822019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147379500192933416387214679 221069250289400124580822019)
    ·
      refine ⟨331603875434100186871233029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221069250289400124580822019 331603875434100186871233029)
      ·
        refine ⟨62175726643893785038356193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331603875434100186871233029 62175726643893785038356193)
        ·
          refine ⟨46631794982920338778767145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62175726643893785038356193 46631794982920338778767145)
          ·
            refine ⟨34973846237190254084075359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46631794982920338778767145 34973846237190254084075359)
            ·
              refine ⟨52460769355785381126113039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34973846237190254084075359 52460769355785381126113039)
              ·
                refine ⟨78691154033678071689169559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52460769355785381126113039 78691154033678071689169559)
                ·
                  refine ⟨118036731050517107533754339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78691154033678071689169559 118036731050517107533754339)
                  ·
                    refine ⟨177055096575775661300631509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118036731050517107533754339 177055096575775661300631509)
                    ·
                      refine ⟨4149728825994742061733551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177055096575775661300631509 4149728825994742061733551)
                      ·
                        rfl

theorem cell23_8081568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_8081568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081568 prefixEnd_8081568 := by exact prefixLift 8081568
  have htrace : WordTrace (prefixWord ++ tailWord_8081568) baseStart_8081568 baseEnd_8081568 := by
    simpa [prefixWord, tailWord_8081568, baseEnd_8081568] using wordTrace_append hprefix tailTrace_8081568
  have hstable : (prefixWord ++ tailWord_8081568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081568).length < 2 ^ (prefixWord ++ tailWord_8081568).sum := by decide
  have hdescent : baseEnd_8081568 < baseStart_8081568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081595 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 4]
def baseStart_8081595 : Nat := 118140960795 + 8081595 * 2 ^ 59
def prefixEnd_8081595 : Nat := 4983230072969 + 3 ^ 40 * 8081595 * 2
def baseEnd_8081595 : Nat := 4149742689972413456095927

theorem tailTrace_8081595 : CollatzResearch.WordTrace tailWord_8081595 prefixEnd_8081595 4149742689972413456095927 := by
  unfold tailWord_8081595
  simp only [CollatzResearch.WordTrace]
  refine ⟨294759985156769016385662239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196506656771179344257108159 294759985156769016385662239)
  ·
    refine ⟨442139977735153524578493359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294759985156769016385662239 442139977735153524578493359)
    ·
      refine ⟨663209966602730286867740039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442139977735153524578493359 663209966602730286867740039)
      ·
        refine ⟨994814949904095430301610059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663209966602730286867740039 994814949904095430301610059)
        ·
          refine ⟨1492222424856143145452415089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994814949904095430301610059 1492222424856143145452415089)
          ·
            refine ⟨1119166818642107359089311317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1492222424856143145452415089 1119166818642107359089311317)
            ·
              refine ⟨13115236155962195614327867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1119166818642107359089311317 13115236155962195614327867)
              ·
                refine ⟨19672854233943293421491801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13115236155962195614327867 19672854233943293421491801)
                ·
                  refine ⟨14754640675457470066118851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19672854233943293421491801 14754640675457470066118851)
                  ·
                    refine ⟨22131961013186205099178277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14754640675457470066118851 22131961013186205099178277)
                    ·
                      refine ⟨4149742689972413456095927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22131961013186205099178277 4149742689972413456095927)
                      ·
                        rfl

theorem cell23_8081595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 4].length) (baseStart_8081595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081595 prefixEnd_8081595 := by exact prefixLift 8081595
  have htrace : WordTrace (prefixWord ++ tailWord_8081595) baseStart_8081595 baseEnd_8081595 := by
    simpa [prefixWord, tailWord_8081595, baseEnd_8081595] using wordTrace_append hprefix tailTrace_8081595
  have hstable : (prefixWord ++ tailWord_8081595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081595).length < 2 ^ (prefixWord ++ tailWord_8081595).sum := by decide
  have hdescent : baseEnd_8081595 < baseStart_8081595 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081608 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_8081608 : Nat := 118140960795 + 8081608 * 2 ^ 59
def prefixEnd_8081608 : Nat := 4983230072969 + 3 ^ 40 * 8081608 * 2
def baseEnd_8081608 : Nat := 4149749365220921905233367

theorem tailTrace_8081608 : CollatzResearch.WordTrace tailWord_8081608 prefixEnd_8081608 4149749365220921905233367 := by
  unfold tailWord_8081608
  simp only [CollatzResearch.WordTrace]
  refine ⟨147380229652860959802942739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196506972870481279737256985 147380229652860959802942739)
  ·
    refine ⟨221070344479291439704414109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147380229652860959802942739 221070344479291439704414109)
    ·
      refine ⟨82901379179734289889155291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221070344479291439704414109 82901379179734289889155291)
      ·
        refine ⟨124352068769601434833732937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82901379179734289889155291 124352068769601434833732937)
        ·
          refine ⟨93264051577201076125299703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124352068769601434833732937 93264051577201076125299703)
          ·
            refine ⟨139896077365801614187949555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93264051577201076125299703 139896077365801614187949555)
            ·
              refine ⟨209844116048702421281924333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139896077365801614187949555 209844116048702421281924333)
              ·
                refine ⟨78691543518263407980721625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209844116048702421281924333 78691543518263407980721625)
                ·
                  refine ⟨59018657638697555985541219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78691543518263407980721625 59018657638697555985541219)
                  ·
                    refine ⟨88527986458046333978311829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59018657638697555985541219 88527986458046333978311829)
                    ·
                      refine ⟨4149749365220921905233367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88527986458046333978311829 4149749365220921905233367)
                      ·
                        rfl

theorem cell23_8081608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_8081608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081608 prefixEnd_8081608 := by exact prefixLift 8081608
  have htrace : WordTrace (prefixWord ++ tailWord_8081608) baseStart_8081608 baseEnd_8081608 := by
    simpa [prefixWord, tailWord_8081608, baseEnd_8081608] using wordTrace_append hprefix tailTrace_8081608
  have hstable : (prefixWord ++ tailWord_8081608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081608).length < 2 ^ (prefixWord ++ tailWord_8081608).sum := by decide
  have hdescent : baseEnd_8081608 < baseStart_8081608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081615 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 3]
def baseStart_8081615 : Nat := 118140960795 + 8081615 * 2 ^ 59
def prefixEnd_8081615 : Nat := 4983230072969 + 3 ^ 40 * 8081615 * 2
def baseEnd_8081615 : Nat := 4149752959585503377845835

theorem tailTrace_8081615 : CollatzResearch.WordTrace tailWord_8081615 prefixEnd_8081615 4149752959585503377845835 := by
  unfold tailWord_8081615
  simp only [CollatzResearch.WordTrace]
  refine ⟨294760714616696559801390299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196507143077797706534260199 294760714616696559801390299)
  ·
    refine ⟨442141071925044839702085449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294760714616696559801390299 442141071925044839702085449)
    ·
      refine ⟨331605803943783629776564087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442141071925044839702085449 331605803943783629776564087)
      ·
        refine ⟨497408705915675444664846131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331605803943783629776564087 497408705915675444664846131)
        ·
          refine ⟨746113058873513166997269197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497408705915675444664846131 746113058873513166997269197)
          ·
            refine ⟨279792397077567437623975949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 746113058873513166997269197 279792397077567437623975949)
            ·
              refine ⟨104922148904087789108990981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279792397077567437623975949 104922148904087789108990981)
              ·
                refine ⟨19672902919516460457935809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104922148904087789108990981 19672902919516460457935809)
                ·
                  refine ⟨14754677189637345343451857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19672902919516460457935809 14754677189637345343451857)
                  ·
                    refine ⟨11066007892228009007588893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14754677189637345343451857 11066007892228009007588893)
                    ·
                      refine ⟨4149752959585503377845835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11066007892228009007588893 4149752959585503377845835)
                      ·
                        rfl

theorem cell23_8081615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 3].length) (baseStart_8081615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081615 prefixEnd_8081615 := by exact prefixLift 8081615
  have htrace : WordTrace (prefixWord ++ tailWord_8081615) baseStart_8081615 baseEnd_8081615 := by
    simpa [prefixWord, tailWord_8081615, baseEnd_8081615] using wordTrace_append hprefix tailTrace_8081615
  have hstable : (prefixWord ++ tailWord_8081615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081615).length < 2 ^ (prefixWord ++ tailWord_8081615).sum := by decide
  have hdescent : baseEnd_8081615 < baseStart_8081615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081629 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_8081629 : Nat := 118140960795 + 8081629 * 2 ^ 59
def prefixEnd_8081629 : Nat := 4983230072969 + 3 ^ 40 * 8081629 * 2
def baseEnd_8081629 : Nat := 4149760148314666323070771

theorem tailTrace_8081629 : CollatzResearch.WordTrace tailWord_8081629 prefixEnd_8081629 4149760148314666323070771 := by
  unfold tailWord_8081629
  simp only [CollatzResearch.WordTrace]
  refine ⟨294761225238645840192399941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196507483492430560128266627 294761225238645840192399941)
  ·
    refine ⟨55267729732246095036074989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294761225238645840192399941 55267729732246095036074989)
    ·
      refine ⟨20725398649592285638528121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55267729732246095036074989 20725398649592285638528121)
      ·
        refine ⟨15544048987194214228896091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20725398649592285638528121 15544048987194214228896091)
        ·
          refine ⟨23316073480791321343344137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15544048987194214228896091 23316073480791321343344137)
          ·
            refine ⟨17487055110593491007508103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23316073480791321343344137 17487055110593491007508103)
            ·
              refine ⟨26230582665890236511262155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17487055110593491007508103 26230582665890236511262155)
              ·
                refine ⟨39345873998835354766893233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26230582665890236511262155 39345873998835354766893233)
                ·
                  refine ⟨29509405499126516075169925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39345873998835354766893233 29509405499126516075169925)
                  ·
                    refine ⟨5533013531086221764094361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29509405499126516075169925 5533013531086221764094361)
                    ·
                      refine ⟨4149760148314666323070771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533013531086221764094361 4149760148314666323070771)
                      ·
                        rfl

theorem cell23_8081629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_8081629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081629 prefixEnd_8081629 := by exact prefixLift 8081629
  have htrace : WordTrace (prefixWord ++ tailWord_8081629) baseStart_8081629 baseEnd_8081629 := by
    simpa [prefixWord, tailWord_8081629, baseEnd_8081629] using wordTrace_append hprefix tailTrace_8081629
  have hstable : (prefixWord ++ tailWord_8081629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081629).length < 2 ^ (prefixWord ++ tailWord_8081629).sum := by decide
  have hdescent : baseEnd_8081629 < baseStart_8081629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081685 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_8081685 : Nat := 118140960795 + 8081685 * 2 ^ 59
def prefixEnd_8081685 : Nat := 4983230072969 + 3 ^ 40 * 8081685 * 2
def baseEnd_8081685 : Nat := 4149788903231318103970513

theorem tailTrace_8081685 : CollatzResearch.WordTrace tailWord_8081685 prefixEnd_8081685 4149788903231318103970513 := by
  unfold tailWord_8081685
  simp only [CollatzResearch.WordTrace]
  refine ⟨294763267726442961756438509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196508845150961974504292339 294763267726442961756438509)
  ·
    refine ⟨110536225397416110658664441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294763267726442961756438509 110536225397416110658664441)
    ·
      refine ⟨82902169048062082993998331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110536225397416110658664441 82902169048062082993998331)
      ·
        refine ⟨124353253572093124490997497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82902169048062082993998331 124353253572093124490997497)
        ·
          refine ⟨93264940179069843368248123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124353253572093124490997497 93264940179069843368248123)
          ·
            refine ⟨139897410268604765052372185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93264940179069843368248123 139897410268604765052372185)
            ·
              refine ⟨104923057701453573789279139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139897410268604765052372185 104923057701453573789279139)
              ·
                refine ⟨157384586552180360683918709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104923057701453573789279139 157384586552180360683918709)
                ·
                  refine ⟨14754804989266908814117379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157384586552180360683918709 14754804989266908814117379)
                  ·
                    refine ⟨22132207483900363221176069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14754804989266908814117379 22132207483900363221176069)
                    ·
                      refine ⟨4149788903231318103970513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22132207483900363221176069 4149788903231318103970513)
                      ·
                        rfl

theorem cell23_8081685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_8081685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081685 prefixEnd_8081685 := by exact prefixLift 8081685
  have htrace : WordTrace (prefixWord ++ tailWord_8081685) baseStart_8081685 baseEnd_8081685 := by
    simpa [prefixWord, tailWord_8081685, baseEnd_8081685] using wordTrace_append hprefix tailTrace_8081685
  have hstable : (prefixWord ++ tailWord_8081685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081685).length < 2 ^ (prefixWord ++ tailWord_8081685).sum := by decide
  have hdescent : baseEnd_8081685 < baseStart_8081685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081713 : List Nat := [1, 2, 2, 3, 4, 2, 1, 3, 1, 1, 3]
def baseStart_8081713 : Nat := 118140960795 + 8081713 * 2 ^ 59
def prefixEnd_8081713 : Nat := 4983230072969 + 3 ^ 40 * 8081713 * 2
def baseEnd_8081713 : Nat := 4149803280689643994420385

theorem tailTrace_8081713 : CollatzResearch.WordTrace tailWord_8081713 prefixEnd_8081713 4149803280689643994420385 := by
  unfold tailWord_8081713
  simp only [CollatzResearch.WordTrace]
  refine ⟨294764288970341522538457793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196509525980227681692305195 294764288970341522538457793)
  ·
    refine ⟨221073216727756141903843345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294764288970341522538457793 221073216727756141903843345)
    ·
      refine ⟨165804912545817106427882509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221073216727756141903843345 165804912545817106427882509)
      ·
        refine ⟨62176842204681414910455941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165804912545817106427882509 62176842204681414910455941)
        ·
          refine ⟨11658157913377765295710489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62176842204681414910455941 11658157913377765295710489)
          ·
            refine ⟨8743618435033323971782867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11658157913377765295710489 8743618435033323971782867)
            ·
              refine ⟨13115427652549985957674301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8743618435033323971782867 13115427652549985957674301)
              ·
                refine ⟨4918285369706244734127863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13115427652549985957674301 4918285369706244734127863)
                ·
                  refine ⟨7377428054559367101191795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918285369706244734127863 7377428054559367101191795)
                  ·
                    refine ⟨11066142081839050651787693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7377428054559367101191795 11066142081839050651787693)
                    ·
                      refine ⟨4149803280689643994420385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11066142081839050651787693 4149803280689643994420385)
                      ·
                        rfl

theorem cell23_8081713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_8081713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081713 prefixEnd_8081713 := by exact prefixLift 8081713
  have htrace : WordTrace (prefixWord ++ tailWord_8081713) baseStart_8081713 baseEnd_8081713 := by
    simpa [prefixWord, tailWord_8081713, baseEnd_8081713] using wordTrace_append hprefix tailTrace_8081713
  have hstable : (prefixWord ++ tailWord_8081713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081713).length < 2 ^ (prefixWord ++ tailWord_8081713).sum := by decide
  have hdescent : baseEnd_8081713 < baseStart_8081713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081715 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 4]
def baseStart_8081715 : Nat := 118140960795 + 8081715 * 2 ^ 59
def prefixEnd_8081715 : Nat := 4983230072969 + 3 ^ 40 * 8081715 * 2
def baseEnd_8081715 : Nat := 4149804307650952986595375

theorem tailTrace_8081715 : CollatzResearch.WordTrace tailWord_8081715 prefixEnd_8081715 4149804307650952986595375 := by
  unfold tailWord_8081715
  simp only [CollatzResearch.WordTrace]
  refine ⟨294764361916334276880030599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196509574610889517920020399 294764361916334276880030599)
  ·
    refine ⟨442146542874501415320045899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294764361916334276880030599 442146542874501415320045899)
    ·
      refine ⟨663219814311752122980068849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442146542874501415320045899 663219814311752122980068849)
      ·
        refine ⟨497414860733814092235051637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 663219814311752122980068849 497414860733814092235051637)
        ·
          refine ⟨46632643193795071147036091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 497414860733814092235051637 46632643193795071147036091)
          ·
            refine ⟨69948964790692606720554137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46632643193795071147036091 69948964790692606720554137)
            ·
              refine ⟨52461723593019455040415603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69948964790692606720554137 52461723593019455040415603)
              ·
                refine ⟨78692585389529182560623405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52461723593019455040415603 78692585389529182560623405)
                ·
                  refine ⟨29509719521073443460233777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78692585389529182560623405 29509719521073443460233777)
                  ·
                    refine ⟨22132289640805082595175333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29509719521073443460233777 22132289640805082595175333)
                    ·
                      refine ⟨4149804307650952986595375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22132289640805082595175333 4149804307650952986595375)
                      ·
                        rfl

theorem cell23_8081715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_8081715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081715 prefixEnd_8081715 := by exact prefixLift 8081715
  have htrace : WordTrace (prefixWord ++ tailWord_8081715) baseStart_8081715 baseEnd_8081715 := by
    simpa [prefixWord, tailWord_8081715, baseEnd_8081715] using wordTrace_append hprefix tailTrace_8081715
  have hstable : (prefixWord ++ tailWord_8081715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081715).length < 2 ^ (prefixWord ++ tailWord_8081715).sum := by decide
  have hdescent : baseEnd_8081715 < baseStart_8081715 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081722 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5]
def baseStart_8081722 : Nat := 118140960795 + 8081722 * 2 ^ 59
def prefixEnd_8081722 : Nat := 4983230072969 + 3 ^ 40 * 8081722 * 2
def baseEnd_8081722 : Nat := 4149807902015534459207843

theorem tailTrace_8081722 : CollatzResearch.WordTrace tailWord_8081722 prefixEnd_8081722 4149807902015534459207843 := by
  unfold tailWord_8081722
  simp only [CollatzResearch.WordTrace]
  refine ⟨73691154306827229268883855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196509744818205944717023613 73691154306827229268883855)
  ·
    refine ⟨110536731460240843903325783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73691154306827229268883855 110536731460240843903325783)
    ·
      refine ⟨165805097190361265854988675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110536731460240843903325783 165805097190361265854988675)
      ·
        refine ⟨248707645785541898782483013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165805097190361265854988675 248707645785541898782483013)
        ·
          refine ⟨46632683584789106021715565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248707645785541898782483013 46632683584789106021715565)
          ·
            refine ⟨17487256344295914758143337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46632683584789106021715565 17487256344295914758143337)
            ·
              refine ⟨13115442258221936068607503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17487256344295914758143337 13115442258221936068607503)
              ·
                refine ⟨19673163387332904102911255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13115442258221936068607503 19673163387332904102911255)
                ·
                  refine ⟨29509745080999356154366883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19673163387332904102911255 29509745080999356154366883)
                  ·
                    refine ⟨44264617621499034231550325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29509745080999356154366883 44264617621499034231550325)
                    ·
                      refine ⟨4149807902015534459207843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44264617621499034231550325 4149807902015534459207843)
                      ·
                        rfl

theorem cell23_8081722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_8081722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081722 prefixEnd_8081722 := by exact prefixLift 8081722
  have htrace : WordTrace (prefixWord ++ tailWord_8081722) baseStart_8081722 baseEnd_8081722 := by
    simpa [prefixWord, tailWord_8081722, baseEnd_8081722] using wordTrace_append hprefix tailTrace_8081722
  have hstable : (prefixWord ++ tailWord_8081722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081722).length < 2 ^ (prefixWord ++ tailWord_8081722).sum := by decide
  have hdescent : baseEnd_8081722 < baseStart_8081722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081736 : List Nat := [2, 1, 3, 1, 1, 2, 2, 6, 1, 2, 2]
def baseStart_8081736 : Nat := 118140960795 + 8081736 * 2 ^ 59
def prefixEnd_8081736 : Nat := 4983230072969 + 3 ^ 40 * 8081736 * 2
def baseEnd_8081736 : Nat := 4149815090744697404432779

theorem tailTrace_8081736 : CollatzResearch.WordTrace tailWord_8081736 prefixEnd_8081736 4149815090744697404432779 := by
  unfold tailWord_8081736
  simp only [CollatzResearch.WordTrace]
  refine ⟨147382563924629098733272531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196510085232838798311030041 147382563924629098733272531)
  ·
    refine ⟨221073845886943648099908797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147382563924629098733272531 221073845886943648099908797)
    ·
      refine ⟨82902692207603868037465799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221073845886943648099908797 82902692207603868037465799)
      ·
        refine ⟨124354038311405802056198699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82902692207603868037465799 124354038311405802056198699)
        ·
          refine ⟨186531057467108703084298049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124354038311405802056198699 186531057467108703084298049)
          ·
            refine ⟨139898293100331527313223537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186531057467108703084298049 139898293100331527313223537)
            ·
              refine ⟨104923719825248645484917653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139898293100331527313223537 104923719825248645484917653)
              ·
                refine ⟨4918299366808530257105515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104923719825248645484917653 4918299366808530257105515)
                ·
                  refine ⟨7377449050212795385658273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918299366808530257105515 7377449050212795385658273)
                  ·
                    refine ⟨5533086787659596539243705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7377449050212795385658273 5533086787659596539243705)
                    ·
                      refine ⟨4149815090744697404432779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533086787659596539243705 4149815090744697404432779)
                      ·
                        rfl

theorem cell23_8081736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_8081736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081736 prefixEnd_8081736 := by exact prefixLift 8081736
  have htrace : WordTrace (prefixWord ++ tailWord_8081736) baseStart_8081736 baseEnd_8081736 := by
    simpa [prefixWord, tailWord_8081736, baseEnd_8081736] using wordTrace_append hprefix tailTrace_8081736
  have hstable : (prefixWord ++ tailWord_8081736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081736).length < 2 ^ (prefixWord ++ tailWord_8081736).sum := by decide
  have hdescent : baseEnd_8081736 < baseStart_8081736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081752 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 6, 1, 3]
def baseStart_8081752 : Nat := 118140960795 + 8081752 * 2 ^ 59
def prefixEnd_8081752 : Nat := 4983230072969 + 3 ^ 40 * 8081752 * 2
def baseEnd_8081752 : Nat := 4149823306435169341832705

theorem tailTrace_8081752 : CollatzResearch.WordTrace tailWord_8081752 prefixEnd_8081752 4149823306435169341832705 := by
  unfold tailWord_8081752
  simp only [CollatzResearch.WordTrace]
  refine ⟨147382855708600116099563755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196510474278133488132751673 147382855708600116099563755)
  ·
    refine ⟨221074283562900174149345633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147382855708600116099563755 221074283562900174149345633)
    ·
      refine ⟨165805712672175130612009225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221074283562900174149345633 165805712672175130612009225)
      ·
        refine ⟨124354284504131347959006919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165805712672175130612009225 124354284504131347959006919)
        ·
          refine ⟨186531426756197021938510379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124354284504131347959006919 186531426756197021938510379)
          ·
            refine ⟨279797140134295532907765569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186531426756197021938510379 279797140134295532907765569)
            ·
              refine ⟨209847855100721649680824177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279797140134295532907765569 209847855100721649680824177)
              ·
                refine ⟨157385891325541237260618133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209847855100721649680824177 157385891325541237260618133)
                ·
                  refine ⟨7377463655884745496591475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157385891325541237260618133 7377463655884745496591475)
                  ·
                    refine ⟨11066195483827118244887213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7377463655884745496591475 11066195483827118244887213)
                    ·
                      refine ⟨4149823306435169341832705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11066195483827118244887213 4149823306435169341832705)
                      ·
                        rfl

theorem cell23_8081752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_8081752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081752 prefixEnd_8081752 := by exact prefixLift 8081752
  have htrace : WordTrace (prefixWord ++ tailWord_8081752) baseStart_8081752 baseEnd_8081752 := by
    simpa [prefixWord, tailWord_8081752, baseEnd_8081752] using wordTrace_append hprefix tailTrace_8081752
  have hstable : (prefixWord ++ tailWord_8081752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081752).length < 2 ^ (prefixWord ++ tailWord_8081752).sum := by decide
  have hdescent : baseEnd_8081752 < baseStart_8081752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081756 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_8081756 : Nat := 118140960795 + 8081756 * 2 ^ 59
def prefixEnd_8081756 : Nat := 4983230072969 + 3 ^ 40 * 8081756 * 2
def baseEnd_8081756 : Nat := 4149825360357787326182687

theorem tailTrace_8081756 : CollatzResearch.WordTrace tailWord_8081756 prefixEnd_8081756 4149825360357787326182687 := by
  unfold tailWord_8081756
  simp only [CollatzResearch.WordTrace]
  refine ⟨147382928654592870441136561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196510571539457160588182081 147382928654592870441136561)
  ·
    refine ⟨110537196490944652830852421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147382928654592870441136561 110537196490944652830852421)
    ·
      refine ⟨20725724342052122405784829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110537196490944652830852421 20725724342052122405784829)
      ·
        refine ⟨7772146628269545902169311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20725724342052122405784829 7772146628269545902169311)
        ·
          refine ⟨11658219942404318853253967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7772146628269545902169311 11658219942404318853253967)
          ·
            refine ⟨17487329913606478279880951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11658219942404318853253967 17487329913606478279880951)
            ·
              refine ⟨26230994870409717419821427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17487329913606478279880951 26230994870409717419821427)
              ·
                refine ⟨39346492305614576129732141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26230994870409717419821427 39346492305614576129732141)
                ·
                  refine ⟨14754934614605466048649553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39346492305614576129732141 14754934614605466048649553)
                  ·
                    refine ⟨11066200960954099536487165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14754934614605466048649553 11066200960954099536487165)
                    ·
                      refine ⟨4149825360357787326182687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11066200960954099536487165 4149825360357787326182687)
                      ·
                        rfl

theorem cell23_8081756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_8081756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081756 prefixEnd_8081756 := by exact prefixLift 8081756
  have htrace : WordTrace (prefixWord ++ tailWord_8081756) baseStart_8081756 baseEnd_8081756 := by
    simpa [prefixWord, tailWord_8081756, baseEnd_8081756] using wordTrace_append hprefix tailTrace_8081756
  have hstable : (prefixWord ++ tailWord_8081756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081756).length < 2 ^ (prefixWord ++ tailWord_8081756).sum := by decide
  have hdescent : baseEnd_8081756 < baseStart_8081756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081785 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 2, 6]
def baseStart_8081785 : Nat := 118140960795 + 8081785 * 2 ^ 59
def prefixEnd_8081785 : Nat := 4983230072969 + 3 ^ 40 * 8081785 * 2
def baseEnd_8081785 : Nat := 1383280083765589237573351

theorem tailTrace_8081785 : CollatzResearch.WordTrace tailWord_8081785 prefixEnd_8081785 1383280083765589237573351 := by
  unfold tailWord_8081785
  simp only [CollatzResearch.WordTrace]
  refine ⟨294766915026080678835078809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196511276684053785890052539 294766915026080678835078809)
  ·
    refine ⟨221075186269560509126309107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294766915026080678835078809 221075186269560509126309107)
    ·
      refine ⟨331612779404340763689463661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221075186269560509126309107 331612779404340763689463661)
      ·
        refine ⟨124354792276627786383548873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331612779404340763689463661 124354792276627786383548873)
        ·
          refine ⟨93266094207470839787661655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124354792276627786383548873 93266094207470839787661655)
          ·
            refine ⟨139899141311206259681492483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93266094207470839787661655 139899141311206259681492483)
            ·
              refine ⟨209848711966809389522238725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139899141311206259681492483 209848711966809389522238725)
              ·
                refine ⟨39346633493776760535419761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209848711966809389522238725 39346633493776760535419761)
                ·
                  refine ⟨29509975120332570401564821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39346633493776760535419761 29509975120332570401564821)
                  ·
                    refine ⟨1383280083765589237573351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29509975120332570401564821 1383280083765589237573351)
                    ·
                      rfl

theorem cell23_8081785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 6].length) (baseStart_8081785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081785 prefixEnd_8081785 := by exact prefixLift 8081785
  have htrace : WordTrace (prefixWord ++ tailWord_8081785) baseStart_8081785 baseEnd_8081785 := by
    simpa [prefixWord, tailWord_8081785, baseEnd_8081785] using wordTrace_append hprefix tailTrace_8081785
  have hstable : (prefixWord ++ tailWord_8081785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081785).length < 2 ^ (prefixWord ++ tailWord_8081785).sum := by decide
  have hdescent : baseEnd_8081785 < baseStart_8081785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081815 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 9]
def baseStart_8081815 : Nat := 118140960795 + 8081815 * 2 ^ 59
def prefixEnd_8081815 : Nat := 4983230072969 + 3 ^ 40 * 8081815 * 2
def baseEnd_8081815 : Nat := 461095072857378066149435

theorem tailTrace_8081815 : CollatzResearch.WordTrace tailWord_8081815 prefixEnd_8081815 461095072857378066149435 := by
  unfold tailWord_8081815
  simp only [CollatzResearch.WordTrace]
  refine ⟨294768009215971993958670899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196512006143981329305780599 294768009215971993958670899)
  ·
    refine ⟨442152013823957990938006349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294768009215971993958670899 442152013823957990938006349)
    ·
      refine ⟨165807005183984246601752381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442152013823957990938006349 165807005183984246601752381)
      ·
        refine ⟨62177626943994092475657143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165807005183984246601752381 62177626943994092475657143)
        ·
          refine ⟨93266440415991138713485715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62177626943994092475657143 93266440415991138713485715)
          ·
            refine ⟨139899660623986708070228573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93266440415991138713485715 139899660623986708070228573)
            ·
              refine ⟨52462372733995015526335715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139899660623986708070228573 52462372733995015526335715)
              ·
                refine ⟨78693559100992523289503573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52462372733995015526335715 78693559100992523289503573)
                ·
                  refine ⟨461095072857378066149435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78693559100992523289503573 461095072857378066149435)
                  ·
                    rfl

theorem cell23_8081815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 9].length) (baseStart_8081815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081815 prefixEnd_8081815 := by exact prefixLift 8081815
  have htrace : WordTrace (prefixWord ++ tailWord_8081815) baseStart_8081815 baseEnd_8081815 := by
    simpa [prefixWord, tailWord_8081815, baseEnd_8081815] using wordTrace_append hprefix tailTrace_8081815
  have hstable : (prefixWord ++ tailWord_8081815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081815).length < 2 ^ (prefixWord ++ tailWord_8081815).sum := by decide
  have hdescent : baseEnd_8081815 < baseStart_8081815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081826 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_8081826 : Nat := 118140960795 + 8081826 * 2 ^ 59
def prefixEnd_8081826 : Nat := 4983230072969 + 3 ^ 40 * 8081826 * 2
def baseEnd_8081826 : Nat := 4149861304003602052307365

theorem tailTrace_8081826 : CollatzResearch.WordTrace tailWord_8081826 prefixEnd_8081826 4149861304003602052307365 := by
  unfold tailWord_8081826
  simp only [CollatzResearch.WordTrace]
  refine ⟨73692102604733035709330333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196512273612621428558214221 73692102604733035709330333)
  ·
    refine ⟨27634538476774888390998875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73692102604733035709330333 27634538476774888390998875)
    ·
      refine ⟨41451807715162332586498313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27634538476774888390998875 41451807715162332586498313)
      ·
        refine ⟨31088855786371749439873735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41451807715162332586498313 31088855786371749439873735)
        ·
          refine ⟨46633283679557624159810603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31088855786371749439873735 46633283679557624159810603)
          ·
            refine ⟨69949925519336436239715905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46633283679557624159810603 69949925519336436239715905)
            ·
              refine ⟨52462444139502327179786929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69949925519336436239715905 52462444139502327179786929)
              ·
                refine ⟨39346833104626745384840197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52462444139502327179786929 39346833104626745384840197)
                ·
                  refine ⟨7377531207117514759657537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39346833104626745384840197 7377531207117514759657537)
                  ·
                    refine ⟨5533148405338136069743153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7377531207117514759657537 5533148405338136069743153)
                    ·
                      refine ⟨4149861304003602052307365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533148405338136069743153 4149861304003602052307365)
                      ·
                        rfl

theorem cell23_8081826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_8081826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081826 prefixEnd_8081826 := by exact prefixLift 8081826
  have htrace : WordTrace (prefixWord ++ tailWord_8081826) baseStart_8081826 baseEnd_8081826 := by
    simpa [prefixWord, tailWord_8081826, baseEnd_8081826] using wordTrace_append hprefix tailTrace_8081826
  have hstable : (prefixWord ++ tailWord_8081826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081826).length < 2 ^ (prefixWord ++ tailWord_8081826).sum := by decide
  have hdescent : baseEnd_8081826 < baseStart_8081826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081842 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_8081842 : Nat := 118140960795 + 8081842 * 2 ^ 59
def prefixEnd_8081842 : Nat := 4983230072969 + 3 ^ 40 * 8081842 * 2
def baseEnd_8081842 : Nat := 4149869519694073989707291

theorem tailTrace_8081842 : CollatzResearch.WordTrace tailWord_8081842 prefixEnd_8081842 4149869519694073989707291 := by
  unfold tailWord_8081842
  simp only [CollatzResearch.WordTrace]
  refine ⟨73692248496718544392475945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196512662657916118379935853 73692248496718544392475945)
  ·
    refine ⟨55269186372538908294356959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73692248496718544392475945 55269186372538908294356959)
    ·
      refine ⟨82903779558808362441535439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55269186372538908294356959 82903779558808362441535439)
      ·
        refine ⟨124355669338212543662303159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82903779558808362441535439 124355669338212543662303159)
        ·
          refine ⟨186533504007318815493454739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124355669338212543662303159 186533504007318815493454739)
          ·
            refine ⟨279800256010978223240182109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186533504007318815493454739 279800256010978223240182109)
            ·
              refine ⟨104925096004116833715068291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279800256010978223240182109 104925096004116833715068291)
              ·
                refine ⟨157387644006175250572602437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104925096004116833715068291 157387644006175250572602437)
                ·
                  refine ⟨29510183251157859482362957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157387644006175250572602437 29510183251157859482362957)
                  ·
                    refine ⟨11066318719184197305886109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29510183251157859482362957 11066318719184197305886109)
                    ·
                      refine ⟨4149869519694073989707291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11066318719184197305886109 4149869519694073989707291)
                      ·
                        rfl

theorem cell23_8081842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_8081842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081842 prefixEnd_8081842 := by exact prefixLift 8081842
  have htrace : WordTrace (prefixWord ++ tailWord_8081842) baseStart_8081842 baseEnd_8081842 := by
    simpa [prefixWord, tailWord_8081842, baseEnd_8081842] using wordTrace_append hprefix tailTrace_8081842
  have hstable : (prefixWord ++ tailWord_8081842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081842).length < 2 ^ (prefixWord ++ tailWord_8081842).sum := by decide
  have hdescent : baseEnd_8081842 < baseStart_8081842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081849 : List Nat := [1, 2, 1, 4, 3, 1, 2, 4, 5]
def baseStart_8081849 : Nat := 118140960795 + 8081849 * 2 ^ 59
def prefixEnd_8081849 : Nat := 4983230072969 + 3 ^ 40 * 8081849 * 2
def baseEnd_8081849 : Nat := 461097012673183940257751

theorem tailTrace_8081849 : CollatzResearch.WordTrace tailWord_8081849 prefixEnd_8081849 461097012673183940257751 := by
  unfold tailWord_8081849
  simp only [CollatzResearch.WordTrace]
  refine ⟨294769249297848817765408601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196512832865232545176939067 294769249297848817765408601)
  ·
    refine ⟨221076936973386613324056451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294769249297848817765408601 221076936973386613324056451)
    ·
      refine ⟨331615405460079919986084677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221076936973386613324056451 331615405460079919986084677)
      ·
        refine ⟨62177888523764984997390877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331615405460079919986084677 62177888523764984997390877)
        ·
          refine ⟨23316708196411869374021579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62177888523764984997390877 23316708196411869374021579)
          ·
            refine ⟨34975062294617804061032369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23316708196411869374021579 34975062294617804061032369)
            ·
              refine ⟨26231296720963353045774277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34975062294617804061032369 26231296720963353045774277)
              ·
                refine ⟨4918368135180628696082677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26231296720963353045774277 4918368135180628696082677)
                ·
                  refine ⟨461097012673183940257751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4918368135180628696082677 461097012673183940257751)
                  ·
                    rfl

theorem cell23_8081849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 5].length) (baseStart_8081849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081849 prefixEnd_8081849 := by exact prefixLift 8081849
  have htrace : WordTrace (prefixWord ++ tailWord_8081849) baseStart_8081849 baseEnd_8081849 := by
    simpa [prefixWord, tailWord_8081849, baseEnd_8081849] using wordTrace_append hprefix tailTrace_8081849
  have hstable : (prefixWord ++ tailWord_8081849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081849).length < 2 ^ (prefixWord ++ tailWord_8081849).sum := by decide
  have hdescent : baseEnd_8081849 < baseStart_8081849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081860 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_8081860 : Nat := 118140960795 + 8081860 * 2 ^ 59
def prefixEnd_8081860 : Nat := 4983230072969 + 3 ^ 40 * 8081860 * 2
def baseEnd_8081860 : Nat := 4149878762345854919282209

theorem tailTrace_8081860 : CollatzResearch.WordTrace tailWord_8081860 prefixEnd_8081860 4149878762345854919282209 := by
  unfold tailWord_8081860
  simp only [CollatzResearch.WordTrace]
  refine ⟨147384825250404483322029517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196513100333872644429372689 147384825250404483322029517)
  ·
    refine ⟨55269309468901681245761069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147384825250404483322029517 55269309468901681245761069)
    ·
      refine ⟨20725991050838130467160401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55269309468901681245761069 20725991050838130467160401)
      ·
        refine ⟨15544493288128597850370301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20725991050838130467160401 15544493288128597850370301)
        ·
          refine ⟨5829184983048224193888863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15544493288128597850370301 5829184983048224193888863)
          ·
            refine ⟨8743777474572336290833295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5829184983048224193888863 8743777474572336290833295)
            ·
              refine ⟨13115666211858504436249943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8743777474572336290833295 13115666211858504436249943)
              ·
                refine ⟨19673499317787756654374915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13115666211858504436249943 19673499317787756654374915)
                ·
                  refine ⟨29510248976681634981562373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19673499317787756654374915 29510248976681634981562373)
                  ·
                    refine ⟨5533171683127806559042945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29510248976681634981562373 5533171683127806559042945)
                    ·
                      refine ⟨4149878762345854919282209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533171683127806559042945 4149878762345854919282209)
                      ·
                        rfl

theorem cell23_8081860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_8081860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081860 prefixEnd_8081860 := by exact prefixLift 8081860
  have htrace : WordTrace (prefixWord ++ tailWord_8081860) baseStart_8081860 baseEnd_8081860 := by
    simpa [prefixWord, tailWord_8081860, baseEnd_8081860] using wordTrace_append hprefix tailTrace_8081860
  have hstable : (prefixWord ++ tailWord_8081860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081860).length < 2 ^ (prefixWord ++ tailWord_8081860).sum := by decide
  have hdescent : baseEnd_8081860 < baseStart_8081860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081882 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_8081882 : Nat := 118140960795 + 8081882 * 2 ^ 59
def prefixEnd_8081882 : Nat := 4983230072969 + 3 ^ 40 * 8081882 * 2
def baseEnd_8081882 : Nat := 4149890058920253833207107

theorem tailTrace_8081882 : CollatzResearch.WordTrace tailWord_8081882 prefixEnd_8081882 4149890058920253833207107 := by
  unfold tailWord_8081882
  simp only [CollatzResearch.WordTrace]
  refine ⟨73692613226682316100339975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196513635271152842934239933 73692613226682316100339975)
  ·
    refine ⟨110538919840023474150509963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73692613226682316100339975 110538919840023474150509963)
    ·
      refine ⟨165808379760035211225764945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110538919840023474150509963 165808379760035211225764945)
      ·
        refine ⟨124356284820026408419323709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165808379760035211225764945 124356284820026408419323709)
        ·
          refine ⟨46633606807509903157246391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124356284820026408419323709 46633606807509903157246391)
          ·
            refine ⟨69950410211264854735869587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46633606807509903157246391 69950410211264854735869587)
            ·
              refine ⟨104925615316897282103804381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69950410211264854735869587 104925615316897282103804381)
              ·
                refine ⟨39347105743836480788926643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104925615316897282103804381 39347105743836480788926643)
                ·
                  refine ⟨59020658615754721183389965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39347105743836480788926643 59020658615754721183389965)
                  ·
                    refine ⟨22132746980908020443771237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59020658615754721183389965 22132746980908020443771237)
                    ·
                      refine ⟨4149890058920253833207107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22132746980908020443771237 4149890058920253833207107)
                      ·
                        rfl

theorem cell23_8081882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_8081882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081882 prefixEnd_8081882 := by exact prefixLift 8081882
  have htrace : WordTrace (prefixWord ++ tailWord_8081882) baseStart_8081882 baseEnd_8081882 := by
    simpa [prefixWord, tailWord_8081882, baseEnd_8081882] using wordTrace_append hprefix tailTrace_8081882
  have hstable : (prefixWord ++ tailWord_8081882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081882).length < 2 ^ (prefixWord ++ tailWord_8081882).sum := by decide
  have hdescent : baseEnd_8081882 < baseStart_8081882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081933 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_8081933 : Nat := 118140960795 + 8081933 * 2 ^ 59
def prefixEnd_8081933 : Nat := 4983230072969 + 3 ^ 40 * 8081933 * 2
def baseEnd_8081933 : Nat := 4149916246433633133669373

theorem tailTrace_8081933 : CollatzResearch.WordTrace tailWord_8081933 prefixEnd_8081933 4149916246433633133669373 := by
  unfold tailWord_8081933
  simp only [CollatzResearch.WordTrace]
  refine ⟨294772313029544500111466453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196514875353029666740977635 294772313029544500111466453)
  ·
    refine ⟨6908726086629949221362495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 294772313029544500111466453 6908726086629949221362495)
    ·
      refine ⟨10363089129944923832043743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6908726086629949221362495 10363089129944923832043743)
      ·
        refine ⟨15544633694917385748065615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10363089129944923832043743 15544633694917385748065615)
        ·
          refine ⟨23316950542376078622098423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15544633694917385748065615 23316950542376078622098423)
          ·
            refine ⟨34975425813564117933147635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23316950542376078622098423 34975425813564117933147635)
            ·
              refine ⟨52463138720346176899721453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34975425813564117933147635 52463138720346176899721453)
              ·
                refine ⟨19673677020129816337395545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52463138720346176899721453 19673677020129816337395545)
                ·
                  refine ⟨14755257765097362253046659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19673677020129816337395545 14755257765097362253046659)
                  ·
                    refine ⟨22132886647646043379569989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14755257765097362253046659 22132886647646043379569989)
                    ·
                      refine ⟨4149916246433633133669373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22132886647646043379569989 4149916246433633133669373)
                      ·
                        rfl

theorem cell23_8081933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_8081933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081933 prefixEnd_8081933 := by exact prefixLift 8081933
  have htrace : WordTrace (prefixWord ++ tailWord_8081933) baseStart_8081933 baseEnd_8081933 := by
    simpa [prefixWord, tailWord_8081933, baseEnd_8081933] using wordTrace_append hprefix tailTrace_8081933
  have hstable : (prefixWord ++ tailWord_8081933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081933).length < 2 ^ (prefixWord ++ tailWord_8081933).sum := by decide
  have hdescent : baseEnd_8081933 < baseStart_8081933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081960 : List Nat := [2, 1, 5, 2, 1, 1, 4, 2, 1, 4]
def baseStart_8081960 : Nat := 118140960795 + 8081960 * 2 ^ 59
def prefixEnd_8081960 : Nat := 4983230072969 + 3 ^ 40 * 8081960 * 2
def baseEnd_8081960 : Nat := 1383310036803768176010583

theorem tailTrace_8081960 : CollatzResearch.WordTrace tailWord_8081960 prefixEnd_8081960 1383310036803768176010583 := by
  unfold tailWord_8081960
  simp only [CollatzResearch.WordTrace]
  refine ⟨147386648900223341861349667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196515531866964455815132889 147386648900223341861349667)
  ·
    refine ⟨221079973350335012792024501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147386648900223341861349667 221079973350335012792024501)
    ·
      refine ⟨20726247501593907449252297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221079973350335012792024501 20726247501593907449252297)
      ·
        refine ⟨15544685626195430586939223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20726247501593907449252297 15544685626195430586939223)
        ·
          refine ⟨23317028439293145880408835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15544685626195430586939223 23317028439293145880408835)
          ·
            refine ⟨34975542658939718820613253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23317028439293145880408835 34975542658939718820613253)
            ·
              refine ⟨6557914248551197278864985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34975542658939718820613253 6557914248551197278864985)
              ·
                refine ⟨4918435686413397959148739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6557914248551197278864985 4918435686413397959148739)
                ·
                  refine ⟨7377653529620096938723109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918435686413397959148739 7377653529620096938723109)
                  ·
                    refine ⟨1383310036803768176010583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7377653529620096938723109 1383310036803768176010583)
                    ·
                      rfl

theorem cell23_8081960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_8081960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081960 prefixEnd_8081960 := by exact prefixLift 8081960
  have htrace : WordTrace (prefixWord ++ tailWord_8081960) baseStart_8081960 baseEnd_8081960 := by
    simpa [prefixWord, tailWord_8081960, baseEnd_8081960] using wordTrace_append hprefix tailTrace_8081960
  have hstable : (prefixWord ++ tailWord_8081960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081960).length < 2 ^ (prefixWord ++ tailWord_8081960).sum := by decide
  have hdescent : baseEnd_8081960 < baseStart_8081960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8081989 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 3, 1, 4]
def baseStart_8081989 : Nat := 118140960795 + 8081989 * 2 ^ 59
def prefixEnd_8081989 : Nat := 4983230072969 + 3 ^ 40 * 8081989 * 2
def baseEnd_8081989 : Nat := 4149945001350284914569115

theorem tailTrace_8081989 : CollatzResearch.WordTrace tailWord_8081989 prefixEnd_8081989 4149945001350284914569115 := by
  unfold tailWord_8081989
  simp only [CollatzResearch.WordTrace]
  refine ⟨294774355517341621675505021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196516237011561081117003347 294774355517341621675505021)
  ·
    refine ⟨110540383319003108128314383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294774355517341621675505021 110540383319003108128314383)
    ·
      refine ⟨165810574978504662192471575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110540383319003108128314383 165810574978504662192471575)
      ·
        refine ⟨248715862467756993288707363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165810574978504662192471575 248715862467756993288707363)
        ·
          refine ⟨373073793701635489933061045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248715862467756993288707363 373073793701635489933061045)
          ·
            refine ⟨34975668159528327181224473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 373073793701635489933061045 34975668159528327181224473)
            ·
              refine ⟨26231751119646245385918355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34975668159528327181224473 26231751119646245385918355)
              ·
                refine ⟨39347626679469368078877533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26231751119646245385918355 39347626679469368078877533)
                ·
                  refine ⟨14755360004801013029579075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39347626679469368078877533 14755360004801013029579075)
                  ·
                    refine ⟨22133040007201519544368613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14755360004801013029579075 22133040007201519544368613)
                    ·
                      refine ⟨4149945001350284914569115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22133040007201519544368613 4149945001350284914569115)
                      ·
                        rfl

theorem cell23_8081989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_8081989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8081989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8081989 prefixEnd_8081989 := by exact prefixLift 8081989
  have htrace : WordTrace (prefixWord ++ tailWord_8081989) baseStart_8081989 baseEnd_8081989 := by
    simpa [prefixWord, tailWord_8081989, baseEnd_8081989] using wordTrace_append hprefix tailTrace_8081989
  have hstable : (prefixWord ++ tailWord_8081989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8081989).length < 2 ^ (prefixWord ++ tailWord_8081989).sum := by decide
  have hdescent : baseEnd_8081989 < baseStart_8081989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8081989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082016 : List Nat := [2, 1, 1, 3, 2, 1, 5, 2, 2, 4]
def baseStart_8082016 : Nat := 118140960795 + 8082016 * 2 ^ 59
def prefixEnd_8082016 : Nat := 4983230072969 + 3 ^ 40 * 8082016 * 2
def baseEnd_8082016 : Nat := 1383319621775985436310497

theorem tailTrace_8082016 : CollatzResearch.WordTrace tailWord_8082016 prefixEnd_8082016 1383319621775985436310497 := by
  unfold tailWord_8082016
  simp only [CollatzResearch.WordTrace]
  refine ⟨147387670144121902643368951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196516893525495870191158601 147387670144121902643368951)
  ·
    refine ⟨221081505216182853965053427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147387670144121902643368951 221081505216182853965053427)
    ·
      refine ⟨331622257824274280947580141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221081505216182853965053427 331622257824274280947580141)
      ·
        refine ⟨124358346684102855355342553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331622257824274280947580141 124358346684102855355342553)
        ·
          refine ⟨93268760013077141516506915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124358346684102855355342553 93268760013077141516506915)
          ·
            refine ⟨139903140019615712274760373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93268760013077141516506915 139903140019615712274760373)
            ·
              refine ⟨13115919376838973025758785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139903140019615712274760373 13115919376838973025758785)
              ·
                refine ⟨9836939532629229769319089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13115919376838973025758785 9836939532629229769319089)
                ·
                  refine ⟨7377704649471922326989317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9836939532629229769319089 7377704649471922326989317)
                  ·
                    refine ⟨1383319621775985436310497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7377704649471922326989317 1383319621775985436310497)
                    ·
                      rfl

theorem cell23_8082016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 2, 4].length) (baseStart_8082016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082016 prefixEnd_8082016 := by exact prefixLift 8082016
  have htrace : WordTrace (prefixWord ++ tailWord_8082016) baseStart_8082016 baseEnd_8082016 := by
    simpa [prefixWord, tailWord_8082016, baseEnd_8082016] using wordTrace_append hprefix tailTrace_8082016
  have hstable : (prefixWord ++ tailWord_8082016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082016).length < 2 ^ (prefixWord ++ tailWord_8082016).sum := by decide
  have hdescent : baseEnd_8082016 < baseStart_8082016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082042 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 3, 9]
def baseStart_8082042 : Nat := 118140960795 + 8082042 * 2 ^ 59
def prefixEnd_8082042 : Nat := 4983230072969 + 3 ^ 40 * 8082042 * 2
def baseEnd_8082042 : Nat := 1383324071941657735735457

theorem tailTrace_8082042 : CollatzResearch.WordTrace tailWord_8082042 prefixEnd_8082042 1383324071941657735735457 := by
  unfold tailWord_8082042
  simp only [CollatzResearch.WordTrace]
  refine ⟨73694072146537402931796095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196517525724099741151456253 73694072146537402931796095)
  ·
    refine ⟨110541108219806104397694143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73694072146537402931796095 110541108219806104397694143)
    ·
      refine ⟨165811662329709156596541215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110541108219806104397694143 165811662329709156596541215)
      ·
        refine ⟨248717493494563734894811823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165811662329709156596541215 248717493494563734894811823)
        ·
          refine ⟨373076240241845602342217735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248717493494563734894811823 373076240241845602342217735)
          ·
            refine ⟨559614360362768403513326603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373076240241845602342217735 559614360362768403513326603)
            ·
              refine ⟨839421540544152605269989905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559614360362768403513326603 839421540544152605269989905)
              ·
                refine ⟨629566155408114453952492429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839421540544152605269989905 629566155408114453952492429)
                ·
                  refine ⟨236087308278042920232184661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629566155408114453952492429 236087308278042920232184661)
                  ·
                    refine ⟨1383324071941657735735457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 236087308278042920232184661 1383324071941657735735457)
                    ·
                      rfl

theorem cell23_8082042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_8082042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082042 prefixEnd_8082042 := by exact prefixLift 8082042
  have htrace : WordTrace (prefixWord ++ tailWord_8082042) baseStart_8082042 baseEnd_8082042 := by
    simpa [prefixWord, tailWord_8082042, baseEnd_8082042] using wordTrace_append hprefix tailTrace_8082042
  have hstable : (prefixWord ++ tailWord_8082042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082042).length < 2 ^ (prefixWord ++ tailWord_8082042).sum := by decide
  have hdescent : baseEnd_8082042 < baseStart_8082042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082074 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2]
def baseStart_8082074 : Nat := 118140960795 + 8082074 * 2 ^ 59
def prefixEnd_8082074 : Nat := 4983230072969 + 3 ^ 40 * 8082074 * 2
def baseEnd_8082074 : Nat := 4149988647205917082006225

theorem tailTrace_8082074 : CollatzResearch.WordTrace tailWord_8082074 prefixEnd_8082074 4149988647205917082006225 := by
  unfold tailWord_8082074
  simp only [CollatzResearch.WordTrace]
  refine ⟨73694363930508420298087319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196518303814689120794899517 73694363930508420298087319)
  ·
    refine ⟨110541545895762630447130979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73694363930508420298087319 110541545895762630447130979)
    ·
      refine ⟨165812318843643945670696469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110541545895762630447130979 165812318843643945670696469)
      ·
        refine ⟨7772452445795809953313897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165812318843643945670696469 7772452445795809953313897)
        ·
          refine ⟨5829339334346857464985423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7772452445795809953313897 5829339334346857464985423)
          ·
            refine ⟨8744009001520286197478135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5829339334346857464985423 8744009001520286197478135)
            ·
              refine ⟨13116013502280429296217203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8744009001520286197478135 13116013502280429296217203)
              ·
                refine ⟨19674020253420643944325805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13116013502280429296217203 19674020253420643944325805)
                ·
                  refine ⟨7377757595032741479122177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19674020253420643944325805 7377757595032741479122177)
                  ·
                    refine ⟨5533318196274556109341633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7377757595032741479122177 5533318196274556109341633)
                    ·
                      refine ⟨4149988647205917082006225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533318196274556109341633 4149988647205917082006225)
                      ·
                        rfl

theorem cell23_8082074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_8082074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082074 prefixEnd_8082074 := by exact prefixLift 8082074
  have htrace : WordTrace (prefixWord ++ tailWord_8082074) baseStart_8082074 baseEnd_8082074 := by
    simpa [prefixWord, tailWord_8082074, baseEnd_8082074] using wordTrace_append hprefix tailTrace_8082074
  have hstable : (prefixWord ++ tailWord_8082074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082074).length < 2 ^ (prefixWord ++ tailWord_8082074).sum := by decide
  have hdescent : baseEnd_8082074 < baseStart_8082074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082096 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 1, 4, 2]
def baseStart_8082096 : Nat := 118140960795 + 8082096 * 2 ^ 59
def prefixEnd_8082096 : Nat := 4983230072969 + 3 ^ 40 * 8082096 * 2
def baseEnd_8082096 : Nat := 4149999943780315995931123

theorem tailTrace_8082096 : CollatzResearch.WordTrace tailWord_8082096 prefixEnd_8082096 4149999943780315995931123 := by
  unfold tailWord_8082096
  simp only [CollatzResearch.WordTrace]
  refine ⟨147389129063976989474825071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196518838751969319299766761 147389129063976989474825071)
  ·
    refine ⟨221083693595965484212237607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147389129063976989474825071 221083693595965484212237607)
    ·
      refine ⟨331625540393948226318356411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221083693595965484212237607 331625540393948226318356411)
      ·
        refine ⟨497438310590922339477534617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331625540393948226318356411 497438310590922339477534617)
        ·
          refine ⟨373078732943191754608150963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497438310590922339477534617 373078732943191754608150963)
          ·
            refine ⟨559618099414787631912226445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373078732943191754608150963 559618099414787631912226445)
            ·
              refine ⟨209856787280545361967084917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559618099414787631912226445 209856787280545361967084917)
              ·
                refine ⟨19674073807551127684414211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209856787280545361967084917 19674073807551127684414211)
                ·
                  refine ⟨29511110711326691526621317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19674073807551127684414211 29511110711326691526621317)
                  ·
                    refine ⟨5533333258373754661241497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29511110711326691526621317 5533333258373754661241497)
                    ·
                      refine ⟨4149999943780315995931123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533333258373754661241497 4149999943780315995931123)
                      ·
                        rfl

theorem cell23_8082096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 1, 4, 2].length) (baseStart_8082096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082096 prefixEnd_8082096 := by exact prefixLift 8082096
  have htrace : WordTrace (prefixWord ++ tailWord_8082096) baseStart_8082096 baseEnd_8082096 := by
    simpa [prefixWord, tailWord_8082096, baseEnd_8082096] using wordTrace_append hprefix tailTrace_8082096
  have hstable : (prefixWord ++ tailWord_8082096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082096).length < 2 ^ (prefixWord ++ tailWord_8082096).sum := by decide
  have hdescent : baseEnd_8082096 < baseStart_8082096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082099 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 5]
def baseStart_8082099 : Nat := 118140960795 + 8082099 * 2 ^ 59
def prefixEnd_8082099 : Nat := 4983230072969 + 3 ^ 40 * 8082099 * 2
def baseEnd_8082099 : Nat := 4150001484222279484193609

theorem tailTrace_8082099 : CollatzResearch.WordTrace tailWord_8082099 prefixEnd_8082099 4150001484222279484193609 := by
  unfold tailWord_8082099
  simp only [CollatzResearch.WordTrace]
  refine ⟨294778367546943110462009351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196518911697962073641339567 294778367546943110462009351)
  ·
    refine ⟨442167551320414665693014027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294778367546943110462009351 442167551320414665693014027)
    ·
      refine ⟨663251326980621998539521041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442167551320414665693014027 663251326980621998539521041)
      ·
        refine ⟨497438495235466498904640781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 663251326980621998539521041 497438495235466498904640781)
        ·
          refine ⟨186539435713299937089240293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497438495235466498904640781 186539435713299937089240293)
          ·
            refine ⟨34976144196243738204232555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186539435713299937089240293 34976144196243738204232555)
            ·
              refine ⟨52464216294365607306348833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34976144196243738204232555 52464216294365607306348833)
              ·
                refine ⟨39348162220774205479761625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52464216294365607306348833 39348162220774205479761625)
                ·
                  refine ⟨29511121665580654109821219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39348162220774205479761625 29511121665580654109821219)
                  ·
                    refine ⟨44266682498370981164731829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29511121665580654109821219 44266682498370981164731829)
                    ·
                      refine ⟨4150001484222279484193609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44266682498370981164731829 4150001484222279484193609)
                      ·
                        rfl

theorem cell23_8082099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_8082099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082099 prefixEnd_8082099 := by exact prefixLift 8082099
  have htrace : WordTrace (prefixWord ++ tailWord_8082099) baseStart_8082099 baseEnd_8082099 := by
    simpa [prefixWord, tailWord_8082099, baseEnd_8082099] using wordTrace_append hprefix tailTrace_8082099
  have hstable : (prefixWord ++ tailWord_8082099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082099).length < 2 ^ (prefixWord ++ tailWord_8082099).sum := by decide
  have hdescent : baseEnd_8082099 < baseStart_8082099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082116 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_8082116 : Nat := 118140960795 + 8082116 * 2 ^ 59
def prefixEnd_8082116 : Nat := 4983230072969 + 3 ^ 40 * 8082116 * 2
def baseEnd_8082116 : Nat := 4150010213393405917681031

theorem tailTrace_8082116 : CollatzResearch.WordTrace tailWord_8082116 prefixEnd_8082116 4150010213393405917681031 := by
  unfold tailWord_8082116
  simp only [CollatzResearch.WordTrace]
  refine ⟨147389493793940761182689101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196519325058587681576918801 147389493793940761182689101)
  ·
    refine ⟨55271060172727785443508413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147389493793940761182689101 55271060172727785443508413)
    ·
      refine ⟨20726647564772919541315655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55271060172727785443508413 20726647564772919541315655)
      ·
        refine ⟨31089971347159379311973483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20726647564772919541315655 31089971347159379311973483)
        ·
          refine ⟨46634957020739068967960225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31089971347159379311973483 46634957020739068967960225)
          ·
            refine ⟨34976217765554301725970169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46634957020739068967960225 34976217765554301725970169)
            ·
              refine ⟨26232163324165726294477627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34976217765554301725970169 26232163324165726294477627)
              ·
                refine ⟨39348244986248589441716441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26232163324165726294477627 39348244986248589441716441)
                ·
                  refine ⟨29511183739686442081287331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39348244986248589441716441 29511183739686442081287331)
                  ·
                    refine ⟨44266775609529663121930997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29511183739686442081287331 44266775609529663121930997)
                    ·
                      refine ⟨4150010213393405917681031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44266775609529663121930997 4150010213393405917681031)
                      ·
                        rfl

theorem cell23_8082116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_8082116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082116 prefixEnd_8082116 := by exact prefixLift 8082116
  have htrace : WordTrace (prefixWord ++ tailWord_8082116) baseStart_8082116 baseEnd_8082116 := by
    simpa [prefixWord, tailWord_8082116, baseEnd_8082116] using wordTrace_append hprefix tailTrace_8082116
  have hstable : (prefixWord ++ tailWord_8082116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082116).length < 2 ^ (prefixWord ++ tailWord_8082116).sum := by decide
  have hdescent : baseEnd_8082116 < baseStart_8082116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082156 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 4, 5, 2]
def baseStart_8082156 : Nat := 118140960795 + 8082156 * 2 ^ 59
def prefixEnd_8082156 : Nat := 4983230072969 + 3 ^ 40 * 8082156 * 2
def baseEnd_8082156 : Nat := 4150030752619585761180847

theorem tailTrace_8082156 : CollatzResearch.WordTrace tailWord_8082156 prefixEnd_8082156 4150030752619585761180847 := by
  unfold tailWord_8082156
  simp only [CollatzResearch.WordTrace]
  refine ⟨147390223253868304598417161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196520297671824406131222881 147390223253868304598417161)
  ·
    refine ⟨110542667440401228448812871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147390223253868304598417161 110542667440401228448812871)
    ·
      refine ⟨165814001160601842673219307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110542667440401228448812871 165814001160601842673219307)
      ·
        refine ⟨248721001740902764009828961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165814001160601842673219307 248721001740902764009828961)
        ·
          refine ⟨186540751305677073007371721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248721001740902764009828961 186540751305677073007371721)
          ·
            refine ⟨139905563479257804755528791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186540751305677073007371721 139905563479257804755528791)
            ·
              refine ⟨209858345218886707133293187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139905563479257804755528791 209858345218886707133293187)
              ·
                refine ⟨314787517828330060699939781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209858345218886707133293187 314787517828330060699939781)
                ·
                  refine ⟨59022659592811886381238709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314787517828330060699939781 59022659592811886381238709)
                  ·
                    refine ⟨5533374336826114348241129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59022659592811886381238709 5533374336826114348241129)
                    ·
                      refine ⟨4150030752619585761180847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533374336826114348241129 4150030752619585761180847)
                      ·
                        rfl

theorem cell23_8082156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 5, 2].length) (baseStart_8082156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082156 prefixEnd_8082156 := by exact prefixLift 8082156
  have htrace : WordTrace (prefixWord ++ tailWord_8082156) baseStart_8082156 baseEnd_8082156 := by
    simpa [prefixWord, tailWord_8082156, baseEnd_8082156] using wordTrace_append hprefix tailTrace_8082156
  have hstable : (prefixWord ++ tailWord_8082156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082156).length < 2 ^ (prefixWord ++ tailWord_8082156).sum := by decide
  have hdescent : baseEnd_8082156 < baseStart_8082156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082166 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_8082166 : Nat := 118140960795 + 8082166 * 2 ^ 59
def prefixEnd_8082166 : Nat := 4983230072969 + 3 ^ 40 * 8082166 * 2
def baseEnd_8082166 : Nat := 1383345295808710240685267

theorem tailTrace_8082166 : CollatzResearch.WordTrace tailWord_8082166 prefixEnd_8082166 1383345295808710240685267 := by
  unfold tailWord_8082166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18423800702356273806543647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196520540825133587269798901 18423800702356273806543647)
  ·
    refine ⟨27635701053534410709815471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18423800702356273806543647 27635701053534410709815471)
    ·
      refine ⟨41453551580301616064723207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27635701053534410709815471 41453551580301616064723207)
      ·
        refine ⟨62180327370452424097084811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41453551580301616064723207 62180327370452424097084811)
        ·
          refine ⟨93270491055678636145627217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62180327370452424097084811 93270491055678636145627217)
          ·
            refine ⟨69952868291758977109220413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93270491055678636145627217 69952868291758977109220413)
            ·
              refine ⟨26232325609409616415957655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69952868291758977109220413 26232325609409616415957655)
              ·
                refine ⟨39348488414114424623936483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26232325609409616415957655 39348488414114424623936483)
                ·
                  refine ⟨59022732621171636935904725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39348488414114424623936483 59022732621171636935904725)
                  ·
                    refine ⟨1383345295808710240685267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59022732621171636935904725 1383345295808710240685267)
                    ·
                      rfl

theorem cell23_8082166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_8082166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082166 prefixEnd_8082166 := by exact prefixLift 8082166
  have htrace : WordTrace (prefixWord ++ tailWord_8082166) baseStart_8082166 baseEnd_8082166 := by
    simpa [prefixWord, tailWord_8082166, baseEnd_8082166] using wordTrace_append hprefix tailTrace_8082166
  have hstable : (prefixWord ++ tailWord_8082166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082166).length < 2 ^ (prefixWord ++ tailWord_8082166).sum := by decide
  have hdescent : baseEnd_8082166 < baseStart_8082166 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082186 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_8082186 : Nat := 118140960795 + 8082186 * 2 ^ 59
def prefixEnd_8082186 : Nat := 4983230072969 + 3 ^ 40 * 8082186 * 2
def baseEnd_8082186 : Nat := 4150046157039220643805709

theorem tailTrace_8082186 : CollatzResearch.WordTrace tailWord_8082186 prefixEnd_8082186 4150046157039220643805709 := by
  unfold tailWord_8082186
  simp only [CollatzResearch.WordTrace]
  refine ⟨73695385174406981080106603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196521027131751949546950941 73695385174406981080106603)
  ·
    refine ⟨110543077761610471620159905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73695385174406981080106603 110543077761610471620159905)
    ·
      refine ⟨82907308321207853715119929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110543077761610471620159905 82907308321207853715119929)
      ·
        refine ⟨62180481240905890286339947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82907308321207853715119929 62180481240905890286339947)
        ·
          refine ⟨93270721861358835429509921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62180481240905890286339947 93270721861358835429509921)
          ·
            refine ⟨69953041396019126572132441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93270721861358835429509921 69953041396019126572132441)
            ·
              refine ⟨52464781047014344929099331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69953041396019126572132441 52464781047014344929099331)
              ·
                refine ⟨78697171570521517393648997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52464781047014344929099331 78697171570521517393648997)
                ·
                  refine ⟨14755719669472784511309187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78697171570521517393648997 14755719669472784511309187)
                  ·
                    refine ⟨22133579504209176766963781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14755719669472784511309187 22133579504209176766963781)
                    ·
                      refine ⟨4150046157039220643805709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22133579504209176766963781 4150046157039220643805709)
                      ·
                        rfl

theorem cell23_8082186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_8082186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082186 prefixEnd_8082186 := by exact prefixLift 8082186
  have htrace : WordTrace (prefixWord ++ tailWord_8082186) baseStart_8082186 baseEnd_8082186 := by
    simpa [prefixWord, tailWord_8082186, baseEnd_8082186] using wordTrace_append hprefix tailTrace_8082186
  have hstable : (prefixWord ++ tailWord_8082186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082186).length < 2 ^ (prefixWord ++ tailWord_8082186).sum := by decide
  have hdescent : baseEnd_8082186 < baseStart_8082186 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082216 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_8082216 : Nat := 118140960795 + 8082216 * 2 ^ 59
def prefixEnd_8082216 : Nat := 4983230072969 + 3 ^ 40 * 8082216 * 2
def baseEnd_8082216 : Nat := 4150061561458855526430571

theorem tailTrace_8082216 : CollatzResearch.WordTrace tailWord_8082216 prefixEnd_8082216 4150061561458855526430571 := by
  unfold tailWord_8082216
  simp only [CollatzResearch.WordTrace]
  refine ⟨147391317443759619722009251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196521756591679492962679001 147391317443759619722009251)
  ·
    refine ⟨221086976165639429583013877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147391317443759619722009251 221086976165639429583013877)
    ·
      refine ⟨20726904015528696523407551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221086976165639429583013877 20726904015528696523407551)
      ·
        refine ⟨31090356023293044785111327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20726904015528696523407551 31090356023293044785111327)
        ·
          refine ⟨46635534034939567177666991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31090356023293044785111327 46635534034939567177666991)
          ·
            refine ⟨69953301052409350766500487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46635534034939567177666991 69953301052409350766500487)
            ·
              refine ⟨104929951578614026149750731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69953301052409350766500487 104929951578614026149750731)
              ·
                refine ⟨157394927367921039224626097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104929951578614026149750731 157394927367921039224626097)
                ·
                  refine ⟨118046195525940779418469573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157394927367921039224626097 118046195525940779418469573)
                  ·
                    refine ⟨22133661661113896140963045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118046195525940779418469573 22133661661113896140963045)
                    ·
                      refine ⟨4150061561458855526430571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22133661661113896140963045 4150061561458855526430571)
                      ·
                        rfl

theorem cell23_8082216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_8082216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082216 prefixEnd_8082216 := by exact prefixLift 8082216
  have htrace : WordTrace (prefixWord ++ tailWord_8082216) baseStart_8082216 baseEnd_8082216 := by
    simpa [prefixWord, tailWord_8082216, baseEnd_8082216] using wordTrace_append hprefix tailTrace_8082216
  have hstable : (prefixWord ++ tailWord_8082216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082216).length < 2 ^ (prefixWord ++ tailWord_8082216).sum := by decide
  have hdescent : baseEnd_8082216 < baseStart_8082216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082280 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_8082280 : Nat := 118140960795 + 8082280 * 2 ^ 59
def prefixEnd_8082280 : Nat := 4983230072969 + 3 ^ 40 * 8082280 * 2
def baseEnd_8082280 : Nat := 4150094424220743276030277

theorem tailTrace_8082280 : CollatzResearch.WordTrace tailWord_8082280 prefixEnd_8082280 4150094424220743276030277 := by
  unfold tailWord_8082280
  simp only [CollatzResearch.WordTrace]
  refine ⟨147392484579643689187174147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196523312772858252249565529 147392484579643689187174147)
  ·
    refine ⟨221088726869465533780761221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147392484579643689187174147 221088726869465533780761221)
    ·
      refine ⟨41454136288024787583892729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221088726869465533780761221 41454136288024787583892729)
      ·
        refine ⟨31090602216018590687919547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41454136288024787583892729 31090602216018590687919547)
        ·
          refine ⟨46635903324027886031879321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31090602216018590687919547 46635903324027886031879321)
          ·
            refine ⟨34976927493020914523909491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46635903324027886031879321 34976927493020914523909491)
            ·
              refine ⟨52465391239531371785864237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34976927493020914523909491 52465391239531371785864237)
              ·
                refine ⟨19674521714824264419699089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52465391239531371785864237 19674521714824264419699089)
                ·
                  refine ⟨14755891286118198314774317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19674521714824264419699089 14755891286118198314774317)
                  ·
                    refine ⟨5533459232294324368040369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14755891286118198314774317 5533459232294324368040369)
                    ·
                      refine ⟨4150094424220743276030277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533459232294324368040369 4150094424220743276030277)
                      ·
                        rfl

theorem cell23_8082280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_8082280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082280 prefixEnd_8082280 := by exact prefixLift 8082280
  have htrace : WordTrace (prefixWord ++ tailWord_8082280) baseStart_8082280 baseEnd_8082280 := by
    simpa [prefixWord, tailWord_8082280, baseEnd_8082280] using wordTrace_append hprefix tailTrace_8082280
  have hstable : (prefixWord ++ tailWord_8082280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082280).length < 2 ^ (prefixWord ++ tailWord_8082280).sum := by decide
  have hdescent : baseEnd_8082280 < baseStart_8082280 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082296 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 1, 1, 5]
def baseStart_8082296 : Nat := 118140960795 + 8082296 * 2 ^ 59
def prefixEnd_8082296 : Nat := 4983230072969 + 3 ^ 40 * 8082296 * 2
def baseEnd_8082296 : Nat := 4150102639911215213430203

theorem tailTrace_8082296 : CollatzResearch.WordTrace tailWord_8082296 prefixEnd_8082296 4150102639911215213430203 := by
  unfold tailWord_8082296
  simp only [CollatzResearch.WordTrace]
  refine ⟨147392776363614706553465371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196523701818152942071287161 147392776363614706553465371)
  ·
    refine ⟨221089164545422059830198057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147392776363614706553465371 221089164545422059830198057)
    ·
      refine ⟨165816873409066544872648543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221089164545422059830198057 165816873409066544872648543)
      ·
        refine ⟨248725310113599817308972815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165816873409066544872648543 248725310113599817308972815)
        ·
          refine ⟨373087965170399725963459223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248725310113599817308972815 373087965170399725963459223)
          ·
            refine ⟨559631947755599588945188835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373087965170399725963459223 559631947755599588945188835)
            ·
              refine ⟨839447921633399383417783253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559631947755599588945188835 839447921633399383417783253)
              ·
                refine ⟨19674560663282798048854295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 839447921633399383417783253 19674560663282798048854295)
                ·
                  refine ⟨29511840994924197073281443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19674560663282798048854295 29511840994924197073281443)
                  ·
                    refine ⟨44267761492386295609922165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29511840994924197073281443 44267761492386295609922165)
                    ·
                      refine ⟨4150102639911215213430203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44267761492386295609922165 4150102639911215213430203)
                      ·
                        rfl

theorem cell23_8082296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_8082296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082296 prefixEnd_8082296 := by exact prefixLift 8082296
  have htrace : WordTrace (prefixWord ++ tailWord_8082296) baseStart_8082296 baseEnd_8082296 := by
    simpa [prefixWord, tailWord_8082296, baseEnd_8082296] using wordTrace_append hprefix tailTrace_8082296
  have hstable : (prefixWord ++ tailWord_8082296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082296).length < 2 ^ (prefixWord ++ tailWord_8082296).sum := by decide
  have hdescent : baseEnd_8082296 < baseStart_8082296 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082303 : List Nat := [1, 1, 2, 2, 1, 1, 5, 4, 2, 4]
def baseStart_8082303 : Nat := 118140960795 + 8082303 * 2 ^ 59
def prefixEnd_8082303 : Nat := 4983230072969 + 3 ^ 40 * 8082303 * 2
def baseEnd_8082303 : Nat := 1383368744758598895347557

theorem tailTrace_8082303 : CollatzResearch.WordTrace tailWord_8082303 prefixEnd_8082303 1383368744758598895347557 := by
  unfold tailWord_8082303
  simp only [CollatzResearch.WordTrace]
  refine ⟨294785808038204053302435563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196523872025469368868290375 294785808038204053302435563)
  ·
    refine ⟨442178712057306079953653345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294785808038204053302435563 442178712057306079953653345)
    ·
      refine ⟨331634034042979559965240009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442178712057306079953653345 331634034042979559965240009)
      ·
        refine ⟨248725525532234669973930007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331634034042979559965240009 248725525532234669973930007)
        ·
          refine ⟨373088288298352004960895011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248725525532234669973930007 373088288298352004960895011)
          ·
            refine ⟨559632432447528007441342517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373088288298352004960895011 559632432447528007441342517)
            ·
              refine ⟨52465540541955750697625861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 559632432447528007441342517 52465540541955750697625861)
              ·
                refine ⟨9837288851616703255804849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52465540541955750697625861 9837288851616703255804849)
                ·
                  refine ⟨7377966638712527441853637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9837288851616703255804849 7377966638712527441853637)
                  ·
                    refine ⟨1383368744758598895347557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7377966638712527441853637 1383368744758598895347557)
                    ·
                      rfl

theorem cell23_8082303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 4].length) (baseStart_8082303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082303 prefixEnd_8082303 := by exact prefixLift 8082303
  have htrace : WordTrace (prefixWord ++ tailWord_8082303) baseStart_8082303 baseEnd_8082303 := by
    simpa [prefixWord, tailWord_8082303, baseEnd_8082303] using wordTrace_append hprefix tailTrace_8082303
  have hstable : (prefixWord ++ tailWord_8082303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082303).length < 2 ^ (prefixWord ++ tailWord_8082303).sum := by decide
  have hdescent : baseEnd_8082303 < baseStart_8082303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082313 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 3, 2, 3]
def baseStart_8082313 : Nat := 118140960795 + 8082313 * 2 ^ 59
def prefixEnd_8082313 : Nat := 4983230072969 + 3 ^ 40 * 8082313 * 2
def baseEnd_8082313 : Nat := 4150111369082341646917625

theorem tailTrace_8082313 : CollatzResearch.WordTrace tailWord_8082313 prefixEnd_8082313 4150111369082341646917625 := by
  unfold tailWord_8082313
  simp only [CollatzResearch.WordTrace]
  refine ⟨294786172768167825010299593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196524115178778550006866395 294786172768167825010299593)
  ·
    refine ⟨221089629576125868757724695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294786172768167825010299593 221089629576125868757724695)
    ·
      refine ⟨331634444364188803136587043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221089629576125868757724695 331634444364188803136587043)
      ·
        refine ⟨497451666546283204704880565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331634444364188803136587043 497451666546283204704880565)
        ·
          refine ⟨46636093738714050441082553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 497451666546283204704880565 46636093738714050441082553)
          ·
            refine ⟨34977070304035537830811915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46636093738714050441082553 34977070304035537830811915)
            ·
              refine ⟨52465605456053306746217873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34977070304035537830811915 52465605456053306746217873)
              ·
                refine ⟨39349204092039980059663405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52465605456053306746217873 39349204092039980059663405)
                ·
                  refine ⟨14755951534514992522373777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39349204092039980059663405 14755951534514992522373777)
                  ·
                    refine ⟨11066963650886244391780333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14755951534514992522373777 11066963650886244391780333)
                    ·
                      refine ⟨4150111369082341646917625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11066963650886244391780333 4150111369082341646917625)
                      ·
                        rfl

theorem cell23_8082313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 2, 3].length) (baseStart_8082313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082313 prefixEnd_8082313 := by exact prefixLift 8082313
  have htrace : WordTrace (prefixWord ++ tailWord_8082313) baseStart_8082313 baseEnd_8082313 := by
    simpa [prefixWord, tailWord_8082313, baseEnd_8082313] using wordTrace_append hprefix tailTrace_8082313
  have hstable : (prefixWord ++ tailWord_8082313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082313).length < 2 ^ (prefixWord ++ tailWord_8082313).sum := by decide
  have hdescent : baseEnd_8082313 < baseStart_8082313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082316 : List Nat := [2, 2, 1, 2, 1, 2, 5, 8]
def baseStart_8082316 : Nat := 118140960795 + 8082316 * 2 ^ 59
def prefixEnd_8082316 : Nat := 4983230072969 + 3 ^ 40 * 8082316 * 2
def baseEnd_8082316 : Nat := 153707885537937227228893

theorem tailTrace_8082316 : CollatzResearch.WordTrace tailWord_8082316 prefixEnd_8082316 153707885537937227228893 := by
  unfold tailWord_8082316
  simp only [CollatzResearch.WordTrace]
  refine ⟨147393141093578478261329401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196524188124771304348439201 147393141093578478261329401)
  ·
    refine ⟨110544855820183858695997051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147393141093578478261329401 110544855820183858695997051)
    ·
      refine ⟨165817283730275788043995577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110544855820183858695997051 165817283730275788043995577)
      ·
        refine ⟨124362962797706841032996683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165817283730275788043995577 124362962797706841032996683)
        ·
          refine ⟨186544444196560261549495025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124362962797706841032996683 186544444196560261549495025)
          ·
            refine ⟨139908333147420196162121269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186544444196560261549495025 139908333147420196162121269)
            ·
              refine ⟨13116406232570643390198869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139908333147420196162121269 13116406232570643390198869)
              ·
                refine ⟨153707885537937227228893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13116406232570643390198869 153707885537937227228893)
                ·
                  rfl

theorem cell23_8082316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 8].length) (baseStart_8082316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082316 prefixEnd_8082316 := by exact prefixLift 8082316
  have htrace : WordTrace (prefixWord ++ tailWord_8082316) baseStart_8082316 baseEnd_8082316 := by
    simpa [prefixWord, tailWord_8082316, baseEnd_8082316] using wordTrace_append hprefix tailTrace_8082316
  have hstable : (prefixWord ++ tailWord_8082316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082316).length < 2 ^ (prefixWord ++ tailWord_8082316).sum := by decide
  have hdescent : baseEnd_8082316 < baseStart_8082316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082333 : List Nat := [1, 4, 2, 1, 2, 1, 5, 7]
def baseStart_8082333 : Nat := 118140960795 + 8082333 * 2 ^ 59
def prefixEnd_8082333 : Nat := 4983230072969 + 3 ^ 40 * 8082333 * 2
def baseEnd_8082333 : Nat := 153708208840571539580279

theorem tailTrace_8082333 : CollatzResearch.WordTrace tailWord_8082333 prefixEnd_8082333 153708208840571539580279 := by
  unfold tailWord_8082333
  simp only [CollatzResearch.WordTrace]
  refine ⟨294786902228095368426027653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196524601485396912284018435 294786902228095368426027653)
  ·
    refine ⟨55272544167767881579880185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294786902228095368426027653 55272544167767881579880185)
    ·
      refine ⟨41454408125825911184910139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55272544167767881579880185 41454408125825911184910139)
      ·
        refine ⟨62181612188738866777365209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41454408125825911184910139 62181612188738866777365209)
        ·
          refine ⟨46636209141554150083023907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62181612188738866777365209 46636209141554150083023907)
          ·
            refine ⟨69954313712331225124535861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46636209141554150083023907 69954313712331225124535861)
            ·
              refine ⟨6558216910531052355425237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69954313712331225124535861 6558216910531052355425237)
              ·
                refine ⟨153708208840571539580279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6558216910531052355425237 153708208840571539580279)
                ·
                  rfl

theorem cell23_8082333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 7].length) (baseStart_8082333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082333 prefixEnd_8082333 := by exact prefixLift 8082333
  have htrace : WordTrace (prefixWord ++ tailWord_8082333) baseStart_8082333 baseEnd_8082333 := by
    simpa [prefixWord, tailWord_8082333, baseEnd_8082333] using wordTrace_append hprefix tailTrace_8082333
  have hstable : (prefixWord ++ tailWord_8082333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082333).length < 2 ^ (prefixWord ++ tailWord_8082333).sum := by decide
  have hdescent : baseEnd_8082333 < baseStart_8082333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082360 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 4, 1, 3]
def baseStart_8082360 : Nat := 118140960795 + 8082360 * 2 ^ 59
def prefixEnd_8082360 : Nat := 4983230072969 + 3 ^ 40 * 8082360 * 2
def baseEnd_8082360 : Nat := 4150135502673102963029909

theorem tailTrace_8082360 : CollatzResearch.WordTrace tailWord_8082360 prefixEnd_8082360 4150135502673102963029909 := by
  unfold tailWord_8082360
  simp only [CollatzResearch.WordTrace]
  refine ⟨147393943499498776018630267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196525257999331701358173689 147393943499498776018630267)
  ·
    refine ⟨221090915249248164027945401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147393943499498776018630267 221090915249248164027945401)
    ·
      refine ⟨165818186436936123020959051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221090915249248164027945401 165818186436936123020959051)
      ·
        refine ⟨248727279655404184531438577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165818186436936123020959051 248727279655404184531438577)
        ·
          refine ⟨186545459741553138398578933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248727279655404184531438577 186545459741553138398578933)
          ·
            refine ⟨17488636850770606724866775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186545459741553138398578933 17488636850770606724866775)
            ·
              refine ⟨26232955276155910087300163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17488636850770606724866775 26232955276155910087300163)
              ·
                refine ⟨39349432914233865130950245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26232955276155910087300163 39349432914233865130950245)
                ·
                  refine ⟨7378018671418849712053171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39349432914233865130950245 7378018671418849712053171)
                  ·
                    refine ⟨11067028007128274568079757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7378018671418849712053171 11067028007128274568079757)
                    ·
                      refine ⟨4150135502673102963029909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11067028007128274568079757 4150135502673102963029909)
                      ·
                        rfl

theorem cell23_8082360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_8082360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082360 prefixEnd_8082360 := by exact prefixLift 8082360
  have htrace : WordTrace (prefixWord ++ tailWord_8082360) baseStart_8082360 baseEnd_8082360 := by
    simpa [prefixWord, tailWord_8082360, baseEnd_8082360] using wordTrace_append hprefix tailTrace_8082360
  have hstable : (prefixWord ++ tailWord_8082360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082360).length < 2 ^ (prefixWord ++ tailWord_8082360).sum := by decide
  have hdescent : baseEnd_8082360 < baseStart_8082360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082390 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_8082390 : Nat := 118140960795 + 8082390 * 2 ^ 59
def prefixEnd_8082390 : Nat := 4983230072969 + 3 ^ 40 * 8082390 * 2
def baseEnd_8082390 : Nat := 4150150907092737845654771

theorem tailTrace_8082390 : CollatzResearch.WordTrace tailWord_8082390 prefixEnd_8082390 4150150907092737845654771 := by
  unfold tailWord_8082390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18424311324305554197553289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196525987459259244773901749 18424311324305554197553289)
  ·
    refine ⟨13818233493229165648164967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18424311324305554197553289 13818233493229165648164967)
    ·
      refine ⟨20727350239843748472247451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13818233493229165648164967 20727350239843748472247451)
      ·
        refine ⟨31091025359765622708371177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20727350239843748472247451 31091025359765622708371177)
        ·
          refine ⟨23318269019824217031278383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31091025359765622708371177 23318269019824217031278383)
          ·
            refine ⟨34977403529736325546917575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23318269019824217031278383 34977403529736325546917575)
            ·
              refine ⟨52466105294604488320376363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34977403529736325546917575 52466105294604488320376363)
              ·
                refine ⟨78699157941906732480564545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52466105294604488320376363 78699157941906732480564545)
                ·
                  refine ⟨59024368456430049360423409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78699157941906732480564545 59024368456430049360423409)
                  ·
                    refine ⟨44268276342322537020317557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59024368456430049360423409 44268276342322537020317557)
                    ·
                      refine ⟨4150150907092737845654771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44268276342322537020317557 4150150907092737845654771)
                      ·
                        rfl

theorem cell23_8082390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_8082390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082390 prefixEnd_8082390 := by exact prefixLift 8082390
  have htrace : WordTrace (prefixWord ++ tailWord_8082390) baseStart_8082390 baseEnd_8082390 := by
    simpa [prefixWord, tailWord_8082390, baseEnd_8082390] using wordTrace_append hprefix tailTrace_8082390
  have hstable : (prefixWord ++ tailWord_8082390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082390).length < 2 ^ (prefixWord ++ tailWord_8082390).sum := by decide
  have hdescent : baseEnd_8082390 < baseStart_8082390 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082403 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 5]
def baseStart_8082403 : Nat := 118140960795 + 8082403 * 2 ^ 59
def prefixEnd_8082403 : Nat := 4983230072969 + 3 ^ 40 * 8082403 * 2
def baseEnd_8082403 : Nat := 4150157582341246294792211

theorem tailTrace_8082403 : CollatzResearch.WordTrace tailWord_8082403 prefixEnd_8082403 4150157582341246294792211 := by
  unfold tailWord_8082403
  simp only [CollatzResearch.WordTrace]
  refine ⟨294789455337841770381075863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196526303558561180254050575 294789455337841770381075863)
  ·
    refine ⟨442184183006762655571613795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294789455337841770381075863 442184183006762655571613795)
    ·
      refine ⟨663276274510143983357420693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442184183006762655571613795 663276274510143983357420693)
      ·
        refine ⟨31091075367662999219879095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 663276274510143983357420693 31091075367662999219879095)
        ·
          refine ⟨46636613051494498829818643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31091075367662999219879095 46636613051494498829818643)
          ·
            refine ⟨69954919577241748244727965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46636613051494498829818643 69954919577241748244727965)
            ·
              refine ⟨26233094841465655591772987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69954919577241748244727965 26233094841465655591772987)
              ·
                refine ⟨39349642262198483387659481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26233094841465655591772987 39349642262198483387659481)
                ·
                  refine ⟨29512231696648862540744611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39349642262198483387659481 29512231696648862540744611)
                  ·
                    refine ⟨44268347544973293811116917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29512231696648862540744611 44268347544973293811116917)
                    ·
                      refine ⟨4150157582341246294792211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44268347544973293811116917 4150157582341246294792211)
                      ·
                        rfl

theorem cell23_8082403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_8082403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082403 prefixEnd_8082403 := by exact prefixLift 8082403
  have htrace : WordTrace (prefixWord ++ tailWord_8082403) baseStart_8082403 baseEnd_8082403 := by
    simpa [prefixWord, tailWord_8082403, baseEnd_8082403] using wordTrace_append hprefix tailTrace_8082403
  have hstable : (prefixWord ++ tailWord_8082403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082403).length < 2 ^ (prefixWord ++ tailWord_8082403).sum := by decide
  have hdescent : baseEnd_8082403 < baseStart_8082403 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082416 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 9]
def baseStart_8082416 : Nat := 118140960795 + 8082416 * 2 ^ 59
def prefixEnd_8082416 : Nat := 4983230072969 + 3 ^ 40 * 8082416 * 2
def baseEnd_8082416 : Nat := 4150164257589754743929651

theorem tailTrace_8082416 : CollatzResearch.WordTrace tailWord_8082416 prefixEnd_8082416 4150164257589754743929651 := by
  unfold tailWord_8082416
  simp only [CollatzResearch.WordTrace]
  refine ⟨147394964743397336800649551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196526619657863115734199401 147394964743397336800649551)
  ·
    refine ⟨221092447115096005200974327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147394964743397336800649551 221092447115096005200974327)
    ·
      refine ⟨331638670672644007801461491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221092447115096005200974327 331638670672644007801461491)
      ·
        refine ⟨497458006008966011702192237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331638670672644007801461491 497458006008966011702192237)
        ·
          refine ⟨186546752253362254388322089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497458006008966011702192237 186546752253362254388322089)
          ·
            refine ⟨139910064190021690791241567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186546752253362254388322089 139910064190021690791241567)
            ·
              refine ⟨209865096285032536186862351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139910064190021690791241567 209865096285032536186862351)
              ·
                refine ⟨314797644427548804280293527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209865096285032536186862351 314797644427548804280293527)
                ·
                  refine ⟨472196466641323206420440291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314797644427548804280293527 472196466641323206420440291)
                  ·
                    refine ⟨708294699961984809630660437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 472196466641323206420440291 708294699961984809630660437)
                    ·
                      refine ⟨4150164257589754743929651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 708294699961984809630660437 4150164257589754743929651)
                      ·
                        rfl

theorem cell23_8082416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_8082416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082416 prefixEnd_8082416 := by exact prefixLift 8082416
  have htrace : WordTrace (prefixWord ++ tailWord_8082416) baseStart_8082416 baseEnd_8082416 := by
    simpa [prefixWord, tailWord_8082416, baseEnd_8082416] using wordTrace_append hprefix tailTrace_8082416
  have hstable : (prefixWord ++ tailWord_8082416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082416).length < 2 ^ (prefixWord ++ tailWord_8082416).sum := by decide
  have hdescent : baseEnd_8082416 < baseStart_8082416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082417 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 4, 2, 2]
def baseStart_8082417 : Nat := 118140960795 + 8082417 * 2 ^ 59
def prefixEnd_8082417 : Nat := 4983230072969 + 3 ^ 40 * 8082417 * 2
def baseEnd_8082417 : Nat := 4150164771070409240017147

theorem tailTrace_8082417 : CollatzResearch.WordTrace tailWord_8082417 prefixEnd_8082417 4150164771070409240017147 := by
  unfold tailWord_8082417
  simp only [CollatzResearch.WordTrace]
  refine ⟨294789965959791050772085505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196526643973194033848057003 294789965959791050772085505)
  ·
    refine ⟨221092474469843288079064129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294789965959791050772085505 221092474469843288079064129)
    ·
      refine ⟨165819355852382466059298097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221092474469843288079064129 165819355852382466059298097)
      ·
        refine ⟨124364516889286849544473573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165819355852382466059298097 124364516889286849544473573)
        ·
          refine ⟨23318346916741284289588795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124364516889286849544473573 23318346916741284289588795)
          ·
            refine ⟨34977520375111926434383193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23318346916741284289588795 34977520375111926434383193)
            ·
              refine ⟨26233140281333944825787395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34977520375111926434383193 26233140281333944825787395)
              ·
                refine ⟨39349710422000917238681093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26233140281333944825787395 39349710422000917238681093)
                ·
                  refine ⟨7378070704125171982252705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39349710422000917238681093 7378070704125171982252705)
                  ·
                    refine ⟨5533553028093878986689529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7378070704125171982252705 5533553028093878986689529)
                    ·
                      refine ⟨4150164771070409240017147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533553028093878986689529 4150164771070409240017147)
                      ·
                        rfl

theorem cell23_8082417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_8082417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082417 prefixEnd_8082417 := by exact prefixLift 8082417
  have htrace : WordTrace (prefixWord ++ tailWord_8082417) baseStart_8082417 baseEnd_8082417 := by
    simpa [prefixWord, tailWord_8082417, baseEnd_8082417] using wordTrace_append hprefix tailTrace_8082417
  have hstable : (prefixWord ++ tailWord_8082417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082417).length < 2 ^ (prefixWord ++ tailWord_8082417).sum := by decide
  have hdescent : baseEnd_8082417 < baseStart_8082417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082463 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 5]
def baseStart_8082463 : Nat := 118140960795 + 8082463 * 2 ^ 59
def prefixEnd_8082463 : Nat := 4983230072969 + 3 ^ 40 * 8082463 * 2
def baseEnd_8082463 : Nat := 4150188391180516060041935

theorem tailTrace_8082463 : CollatzResearch.WordTrace tailWord_8082463 prefixEnd_8082463 4150188391180516060041935 := by
  unfold tailWord_8082463
  simp only [CollatzResearch.WordTrace]
  refine ⟨294791643717624400628260043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196527762478416267085506695 294791643717624400628260043)
  ·
    refine ⟨442187465576436600942390065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294791643717624400628260043 442187465576436600942390065)
    ·
      refine ⟨331640599182327450706792549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442187465576436600942390065 331640599182327450706792549)
      ·
        refine ⟨62182612346686397007523603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331640599182327450706792549 62182612346686397007523603)
        ·
          refine ⟨93273918520029595511285405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62182612346686397007523603 93273918520029595511285405)
          ·
            refine ⟨34977719445011098316732027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93273918520029595511285405 34977719445011098316732027)
            ·
              refine ⟨52466579167516647475098041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34977719445011098316732027 52466579167516647475098041)
              ·
                refine ⟨39349934375637485606323531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52466579167516647475098041 39349934375637485606323531)
                ·
                  refine ⟨59024901563456228409485297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39349934375637485606323531 59024901563456228409485297)
                  ·
                    refine ⟨44268676172592171307113973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59024901563456228409485297 44268676172592171307113973)
                    ·
                      refine ⟨4150188391180516060041935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44268676172592171307113973 4150188391180516060041935)
                      ·
                        rfl

theorem cell23_8082463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_8082463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082463 prefixEnd_8082463 := by exact prefixLift 8082463
  have htrace : WordTrace (prefixWord ++ tailWord_8082463) baseStart_8082463 baseEnd_8082463 := by
    simpa [prefixWord, tailWord_8082463, baseEnd_8082463] using wordTrace_append hprefix tailTrace_8082463
  have hstable : (prefixWord ++ tailWord_8082463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082463).length < 2 ^ (prefixWord ++ tailWord_8082463).sum := by decide
  have hdescent : baseEnd_8082463 < baseStart_8082463 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082490 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2]
def baseStart_8082490 : Nat := 118140960795 + 8082490 * 2 ^ 59
def prefixEnd_8082490 : Nat := 4983230072969 + 3 ^ 40 * 8082490 * 2
def baseEnd_8082490 : Nat := 4150202255158187454404311

theorem tailTrace_8082490 : CollatzResearch.WordTrace tailWord_8082490 prefixEnd_8082490 4150202255158187454404311 := by
  unfold tailWord_8082490
  simp only [CollatzResearch.WordTrace]
  refine ⟨73698157122131646059873231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196528418992351056159661949 73698157122131646059873231)
  ·
    refine ⟨110547235683197469089809847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73698157122131646059873231 110547235683197469089809847)
    ·
      refine ⟨165820853524796203634714771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110547235683197469089809847 165820853524796203634714771)
      ·
        refine ⟨248731280287194305452072157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165820853524796203634714771 248731280287194305452072157)
        ·
          refine ⟨93274230107697864544527059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248731280287194305452072157 93274230107697864544527059)
          ·
            refine ⟨139911345161546796816790589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93274230107697864544527059 139911345161546796816790589)
            ·
              refine ⟨52466754435580048806296471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139911345161546796816790589 52466754435580048806296471)
              ·
                refine ⟨78700131653370073209444707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52466754435580048806296471 78700131653370073209444707)
                ·
                  refine ⟨118050197480055109814167061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78700131653370073209444707 118050197480055109814167061)
                  ·
                    refine ⟨5533603006877583272539081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118050197480055109814167061 5533603006877583272539081)
                    ·
                      refine ⟨4150202255158187454404311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533603006877583272539081 4150202255158187454404311)
                      ·
                        rfl

theorem cell23_8082490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2].length) (baseStart_8082490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082490 prefixEnd_8082490 := by exact prefixLift 8082490
  have htrace : WordTrace (prefixWord ++ tailWord_8082490) baseStart_8082490 baseEnd_8082490 := by
    simpa [prefixWord, tailWord_8082490, baseEnd_8082490] using wordTrace_append hprefix tailTrace_8082490
  have hstable : (prefixWord ++ tailWord_8082490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082490).length < 2 ^ (prefixWord ++ tailWord_8082490).sum := by decide
  have hdescent : baseEnd_8082490 < baseStart_8082490 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082510 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_8082510 : Nat := 118140960795 + 8082510 * 2 ^ 59
def prefixEnd_8082510 : Nat := 4983230072969 + 3 ^ 40 * 8082510 * 2
def baseEnd_8082510 : Nat := 4150212524771277376154219

theorem tailTrace_8082510 : CollatzResearch.WordTrace tailWord_8082510 prefixEnd_8082510 4150212524771277376154219 := by
  unfold tailWord_8082510
  simp only [CollatzResearch.WordTrace]
  refine ⟨36849169743556765956902623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196528905298969418436813989 36849169743556765956902623)
  ·
    refine ⟨55273754615335148935353935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36849169743556765956902623 55273754615335148935353935)
    ·
      refine ⟨82910631923002723403030903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55273754615335148935353935 82910631923002723403030903)
      ·
        refine ⟨124365947884504085104546355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82910631923002723403030903 124365947884504085104546355)
        ·
          refine ⟨186548921826756127656819533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124365947884504085104546355 186548921826756127656819533)
          ·
            refine ⟨69955845685033547871307325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186548921826756127656819533 69955845685033547871307325)
            ·
              refine ⟨26233442131887580451740247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69955845685033547871307325 26233442131887580451740247)
              ·
                refine ⟨39350163197831370677610371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26233442131887580451740247 39350163197831370677610371)
                ·
                  refine ⟨59025244796747056016415557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39350163197831370677610371 59025244796747056016415557)
                  ·
                    refine ⟨11067233399390073003077917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59025244796747056016415557 11067233399390073003077917)
                    ·
                      refine ⟨4150212524771277376154219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11067233399390073003077917 4150212524771277376154219)
                      ·
                        rfl

theorem cell23_8082510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_8082510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082510 prefixEnd_8082510 := by exact prefixLift 8082510
  have htrace : WordTrace (prefixWord ++ tailWord_8082510) baseStart_8082510 baseEnd_8082510 := by
    simpa [prefixWord, tailWord_8082510, baseEnd_8082510] using wordTrace_append hprefix tailTrace_8082510
  have hstable : (prefixWord ++ tailWord_8082510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082510).length < 2 ^ (prefixWord ++ tailWord_8082510).sum := by decide
  have hdescent : baseEnd_8082510 < baseStart_8082510 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082533 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_8082533 : Nat := 118140960795 + 8082533 * 2 ^ 59
def prefixEnd_8082533 : Nat := 4983230072969 + 3 ^ 40 * 8082533 * 2
def baseEnd_8082533 : Nat := 4150224334826330786166613

theorem tailTrace_8082533 : CollatzResearch.WordTrace tailWord_8082533 prefixEnd_8082533 4150224334826330786166613 := by
  unfold tailWord_8082533
  simp only [CollatzResearch.WordTrace]
  refine ⟨294794196827370802583308253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196529464551580535055538835 294794196827370802583308253)
  ·
    refine ⟨110547823810264050968740595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294794196827370802583308253 110547823810264050968740595)
    ·
      refine ⟨165821735715396076453110893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110547823810264050968740595 165821735715396076453110893)
      ·
        refine ⟨62183150893273528669916585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165821735715396076453110893 62183150893273528669916585)
        ·
          refine ⟨46637363169955146502437439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62183150893273528669916585 46637363169955146502437439)
          ·
            refine ⟨69956044754932719753656159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46637363169955146502437439 69956044754932719753656159)
            ·
              refine ⟨104934067132399079630484239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69956044754932719753656159 104934067132399079630484239)
              ·
                refine ⟨157401100698598619445726359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104934067132399079630484239 157401100698598619445726359)
                ·
                  refine ⟨236101651047897929168589539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157401100698598619445726359 236101651047897929168589539)
                  ·
                    refine ⟨354152476571846893752884309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 236101651047897929168589539 354152476571846893752884309)
                    ·
                      refine ⟨4150224334826330786166613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 354152476571846893752884309 4150224334826330786166613)
                      ·
                        rfl

theorem cell23_8082533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_8082533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082533 prefixEnd_8082533 := by exact prefixLift 8082533
  have htrace : WordTrace (prefixWord ++ tailWord_8082533) baseStart_8082533 baseEnd_8082533 := by
    simpa [prefixWord, tailWord_8082533, baseEnd_8082533] using wordTrace_append hprefix tailTrace_8082533
  have hstable : (prefixWord ++ tailWord_8082533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082533).length < 2 ^ (prefixWord ++ tailWord_8082533).sum := by decide
  have hdescent : baseEnd_8082533 < baseStart_8082533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082550 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_8082550 : Nat := 118140960795 + 8082550 * 2 ^ 59
def prefixEnd_8082550 : Nat := 4983230072969 + 3 ^ 40 * 8082550 * 2
def baseEnd_8082550 : Nat := 4150233063997457219654035

theorem tailTrace_8082550 : CollatzResearch.WordTrace tailWord_8082550 prefixEnd_8082550 4150233063997457219654035 := by
  unfold tailWord_8082550
  simp only [CollatzResearch.WordTrace]
  refine ⟨18424676054269325905417319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196529877912206142991118069 18424676054269325905417319)
  ·
    refine ⟨27637014081403988858125979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18424676054269325905417319 27637014081403988858125979)
    ·
      refine ⟨41455521122105983287188969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27637014081403988858125979 41455521122105983287188969)
      ·
        refine ⟨31091640841579487465391727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41455521122105983287188969 31091640841579487465391727)
        ·
          refine ⟨46637461262369231198087591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31091640841579487465391727 46637461262369231198087591)
          ·
            refine ⟨69956191893553846797131387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46637461262369231198087591 69956191893553846797131387)
            ·
              refine ⟨104934287840330770195697081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69956191893553846797131387 104934287840330770195697081)
              ·
                refine ⟨78700715880248077646772811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104934287840330770195697081 78700715880248077646772811)
                ·
                  refine ⟨118051073820372116470159217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78700715880248077646772811 118051073820372116470159217)
                  ·
                    refine ⟨88538305365279087352619413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118051073820372116470159217 88538305365279087352619413)
                    ·
                      refine ⟨4150233063997457219654035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88538305365279087352619413 4150233063997457219654035)
                      ·
                        rfl

theorem cell23_8082550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_8082550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082550 prefixEnd_8082550 := by exact prefixLift 8082550
  have htrace : WordTrace (prefixWord ++ tailWord_8082550) baseStart_8082550 baseEnd_8082550 := by
    simpa [prefixWord, tailWord_8082550, baseEnd_8082550] using wordTrace_append hprefix tailTrace_8082550
  have hstable : (prefixWord ++ tailWord_8082550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082550).length < 2 ^ (prefixWord ++ tailWord_8082550).sum := by decide
  have hdescent : baseEnd_8082550 < baseStart_8082550 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082557 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 3, 1, 3]
def baseStart_8082557 : Nat := 118140960795 + 8082557 * 2 ^ 59
def prefixEnd_8082557 : Nat := 4983230072969 + 3 ^ 40 * 8082557 * 2
def baseEnd_8082557 : Nat := 4150236658362038692266503

theorem tailTrace_8082557 : CollatzResearch.WordTrace tailWord_8082557 prefixEnd_8082557 4150236658362038692266503 := by
  unfold tailWord_8082557
  simp only [CollatzResearch.WordTrace]
  refine ⟨294795072179283854682181925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196530048119522569788121283 294795072179283854682181925)
  ·
    refine ⟨55274076033615722752909111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294795072179283854682181925 55274076033615722752909111)
    ·
      refine ⟨82911114050423584129363667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55274076033615722752909111 82911114050423584129363667)
      ·
        refine ⟨124366671075635376194045501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82911114050423584129363667 124366671075635376194045501)
        ·
          refine ⟨46637501653363266072767063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124366671075635376194045501 46637501653363266072767063)
          ·
            refine ⟨69956252480044899109150595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46637501653363266072767063 69956252480044899109150595)
            ·
              refine ⟨104934378720067348663725893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69956252480044899109150595 104934378720067348663725893)
              ·
                refine ⟨19675196010012627874448605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104934378720067348663725893 19675196010012627874448605)
                ·
                  refine ⟨7378198503754735452918227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19675196010012627874448605 7378198503754735452918227)
                  ·
                    refine ⟨11067297755632103179377341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7378198503754735452918227 11067297755632103179377341)
                    ·
                      refine ⟨4150236658362038692266503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11067297755632103179377341 4150236658362038692266503)
                      ·
                        rfl

theorem cell23_8082557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_8082557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082557 prefixEnd_8082557 := by exact prefixLift 8082557
  have htrace : WordTrace (prefixWord ++ tailWord_8082557) baseStart_8082557 baseEnd_8082557 := by
    simpa [prefixWord, tailWord_8082557, baseEnd_8082557] using wordTrace_append hprefix tailTrace_8082557
  have hstable : (prefixWord ++ tailWord_8082557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082557).length < 2 ^ (prefixWord ++ tailWord_8082557).sum := by decide
  have hdescent : baseEnd_8082557 < baseStart_8082557 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082560 : List Nat := [2, 1, 1, 2, 1, 3, 3, 4, 1, 5]
def baseStart_8082560 : Nat := 118140960795 + 8082560 * 2 ^ 59
def prefixEnd_8082560 : Nat := 4983230072969 + 3 ^ 40 * 8082560 * 2
def baseEnd_8082560 : Nat := 1383412732934667393509663

theorem tailTrace_8082560 : CollatzResearch.WordTrace tailWord_8082560 prefixEnd_8082560 1383412732934667393509663 := by
  unfold tailWord_8082560
  simp only [CollatzResearch.WordTrace]
  refine ⟨147397590799136493097270567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196530121065515324129694089 147397590799136493097270567)
  ·
    refine ⟨221096386198704739645905851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147397590799136493097270567 221096386198704739645905851)
    ·
      refine ⟨331644579298057109468858777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221096386198704739645905851 331644579298057109468858777)
      ·
        refine ⟨248733434473542832101644083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331644579298057109468858777 248733434473542832101644083)
        ·
          refine ⟨373100151710314248152466125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248733434473542832101644083 373100151710314248152466125)
          ·
            refine ⟨139912556891367843057174797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373100151710314248152466125 139912556891367843057174797)
            ·
              refine ⟨52467208834262941146440549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139912556891367843057174797 52467208834262941146440549)
              ·
                refine ⟨9837601656424301464957603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52467208834262941146440549 9837601656424301464957603)
                ·
                  refine ⟨14756402484636452197436405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9837601656424301464957603 14756402484636452197436405)
                  ·
                    refine ⟨1383412732934667393509663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14756402484636452197436405 1383412732934667393509663)
                    ·
                      rfl

theorem cell23_8082560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 1, 5].length) (baseStart_8082560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082560 prefixEnd_8082560 := by exact prefixLift 8082560
  have htrace : WordTrace (prefixWord ++ tailWord_8082560) baseStart_8082560 baseEnd_8082560 := by
    simpa [prefixWord, tailWord_8082560, baseEnd_8082560] using wordTrace_append hprefix tailTrace_8082560
  have hstable : (prefixWord ++ tailWord_8082560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082560).length < 2 ^ (prefixWord ++ tailWord_8082560).sum := by decide
  have hdescent : baseEnd_8082560 < baseStart_8082560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082567 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 2, 3, 2]
def baseStart_8082567 : Nat := 118140960795 + 8082567 * 2 ^ 59
def prefixEnd_8082567 : Nat := 4983230072969 + 3 ^ 40 * 8082567 * 2
def baseEnd_8082567 : Nat := 4150241793168583653141457

theorem tailTrace_8082567 : CollatzResearch.WordTrace tailWord_8082567 prefixEnd_8082567 4150241793168583653141457 := by
  unfold tailWord_8082567
  simp only [CollatzResearch.WordTrace]
  refine ⟨294795436909247626390045955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196530291272831750926697303 294795436909247626390045955)
  ·
    refine ⟨442193155363871439585068933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294795436909247626390045955 442193155363871439585068933)
    ·
      refine ⟨82911216630725894922200425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442193155363871439585068933 82911216630725894922200425)
      ·
        refine ⟨62183412473044421191650319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82911216630725894922200425 62183412473044421191650319)
        ·
          refine ⟨93275118709566631787475479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62183412473044421191650319 93275118709566631787475479)
          ·
            refine ⟨139912678064349947681213219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93275118709566631787475479 139912678064349947681213219)
            ·
              refine ⟨209869017096524921521819829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139912678064349947681213219 209869017096524921521819829)
              ·
                refine ⟨19675220352799211392670609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209869017096524921521819829 19675220352799211392670609)
                ·
                  refine ⟨14756415264599408544502957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19675220352799211392670609 14756415264599408544502957)
                  ·
                    refine ⟨5533655724224778204188609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14756415264599408544502957 5533655724224778204188609)
                    ·
                      refine ⟨4150241793168583653141457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533655724224778204188609 4150241793168583653141457)
                      ·
                        rfl

theorem cell23_8082567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_8082567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082567 prefixEnd_8082567 := by exact prefixLift 8082567
  have htrace : WordTrace (prefixWord ++ tailWord_8082567) baseStart_8082567 baseEnd_8082567 := by
    simpa [prefixWord, tailWord_8082567, baseEnd_8082567] using wordTrace_append hprefix tailTrace_8082567
  have hstable : (prefixWord ++ tailWord_8082567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082567).length < 2 ^ (prefixWord ++ tailWord_8082567).sum := by decide
  have hdescent : baseEnd_8082567 < baseStart_8082567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082568 : List Nat := [2, 1, 3, 4, 3, 1, 1, 3, 1, 4]
def baseStart_8082568 : Nat := 118140960795 + 8082568 * 2 ^ 59
def prefixEnd_8082568 : Nat := 4983230072969 + 3 ^ 40 * 8082568 * 2
def baseEnd_8082568 : Nat := 1383414102216412716409651

theorem tailTrace_8082568 : CollatzResearch.WordTrace tailWord_8082568 prefixEnd_8082568 1383414102216412716409651 := by
  unfold tailWord_8082568
  simp only [CollatzResearch.WordTrace]
  refine ⟨147397736691122001780416179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196530315588162669040554905 147397736691122001780416179)
  ·
    refine ⟨221096605036683002670624269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147397736691122001780416179 221096605036683002670624269)
    ·
      refine ⟨82911226888756126001484101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221096605036683002670624269 82911226888756126001484101)
      ·
        refine ⟨15545855041641773625278269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82911226888756126001484101 15545855041641773625278269)
        ·
          refine ⟨5829695640615665109479351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15545855041641773625278269 5829695640615665109479351)
          ·
            refine ⟨8744543460923497664219027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5829695640615665109479351 8744543460923497664219027)
            ·
              refine ⟨13116815191385246496328541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8744543460923497664219027 13116815191385246496328541)
              ·
                refine ⟨4918805696769467436123203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13116815191385246496328541 4918805696769467436123203)
                ·
                  refine ⟨7378208545154201154184805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918805696769467436123203 7378208545154201154184805)
                  ·
                    refine ⟨1383414102216412716409651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7378208545154201154184805 1383414102216412716409651)
                    ·
                      rfl

theorem cell23_8082568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_8082568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082568 prefixEnd_8082568 := by exact prefixLift 8082568
  have htrace : WordTrace (prefixWord ++ tailWord_8082568) baseStart_8082568 baseEnd_8082568 := by
    simpa [prefixWord, tailWord_8082568, baseEnd_8082568] using wordTrace_append hprefix tailTrace_8082568
  have hstable : (prefixWord ++ tailWord_8082568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082568).length < 2 ^ (prefixWord ++ tailWord_8082568).sum := by decide
  have hdescent : baseEnd_8082568 < baseStart_8082568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082584 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 2, 3, 2]
def baseStart_8082584 : Nat := 118140960795 + 8082584 * 2 ^ 59
def prefixEnd_8082584 : Nat := 4983230072969 + 3 ^ 40 * 8082584 * 2
def baseEnd_8082584 : Nat := 4150250522339710086628879

theorem tailTrace_8082584 : CollatzResearch.WordTrace tailWord_8082584 prefixEnd_8082584 4150250522339710086628879 := by
  unfold tailWord_8082584
  simp only [CollatzResearch.WordTrace]
  refine ⟨147398028475093019146707403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196530704633457358862276537 147398028475093019146707403)
  ·
    refine ⟨221097042712639528720061105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147398028475093019146707403 221097042712639528720061105)
    ·
      refine ⟨165822782034479646540045829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221097042712639528720061105 165822782034479646540045829)
      ·
        refine ⟨31091771631464933726258593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165822782034479646540045829 31091771631464933726258593)
        ·
          refine ⟨23318828723598700294693945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31091771631464933726258593 23318828723598700294693945)
          ·
            refine ⟨17489121542699025221020459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23318828723598700294693945 17489121542699025221020459)
            ·
              refine ⟨26233682314048537831530689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17489121542699025221020459 26233682314048537831530689)
              ·
                refine ⟨19675261735536403373648017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26233682314048537831530689 19675261735536403373648017)
                ·
                  refine ⟨14756446301652302530236013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19675261735536403373648017 14756446301652302530236013)
                  ·
                    refine ⟨5533667363119613448838505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14756446301652302530236013 5533667363119613448838505)
                    ·
                      refine ⟨4150250522339710086628879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533667363119613448838505 4150250522339710086628879)
                      ·
                        rfl

theorem cell23_8082584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_8082584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082584 prefixEnd_8082584 := by exact prefixLift 8082584
  have htrace : WordTrace (prefixWord ++ tailWord_8082584) baseStart_8082584 baseEnd_8082584 := by
    simpa [prefixWord, tailWord_8082584, baseEnd_8082584] using wordTrace_append hprefix tailTrace_8082584
  have hstable : (prefixWord ++ tailWord_8082584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082584).length < 2 ^ (prefixWord ++ tailWord_8082584).sum := by decide
  have hdescent : baseEnd_8082584 < baseStart_8082584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082591 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 3, 1, 3]
def baseStart_8082591 : Nat := 118140960795 + 8082591 * 2 ^ 59
def prefixEnd_8082591 : Nat := 4983230072969 + 3 ^ 40 * 8082591 * 2
def baseEnd_8082591 : Nat := 4150254116704291559241347

theorem tailTrace_8082591 : CollatzResearch.WordTrace tailWord_8082591 prefixEnd_8082591 4150254116704291559241347 := by
  unfold tailWord_8082591
  simp only [CollatzResearch.WordTrace]
  refine ⟨294796312261160678488919627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196530874840773785659279751 294796312261160678488919627)
  ·
    refine ⟨442194468391741017733379441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294796312261160678488919627 442194468391741017733379441)
    ·
      refine ⟨331645851293805763300034581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442194468391741017733379441 331645851293805763300034581)
      ·
        refine ⟨15545899279397145154689121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 331645851293805763300034581 15545899279397145154689121)
        ·
          refine ⟨11659424459547858866016841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15545899279397145154689121 11659424459547858866016841)
          ·
            refine ⟨8744568344660894149512631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11659424459547858866016841 8744568344660894149512631)
            ·
              refine ⟨13116852516991341224268947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8744568344660894149512631 13116852516991341224268947)
              ·
                refine ⟨19675278775487011836403421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13116852516991341224268947 19675278775487011836403421)
                ·
                  refine ⟨7378229540807629438651283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19675278775487011836403421 7378229540807629438651283)
                  ·
                    refine ⟨11067344311211444157976925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7378229540807629438651283 11067344311211444157976925)
                    ·
                      refine ⟨4150254116704291559241347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11067344311211444157976925 4150254116704291559241347)
                      ·
                        rfl

theorem cell23_8082591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_8082591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082591 prefixEnd_8082591 := by exact prefixLift 8082591
  have htrace : WordTrace (prefixWord ++ tailWord_8082591) baseStart_8082591 baseEnd_8082591 := by
    simpa [prefixWord, tailWord_8082591, baseEnd_8082591] using wordTrace_append hprefix tailTrace_8082591
  have hstable : (prefixWord ++ tailWord_8082591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082591).length < 2 ^ (prefixWord ++ tailWord_8082591).sum := by decide
  have hdescent : baseEnd_8082591 < baseStart_8082591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082610 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_8082610 : Nat := 118140960795 + 8082610 * 2 ^ 59
def prefixEnd_8082610 : Nat := 4983230072969 + 3 ^ 40 * 8082610 * 2
def baseEnd_8082610 : Nat := 4150263872836726984903759

theorem tailTrace_8082610 : CollatzResearch.WordTrace tailWord_8082610 prefixEnd_8082610 4150263872836726984903759 := by
  unfold tailWord_8082610
  simp only [CollatzResearch.WordTrace]
  refine ⟨73699251312022961183465321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196531336832061229822574189 73699251312022961183465321)
  ·
    refine ⟨55274438484017220887598991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73699251312022961183465321 55274438484017220887598991)
    ·
      refine ⟨82911657726025831331398487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55274438484017220887598991 82911657726025831331398487)
      ·
        refine ⟨124367486589038746997097731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82911657726025831331398487 124367486589038746997097731)
        ·
          refine ⟨186551229883558120495646597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124367486589038746997097731 186551229883558120495646597)
          ·
            refine ⟨34978355603167147592933737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186551229883558120495646597 34978355603167147592933737)
            ·
              refine ⟨26233766702375360694700303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34978355603167147592933737 26233766702375360694700303)
              ·
                refine ⟨39350650053563041042050455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26233766702375360694700303 39350650053563041042050455)
                ·
                  refine ⟨59025975080344561563075683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39350650053563041042050455 59025975080344561563075683)
                  ·
                    refine ⟨88538962620516842344613525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59025975080344561563075683 88538962620516842344613525)
                    ·
                      refine ⟨4150263872836726984903759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88538962620516842344613525 4150263872836726984903759)
                      ·
                        rfl

theorem cell23_8082610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_8082610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082610 prefixEnd_8082610 := by exact prefixLift 8082610
  have htrace : WordTrace (prefixWord ++ tailWord_8082610) baseStart_8082610 baseEnd_8082610 := by
    simpa [prefixWord, tailWord_8082610, baseEnd_8082610] using wordTrace_append hprefix tailTrace_8082610
  have hstable : (prefixWord ++ tailWord_8082610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082610).length < 2 ^ (prefixWord ++ tailWord_8082610).sum := by decide
  have hdescent : baseEnd_8082610 < baseStart_8082610 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082617 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 3, 2, 3]
def baseStart_8082617 : Nat := 118140960795 + 8082617 * 2 ^ 59
def prefixEnd_8082617 : Nat := 4983230072969 + 3 ^ 40 * 8082617 * 2
def baseEnd_8082617 : Nat := 4150267467201308457516227

theorem tailTrace_8082617 : CollatzResearch.WordTrace tailWord_8082617 prefixEnd_8082617 4150267467201308457516227 := by
  unfold tailWord_8082617
  simp only [CollatzResearch.WordTrace]
  refine ⟨294797260559066484929366105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196531507039377656619577403 294797260559066484929366105)
  ·
    refine ⟨221097945419299863697024579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294797260559066484929366105 221097945419299863697024579)
    ·
      refine ⟨331646918128949795545536869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221097945419299863697024579 331646918128949795545536869)
      ·
        refine ⟨62183797149178086664788163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331646918128949795545536869 62183797149178086664788163)
        ·
          refine ⟨93275695723767129997182245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62183797149178086664788163 93275695723767129997182245)
          ·
            refine ⟨17489192948206336874471671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93275695723767129997182245 17489192948206336874471671)
            ·
              refine ⟨26233789422309505311707507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17489192948206336874471671 26233789422309505311707507)
              ·
                refine ⟨39350684133464257967561261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26233789422309505311707507 39350684133464257967561261)
                ·
                  refine ⟨14756506550049096737835473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39350684133464257967561261 14756506550049096737835473)
                  ·
                    refine ⟨11067379912536822553376605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14756506550049096737835473 11067379912536822553376605)
                    ·
                      refine ⟨4150267467201308457516227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11067379912536822553376605 4150267467201308457516227)
                      ·
                        rfl

theorem cell23_8082617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_8082617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082617 prefixEnd_8082617 := by exact prefixLift 8082617
  have htrace : WordTrace (prefixWord ++ tailWord_8082617) baseStart_8082617 baseEnd_8082617 := by
    simpa [prefixWord, tailWord_8082617, baseEnd_8082617] using wordTrace_append hprefix tailTrace_8082617
  have hstable : (prefixWord ++ tailWord_8082617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082617).length < 2 ^ (prefixWord ++ tailWord_8082617).sum := by decide
  have hdescent : baseEnd_8082617 < baseStart_8082617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082620 : List Nat := [2, 2, 2, 3, 2, 1, 2, 9]
def baseStart_8082620 : Nat := 118140960795 + 8082620 * 2 ^ 59
def prefixEnd_8082620 : Nat := 4983230072969 + 3 ^ 40 * 8082620 * 2
def baseEnd_8082620 : Nat := 153713666949750812806619

theorem tailTrace_8082620 : CollatzResearch.WordTrace tailWord_8082620 prefixEnd_8082620 153713666949750812806619 := by
  unfold tailWord_8082620
  simp only [CollatzResearch.WordTrace]
  refine ⟨147398684989027808220862657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196531579985370410961150209 147398684989027808220862657)
  ·
    refine ⟨110549013741770856165646993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147398684989027808220862657 110549013741770856165646993)
    ·
      refine ⟨82911760306328142124235245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110549013741770856165646993 82911760306328142124235245)
      ·
        refine ⟨31091910114873053296588217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82911760306328142124235245 31091910114873053296588217)
        ·
          refine ⟨23318932586154789972441163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31091910114873053296588217 23318932586154789972441163)
          ·
            refine ⟨34978398879232184958661745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23318932586154789972441163 34978398879232184958661745)
            ·
              refine ⟨26233799159424138718996309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34978398879232184958661745 26233799159424138718996309)
              ·
                refine ⟨153713666949750812806619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26233799159424138718996309 153713666949750812806619)
                ·
                  rfl

theorem cell23_8082620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 9].length) (baseStart_8082620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082620 prefixEnd_8082620 := by exact prefixLift 8082620
  have htrace : WordTrace (prefixWord ++ tailWord_8082620) baseStart_8082620 baseEnd_8082620 := by
    simpa [prefixWord, tailWord_8082620, baseEnd_8082620] using wordTrace_append hprefix tailTrace_8082620
  have hstable : (prefixWord ++ tailWord_8082620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082620).length < 2 ^ (prefixWord ++ tailWord_8082620).sum := by decide
  have hdescent : baseEnd_8082620 < baseStart_8082620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082637 : List Nat := [1, 6, 2, 2, 12]
def baseStart_8082637 : Nat := 118140960795 + 8082637 * 2 ^ 59
def prefixEnd_8082637 : Nat := 4983230072969 + 3 ^ 40 * 8082637 * 2
def baseEnd_8082637 : Nat := 5693110750088337968815

theorem tailTrace_8082637 : CollatzResearch.WordTrace tailWord_8082637 prefixEnd_8082637 5693110750088337968815 := by
  unfold tailWord_8082637
  simp only [CollatzResearch.WordTrace]
  refine ⟨294797990018994028345094165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196531993345996018896729443 294797990018994028345094165)
  ·
    refine ⟨13818655782140345078676289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 294797990018994028345094165 13818655782140345078676289)
    ·
      refine ⟨10363991836605258809007217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13818655782140345078676289 10363991836605258809007217)
      ·
        refine ⟨7772993877453944106755413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10363991836605258809007217 7772993877453944106755413)
        ·
          refine ⟨5693110750088337968815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7772993877453944106755413 5693110750088337968815)
          ·
            rfl

theorem cell23_8082637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 12].length) (baseStart_8082637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082637 prefixEnd_8082637 := by exact prefixLift 8082637
  have htrace : WordTrace (prefixWord ++ tailWord_8082637) baseStart_8082637 baseEnd_8082637 := by
    simpa [prefixWord, tailWord_8082637, baseEnd_8082637] using wordTrace_append hprefix tailTrace_8082637
  have hstable : (prefixWord ++ tailWord_8082637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082637).length < 2 ^ (prefixWord ++ tailWord_8082637).sum := by decide
  have hdescent : baseEnd_8082637 < baseStart_8082637 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082647 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 4, 1, 3]
def baseStart_8082647 : Nat := 118140960795 + 8082647 * 2 ^ 59
def prefixEnd_8082647 : Nat := 4983230072969 + 3 ^ 40 * 8082647 * 2
def baseEnd_8082647 : Nat := 4150282871620943340141089

theorem tailTrace_8082647 : CollatzResearch.WordTrace tailWord_8082647 prefixEnd_8082647 4150282871620943340141089 := by
  unfold tailWord_8082647
  simp only [CollatzResearch.WordTrace]
  refine ⟨294798354748957800052958195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196532236499305200035305463 294798354748957800052958195)
  ·
    refine ⟨442197532123436700079437293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294798354748957800052958195 442197532123436700079437293)
    ·
      refine ⟨165824074546288762529788985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442197532123436700079437293 165824074546288762529788985)
      ·
        refine ⟨124368055909716571897341739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165824074546288762529788985 124368055909716571897341739)
        ·
          refine ⟨186552083864574857846012609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124368055909716571897341739 186552083864574857846012609)
          ·
            refine ⟨139914062898431143384509457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186552083864574857846012609 139914062898431143384509457)
            ·
              refine ⟨104935547173823357538382093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139914062898431143384509457 104935547173823357538382093)
              ·
                refine ⟨39350830190183759076893285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104935547173823357538382093 39350830190183759076893285)
                ·
                  refine ⟨7378280660659454826917491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39350830190183759076893285 7378280660659454826917491)
                  ·
                    refine ⟨11067420990989182240376237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7378280660659454826917491 11067420990989182240376237)
                    ·
                      refine ⟨4150282871620943340141089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11067420990989182240376237 4150282871620943340141089)
                      ·
                        rfl

theorem cell23_8082647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_8082647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082647 prefixEnd_8082647 := by exact prefixLift 8082647
  have htrace : WordTrace (prefixWord ++ tailWord_8082647) baseStart_8082647 baseEnd_8082647 := by
    simpa [prefixWord, tailWord_8082647, baseEnd_8082647] using wordTrace_append hprefix tailTrace_8082647
  have hstable : (prefixWord ++ tailWord_8082647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082647).length < 2 ^ (prefixWord ++ tailWord_8082647).sum := by decide
  have hdescent : baseEnd_8082647 < baseStart_8082647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082648 : List Nat := [2, 1, 2, 2, 5, 1, 1, 4, 1, 2, 2]
def baseStart_8082648 : Nat := 118140960795 + 8082648 * 2 ^ 59
def prefixEnd_8082648 : Nat := 4983230072969 + 3 ^ 40 * 8082648 * 2
def baseEnd_8082648 : Nat := 4150283385101597836228585

theorem tailTrace_8082648 : CollatzResearch.WordTrace tailWord_8082648 prefixEnd_8082648 4150283385101597836228585 := by
  unfold tailWord_8082648
  simp only [CollatzResearch.WordTrace]
  refine ⟨147399195610977088611872299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196532260814636118149163065 147399195610977088611872299)
  ·
    refine ⟨221098793416465632917808449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147399195610977088611872299 221098793416465632917808449)
    ·
      refine ⟨165824095062349224688356337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221098793416465632917808449 165824095062349224688356337)
      ·
        refine ⟨124368071296761918516267253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165824095062349224688356337 124368071296761918516267253)
        ·
          refine ⟨11659506684071429860900055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124368071296761918516267253 11659506684071429860900055)
          ·
            refine ⟨17489260026107144791350083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11659506684071429860900055 17489260026107144791350083)
            ·
              refine ⟨26233890039160717187025125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17489260026107144791350083 26233890039160717187025125)
              ·
                refine ⟨4918854382342634472567211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26233890039160717187025125 4918854382342634472567211)
                ·
                  refine ⟨7378281573513951708850817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4918854382342634472567211 7378281573513951708850817)
                  ·
                    refine ⟨5533711180135463781638113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7378281573513951708850817 5533711180135463781638113)
                    ·
                      refine ⟨4150283385101597836228585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533711180135463781638113 4150283385101597836228585)
                      ·
                        rfl

theorem cell23_8082648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_8082648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082648 prefixEnd_8082648 := by exact prefixLift 8082648
  have htrace : WordTrace (prefixWord ++ tailWord_8082648) baseStart_8082648 baseEnd_8082648 := by
    simpa [prefixWord, tailWord_8082648, baseEnd_8082648] using wordTrace_append hprefix tailTrace_8082648
  have hstable : (prefixWord ++ tailWord_8082648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082648).length < 2 ^ (prefixWord ++ tailWord_8082648).sum := by decide
  have hdescent : baseEnd_8082648 < baseStart_8082648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082664 : List Nat := [2, 1, 4, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_8082664 : Nat := 118140960795 + 8082664 * 2 ^ 59
def prefixEnd_8082664 : Nat := 4983230072969 + 3 ^ 40 * 8082664 * 2
def baseEnd_8082664 : Nat := 4150291600792069773628511

theorem tailTrace_8082664 : CollatzResearch.WordTrace tailWord_8082664 prefixEnd_8082664 4150291600792069773628511 := by
  unfold tailWord_8082664
  simp only [CollatzResearch.WordTrace]
  refine ⟨147399487394948105978163523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196532649859930807970884697 147399487394948105978163523)
  ·
    refine ⟨221099231092422158967245285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147399487394948105978163523 221099231092422158967245285)
    ·
      refine ⟨41456105829829154806358491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221099231092422158967245285 41456105829829154806358491)
      ·
        refine ⟨62184158744743732209537737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41456105829829154806358491 62184158744743732209537737)
        ·
          refine ⟨46638119058557799157153303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62184158744743732209537737 46638119058557799157153303)
          ·
            refine ⟨69957178587836698735729955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46638119058557799157153303 69957178587836698735729955)
            ·
              refine ⟨104935767881755048103594933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69957178587836698735729955 104935767881755048103594933)
              ·
                refine ⟨9837728238914535759712025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104935767881755048103594933 9837728238914535759712025)
                ·
                  refine ⟨7378296179185901819784019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9837728238914535759712025 7378296179185901819784019)
                  ·
                    refine ⟨11067444268778852729676029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7378296179185901819784019 11067444268778852729676029)
                    ·
                      refine ⟨4150291600792069773628511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11067444268778852729676029 4150291600792069773628511)
                      ·
                        rfl

theorem cell23_8082664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_8082664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082664 prefixEnd_8082664 := by exact prefixLift 8082664
  have htrace : WordTrace (prefixWord ++ tailWord_8082664) baseStart_8082664 baseEnd_8082664 := by
    simpa [prefixWord, tailWord_8082664, baseEnd_8082664] using wordTrace_append hprefix tailTrace_8082664
  have hstable : (prefixWord ++ tailWord_8082664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082664).length < 2 ^ (prefixWord ++ tailWord_8082664).sum := by decide
  have hdescent : baseEnd_8082664 < baseStart_8082664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082691 : List Nat := [1, 1, 1, 3, 2, 4, 4, 1, 1, 3, 2]
def baseStart_8082691 : Nat := 118140960795 + 8082691 * 2 ^ 59
def prefixEnd_8082691 : Nat := 4983230072969 + 3 ^ 40 * 8082691 * 2
def baseEnd_8082691 : Nat := 4150305464769741167990887

theorem tailTrace_8082691 : CollatzResearch.WordTrace tailWord_8082691 prefixEnd_8082691 4150305464769741167990887 := by
  unfold tailWord_8082691
  simp only [CollatzResearch.WordTrace]
  refine ⟨294799959560798395567559927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196533306373865597045039951 294799959560798395567559927)
  ·
    refine ⟨442199939341197593351339891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294799959560798395567559927 442199939341197593351339891)
    ·
      refine ⟨663299909011796390027009837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442199939341197593351339891 663299909011796390027009837)
      ·
        refine ⟨248737465879423646260128689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 663299909011796390027009837 248737465879423646260128689)
        ·
          refine ⟨186553099409567734695096517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248737465879423646260128689 186553099409567734695096517)
          ·
            refine ⟨34978706139293950255330597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186553099409567734695096517 34978706139293950255330597)
            ·
              refine ⟨6558507401117615672874487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34978706139293950255330597 6558507401117615672874487)
              ·
                refine ⟨9837761101676423509311731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6558507401117615672874487 9837761101676423509311731)
                ·
                  refine ⟨14756641652514635263967597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9837761101676423509311731 14756641652514635263967597)
                  ·
                    refine ⟨5533740619692988223987849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14756641652514635263967597 5533740619692988223987849)
                    ·
                      refine ⟨4150305464769741167990887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533740619692988223987849 4150305464769741167990887)
                      ·
                        rfl

theorem cell23_8082691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 1, 3, 2].length) (baseStart_8082691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082691 prefixEnd_8082691 := by exact prefixLift 8082691
  have htrace : WordTrace (prefixWord ++ tailWord_8082691) baseStart_8082691 baseEnd_8082691 := by
    simpa [prefixWord, tailWord_8082691, baseEnd_8082691] using wordTrace_append hprefix tailTrace_8082691
  have hstable : (prefixWord ++ tailWord_8082691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082691).length < 2 ^ (prefixWord ++ tailWord_8082691).sum := by decide
  have hdescent : baseEnd_8082691 < baseStart_8082691 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082894 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_8082894 : Nat := 118140960795 + 8082894 * 2 ^ 59
def prefixEnd_8082894 : Nat := 4983230072969 + 3 ^ 40 * 8082894 * 2
def baseEnd_8082894 : Nat := 1383469900447534624584151

theorem tailTrace_8082894 : CollatzResearch.WordTrace tailWord_8082894 prefixEnd_8082894 1383469900447534624584151 := by
  unfold tailWord_8082894
  simp only [CollatzResearch.WordTrace]
  refine ⟨36850920447382870154649967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196538242386041974158133157 36850920447382870154649967)
  ·
    refine ⟨55276380671074305231974951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36850920447382870154649967 55276380671074305231974951)
    ·
      refine ⟨82914571006611457847962427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55276380671074305231974951 82914571006611457847962427)
      ·
        refine ⟨124371856509917186771943641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82914571006611457847962427 124371856509917186771943641)
        ·
          refine ⟨93278892382437890078957731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124371856509917186771943641 93278892382437890078957731)
          ·
            refine ⟨139918338573656835118436597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93278892382437890078957731 139918338573656835118436597)
            ·
              refine ⟨13117344241280328292353431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139918338573656835118436597 13117344241280328292353431)
              ·
                refine ⟨19676016361920492438530147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13117344241280328292353431 19676016361920492438530147)
                ·
                  refine ⟨29514024542880738657795221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19676016361920492438530147 29514024542880738657795221)
                  ·
                    refine ⟨1383469900447534624584151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29514024542880738657795221 1383469900447534624584151)
                    ·
                      rfl

theorem cell23_8082894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_8082894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082894 prefixEnd_8082894 := by exact prefixLift 8082894
  have htrace : WordTrace (prefixWord ++ tailWord_8082894) baseStart_8082894 baseEnd_8082894 := by
    simpa [prefixWord, tailWord_8082894, baseEnd_8082894] using wordTrace_append hprefix tailTrace_8082894
  have hstable : (prefixWord ++ tailWord_8082894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082894).length < 2 ^ (prefixWord ++ tailWord_8082894).sum := by decide
  have hdescent : baseEnd_8082894 < baseStart_8082894 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082901 : List Nat := [1, 3, 2, 3, 1, 1, 4, 2, 1, 1, 4]
def baseStart_8082901 : Nat := 118140960795 + 8082901 * 2 ^ 59
def prefixEnd_8082901 : Nat := 4983230072969 + 3 ^ 40 * 8082901 * 2
def baseEnd_8082901 : Nat := 4150413295707185346364921

theorem tailTrace_8082901 : CollatzResearch.WordTrace tailWord_8082901 prefixEnd_8082901 4150413295707185346364921 := by
  unfold tailWord_8082901
  simp only [CollatzResearch.WordTrace]
  refine ⟨294807618890037601432704557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196538412593358400955136371 294807618890037601432704557)
  ·
    refine ⟨110552857083764100537264209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294807618890037601432704557 110552857083764100537264209)
    ·
      refine ⟨82914642812823075402948157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110552857083764100537264209 82914642812823075402948157)
      ·
        refine ⟨31092991054808653276105559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82914642812823075402948157 31092991054808653276105559)
        ·
          refine ⟨46639486582212979914158339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31092991054808653276105559 46639486582212979914158339)
          ·
            refine ⟨69959229873319469871237509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46639486582212979914158339 69959229873319469871237509)
            ·
              refine ⟨13117355601247400600857033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69959229873319469871237509 13117355601247400600857033)
              ·
                refine ⟨9838016700935550450642775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13117355601247400600857033 9838016700935550450642775)
                ·
                  refine ⟨14757025051403325675964163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9838016700935550450642775 14757025051403325675964163)
                  ·
                    refine ⟨22135537577104988513946245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14757025051403325675964163 22135537577104988513946245)
                    ·
                      refine ⟨4150413295707185346364921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22135537577104988513946245 4150413295707185346364921)
                      ·
                        rfl

theorem cell23_8082901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_8082901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082901 prefixEnd_8082901 := by exact prefixLift 8082901
  have htrace : WordTrace (prefixWord ++ tailWord_8082901) baseStart_8082901 baseEnd_8082901 := by
    simpa [prefixWord, tailWord_8082901, baseEnd_8082901] using wordTrace_append hprefix tailTrace_8082901
  have hstable : (prefixWord ++ tailWord_8082901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082901).length < 2 ^ (prefixWord ++ tailWord_8082901).sum := by decide
  have hdescent : baseEnd_8082901 < baseStart_8082901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082904 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 3, 2, 3]
def baseStart_8082904 : Nat := 118140960795 + 8082904 * 2 ^ 59
def prefixEnd_8082904 : Nat := 4983230072969 + 3 ^ 40 * 8082904 * 2
def baseEnd_8082904 : Nat := 4150414836149148834627407

theorem tailTrace_8082904 : CollatzResearch.WordTrace tailWord_8082904 prefixEnd_8082904 4150414836149148834627407 := by
  unfold tailWord_8082904
  simp only [CollatzResearch.WordTrace]
  refine ⟨147403864154513366472531883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196538485539351155296709177 147403864154513366472531883)
  ·
    refine ⟨221105796231770049708797825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147403864154513366472531883 221105796231770049708797825)
    ·
      refine ⟨165829347173827537281598369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221105796231770049708797825 165829347173827537281598369)
      ·
        refine ⟨124372010380370652961198777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165829347173827537281598369 124372010380370652961198777)
        ·
          refine ⟨93279007785277989720899083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124372010380370652961198777 93279007785277989720899083)
          ·
            refine ⟨139918511677916984581348625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93279007785277989720899083 139918511677916984581348625)
            ·
              refine ⟨104938883758437738436011469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139918511677916984581348625 104938883758437738436011469)
              ·
                refine ⟨39352081409414151913504301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104938883758437738436011469 39352081409414151913504301)
                ·
                  refine ⟨14757030528530306967564113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39352081409414151913504301 14757030528530306967564113)
                  ·
                    refine ⟨11067772896397730225673085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14757030528530306967564113 11067772896397730225673085)
                    ·
                      refine ⟨4150414836149148834627407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11067772896397730225673085 4150414836149148834627407)
                      ·
                        rfl

theorem cell23_8082904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_8082904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082904 prefixEnd_8082904 := by exact prefixLift 8082904
  have htrace : WordTrace (prefixWord ++ tailWord_8082904) baseStart_8082904 baseEnd_8082904 := by
    simpa [prefixWord, tailWord_8082904, baseEnd_8082904] using wordTrace_append hprefix tailTrace_8082904
  have hstable : (prefixWord ++ tailWord_8082904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082904).length < 2 ^ (prefixWord ++ tailWord_8082904).sum := by decide
  have hdescent : baseEnd_8082904 < baseStart_8082904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082937 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 2, 7]
def baseStart_8082937 : Nat := 118140960795 + 8082937 * 2 ^ 59
def prefixEnd_8082937 : Nat := 4983230072969 + 3 ^ 40 * 8082937 * 2
def baseEnd_8082937 : Nat := 1383477260336915735171585

theorem tailTrace_8082937 : CollatzResearch.WordTrace tailWord_8082937 prefixEnd_8082937 1383477260336915735171585 := by
  unfold tailWord_8082937
  simp only [CollatzResearch.WordTrace]
  refine ⟨294808931917907179581015065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196539287945271453054010043 294808931917907179581015065)
  ·
    refine ⟨221106698938430384685761299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294808931917907179581015065 221106698938430384685761299)
    ·
      refine ⟨331660048407645577028641949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221106698938430384685761299 331660048407645577028641949)
      ·
        refine ⟨124372518152867091385740731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331660048407645577028641949 124372518152867091385740731)
        ·
          refine ⟨186558777229300637078611097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124372518152867091385740731 186558777229300637078611097)
          ·
            refine ⟨139919082921975477808958323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186558777229300637078611097 139919082921975477808958323)
            ·
              refine ⟨209878624382963216713437485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139919082921975477808958323 209878624382963216713437485)
              ·
                refine ⟨78704484143611206267539057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209878624382963216713437485 78704484143611206267539057)
                ·
                  refine ⟨59028363107708404700654293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78704484143611206267539057 59028363107708404700654293)
                  ·
                    refine ⟨1383477260336915735171585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59028363107708404700654293 1383477260336915735171585)
                    ·
                      rfl

theorem cell23_8082937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_8082937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082937 prefixEnd_8082937 := by exact prefixLift 8082937
  have htrace : WordTrace (prefixWord ++ tailWord_8082937) baseStart_8082937 baseEnd_8082937 := by
    simpa [prefixWord, tailWord_8082937, baseEnd_8082937] using wordTrace_append hprefix tailTrace_8082937
  have hstable : (prefixWord ++ tailWord_8082937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082937).length < 2 ^ (prefixWord ++ tailWord_8082937).sum := by decide
  have hdescent : baseEnd_8082937 < baseStart_8082937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082945 : List Nat := [1, 2, 4, 1, 4, 2, 2, 1, 2, 4]
def baseStart_8082945 : Nat := 118140960795 + 8082945 * 2 ^ 59
def prefixEnd_8082945 : Nat := 4983230072969 + 3 ^ 40 * 8082945 * 2
def baseEnd_8082945 : Nat := 1383478629618661058071573

theorem tailTrace_8082945 : CollatzResearch.WordTrace tailWord_8082945 prefixEnd_8082945 1383478629618661058071573 := by
  unfold tailWord_8082945
  simp only [CollatzResearch.WordTrace]
  refine ⟨294809223701878196947306289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196539482467918797964870859 294809223701878196947306289)
  ·
    refine ⟨221106917776408647710479717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294809223701878196947306289 221106917776408647710479717)
    ·
      refine ⟨41457547083076621445714947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221106917776408647710479717 41457547083076621445714947)
      ·
        refine ⟨62186320624614932168572421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41457547083076621445714947 62186320624614932168572421)
        ·
          refine ⟨11659935117115299781607329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62186320624614932168572421 11659935117115299781607329)
          ·
            refine ⟨8744951337836474836205497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11659935117115299781607329 8744951337836474836205497)
            ·
              refine ⟨6558713503377356127154123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8744951337836474836205497 6558713503377356127154123)
              ·
                refine ⟨9838070255066034190731185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6558713503377356127154123 9838070255066034190731185)
                ·
                  refine ⟨7378552691299525643048389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9838070255066034190731185 7378552691299525643048389)
                  ·
                    refine ⟨1383478629618661058071573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7378552691299525643048389 1383478629618661058071573)
                    ·
                      rfl

theorem cell23_8082945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_8082945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082945 prefixEnd_8082945 := by exact prefixLift 8082945
  have htrace : WordTrace (prefixWord ++ tailWord_8082945) baseStart_8082945 baseEnd_8082945 := by
    simpa [prefixWord, tailWord_8082945, baseEnd_8082945] using wordTrace_append hprefix tailTrace_8082945
  have hstable : (prefixWord ++ tailWord_8082945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082945).length < 2 ^ (prefixWord ++ tailWord_8082945).sum := by decide
  have hdescent : baseEnd_8082945 < baseStart_8082945 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082947 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 5]
def baseStart_8082947 : Nat := 118140960795 + 8082947 * 2 ^ 59
def prefixEnd_8082947 : Nat := 4983230072969 + 3 ^ 40 * 8082947 * 2
def baseEnd_8082947 : Nat := 4150436915817292166389709

theorem tailTrace_8082947 : CollatzResearch.WordTrace tailWord_8082947 prefixEnd_8082947 4150436915817292166389709 := by
  unfold tailWord_8082947
  simp only [CollatzResearch.WordTrace]
  refine ⟨294809296647870951288879095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196539531098580634192586063 294809296647870951288879095)
  ·
    refine ⟨442213944971806426933318643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294809296647870951288879095 442213944971806426933318643)
    ·
      refine ⟨663320917457709640399977965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442213944971806426933318643 663320917457709640399977965)
      ·
        refine ⟨248745344046641115149991737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 663320917457709640399977965 248745344046641115149991737)
        ·
          refine ⟨186559008034980836362493803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248745344046641115149991737 186559008034980836362493803)
          ·
            refine ⟨279838512052471254543740705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186559008034980836362493803 279838512052471254543740705)
            ·
              refine ⟨209878884039353440907805529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279838512052471254543740705 209878884039353440907805529)
              ·
                refine ⟨157409163029515080680854147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209878884039353440907805529 157409163029515080680854147)
                ·
                  refine ⟨236113744544272621021281221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157409163029515080680854147 236113744544272621021281221)
                  ·
                    refine ⟨44271327102051116441490229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236113744544272621021281221 44271327102051116441490229)
                    ·
                      refine ⟨4150436915817292166389709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44271327102051116441490229 4150436915817292166389709)
                      ·
                        rfl

theorem cell23_8082947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_8082947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082947 prefixEnd_8082947 := by exact prefixLift 8082947
  have htrace : WordTrace (prefixWord ++ tailWord_8082947) baseStart_8082947 baseEnd_8082947 := by
    simpa [prefixWord, tailWord_8082947, baseEnd_8082947] using wordTrace_append hprefix tailTrace_8082947
  have hstable : (prefixWord ++ tailWord_8082947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082947).length < 2 ^ (prefixWord ++ tailWord_8082947).sum := by decide
  have hdescent : baseEnd_8082947 < baseStart_8082947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082955 : List Nat := [1, 1, 1, 1, 9, 1, 1, 2, 1, 2, 3]
def baseStart_8082955 : Nat := 118140960795 + 8082955 * 2 ^ 59
def prefixEnd_8082955 : Nat := 4983230072969 + 3 ^ 40 * 8082955 * 2
def baseEnd_8082955 : Nat := 4150441023662528135089673

theorem tailTrace_8082955 : CollatzResearch.WordTrace tailWord_8082955 prefixEnd_8082955 4150441023662528135089673 := by
  unfold tailWord_8082955
  simp only [CollatzResearch.WordTrace]
  refine ⟨294809588431841968655170319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196539725621227979103446879 294809588431841968655170319)
  ·
    refine ⟨442214382647762952982755479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294809588431841968655170319 442214382647762952982755479)
    ·
      refine ⟨663321573971644429474133219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442214382647762952982755479 663321573971644429474133219)
      ·
        refine ⟨994982360957466644211199829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663321573971644429474133219 994982360957466644211199829)
        ·
          refine ⟨5829974771235156118424999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 994982360957466644211199829 5829974771235156118424999)
          ·
            refine ⟨8744962156852734177637499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5829974771235156118424999 8744962156852734177637499)
            ·
              refine ⟨13117443235279101266456249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8744962156852734177637499 13117443235279101266456249)
              ·
                refine ⟨9838082426459325949842187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13117443235279101266456249 9838082426459325949842187)
                ·
                  refine ⟨14757123639688988924763281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9838082426459325949842187 14757123639688988924763281)
                  ·
                    refine ⟨11067842729766741693572461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14757123639688988924763281 11067842729766741693572461)
                    ·
                      refine ⟨4150441023662528135089673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11067842729766741693572461 4150441023662528135089673)
                      ·
                        rfl

theorem cell23_8082955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 1, 2, 3].length) (baseStart_8082955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082955 prefixEnd_8082955 := by exact prefixLift 8082955
  have htrace : WordTrace (prefixWord ++ tailWord_8082955) baseStart_8082955 baseEnd_8082955 := by
    simpa [prefixWord, tailWord_8082955, baseEnd_8082955] using wordTrace_append hprefix tailTrace_8082955
  have hstable : (prefixWord ++ tailWord_8082955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082955).length < 2 ^ (prefixWord ++ tailWord_8082955).sum := by decide
  have hdescent : baseEnd_8082955 < baseStart_8082955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082961 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 3, 3, 2]
def baseStart_8082961 : Nat := 118140960795 + 8082961 * 2 ^ 59
def prefixEnd_8082961 : Nat := 4983230072969 + 3 ^ 40 * 8082961 * 2
def baseEnd_8082961 : Nat := 4150444104546455111614645

theorem tailTrace_8082961 : CollatzResearch.WordTrace tailWord_8082961 prefixEnd_8082961 4150444104546455111614645 := by
  unfold tailWord_8082961
  simp only [CollatzResearch.WordTrace]
  refine ⟨294809807269820231679888737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196539871513213487786592491 294809807269820231679888737)
  ·
    refine ⟨221107355452365173759916553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294809807269820231679888737 221107355452365173759916553)
    ·
      refine ⟨165830516589273880319937415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221107355452365173759916553 165830516589273880319937415)
      ·
        refine ⟨248745774883910820479906123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165830516589273880319937415 248745774883910820479906123)
        ·
          refine ⟨373118662325866230719859185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248745774883910820479906123 373118662325866230719859185)
          ·
            refine ⟨279838996744399673039894389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373118662325866230719859185 279838996744399673039894389)
            ·
              refine ⟨26234905944787469347490099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279838996744399673039894389 26234905944787469347490099)
              ·
                refine ⟨39352358917181204021235149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26234905944787469347490099 39352358917181204021235149)
                ·
                  refine ⟨14757134593942951507963181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39352358917181204021235149 14757134593942951507963181)
                  ·
                    refine ⟨5533925472728606815486193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14757134593942951507963181 5533925472728606815486193)
                    ·
                      refine ⟨4150444104546455111614645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533925472728606815486193 4150444104546455111614645)
                      ·
                        rfl

theorem cell23_8082961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 3, 2].length) (baseStart_8082961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082961 prefixEnd_8082961 := by exact prefixLift 8082961
  have htrace : WordTrace (prefixWord ++ tailWord_8082961) baseStart_8082961 baseEnd_8082961 := by
    simpa [prefixWord, tailWord_8082961, baseEnd_8082961] using wordTrace_append hprefix tailTrace_8082961
  have hstable : (prefixWord ++ tailWord_8082961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082961).length < 2 ^ (prefixWord ++ tailWord_8082961).sum := by decide
  have hdescent : baseEnd_8082961 < baseStart_8082961 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082978 : List Nat := [3, 3, 1, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_8082978 : Nat := 118140960795 + 8082978 * 2 ^ 59
def prefixEnd_8082978 : Nat := 4983230072969 + 3 ^ 40 * 8082978 * 2
def baseEnd_8082978 : Nat := 4150452833717581545102067

theorem tailTrace_8082978 : CollatzResearch.WordTrace tailWord_8082978 prefixEnd_8082978 4150452833717581545102067 := by
  unfold tailWord_8082978
  simp only [CollatzResearch.WordTrace]
  refine ⟨73702606827689660895814397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196540284873839095722171725 73702606827689660895814397)
  ·
    refine ⟨27638477560383622835930399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73702606827689660895814397 27638477560383622835930399)
    ·
      refine ⟨41457716340575434253895599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27638477560383622835930399 41457716340575434253895599)
      ·
        refine ⟨62186574510863151380843399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41457716340575434253895599 62186574510863151380843399)
        ·
          refine ⟨93279861766294727071265099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62186574510863151380843399 93279861766294727071265099)
          ·
            refine ⟨139919792649442090606897649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93279861766294727071265099 139919792649442090606897649)
            ·
              refine ⟨104939844487081567955173237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139919792649442090606897649 104939844487081567955173237)
              ·
                refine ⟨9838110420663896995797491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104939844487081567955173237 9838110420663896995797491)
                ·
                  refine ⟨14757165630995845493696237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9838110420663896995797491 14757165630995845493696237)
                  ·
                    refine ⟨5533937111623442060136089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14757165630995845493696237 5533937111623442060136089)
                    ·
                      refine ⟨4150452833717581545102067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5533937111623442060136089 4150452833717581545102067)
                      ·
                        rfl

theorem cell23_8082978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_8082978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082978 prefixEnd_8082978 := by exact prefixLift 8082978
  have htrace : WordTrace (prefixWord ++ tailWord_8082978) baseStart_8082978 baseEnd_8082978 := by
    simpa [prefixWord, tailWord_8082978, baseEnd_8082978] using wordTrace_append hprefix tailTrace_8082978
  have hstable : (prefixWord ++ tailWord_8082978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082978).length < 2 ^ (prefixWord ++ tailWord_8082978).sum := by decide
  have hdescent : baseEnd_8082978 < baseStart_8082978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8082987 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 6]
def baseStart_8082987 : Nat := 118140960795 + 8082987 * 2 ^ 59
def prefixEnd_8082987 : Nat := 4983230072969 + 3 ^ 40 * 8082987 * 2
def baseEnd_8082987 : Nat := 4150457455043472009889525

theorem tailTrace_8082987 : CollatzResearch.WordTrace tailWord_8082987 prefixEnd_8082987 4150457455043472009889525 := by
  unfold tailWord_8082987
  simp only [CollatzResearch.WordTrace]
  refine ⟨294810755567726038120335215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196540503711817358746890143 294810755567726038120335215)
  ·
    refine ⟨442216133351589057180502823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294810755567726038120335215 442216133351589057180502823)
    ·
      refine ⟨663324200027383585770754235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442216133351589057180502823 663324200027383585770754235)
      ·
        refine ⟨994986300041075378656131353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663324200027383585770754235 994986300041075378656131353)
        ·
          refine ⟨746239725030806533992098515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 994986300041075378656131353 746239725030806533992098515)
          ·
            refine ⟨1119359587546209800988147773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746239725030806533992098515 1119359587546209800988147773)
            ·
              refine ⟨419759845329828675370555415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1119359587546209800988147773 419759845329828675370555415)
              ·
                refine ⟨629639767994743013055833123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419759845329828675370555415 629639767994743013055833123)
                ·
                  refine ⟨944459651992114519583749685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629639767994743013055833123 944459651992114519583749685)
                  ·
                    refine ⟨88543092374260736210976533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 944459651992114519583749685 88543092374260736210976533)
                    ·
                      refine ⟨4150457455043472009889525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88543092374260736210976533 4150457455043472009889525)
                      ·
                        rfl

theorem cell23_8082987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 6].length) (baseStart_8082987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8082987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8082987 prefixEnd_8082987 := by exact prefixLift 8082987
  have htrace : WordTrace (prefixWord ++ tailWord_8082987) baseStart_8082987 baseEnd_8082987 := by
    simpa [prefixWord, tailWord_8082987, baseEnd_8082987] using wordTrace_append hprefix tailTrace_8082987
  have hstable : (prefixWord ++ tailWord_8082987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8082987).length < 2 ^ (prefixWord ++ tailWord_8082987).sum := by decide
  have hdescent : baseEnd_8082987 < baseStart_8082987 := by decide
  rcases family_descends (prefixWord ++ tailWord_8082987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083024 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 3]
def baseStart_8083024 : Nat := 118140960795 + 8083024 * 2 ^ 59
def prefixEnd_8083024 : Nat := 4983230072969 + 3 ^ 40 * 8083024 * 2
def baseEnd_8083024 : Nat := 4150476453827688365126855

theorem tailTrace_8083024 : CollatzResearch.WordTrace tailWord_8083024 prefixEnd_8083024 4150476453827688365126855 := by
  unfold tailWord_8083024
  simp only [CollatzResearch.WordTrace]
  refine ⟨147406052534295996719716063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196541403379061328959621417 147406052534295996719716063)
  ·
    refine ⟨221109078801443995079574095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147406052534295996719716063 221109078801443995079574095)
    ·
      refine ⟨331663618202165992619361143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221109078801443995079574095 331663618202165992619361143)
      ·
        refine ⟨497495427303248988929041715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331663618202165992619361143 497495427303248988929041715)
        ·
          refine ⟨746243140954873483393562573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497495427303248988929041715 746243140954873483393562573)
          ·
            refine ⟨279841177858077556272585965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 746243140954873483393562573 279841177858077556272585965)
            ·
              refine ⟨104940441696779083602219737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279841177858077556272585965 104940441696779083602219737)
              ·
                refine ⟨78705331272584312701664803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104940441696779083602219737 78705331272584312701664803)
                ·
                  refine ⟨118057996908876469052497205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78705331272584312701664803 118057996908876469052497205)
                  ·
                    refine ⟨11067937210207168973671613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118057996908876469052497205 11067937210207168973671613)
                    ·
                      refine ⟨4150476453827688365126855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11067937210207168973671613 4150476453827688365126855)
                      ·
                        rfl

theorem cell23_8083024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 3].length) (baseStart_8083024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083024 prefixEnd_8083024 := by exact prefixLift 8083024
  have htrace : WordTrace (prefixWord ++ tailWord_8083024) baseStart_8083024 baseEnd_8083024 := by
    simpa [prefixWord, tailWord_8083024, baseEnd_8083024] using wordTrace_append hprefix tailTrace_8083024
  have hstable : (prefixWord ++ tailWord_8083024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083024).length < 2 ^ (prefixWord ++ tailWord_8083024).sum := by decide
  have hdescent : baseEnd_8083024 < baseStart_8083024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083031 : List Nat := [1, 1, 3, 2, 2, 3, 1, 5, 5]
def baseStart_8083031 : Nat := 118140960795 + 8083031 * 2 ^ 59
def prefixEnd_8083031 : Nat := 4983230072969 + 3 ^ 40 * 8083031 * 2
def baseEnd_8083031 : Nat := 461164449799141093082147

theorem tailTrace_8083031 : CollatzResearch.WordTrace tailWord_8083031 prefixEnd_8083031 461164449799141093082147 := by
  unfold tailWord_8083031
  simp only [CollatzResearch.WordTrace]
  refine ⟨294812360379566633634936947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196541573586377755756624631 294812360379566633634936947)
  ·
    refine ⟨442218540569349950452405421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294812360379566633634936947 442218540569349950452405421)
    ·
      refine ⟨165831952713506231419652033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442218540569349950452405421 165831952713506231419652033)
      ·
        refine ⟨124373964535129673564739025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165831952713506231419652033 124373964535129673564739025)
        ·
          refine ⟨93280473401347255173554269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124373964535129673564739025 93280473401347255173554269)
          ·
            refine ⟨34980177525505220690082851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93280473401347255173554269 34980177525505220690082851)
            ·
              refine ⟨52470266288257831035124277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34980177525505220690082851 52470266288257831035124277)
              ·
                refine ⟨4919087464524171659542901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52470266288257831035124277 4919087464524171659542901)
                ·
                  refine ⟨461164449799141093082147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4919087464524171659542901 461164449799141093082147)
                  ·
                    rfl

theorem cell23_8083031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 5].length) (baseStart_8083031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083031 prefixEnd_8083031 := by exact prefixLift 8083031
  have htrace : WordTrace (prefixWord ++ tailWord_8083031) baseStart_8083031 baseEnd_8083031 := by
    simpa [prefixWord, tailWord_8083031, baseEnd_8083031] using wordTrace_append hprefix tailTrace_8083031
  have hstable : (prefixWord ++ tailWord_8083031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083031).length < 2 ^ (prefixWord ++ tailWord_8083031).sum := by decide
  have hdescent : baseEnd_8083031 < baseStart_8083031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083048 : List Nat := [2, 1, 4, 3, 1, 1, 2, 4, 5]
def baseStart_8083048 : Nat := 118140960795 + 8083048 * 2 ^ 59
def prefixEnd_8083048 : Nat := 4983230072969 + 3 ^ 40 * 8083048 * 2
def baseEnd_8083048 : Nat := 461165419707044030136305

theorem tailTrace_8083048 : CollatzResearch.WordTrace tailWord_8083048 prefixEnd_8083048 461165419707044030136305 := by
  unfold tailWord_8083048
  simp only [CollatzResearch.WordTrace]
  refine ⟨147406490210252522769152899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196541986947003363692203865 147406490210252522769152899)
  ·
    refine ⟨221109735315378784153729349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147406490210252522769152899 221109735315378784153729349)
    ·
      refine ⟨41458075371633522028824253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221109735315378784153729349 41458075371633522028824253)
      ·
        refine ⟨15546778264362570760809095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41458075371633522028824253 15546778264362570760809095)
        ·
          refine ⟨23320167396543856141213643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15546778264362570760809095 23320167396543856141213643)
          ·
            refine ⟨34980251094815784211820465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23320167396543856141213643 34980251094815784211820465)
            ·
              refine ⟨26235188321111838158865349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34980251094815784211820465 26235188321111838158865349)
              ·
                refine ⟨4919097810208469654787253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26235188321111838158865349 4919097810208469654787253)
                ·
                  refine ⟨461165419707044030136305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4919097810208469654787253 461165419707044030136305)
                  ·
                    rfl

theorem cell23_8083048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 5].length) (baseStart_8083048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083048 prefixEnd_8083048 := by exact prefixLift 8083048
  have htrace : WordTrace (prefixWord ++ tailWord_8083048) baseStart_8083048 baseEnd_8083048 := by
    simpa [prefixWord, tailWord_8083048, baseEnd_8083048] using wordTrace_append hprefix tailTrace_8083048
  have hstable : (prefixWord ++ tailWord_8083048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083048).length < 2 ^ (prefixWord ++ tailWord_8083048).sum := by decide
  have hdescent : baseEnd_8083048 < baseStart_8083048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083061 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 1, 7]
def baseStart_8083061 : Nat := 118140960795 + 8083061 * 2 ^ 59
def prefixEnd_8083061 : Nat := 4983230072969 + 3 ^ 40 * 8083061 * 2
def baseEnd_8083061 : Nat := 1383498484203968240121395

theorem tailTrace_8083061 : CollatzResearch.WordTrace tailWord_8083061 prefixEnd_8083061 1383498484203968240121395 := by
  unfold tailWord_8083061
  simp only [CollatzResearch.WordTrace]
  refine ⟨294813454569457948758529037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196542303046305299172352691 294813454569457948758529037)
  ·
    refine ⟨110555045463546730784448389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294813454569457948758529037 110555045463546730784448389)
    ·
      refine ⟨20729071024415012022084073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110555045463546730784448389 20729071024415012022084073)
      ·
        refine ⟨15546803268311259016563055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20729071024415012022084073 15546803268311259016563055)
        ·
          refine ⟨23320204902466888524844583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15546803268311259016563055 23320204902466888524844583)
          ·
            refine ⟨34980307353700332787266875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23320204902466888524844583 34980307353700332787266875)
            ·
              refine ⟨52470461030550499180900313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34980307353700332787266875 52470461030550499180900313)
              ·
                refine ⟨39352845772912874385675235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52470461030550499180900313 39352845772912874385675235)
                ·
                  refine ⟨59029268659369311578512853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39352845772912874385675235 59029268659369311578512853)
                  ·
                    refine ⟨1383498484203968240121395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59029268659369311578512853 1383498484203968240121395)
                    ·
                      rfl

theorem cell23_8083061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_8083061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083061 prefixEnd_8083061 := by exact prefixLift 8083061
  have htrace : WordTrace (prefixWord ++ tailWord_8083061) baseStart_8083061 baseEnd_8083061 := by
    simpa [prefixWord, tailWord_8083061, baseEnd_8083061] using wordTrace_append hprefix tailTrace_8083061
  have hstable : (prefixWord ++ tailWord_8083061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083061).length < 2 ^ (prefixWord ++ tailWord_8083061).sum := by decide
  have hdescent : baseEnd_8083061 < baseStart_8083061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083081 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 1, 6, 2]
def baseStart_8083081 : Nat := 118140960795 + 8083081 * 2 ^ 59
def prefixEnd_8083081 : Nat := 4983230072969 + 3 ^ 40 * 8083081 * 2
def baseEnd_8083081 : Nat := 4150505722224994642114093

theorem tailTrace_8083081 : CollatzResearch.WordTrace tailWord_8083081 prefixEnd_8083081 4150505722224994642114093 := by
  unfold tailWord_8083081
  simp only [CollatzResearch.WordTrace]
  refine ⟨294814184029385492174257097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196542789352923661449504731 294814184029385492174257097)
  ·
    refine ⟨221110638022039119130692823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294814184029385492174257097 221110638022039119130692823)
    ·
      refine ⟨331665957033058678696039235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221110638022039119130692823 331665957033058678696039235)
      ·
        refine ⟨497498935549588018044058853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331665957033058678696039235 497498935549588018044058853)
        ·
          refine ⟨93281050415547753383261035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 497498935549588018044058853 93281050415547753383261035)
          ·
            refine ⟨139921575623321630074891553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93281050415547753383261035 139921575623321630074891553)
            ·
              refine ⟨104941181717491222556168665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139921575623321630074891553 104941181717491222556168665)
              ·
                refine ⟨78705886288118416917126499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104941181717491222556168665 78705886288118416917126499)
                ·
                  refine ⟨118058829432177625375689749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78705886288118416917126499 118058829432177625375689749)
                  ·
                    refine ⟨5534007629633326189485457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118058829432177625375689749 5534007629633326189485457)
                    ·
                      refine ⟨4150505722224994642114093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5534007629633326189485457 4150505722224994642114093)
                      ·
                        rfl

theorem cell23_8083081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 6, 2].length) (baseStart_8083081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083081 prefixEnd_8083081 := by exact prefixLift 8083081
  have htrace : WordTrace (prefixWord ++ tailWord_8083081) baseStart_8083081 baseEnd_8083081 := by
    simpa [prefixWord, tailWord_8083081, baseEnd_8083081] using wordTrace_append hprefix tailTrace_8083081
  have hstable : (prefixWord ++ tailWord_8083081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083081).length < 2 ^ (prefixWord ++ tailWord_8083081).sum := by decide
  have hdescent : baseEnd_8083081 < baseStart_8083081 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083108 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_8083108 : Nat := 118140960795 + 8083108 * 2 ^ 59
def prefixEnd_8083108 : Nat := 4983230072969 + 3 ^ 40 * 8083108 * 2
def baseEnd_8083108 : Nat := 1383506528734222012158823

theorem tailTrace_8083108 : CollatzResearch.WordTrace tailWord_8083108 prefixEnd_8083108 1383506528734222012158823 := by
  unfold tailWord_8083108
  simp only [CollatzResearch.WordTrace]
  refine ⟨147407584400143837892744989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196543445866858450523659985 147407584400143837892744989)
  ·
    refine ⟨55277844150053939209779371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147407584400143837892744989 55277844150053939209779371)
    ·
      refine ⟨82916766225080908814669057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55277844150053939209779371 82916766225080908814669057)
      ·
        refine ⟨62187574668810681611001793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82916766225080908814669057 62187574668810681611001793)
        ·
          refine ⟨46640681001608011208251345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62187574668810681611001793 46640681001608011208251345)
          ·
            refine ⟨34980510751206008406188509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46640681001608011208251345 34980510751206008406188509)
            ·
              refine ⟨13117691531702253152320691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34980510751206008406188509 13117691531702253152320691)
              ·
                refine ⟨19676537297553379728481037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13117691531702253152320691 19676537297553379728481037)
                ·
                  refine ⟨7378701486582517398180389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19676537297553379728481037 7378701486582517398180389)
                  ·
                    refine ⟨1383506528734222012158823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7378701486582517398180389 1383506528734222012158823)
                    ·
                      rfl

theorem cell23_8083108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_8083108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083108 prefixEnd_8083108 := by exact prefixLift 8083108
  have htrace : WordTrace (prefixWord ++ tailWord_8083108) baseStart_8083108 baseEnd_8083108 := by
    simpa [prefixWord, tailWord_8083108, baseEnd_8083108] using wordTrace_append hprefix tailTrace_8083108
  have hstable : (prefixWord ++ tailWord_8083108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083108).length < 2 ^ (prefixWord ++ tailWord_8083108).sum := by decide
  have hdescent : baseEnd_8083108 < baseStart_8083108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083151 : List Nat := [1, 1, 2, 1, 1, 3, 1, 7, 1, 5]
def baseStart_8083151 : Nat := 118140960795 + 8083151 * 2 ^ 59
def prefixEnd_8083151 : Nat := 4983230072969 + 3 ^ 40 * 8083151 * 2
def baseEnd_8083151 : Nat := 1383513888623603122746257

theorem tailTrace_8083151 : CollatzResearch.WordTrace tailWord_8083151 prefixEnd_8083151 1383513888623603122746257 := by
  unfold tailWord_8083151
  simp only [CollatzResearch.WordTrace]
  refine ⟨294816737139131894129305307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196544491426087929419536871 294816737139131894129305307)
  ·
    refine ⟨442225105708697841193957961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294816737139131894129305307 442225105708697841193957961)
    ·
      refine ⟨331668829281523380895468471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442225105708697841193957961 331668829281523380895468471)
      ·
        refine ⟨497503243922285071343202707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331668829281523380895468471 497503243922285071343202707)
        ·
          refine ⟨746254865883427607014804061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497503243922285071343202707 746254865883427607014804061)
          ·
            refine ⟨279845574706285352630551523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 746254865883427607014804061 279845574706285352630551523)
            ·
              refine ⟨419768362059428028945827285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279845574706285352630551523 419768362059428028945827285)
              ·
                refine ⟨9838320985767844428417827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 419768362059428028945827285 9838320985767844428417827)
                ·
                  refine ⟨14757481478651766642626741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9838320985767844428417827 14757481478651766642626741)
                  ·
                    refine ⟨1383513888623603122746257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14757481478651766642626741 1383513888623603122746257)
                    ·
                      rfl

theorem cell23_8083151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 5].length) (baseStart_8083151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083151 prefixEnd_8083151 := by exact prefixLift 8083151
  have htrace : WordTrace (prefixWord ++ tailWord_8083151) baseStart_8083151 baseEnd_8083151 := by
    simpa [prefixWord, tailWord_8083151, baseEnd_8083151] using wordTrace_append hprefix tailTrace_8083151
  have hstable : (prefixWord ++ tailWord_8083151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083151).length < 2 ^ (prefixWord ++ tailWord_8083151).sum := by decide
  have hdescent : baseEnd_8083151 < baseStart_8083151 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083271 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 4, 6]
def baseStart_8083271 : Nat := 118140960795 + 8083271 * 2 ^ 59
def prefixEnd_8083271 : Nat := 4983230072969 + 3 ^ 40 * 8083271 * 2
def baseEnd_8083271 : Nat := 1383534427849782966246073

theorem tailTrace_8083271 : CollatzResearch.WordTrace tailWord_8083271 prefixEnd_8083271 1383534427849782966246073 := by
  unfold tailWord_8083271
  simp only [CollatzResearch.WordTrace]
  refine ⟨294821113898697154623673667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196547409265798103082449111 294821113898697154623673667)
  ·
    refine ⟨442231670848045731935510501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294821113898697154623673667 442231670848045731935510501)
    ·
      refine ⟨82918438284008574737908219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442231670848045731935510501 82918438284008574737908219)
      ·
        refine ⟨124377657426012862106862329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82918438284008574737908219 124377657426012862106862329)
        ·
          refine ⟨93283243069509646580146747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124377657426012862106862329 93283243069509646580146747)
          ·
            refine ⟨139924864604264469870220121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93283243069509646580146747 139924864604264469870220121)
            ·
              refine ⟨104943648453198352402665091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139924864604264469870220121 104943648453198352402665091)
              ·
                refine ⟨157415472679797528603997637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104943648453198352402665091 157415472679797528603997637)
                ·
                  refine ⟨29515401127462036613249557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157415472679797528603997637 29515401127462036613249557)
                  ·
                    refine ⟨1383534427849782966246073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29515401127462036613249557 1383534427849782966246073)
                    ·
                      rfl

theorem cell23_8083271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_8083271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083271 prefixEnd_8083271 := by exact prefixLift 8083271
  have htrace : WordTrace (prefixWord ++ tailWord_8083271) baseStart_8083271 baseEnd_8083271 := by
    simpa [prefixWord, tailWord_8083271, baseEnd_8083271] using wordTrace_append hprefix tailTrace_8083271
  have hstable : (prefixWord ++ tailWord_8083271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083271).length < 2 ^ (prefixWord ++ tailWord_8083271).sum := by decide
  have hdescent : baseEnd_8083271 < baseStart_8083271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083299 : List Nat := [1, 1, 1, 5, 4, 2, 1, 2, 1, 3, 2]
def baseStart_8083299 : Nat := 118140960795 + 8083299 * 2 ^ 59
def prefixEnd_8083299 : Nat := 4983230072969 + 3 ^ 40 * 8083299 * 2
def baseEnd_8083299 : Nat := 4150617661007674789188091

theorem tailTrace_8083299 : CollatzResearch.WordTrace tailWord_8083299 prefixEnd_8083299 4150617661007674789188091 := by
  unfold tailWord_8083299
  simp only [CollatzResearch.WordTrace]
  refine ⟨294822135142595715405692951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196548090095063810270461967 294822135142595715405692951)
  ·
    refine ⟨442233202713893573108539427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294822135142595715405692951 442233202713893573108539427)
    ·
      refine ⟨663349804070840359662809141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442233202713893573108539427 663349804070840359662809141)
      ·
        refine ⟨62189044131641283718388357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 663349804070840359662809141 62189044131641283718388357)
        ·
          refine ⟨11660445774682740697197817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62189044131641283718388357 11660445774682740697197817)
          ·
            refine ⟨8745334331012055522898363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11660445774682740697197817 8745334331012055522898363)
            ·
              refine ⟨13118001496518083284347545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8745334331012055522898363 13118001496518083284347545)
              ·
                refine ⟨9838501122388562463260659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13118001496518083284347545 9838501122388562463260659)
                ·
                  refine ⟨14757751683582843694890989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9838501122388562463260659 14757751683582843694890989)
                  ·
                    refine ⟨5534156881343566385584121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14757751683582843694890989 5534156881343566385584121)
                    ·
                      refine ⟨4150617661007674789188091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5534156881343566385584121 4150617661007674789188091)
                      ·
                        rfl

theorem cell23_8083299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_8083299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083299 prefixEnd_8083299 := by exact prefixLift 8083299
  have htrace : WordTrace (prefixWord ++ tailWord_8083299) baseStart_8083299 baseEnd_8083299 := by
    simpa [prefixWord, tailWord_8083299, baseEnd_8083299] using wordTrace_append hprefix tailTrace_8083299
  have hstable : (prefixWord ++ tailWord_8083299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083299).length < 2 ^ (prefixWord ++ tailWord_8083299).sum := by decide
  have hdescent : baseEnd_8083299 < baseStart_8083299 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083301 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 9]
def baseStart_8083301 : Nat := 118140960795 + 8083301 * 2 ^ 59
def prefixEnd_8083301 : Nat := 4983230072969 + 3 ^ 40 * 8083301 * 2
def baseEnd_8083301 : Nat := 461179854218775975707009

theorem tailTrace_8083301 : CollatzResearch.WordTrace tailWord_8083301 prefixEnd_8083301 461179854218775975707009 := by
  unfold tailWord_8083301
  simp only [CollatzResearch.WordTrace]
  refine ⟨294822208088588469747265757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196548138725725646498177171 294822208088588469747265757)
  ·
    refine ⟨110558328033220676155224659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294822208088588469747265757 110558328033220676155224659)
    ·
      refine ⟨165837492049831014232836989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110558328033220676155224659 165837492049831014232836989)
      ·
        refine ⟨62189059518686630337313871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165837492049831014232836989 62189059518686630337313871)
        ·
          refine ⟨93283589278029945505970807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62189059518686630337313871 93283589278029945505970807)
          ·
            refine ⟨139925383917044918258956211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93283589278029945505970807 139925383917044918258956211)
            ·
              refine ⟨209888075875567377388434317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139925383917044918258956211 209888075875567377388434317)
              ·
                refine ⟨78708028453337766520662869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209888075875567377388434317 78708028453337766520662869)
                ·
                  refine ⟨461179854218775975707009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78708028453337766520662869 461179854218775975707009)
                  ·
                    rfl

theorem cell23_8083301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_8083301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083301 prefixEnd_8083301 := by exact prefixLift 8083301
  have htrace : WordTrace (prefixWord ++ tailWord_8083301) baseStart_8083301 baseEnd_8083301 := by
    simpa [prefixWord, tailWord_8083301, baseEnd_8083301] using wordTrace_append hprefix tailTrace_8083301
  have hstable : (prefixWord ++ tailWord_8083301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083301).length < 2 ^ (prefixWord ++ tailWord_8083301).sum := by decide
  have hdescent : baseEnd_8083301 < baseStart_8083301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083328 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 3]
def baseStart_8083328 : Nat := 118140960795 + 8083328 * 2 ^ 59
def prefixEnd_8083328 : Nat := 4983230072969 + 3 ^ 40 * 8083328 * 2
def baseEnd_8083328 : Nat := 4150632551946655175725457

theorem tailTrace_8083328 : CollatzResearch.WordTrace tailWord_8083328 prefixEnd_8083328 4150632551946655175725457 := by
  unfold tailWord_8083328
  simp only [CollatzResearch.WordTrace]
  refine ⟨147411596429745326679249319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196548795239660435572332425 147411596429745326679249319)
  ·
    refine ⟨221117394644617990018873979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147411596429745326679249319 221117394644617990018873979)
    ·
      refine ⟨331676091966926985028310969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221117394644617990018873979 331676091966926985028310969)
      ·
        refine ⟨248757068975195238771233227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331676091966926985028310969 248757068975195238771233227)
        ·
          refine ⟨373135603462792858156849841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248757068975195238771233227 373135603462792858156849841)
          ·
            refine ⟨279851702597094643617637381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373135603462792858156849841 279851702597094643617637381)
            ·
              refine ⟨52472194236955245678307009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279851702597094643617637381 52472194236955245678307009)
              ·
                refine ⟨39354145677716434258730257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52472194236955245678307009 39354145677716434258730257)
                ·
                  refine ⟨29515609258287325694047693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39354145677716434258730257 29515609258287325694047693)
                  ·
                    refine ⟨11068353471857747135267885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29515609258287325694047693 11068353471857747135267885)
                    ·
                      refine ⟨4150632551946655175725457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11068353471857747135267885 4150632551946655175725457)
                      ·
                        rfl

theorem cell23_8083328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_8083328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083328 prefixEnd_8083328 := by exact prefixLift 8083328
  have htrace : WordTrace (prefixWord ++ tailWord_8083328) baseStart_8083328 baseEnd_8083328 := by
    simpa [prefixWord, tailWord_8083328, baseEnd_8083328] using wordTrace_append hprefix tailTrace_8083328
  have hstable : (prefixWord ++ tailWord_8083328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083328).length < 2 ^ (prefixWord ++ tailWord_8083328).sum := by decide
  have hdescent : baseEnd_8083328 < baseStart_8083328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083342 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4]
def baseStart_8083342 : Nat := 118140960795 + 8083342 * 2 ^ 59
def prefixEnd_8083342 : Nat := 4983230072969 + 3 ^ 40 * 8083342 * 2
def baseEnd_8083342 : Nat := 4150639740675818120950393

theorem tailTrace_8083342 : CollatzResearch.WordTrace tailWord_8083342 prefixEnd_8083342 4150639740675818120950393 := by
  unfold tailWord_8083342
  simp only [CollatzResearch.WordTrace]
  refine ⟨36852962935179991718688535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196549135654293289166338853 36852962935179991718688535)
  ·
    refine ⟨55279444402769987578032803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36852962935179991718688535 55279444402769987578032803)
    ·
      refine ⟨82919166604154981367049205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55279444402769987578032803 82919166604154981367049205)
      ·
        refine ⟨7773671869139529503160863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82919166604154981367049205 7773671869139529503160863)
        ·
          refine ⟨11660507803709294254741295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7773671869139529503160863 11660507803709294254741295)
          ·
            refine ⟨17490761705563941382111943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11660507803709294254741295 17490761705563941382111943)
            ·
              refine ⟨26236142558345912073167915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17490761705563941382111943 26236142558345912073167915)
              ·
                refine ⟨39354213837518868109751873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26236142558345912073167915 39354213837518868109751873)
                ·
                  refine ⟨29515660378139151082313905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39354213837518868109751873 29515660378139151082313905)
                  ·
                    refine ⟨22136745283604363311735429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29515660378139151082313905 22136745283604363311735429)
                    ·
                      refine ⟨4150639740675818120950393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22136745283604363311735429 4150639740675818120950393)
                      ·
                        rfl

theorem cell23_8083342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_8083342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083342 prefixEnd_8083342 := by exact prefixLift 8083342
  have htrace : WordTrace (prefixWord ++ tailWord_8083342) baseStart_8083342 baseEnd_8083342 := by
    simpa [prefixWord, tailWord_8083342, baseEnd_8083342] using wordTrace_append hprefix tailTrace_8083342
  have hstable : (prefixWord ++ tailWord_8083342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083342).length < 2 ^ (prefixWord ++ tailWord_8083342).sum := by decide
  have hdescent : baseEnd_8083342 < baseStart_8083342 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083371 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 9]
def baseStart_8083371 : Nat := 118140960795 + 8083371 * 2 ^ 59
def prefixEnd_8083371 : Nat := 4983230072969 + 3 ^ 40 * 8083371 * 2
def baseEnd_8083371 : Nat := 4150654631614798507487759

theorem tailTrace_8083371 : CollatzResearch.WordTrace tailWord_8083371 prefixEnd_8083371 4150654631614798507487759 := by
  unfold tailWord_8083371
  simp only [CollatzResearch.WordTrace]
  refine ⟨294824761198334871702313967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196549840798889914468209311 294824761198334871702313967)
  ·
    refine ⟨442237141797502307553470951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294824761198334871702313967 442237141797502307553470951)
    ·
      refine ⟨663355712696253461330206427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442237141797502307553470951 663355712696253461330206427)
      ·
        refine ⟨995033569044380191995309641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663355712696253461330206427 995033569044380191995309641)
        ·
          refine ⟨746275176783285143996482231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 995033569044380191995309641 746275176783285143996482231)
          ·
            refine ⟨1119412765174927715994723347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746275176783285143996482231 1119412765174927715994723347)
            ·
              refine ⟨1679119147762391573992085021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119412765174927715994723347 1679119147762391573992085021)
              ·
                refine ⟨629669680410896840247031883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1679119147762391573992085021 629669680410896840247031883)
                ·
                  refine ⟨944504520616345260370547825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629669680410896840247031883 944504520616345260370547825)
                  ·
                    refine ⟨708378390462258945277910869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 944504520616345260370547825 708378390462258945277910869)
                    ·
                      refine ⟨4150654631614798507487759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 708378390462258945277910869 4150654631614798507487759)
                      ·
                        rfl

theorem cell23_8083371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_8083371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083371 prefixEnd_8083371 := by exact prefixLift 8083371
  have htrace : WordTrace (prefixWord ++ tailWord_8083371) baseStart_8083371 baseEnd_8083371 := by
    simpa [prefixWord, tailWord_8083371, baseEnd_8083371] using wordTrace_append hprefix tailTrace_8083371
  have hstable : (prefixWord ++ tailWord_8083371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083371).length < 2 ^ (prefixWord ++ tailWord_8083371).sum := by decide
  have hdescent : baseEnd_8083371 < baseStart_8083371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083380 : List Nat := [2, 5, 2, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_8083380 : Nat := 118140960795 + 8083380 * 2 ^ 59
def prefixEnd_8083380 : Nat := 4983230072969 + 3 ^ 40 * 8083380 * 2
def baseEnd_8083380 : Nat := 4150659252940688972275219

theorem tailTrace_8083380 : CollatzResearch.WordTrace tailWord_8083380 prefixEnd_8083380 4150659252940688972275219 := by
  unfold tailWord_8083380
  simp only [CollatzResearch.WordTrace]
  refine ⟨147412544727651133119695797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196550059636868177492927729 147412544727651133119695797)
  ·
    refine ⟨13819926068217293729971481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147412544727651133119695797 13819926068217293729971481)
    ·
      refine ⟨10364944551162970297478611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13819926068217293729971481 10364944551162970297478611)
      ·
        refine ⟨15547416826744455446217917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10364944551162970297478611 15547416826744455446217917)
        ·
          refine ⟨5830281310029170792331719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15547416826744455446217917 5830281310029170792331719)
          ·
            refine ⟨8745421965043756188497579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5830281310029170792331719 8745421965043756188497579)
            ·
              refine ⟨13118132947565634282746369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8745421965043756188497579 13118132947565634282746369)
              ·
                refine ⟨9838599710674225712059777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13118132947565634282746369 9838599710674225712059777)
                ·
                  refine ⟨7378949783005669284044833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9838599710674225712059777 7378949783005669284044833)
                  ·
                    refine ⟨5534212337254251963033625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7378949783005669284044833 5534212337254251963033625)
                    ·
                      refine ⟨4150659252940688972275219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5534212337254251963033625 4150659252940688972275219)
                      ·
                        rfl

theorem cell23_8083380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_8083380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083380 prefixEnd_8083380 := by exact prefixLift 8083380
  have htrace : WordTrace (prefixWord ++ tailWord_8083380) baseStart_8083380 baseEnd_8083380 := by
    simpa [prefixWord, tailWord_8083380, baseEnd_8083380] using wordTrace_append hprefix tailTrace_8083380
  have hstable : (prefixWord ++ tailWord_8083380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083380).length < 2 ^ (prefixWord ++ tailWord_8083380).sum := by decide
  have hdescent : baseEnd_8083380 < baseStart_8083380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083385 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 4, 4, 2]
def baseStart_8083385 : Nat := 118140960795 + 8083385 * 2 ^ 59
def prefixEnd_8083385 : Nat := 4983230072969 + 3 ^ 40 * 8083385 * 2
def baseEnd_8083385 : Nat := 4150661820343961452712695

theorem tailTrace_8083385 : CollatzResearch.WordTrace tailWord_8083385 prefixEnd_8083385 4150661820343961452712695 := by
  unfold tailWord_8083385
  simp only [CollatzResearch.WordTrace]
  refine ⟨294825271820284152093323609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196550181213522768062215739 294825271820284152093323609)
  ·
    refine ⟨221118953865213114069992707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294825271820284152093323609 221118953865213114069992707)
    ·
      refine ⟨331678430797819671104989061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221118953865213114069992707 331678430797819671104989061)
      ·
        refine ⟨62189705774591188332185449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331678430797819671104989061 62189705774591188332185449)
        ·
          refine ⟨46642279330943391249139087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62189705774591188332185449 46642279330943391249139087)
          ·
            refine ⟨69963418996415086873708631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46642279330943391249139087 69963418996415086873708631)
            ·
              refine ⟨104945128494622630310562947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69963418996415086873708631 104945128494622630310562947)
              ·
                refine ⟨157417692741933945465844421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104945128494622630310562947 157417692741933945465844421)
                ·
                  refine ⟨29515817389112614774845829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157417692741933945465844421 29515817389112614774845829)
                  ·
                    refine ⟨5534215760458615270283593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29515817389112614774845829 5534215760458615270283593)
                    ·
                      refine ⟨4150661820343961452712695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5534215760458615270283593 4150661820343961452712695)
                      ·
                        rfl

theorem cell23_8083385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_8083385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083385 prefixEnd_8083385 := by exact prefixLift 8083385
  have htrace : WordTrace (prefixWord ++ tailWord_8083385) baseStart_8083385 baseEnd_8083385 := by
    simpa [prefixWord, tailWord_8083385, baseEnd_8083385] using wordTrace_append hprefix tailTrace_8083385
  have hstable : (prefixWord ++ tailWord_8083385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083385).length < 2 ^ (prefixWord ++ tailWord_8083385).sum := by decide
  have hdescent : baseEnd_8083385 < baseStart_8083385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083408 : List Nat := [2, 1, 1, 1, 1, 2, 4, 5, 6]
def baseStart_8083408 : Nat := 118140960795 + 8083408 * 2 ^ 59
def prefixEnd_8083408 : Nat := 4983230072969 + 3 ^ 40 * 8083408 * 2
def baseEnd_8083408 : Nat := 461185958933223873636121

theorem tailTrace_8083408 : CollatzResearch.WordTrace tailWord_8083408 prefixEnd_8083408 461185958933223873636121 := by
  unfold tailWord_8083408
  simp only [CollatzResearch.WordTrace]
  refine ⟨147413055349600413510705439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196550740466133884680940585 147413055349600413510705439)
  ·
    refine ⟨221119583024400620266058159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147413055349600413510705439 221119583024400620266058159)
    ·
      refine ⟨331679374536600930399087239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221119583024400620266058159 331679374536600930399087239)
      ·
        refine ⟨497519061804901395598630859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331679374536600930399087239 497519061804901395598630859)
        ·
          refine ⟨746278592707352093397946289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497519061804901395598630859 746278592707352093397946289)
          ·
            refine ⟨559708944530514070048459717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 746278592707352093397946289 559708944530514070048459717)
            ·
              refine ⟨104945427099471388134086197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 559708944530514070048459717 104945427099471388134086197)
              ·
                refine ⟨9838633790575442637570581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104945427099471388134086197 9838633790575442637570581)
                ·
                  refine ⟨461185958933223873636121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9838633790575442637570581 461185958933223873636121)
                  ·
                    rfl

theorem cell23_8083408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 6].length) (baseStart_8083408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083408 prefixEnd_8083408 := by exact prefixLift 8083408
  have htrace : WordTrace (prefixWord ++ tailWord_8083408) baseStart_8083408 baseEnd_8083408 := by
    simpa [prefixWord, tailWord_8083408, baseEnd_8083408] using wordTrace_append hprefix tailTrace_8083408
  have hstable : (prefixWord ++ tailWord_8083408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083408).length < 2 ^ (prefixWord ++ tailWord_8083408).sum := by decide
  have hdescent : baseEnd_8083408 < baseStart_8083408 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083435 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 5, 1, 3]
def baseStart_8083435 : Nat := 118140960795 + 8083435 * 2 ^ 59
def prefixEnd_8083435 : Nat := 4983230072969 + 3 ^ 40 * 8083435 * 2
def baseEnd_8083435 : Nat := 4150687494376686257087465

theorem tailTrace_8083435 : CollatzResearch.WordTrace tailWord_8083435 prefixEnd_8083435 4150687494376686257087465 := by
  unfold tailWord_8083435
  simp only [CollatzResearch.WordTrace]
  refine ⟨294827095470103010632643759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196551396980068673755095839 294827095470103010632643759)
  ·
    refine ⟨442240643205154515948965639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294827095470103010632643759 442240643205154515948965639)
    ·
      refine ⟨663360964807731773923448459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442240643205154515948965639 663360964807731773923448459)
      ·
        refine ⟨995041447211597660885172689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663360964807731773923448459 995041447211597660885172689)
        ·
          refine ⟨746281085408698245663879517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 995041447211597660885172689 746281085408698245663879517)
          ·
            refine ⟨279855407028261842123954819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 746281085408698245663879517 279855407028261842123954819)
            ·
              refine ⟨419783110542392763185932229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279855407028261842123954819 419783110542392763185932229)
              ·
                refine ⟨78709333226698643097362293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 419783110542392763185932229 78709333226698643097362293)
                ·
                  refine ⟨7378999990002997790377715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78709333226698643097362293 7378999990002997790377715)
                  ·
                    refine ⟨11068499985004496685566573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7378999990002997790377715 11068499985004496685566573)
                    ·
                      refine ⟨4150687494376686257087465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11068499985004496685566573 4150687494376686257087465)
                      ·
                        rfl

theorem cell23_8083435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 1, 3].length) (baseStart_8083435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083435 prefixEnd_8083435 := by exact prefixLift 8083435
  have htrace : WordTrace (prefixWord ++ tailWord_8083435) baseStart_8083435 baseEnd_8083435 := by
    simpa [prefixWord, tailWord_8083435, baseEnd_8083435] using wordTrace_append hprefix tailTrace_8083435
  have hstable : (prefixWord ++ tailWord_8083435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083435).length < 2 ^ (prefixWord ++ tailWord_8083435).sum := by decide
  have hdescent : baseEnd_8083435 < baseStart_8083435 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083446 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_8083446 : Nat := 118140960795 + 8083446 * 2 ^ 59
def prefixEnd_8083446 : Nat := 4983230072969 + 3 ^ 40 * 8083446 * 2
def baseEnd_8083446 : Nat := 1383564380887961904683305

theorem tailTrace_8083446 : CollatzResearch.WordTrace tailWord_8083446 prefixEnd_8083446 1383564380887961904683305 := by
  unfold tailWord_8083446
  simp only [CollatzResearch.WordTrace]
  refine ⟨18426718542066447469455887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196551664448708773007529461 18426718542066447469455887)
  ·
    refine ⟨27640077813099671204183831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18426718542066447469455887 27640077813099671204183831)
    ·
      refine ⟨41460116719649506806275747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27640077813099671204183831 41460116719649506806275747)
      ·
        refine ⟨62190175079474260209413621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41460116719649506806275747 62190175079474260209413621)
        ·
          refine ⟨5830328913700711894632527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62190175079474260209413621 5830328913700711894632527)
          ·
            refine ⟨8745493370551067841948791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5830328913700711894632527 8745493370551067841948791)
            ·
              refine ⟨13118240055826601762923187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8745493370551067841948791 13118240055826601762923187)
              ·
                refine ⟨19677360083739902644384781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13118240055826601762923187 19677360083739902644384781)
                ·
                  refine ⟨7379010031402463491644293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19677360083739902644384781 7379010031402463491644293)
                  ·
                    refine ⟨1383564380887961904683305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7379010031402463491644293 1383564380887961904683305)
                    ·
                      rfl

theorem cell23_8083446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_8083446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083446 prefixEnd_8083446 := by exact prefixLift 8083446
  have htrace : WordTrace (prefixWord ++ tailWord_8083446) baseStart_8083446 baseEnd_8083446 := by
    simpa [prefixWord, tailWord_8083446, baseEnd_8083446] using wordTrace_append hprefix tailTrace_8083446
  have hstable : (prefixWord ++ tailWord_8083446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083446).length < 2 ^ (prefixWord ++ tailWord_8083446).sum := by decide
  have hdescent : baseEnd_8083446 < baseStart_8083446 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083475 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 2, 6, 2]
def baseStart_8083475 : Nat := 118140960795 + 8083475 * 2 ^ 59
def prefixEnd_8083475 : Nat := 4983230072969 + 3 ^ 40 * 8083475 * 2
def baseEnd_8083475 : Nat := 4150708033602866100587281

theorem tailTrace_8083475 : CollatzResearch.WordTrace tailWord_8083475 prefixEnd_8083475 4150708033602866100587281 := by
  unfold tailWord_8083475
  simp only [CollatzResearch.WordTrace]
  refine ⟨294828554389958097464099879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196552369593305398309399919 294828554389958097464099879)
  ·
    refine ⟨442242831584937146196149819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294828554389958097464099879 442242831584937146196149819)
    ·
      refine ⟨663364247377405719294224729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442242831584937146196149819 663364247377405719294224729)
      ·
        refine ⟨497523185533054289470668547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 663364247377405719294224729 497523185533054289470668547)
        ·
          refine ⟨746284778299581434206002821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497523185533054289470668547 746284778299581434206002821)
          ·
            refine ⟨139928395931171518913625529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 746284778299581434206002821 139928395931171518913625529)
            ·
              refine ⟨104946296948378639185219147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139928395931171518913625529 104946296948378639185219147)
              ·
                refine ⟨157419445422567958777828721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104946296948378639185219147 157419445422567958777828721)
                ·
                  refine ⟨118064584066925969083371541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157419445422567958777828721 118064584066925969083371541)
                  ·
                    refine ⟨5534277378137154800783041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118064584066925969083371541 5534277378137154800783041)
                    ·
                      refine ⟨4150708033602866100587281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5534277378137154800783041 4150708033602866100587281)
                      ·
                        rfl

theorem cell23_8083475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 6, 2].length) (baseStart_8083475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083475 prefixEnd_8083475 := by exact prefixLift 8083475
  have htrace : WordTrace (prefixWord ++ tailWord_8083475) baseStart_8083475 baseEnd_8083475 := by
    simpa [prefixWord, tailWord_8083475, baseEnd_8083475] using wordTrace_append hprefix tailTrace_8083475
  have hstable : (prefixWord ++ tailWord_8083475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083475).length < 2 ^ (prefixWord ++ tailWord_8083475).sum := by decide
  have hdescent : baseEnd_8083475 < baseStart_8083475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083485 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_8083485 : Nat := 118140960795 + 8083485 * 2 ^ 59
def prefixEnd_8083485 : Nat := 4983230072969 + 3 ^ 40 * 8083485 * 2
def baseEnd_8083485 : Nat := 1383571056136470353820745

theorem tailTrace_8083485 : CollatzResearch.WordTrace tailWord_8083485 prefixEnd_8083485 1383571056136470353820745 := by
  unfold tailWord_8083485
  simp only [CollatzResearch.WordTrace]
  refine ⟨294828919119921869171963909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196552612746614579447975939 294828919119921869171963909)
  ·
    refine ⟨55280422334985350469743233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294828919119921869171963909 55280422334985350469743233)
    ·
      refine ⟨41460316751239012852307425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55280422334985350469743233 41460316751239012852307425)
      ·
        refine ⟨31095237563429259639230569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41460316751239012852307425 31095237563429259639230569)
        ·
          refine ⟨23321428172571944729422927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31095237563429259639230569 23321428172571944729422927)
          ·
            refine ⟨34982142258857917094134391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23321428172571944729422927 34982142258857917094134391)
            ·
              refine ⟨52473213388286875641201587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34982142258857917094134391 52473213388286875641201587)
              ·
                refine ⟨78709820082430313461802381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52473213388286875641201587 78709820082430313461802381)
                ·
                  refine ⟨29516182530911367548175893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78709820082430313461802381 29516182530911367548175893)
                  ·
                    refine ⟨1383571056136470353820745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29516182530911367548175893 1383571056136470353820745)
                    ·
                      rfl

theorem cell23_8083485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_8083485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083485 prefixEnd_8083485 := by exact prefixLift 8083485
  have htrace : WordTrace (prefixWord ++ tailWord_8083485) baseStart_8083485 baseEnd_8083485 := by
    simpa [prefixWord, tailWord_8083485, baseEnd_8083485] using wordTrace_append hprefix tailTrace_8083485
  have hstable : (prefixWord ++ tailWord_8083485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083485).length < 2 ^ (prefixWord ++ tailWord_8083485).sum := by decide
  have hdescent : baseEnd_8083485 < baseStart_8083485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083489 : List Nat := [1, 2, 3, 2, 4, 1, 3, 1, 1, 5]
def baseStart_8083489 : Nat := 118140960795 + 8083489 * 2 ^ 59
def prefixEnd_8083489 : Nat := 4983230072969 + 3 ^ 40 * 8083489 * 2
def baseEnd_8083489 : Nat := 1383571740777343015270739

theorem tailTrace_8083489 : CollatzResearch.WordTrace tailWord_8083489 prefixEnd_8083489 1383571740777343015270739 := by
  unfold tailWord_8083489
  simp only [CollatzResearch.WordTrace]
  refine ⟨294829065011907377855109521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196552710007938251903406347 294829065011907377855109521)
  ·
    refine ⟨221121798758930533391332141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294829065011907377855109521 221121798758930533391332141)
    ·
      refine ⟨82920674534598950021749553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221121798758930533391332141 82920674534598950021749553)
      ·
        refine ⟨62190505900949212516312165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82920674534598950021749553 62190505900949212516312165)
        ·
          refine ⟨11660719856427977346808531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62190505900949212516312165 11660719856427977346808531)
          ·
            refine ⟨17491079784641966020212797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11660719856427977346808531 17491079784641966020212797)
            ·
              refine ⟨6559154919240737257579799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17491079784641966020212797 6559154919240737257579799)
              ·
                refine ⟨9838732378861105886369699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559154919240737257579799 9838732378861105886369699)
                ·
                  refine ⟨14758098568291658829554549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9838732378861105886369699 14758098568291658829554549)
                  ·
                    refine ⟨1383571740777343015270739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14758098568291658829554549 1383571740777343015270739)
                    ·
                      rfl

theorem cell23_8083489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_8083489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083489 prefixEnd_8083489 := by exact prefixLift 8083489
  have htrace : WordTrace (prefixWord ++ tailWord_8083489) baseStart_8083489 baseEnd_8083489 := by
    simpa [prefixWord, tailWord_8083489, baseEnd_8083489] using wordTrace_append hprefix tailTrace_8083489
  have hstable : (prefixWord ++ tailWord_8083489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083489).length < 2 ^ (prefixWord ++ tailWord_8083489).sum := by decide
  have hdescent : baseEnd_8083489 < baseStart_8083489 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083575 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 2, 6]
def baseStart_8083575 : Nat := 118140960795 + 8083575 * 2 ^ 59
def prefixEnd_8083575 : Nat := 4983230072969 + 3 ^ 40 * 8083575 * 2
def baseEnd_8083575 : Nat := 1383586460556105236445607

theorem tailTrace_8083575 : CollatzResearch.WordTrace tailWord_8083575 prefixEnd_8083575 1383586460556105236445607 := by
  unfold tailWord_8083575
  simp only [CollatzResearch.WordTrace]
  refine ⟨294832201689595814542740179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196554801126397209695160119 294832201689595814542740179)
  ·
    refine ⟨442248302534393721814110269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294832201689595814542740179 442248302534393721814110269)
    ·
      refine ⟨165843113450397645680291351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442248302534393721814110269 165843113450397645680291351)
      ·
        refine ⟨248764670175596468520437027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165843113450397645680291351 248764670175596468520437027)
        ·
          refine ⟨373147005263394702780655541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248764670175596468520437027 373147005263394702780655541)
          ·
            refine ⟨34982531743443253385686457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 373147005263394702780655541 34982531743443253385686457)
            ·
              refine ⟨26236898807582440039264843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34982531743443253385686457 26236898807582440039264843)
              ·
                refine ⟨39355348211373660058897265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26236898807582440039264843 39355348211373660058897265)
                ·
                  refine ⟨29516511158530245044172949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39355348211373660058897265 29516511158530245044172949)
                  ·
                    refine ⟨1383586460556105236445607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29516511158530245044172949 1383586460556105236445607)
                    ·
                      rfl

theorem cell23_8083575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_8083575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083575 prefixEnd_8083575 := by exact prefixLift 8083575
  have htrace : WordTrace (prefixWord ++ tailWord_8083575) baseStart_8083575 baseEnd_8083575 := by
    simpa [prefixWord, tailWord_8083575, baseEnd_8083575] using wordTrace_append hprefix tailTrace_8083575
  have hstable : (prefixWord ++ tailWord_8083575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083575).length < 2 ^ (prefixWord ++ tailWord_8083575).sum := by decide
  have hdescent : baseEnd_8083575 < baseStart_8083575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083602 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_8083602 : Nat := 118140960795 + 8083602 * 2 ^ 59
def prefixEnd_8083602 : Nat := 4983230072969 + 3 ^ 40 * 8083602 * 2
def baseEnd_8083602 : Nat := 4150773245645987103699197

theorem tailTrace_8083602 : CollatzResearch.WordTrace tailWord_8083602 prefixEnd_8083602 4150773245645987103699197 := by
  unfold tailWord_8083602
  simp only [CollatzResearch.WordTrace]
  refine ⟨73708296615124499538493265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196555457640331998769315373 73708296615124499538493265)
  ·
    refine ⟨55281222461343374653869949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73708296615124499538493265 55281222461343374653869949)
    ·
      refine ⟨20730458423003765495201231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55281222461343374653869949 20730458423003765495201231)
      ·
        refine ⟨31095687634505648242801847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20730458423003765495201231 31095687634505648242801847)
        ·
          refine ⟨46643531451758472364202771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31095687634505648242801847 46643531451758472364202771)
          ·
            refine ⟨69965297177637708546304157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46643531451758472364202771 69965297177637708546304157)
            ·
              refine ⟨26236986441614140704864059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69965297177637708546304157 26236986441614140704864059)
              ·
                refine ⟨39355479662421211057296089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26236986441614140704864059 39355479662421211057296089)
                ·
                  refine ⟨29516609746815908292972067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39355479662421211057296089 29516609746815908292972067)
                  ·
                    refine ⟨44274914620223862439458101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29516609746815908292972067 44274914620223862439458101)
                    ·
                      refine ⟨4150773245645987103699197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44274914620223862439458101 4150773245645987103699197)
                      ·
                        rfl

theorem cell23_8083602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_8083602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083602 prefixEnd_8083602 := by exact prefixLift 8083602
  have htrace : WordTrace (prefixWord ++ tailWord_8083602) baseStart_8083602 baseEnd_8083602 := by
    simpa [prefixWord, tailWord_8083602, baseEnd_8083602] using wordTrace_append hprefix tailTrace_8083602
  have hstable : (prefixWord ++ tailWord_8083602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083602).length < 2 ^ (prefixWord ++ tailWord_8083602).sum := by decide
  have hdescent : baseEnd_8083602 < baseStart_8083602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083633 : List Nat := [1, 2, 2, 5, 2, 1, 1, 3, 2, 2, 2]
def baseStart_8083633 : Nat := 118140960795 + 8083633 * 2 ^ 59
def prefixEnd_8083633 : Nat := 4983230072969 + 3 ^ 40 * 8083633 * 2
def baseEnd_8083633 : Nat := 4150789163546276482411555

theorem tailTrace_8083633 : CollatzResearch.WordTrace tailWord_8083633 prefixEnd_8083633 4150789163546276482411555 := by
  unfold tailWord_8083633
  simp only [CollatzResearch.WordTrace]
  refine ⟨294834317123385690448351553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196556211415590460298901035 294834317123385690448351553)
  ·
    refine ⟨221125737842539267836263665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294834317123385690448351553 221125737842539267836263665)
    ·
      refine ⟨165844303381904450877197749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221125737842539267836263665 165844303381904450877197749)
      ·
        refine ⟨15547903442053542269737289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165844303381904450877197749 15547903442053542269737289)
        ·
          refine ⟨11660927581540156702302967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15547903442053542269737289 11660927581540156702302967)
          ·
            refine ⟨17491391372310235053454451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11660927581540156702302967 17491391372310235053454451)
            ·
              refine ⟨26237087058465352580181677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17491391372310235053454451 26237087058465352580181677)
              ·
                refine ⟨9838907646924507217568129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26237087058465352580181677 9838907646924507217568129)
                ·
                  refine ⟨7379180735193380413176097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9838907646924507217568129 7379180735193380413176097)
                  ·
                    refine ⟨5534385551395035309882073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7379180735193380413176097 5534385551395035309882073)
                    ·
                      refine ⟨4150789163546276482411555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5534385551395035309882073 4150789163546276482411555)
                      ·
                        rfl

theorem cell23_8083633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_8083633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083633 prefixEnd_8083633 := by exact prefixLift 8083633
  have htrace : WordTrace (prefixWord ++ tailWord_8083633) baseStart_8083633 baseEnd_8083633 := by
    simpa [prefixWord, tailWord_8083633, baseEnd_8083633] using wordTrace_append hprefix tailTrace_8083633
  have hstable : (prefixWord ++ tailWord_8083633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083633).length < 2 ^ (prefixWord ++ tailWord_8083633).sum := by decide
  have hdescent : baseEnd_8083633 < baseStart_8083633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083635 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 6, 5]
def baseStart_8083635 : Nat := 118140960795 + 8083635 * 2 ^ 59
def prefixEnd_8083635 : Nat := 4983230072969 + 3 ^ 40 * 8083635 * 2
def baseEnd_8083635 : Nat := 1383596730169195158195515

theorem tailTrace_8083635 : CollatzResearch.WordTrace tailWord_8083635 prefixEnd_8083635 1383596730169195158195515 := by
  unfold tailWord_8083635
  simp only [CollatzResearch.WordTrace]
  refine ⟨294834390069378444789924359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196556260046252296526616239 294834390069378444789924359)
  ·
    refine ⟨442251585104067667184886539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294834390069378444789924359 442251585104067667184886539)
    ·
      refine ⟨663377377656101500777329809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442251585104067667184886539 663377377656101500777329809)
      ·
        refine ⟨497533033242076125582997357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 663377377656101500777329809 497533033242076125582997357)
        ·
          refine ⟨186574887465778547093624009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497533033242076125582997357 186574887465778547093624009)
          ·
            refine ⟨139931165599333910320218007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186574887465778547093624009 139931165599333910320218007)
            ·
              refine ⟨209896748399000865480327011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139931165599333910320218007 209896748399000865480327011)
              ·
                refine ⟨314845122598501298220490517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209896748399000865480327011 314845122598501298220490517)
                ·
                  refine ⟨14758365121804748354085493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 314845122598501298220490517 14758365121804748354085493)
                  ·
                    refine ⟨1383596730169195158195515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14758365121804748354085493 1383596730169195158195515)
                    ·
                      rfl

theorem cell23_8083635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 5].length) (baseStart_8083635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083635 prefixEnd_8083635 := by exact prefixLift 8083635
  have htrace : WordTrace (prefixWord ++ tailWord_8083635) baseStart_8083635 baseEnd_8083635 := by
    simpa [prefixWord, tailWord_8083635, baseEnd_8083635] using wordTrace_append hprefix tailTrace_8083635
  have hstable : (prefixWord ++ tailWord_8083635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083635).length < 2 ^ (prefixWord ++ tailWord_8083635).sum := by decide
  have hdescent : baseEnd_8083635 < baseStart_8083635 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083645 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_8083645 : Nat := 118140960795 + 8083645 * 2 ^ 59
def prefixEnd_8083645 : Nat := 4983230072969 + 3 ^ 40 * 8083645 * 2
def baseEnd_8083645 : Nat := 4150795325314130435461499

theorem tailTrace_8083645 : CollatzResearch.WordTrace tailWord_8083645 prefixEnd_8083645 4150795325314130435461499 := by
  unfold tailWord_8083645
  simp only [CollatzResearch.WordTrace]
  refine ⟨294834754799342216497788389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196556503199561477665192259 294834754799342216497788389)
  ·
    refine ⟨55281516524876665593335323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294834754799342216497788389 55281516524876665593335323)
    ·
      refine ⟨82922274787314998390002985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55281516524876665593335323 82922274787314998390002985)
      ·
        refine ⟨62191706090486248792502239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82922274787314998390002985 62191706090486248792502239)
        ·
          refine ⟨93287559135729373188753359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62191706090486248792502239 93287559135729373188753359)
          ·
            refine ⟨139931338703594059783130039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93287559135729373188753359 139931338703594059783130039)
            ·
              refine ⟨209897008055391089674695059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139931338703594059783130039 209897008055391089674695059)
              ·
                refine ⟨314845512083086634512042589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209897008055391089674695059 314845512083086634512042589)
                ·
                  refine ⟨118067067031157487942015971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314845512083086634512042589 118067067031157487942015971)
                  ·
                    refine ⟨177100600546736231913023957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118067067031157487942015971 177100600546736231913023957)
                    ·
                      refine ⟨4150795325314130435461499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177100600546736231913023957 4150795325314130435461499)
                      ·
                        rfl

theorem cell23_8083645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_8083645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083645 prefixEnd_8083645 := by exact prefixLift 8083645
  have htrace : WordTrace (prefixWord ++ tailWord_8083645) baseStart_8083645 baseEnd_8083645 := by
    simpa [prefixWord, tailWord_8083645, baseEnd_8083645] using wordTrace_append hprefix tailTrace_8083645
  have hstable : (prefixWord ++ tailWord_8083645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083645).length < 2 ^ (prefixWord ++ tailWord_8083645).sum := by decide
  have hdescent : baseEnd_8083645 < baseStart_8083645 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083662 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_8083662 : Nat := 118140960795 + 8083662 * 2 ^ 59
def prefixEnd_8083662 : Nat := 4983230072969 + 3 ^ 40 * 8083662 * 2
def baseEnd_8083662 : Nat := 4150804054485256868948921

theorem tailTrace_8083662 : CollatzResearch.WordTrace tailWord_8083662 prefixEnd_8083662 4150804054485256868948921 := by
  unfold tailWord_8083662
  simp only [CollatzResearch.WordTrace]
  refine ⟨36854421855035078550144655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196556916560187085600771493 36854421855035078550144655)
  ·
    refine ⟨55281632782552617825216983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36854421855035078550144655 55281632782552617825216983)
    ·
      refine ⟨82922449173828926737825475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55281632782552617825216983 82922449173828926737825475)
      ·
        refine ⟨124383673760743390106738213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82922449173828926737825475 124383673760743390106738213)
        ·
          refine ⟨23321938830139385645013415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124383673760743390106738213 23321938830139385645013415)
          ·
            refine ⟨34982908245209078467520123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23321938830139385645013415 34982908245209078467520123)
            ·
              refine ⟨52474362367813617701280185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34982908245209078467520123 52474362367813617701280185)
              ·
                refine ⟨39355771775860213275960139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52474362367813617701280185 39355771775860213275960139)
                ·
                  refine ⟨59033657663790319913940209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39355771775860213275960139 59033657663790319913940209)
                  ·
                    refine ⟨44275243247842739935455157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59033657663790319913940209 44275243247842739935455157)
                    ·
                      refine ⟨4150804054485256868948921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44275243247842739935455157 4150804054485256868948921)
                      ·
                        rfl

theorem cell23_8083662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_8083662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083662 prefixEnd_8083662 := by exact prefixLift 8083662
  have htrace : WordTrace (prefixWord ++ tailWord_8083662) baseStart_8083662 baseEnd_8083662 := by
    simpa [prefixWord, tailWord_8083662, baseEnd_8083662] using wordTrace_append hprefix tailTrace_8083662
  have hstable : (prefixWord ++ tailWord_8083662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083662).length < 2 ^ (prefixWord ++ tailWord_8083662).sum := by decide
  have hdescent : baseEnd_8083662 < baseStart_8083662 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083692 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 3]
def baseStart_8083692 : Nat := 118140960795 + 8083692 * 2 ^ 59
def prefixEnd_8083692 : Nat := 4983230072969 + 3 ^ 40 * 8083692 * 2
def baseEnd_8083692 : Nat := 4150819458904891751573783

theorem tailTrace_8083692 : CollatzResearch.WordTrace tailWord_8083692 prefixEnd_8083692 4150819458904891751573783 := by
  unfold tailWord_8083692
  simp only [CollatzResearch.WordTrace]
  refine ⟨147418234515085971762374665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196557646020114629016499553 147418234515085971762374665)
  ·
    refine ⟨110563675886314478821780999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147418234515085971762374665 110563675886314478821780999)
    ·
      refine ⟨165845513829471718232671499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110563675886314478821780999 165845513829471718232671499)
      ·
        refine ⟨248768270744207577349007249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165845513829471718232671499 248768270744207577349007249)
        ·
          refine ⟨186576203058155683011755437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248768270744207577349007249 186576203058155683011755437)
          ·
            refine ⟨69966076146808381129408289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186576203058155683011755437 69966076146808381129408289)
            ·
              refine ⟨52474557110106285847056217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69966076146808381129408289 52474557110106285847056217)
              ·
                refine ⟨39355917832579714385292163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52474557110106285847056217 39355917832579714385292163)
                ·
                  refine ⟨59033876748869571577938245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39355917832579714385292163 59033876748869571577938245)
                  ·
                    refine ⟨11068851890413044670863421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59033876748869571577938245 11068851890413044670863421)
                    ·
                      refine ⟨4150819458904891751573783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11068851890413044670863421 4150819458904891751573783)
                      ·
                        rfl

theorem cell23_8083692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_8083692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083692 prefixEnd_8083692 := by exact prefixLift 8083692
  have htrace : WordTrace (prefixWord ++ tailWord_8083692) baseStart_8083692 baseEnd_8083692 := by
    simpa [prefixWord, tailWord_8083692, baseEnd_8083692] using wordTrace_append hprefix tailTrace_8083692
  have hstable : (prefixWord ++ tailWord_8083692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083692).length < 2 ^ (prefixWord ++ tailWord_8083692).sum := by decide
  have hdescent : baseEnd_8083692 < baseStart_8083692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083729 : List Nat := [1, 2, 2, 1, 1, 7, 1, 2, 6]
def baseStart_8083729 : Nat := 118140960795 + 8083729 * 2 ^ 59
def prefixEnd_8083729 : Nat := 4983230072969 + 3 ^ 40 * 8083729 * 2
def baseEnd_8083729 : Nat := 461204273076567567423457

theorem tailTrace_8083729 : CollatzResearch.WordTrace tailWord_8083729 prefixEnd_8083729 461204273076567567423457 := by
  unfold tailWord_8083729
  simp only [CollatzResearch.WordTrace]
  refine ⟨294837818531037898843846241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196558545687358599229230827 294837818531037898843846241)
  ·
    refine ⟨221128363898278424132884681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294837818531037898843846241 221128363898278424132884681)
    ·
      refine ⟨165846272923708818099663511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221128363898278424132884681 165846272923708818099663511)
      ·
        refine ⟨248769409385563227149495267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165846272923708818099663511 248769409385563227149495267)
        ·
          refine ⟨373154114078344840724242901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248769409385563227149495267 373154114078344840724242901)
          ·
            refine ⟨8745799548711207204474443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 373154114078344840724242901 8745799548711207204474443)
            ·
              refine ⟨13118699323066810806711665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8745799548711207204474443 13118699323066810806711665)
              ·
                refine ⟨9839024492300108105033749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13118699323066810806711665 9839024492300108105033749)
                ·
                  refine ⟨461204273076567567423457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9839024492300108105033749 461204273076567567423457)
                  ·
                    rfl

theorem cell23_8083729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 6].length) (baseStart_8083729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083729 prefixEnd_8083729 := by exact prefixLift 8083729
  have htrace : WordTrace (prefixWord ++ tailWord_8083729) baseStart_8083729 baseEnd_8083729 := by
    simpa [prefixWord, tailWord_8083729, baseEnd_8083729] using wordTrace_append hprefix tailTrace_8083729
  have hstable : (prefixWord ++ tailWord_8083729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083729).length < 2 ^ (prefixWord ++ tailWord_8083729).sum := by decide
  have hdescent : baseEnd_8083729 < baseStart_8083729 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083739 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 3, 1, 3]
def baseStart_8083739 : Nat := 118140960795 + 8083739 * 2 ^ 59
def prefixEnd_8083739 : Nat := 4983230072969 + 3 ^ 40 * 8083739 * 2
def baseEnd_8083739 : Nat := 4150843592495653067686067

theorem tailTrace_8083739 : CollatzResearch.WordTrace tailWord_8083739 prefixEnd_8083739 4150843592495653067686067 := by
  unfold tailWord_8083739
  simp only [CollatzResearch.WordTrace]
  refine ⟨294838183261001670551710271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196558788840667780367806847 294838183261001670551710271)
  ·
    refine ⟨442257274891502505827565407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294838183261001670551710271 442257274891502505827565407)
    ·
      refine ⟨663385912337253758741348111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442257274891502505827565407 663385912337253758741348111)
      ·
        refine ⟨995078868505880638112022167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663385912337253758741348111 995078868505880638112022167)
        ·
          refine ⟨1492618302758820957168033251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995078868505880638112022167 1492618302758820957168033251)
          ·
            refine ⟨2238927454138231435752049877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492618302758820957168033251 2238927454138231435752049877)
            ·
              refine ⟨52474862206364799275438669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2238927454138231435752049877 52474862206364799275438669)
              ·
                refine ⟨19678073327386799728289501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52474862206364799275438669 19678073327386799728289501)
                ·
                  refine ⟨7379277497770049898108563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19678073327386799728289501 7379277497770049898108563)
                  ·
                    refine ⟨11068916246655074847162845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7379277497770049898108563 11068916246655074847162845)
                    ·
                      refine ⟨4150843592495653067686067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11068916246655074847162845 4150843592495653067686067)
                      ·
                        rfl

theorem cell23_8083739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 1, 3].length) (baseStart_8083739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083739 prefixEnd_8083739 := by exact prefixLift 8083739
  have htrace : WordTrace (prefixWord ++ tailWord_8083739) baseStart_8083739 baseEnd_8083739 := by
    simpa [prefixWord, tailWord_8083739, baseEnd_8083739] using wordTrace_append hprefix tailTrace_8083739
  have hstable : (prefixWord ++ tailWord_8083739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083739).length < 2 ^ (prefixWord ++ tailWord_8083739).sum := by decide
  have hdescent : baseEnd_8083739 < baseStart_8083739 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083746 : List Nat := [3, 3, 1, 1, 3, 2, 3, 1, 6]
def baseStart_8083746 : Nat := 118140960795 + 8083746 * 2 ^ 59
def prefixEnd_8083746 : Nat := 4983230072969 + 3 ^ 40 * 8083746 * 2
def baseEnd_8083746 : Nat := 461205242984470504477615

theorem tailTrace_8083746 : CollatzResearch.WordTrace tailWord_8083746 prefixEnd_8083746 461205242984470504477615 := by
  unfold tailWord_8083746
  simp only [CollatzResearch.WordTrace]
  refine ⟨73709609642994077686803773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196558959047984207164810061 73709609642994077686803773)
  ·
    refine ⟨27641103616122779132551415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73709609642994077686803773 27641103616122779132551415)
    ·
      refine ⟨41461655424184168698827123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27641103616122779132551415 41461655424184168698827123)
      ·
        refine ⟨62192483136276253048240685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41461655424184168698827123 62192483136276253048240685)
        ·
          refine ⟨23322181176103594893090257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62192483136276253048240685 23322181176103594893090257)
          ·
            refine ⟨17491635882077696169817693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23322181176103594893090257 17491635882077696169817693)
            ·
              refine ⟨6559363455779136063681635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17491635882077696169817693 6559363455779136063681635)
              ·
                refine ⟨9839045183668704095522453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559363455779136063681635 9839045183668704095522453)
                ·
                  refine ⟨461205242984470504477615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9839045183668704095522453 461205242984470504477615)
                  ·
                    rfl

theorem cell23_8083746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_8083746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083746 prefixEnd_8083746 := by exact prefixLift 8083746
  have htrace : WordTrace (prefixWord ++ tailWord_8083746) baseStart_8083746 baseEnd_8083746 := by
    simpa [prefixWord, tailWord_8083746, baseEnd_8083746] using wordTrace_append hprefix tailTrace_8083746
  have hstable : (prefixWord ++ tailWord_8083746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083746).length < 2 ^ (prefixWord ++ tailWord_8083746).sum := by decide
  have hdescent : baseEnd_8083746 < baseStart_8083746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083772 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 3, 6]
def baseStart_8083772 : Nat := 118140960795 + 8083772 * 2 ^ 59
def prefixEnd_8083772 : Nat := 4983230072969 + 3 ^ 40 * 8083772 * 2
def baseEnd_8083772 : Nat := 1383620179119083812857805

theorem tailTrace_8083772 : CollatzResearch.WordTrace tailWord_8083772 prefixEnd_8083772 1383620179119083812857805 := by
  unfold tailWord_8083772
  simp only [CollatzResearch.WordTrace]
  refine ⟨147419693434941058593830785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196559591246588078125107713 147419693434941058593830785)
  ·
    refine ⟨110564770076205793945373089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147419693434941058593830785 110564770076205793945373089)
    ·
      refine ⟨82923577557154345459029817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110564770076205793945373089 82923577557154345459029817)
      ·
        refine ⟨62192683167865759094272363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82923577557154345459029817 62192683167865759094272363)
        ·
          refine ⟨93289024751798638641408545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62192683167865759094272363 93289024751798638641408545)
          ·
            refine ⟨69966768563848978981056409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93289024751798638641408545 69966768563848978981056409)
            ·
              refine ⟨52475076422886734235792307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69966768563848978981056409 52475076422886734235792307)
              ·
                refine ⟨78712614634330101353688461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52475076422886734235792307 78712614634330101353688461)
                ·
                  refine ⟨29517230487873788007633173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78712614634330101353688461 29517230487873788007633173)
                  ·
                    refine ⟨1383620179119083812857805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29517230487873788007633173 1383620179119083812857805)
                    ·
                      rfl

theorem cell23_8083772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_8083772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083772 prefixEnd_8083772 := by exact prefixLift 8083772
  have htrace : WordTrace (prefixWord ++ tailWord_8083772) baseStart_8083772 baseEnd_8083772 := by
    simpa [prefixWord, tailWord_8083772, baseEnd_8083772] using wordTrace_append hprefix tailTrace_8083772
  have hstable : (prefixWord ++ tailWord_8083772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083772).length < 2 ^ (prefixWord ++ tailWord_8083772).sum := by decide
  have hdescent : baseEnd_8083772 < baseStart_8083772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083779 : List Nat := [1, 1, 1, 3, 1, 3, 4, 3, 1, 1, 4]
def baseStart_8083779 : Nat := 118140960795 + 8083779 * 2 ^ 59
def prefixEnd_8083779 : Nat := 4983230072969 + 3 ^ 40 * 8083779 * 2
def baseEnd_8083779 : Nat := 4150864131721832911185883

theorem tailTrace_8083779 : CollatzResearch.WordTrace tailWord_8083779 prefixEnd_8083779 4150864131721832911185883 := by
  unfold tailWord_8083779
  simp only [CollatzResearch.WordTrace]
  refine ⟨294839642180856757383166391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196559761453904504922110927 294839642180856757383166391)
  ·
    refine ⟨442259463271285136074749587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294839642180856757383166391 442259463271285136074749587)
    ·
      refine ⟨663389194906927704112124381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442259463271285136074749587 663389194906927704112124381)
      ·
        refine ⟨248770948090097889042046643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 663389194906927704112124381 248770948090097889042046643)
        ·
          refine ⟨373156422135146833563069965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248770948090097889042046643 373156422135146833563069965)
          ·
            refine ⟨139933658300680062586151237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373156422135146833563069965 139933658300680062586151237)
            ·
              refine ⟨26237560931377511734903357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139933658300680062586151237 26237560931377511734903357)
              ·
                refine ⟨9839085349266566900588759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26237560931377511734903357 9839085349266566900588759)
                ·
                  refine ⟨14758628023899850350883139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9839085349266566900588759 14758628023899850350883139)
                  ·
                    refine ⟨22137942035849775526324709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14758628023899850350883139 22137942035849775526324709)
                    ·
                      refine ⟨4150864131721832911185883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22137942035849775526324709 4150864131721832911185883)
                      ·
                        rfl

theorem cell23_8083779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_8083779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083779 prefixEnd_8083779 := by exact prefixLift 8083779
  have htrace : WordTrace (prefixWord ++ tailWord_8083779) baseStart_8083779 baseEnd_8083779 := by
    simpa [prefixWord, tailWord_8083779, baseEnd_8083779] using wordTrace_append hprefix tailTrace_8083779
  have hstable : (prefixWord ++ tailWord_8083779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083779).length < 2 ^ (prefixWord ++ tailWord_8083779).sum := by decide
  have hdescent : baseEnd_8083779 < baseStart_8083779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083792 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 6]
def baseStart_8083792 : Nat := 118140960795 + 8083792 * 2 ^ 59
def prefixEnd_8083792 : Nat := 4983230072969 + 3 ^ 40 * 8083792 * 2
def baseEnd_8083792 : Nat := 4150870806970341360323323

theorem tailTrace_8083792 : CollatzResearch.WordTrace tailWord_8083792 prefixEnd_8083792 4150870806970341360323323 := by
  unfold tailWord_8083792
  simp only [CollatzResearch.WordTrace]
  refine ⟨147420058164904830301694815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196560077553206440402259753 147420058164904830301694815)
  ·
    refine ⟨221130087247357245452542223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147420058164904830301694815 221130087247357245452542223)
    ·
      refine ⟨331695130871035868178813335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221130087247357245452542223 331695130871035868178813335)
      ·
        refine ⟨497542696306553802268220003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331695130871035868178813335 497542696306553802268220003)
        ·
          refine ⟨746314044459830703402330005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497542696306553802268220003 746314044459830703402330005)
          ·
            refine ⟨34983470834054564221984219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 746314044459830703402330005 34983470834054564221984219)
            ·
              refine ⟨52475206251081846332976329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34983470834054564221984219 52475206251081846332976329)
              ·
                refine ⟨39356404688311384749732247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52475206251081846332976329 39356404688311384749732247)
                ·
                  refine ⟨59034607032467077124598371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39356404688311384749732247 59034607032467077124598371)
                  ·
                    refine ⟨88551910548700615686897557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59034607032467077124598371 88551910548700615686897557)
                    ·
                      refine ⟨4150870806970341360323323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88551910548700615686897557 4150870806970341360323323)
                      ·
                        rfl

theorem cell23_8083792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_8083792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083792 prefixEnd_8083792 := by exact prefixLift 8083792
  have htrace : WordTrace (prefixWord ++ tailWord_8083792) baseStart_8083792 baseEnd_8083792 := by
    simpa [prefixWord, tailWord_8083792, baseEnd_8083792] using wordTrace_append hprefix tailTrace_8083792
  have hstable : (prefixWord ++ tailWord_8083792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083792).length < 2 ^ (prefixWord ++ tailWord_8083792).sum := by decide
  have hdescent : baseEnd_8083792 < baseStart_8083792 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083799 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 3]
def baseStart_8083799 : Nat := 118140960795 + 8083799 * 2 ^ 59
def prefixEnd_8083799 : Nat := 4983230072969 + 3 ^ 40 * 8083799 * 2
def baseEnd_8083799 : Nat := 4150874401334922832935791

theorem tailTrace_8083799 : CollatzResearch.WordTrace tailWord_8083799 prefixEnd_8083799 4150874401334922832935791 := by
  unfold tailWord_8083799
  simp only [CollatzResearch.WordTrace]
  refine ⟨294840371640784300798894451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196560247760522867199262967 294840371640784300798894451)
  ·
    refine ⟨442260557461176451198341677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294840371640784300798894451 442260557461176451198341677)
    ·
      refine ⟨165847709047941169199378129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442260557461176451198341677 165847709047941169199378129)
      ·
        refine ⟨124385781785955876899533597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165847709047941169199378129 124385781785955876899533597)
        ·
          refine ⟨46644668169733453837325099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124385781785955876899533597 46644668169733453837325099)
          ·
            refine ⟨69967002254600180755987649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46644668169733453837325099 69967002254600180755987649)
            ·
              refine ⟨52475251690950135566990737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69967002254600180755987649 52475251690950135566990737)
              ·
                refine ⟨39356438768212601675243053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52475251690950135566990737 39356438768212601675243053)
                ·
                  refine ⟨14758664538079725628216145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39356438768212601675243053 14758664538079725628216145)
                  ·
                    refine ⟨11068998403559794221162109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14758664538079725628216145 11068998403559794221162109)
                    ·
                      refine ⟨4150874401334922832935791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11068998403559794221162109 4150874401334922832935791)
                      ·
                        rfl

theorem cell23_8083799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_8083799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083799 prefixEnd_8083799 := by exact prefixLift 8083799
  have htrace : WordTrace (prefixWord ++ tailWord_8083799) baseStart_8083799 baseEnd_8083799 := by
    simpa [prefixWord, tailWord_8083799, baseEnd_8083799] using wordTrace_append hprefix tailTrace_8083799
  have hstable : (prefixWord ++ tailWord_8083799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083799).length < 2 ^ (prefixWord ++ tailWord_8083799).sum := by decide
  have hdescent : baseEnd_8083799 < baseStart_8083799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083816 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_8083816 : Nat := 118140960795 + 8083816 * 2 ^ 59
def prefixEnd_8083816 : Nat := 4983230072969 + 3 ^ 40 * 8083816 * 2
def baseEnd_8083816 : Nat := 4150883130506049266423213

theorem tailTrace_8083816 : CollatzResearch.WordTrace tailWord_8083816 prefixEnd_8083816 4150883130506049266423213 := by
  unfold tailWord_8083816
  simp only [CollatzResearch.WordTrace]
  refine ⟨147420495840861356351131651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196560661121148475134842201 147420495840861356351131651)
  ·
    refine ⟨221130743761292034526697477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147420495840861356351131651 221130743761292034526697477)
    ·
      refine ⟨41462014455242256473755777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221130743761292034526697477 41462014455242256473755777)
      ·
        refine ⟨31096510841431692355316833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41462014455242256473755777 31096510841431692355316833)
        ·
          refine ⟨23322383131073769266487625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31096510841431692355316833 23322383131073769266487625)
          ·
            refine ⟨17491787348305326949865719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23322383131073769266487625 17491787348305326949865719)
            ·
              refine ⟨26237681022457990424798579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17491787348305326949865719 26237681022457990424798579)
              ·
                refine ⟨39356521533686985637197869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26237681022457990424798579 39356521533686985637197869)
                ·
                  refine ⟨14758695575132619613949201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39356521533686985637197869 14758695575132619613949201)
                  ·
                    refine ⟨11069021681349464710461901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14758695575132619613949201 11069021681349464710461901)
                    ·
                      refine ⟨4150883130506049266423213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11069021681349464710461901 4150883130506049266423213)
                      ·
                        rfl

theorem cell23_8083816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_8083816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083816 prefixEnd_8083816 := by exact prefixLift 8083816
  have htrace : WordTrace (prefixWord ++ tailWord_8083816) baseStart_8083816 baseEnd_8083816 := by
    simpa [prefixWord, tailWord_8083816, baseEnd_8083816] using wordTrace_append hprefix tailTrace_8083816
  have hstable : (prefixWord ++ tailWord_8083816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083816).length < 2 ^ (prefixWord ++ tailWord_8083816).sum := by decide
  have hdescent : baseEnd_8083816 < baseStart_8083816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083926 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_8083926 : Nat := 118140960795 + 8083926 * 2 ^ 59
def prefixEnd_8083926 : Nat := 4983230072969 + 3 ^ 40 * 8083926 * 2
def baseEnd_8083926 : Nat := 461215512597560426227523

theorem tailTrace_8083926 : CollatzResearch.WordTrace tailWord_8083926 prefixEnd_8083926 461215512597560426227523 := by
  unfold tailWord_8083926
  simp only [CollatzResearch.WordTrace]
  refine ⟨18427812731957762593047977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196563335807549467659178421 18427812731957762593047977)
  ·
    refine ⟨13820859548968321944785983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18427812731957762593047977 13820859548968321944785983)
    ·
      refine ⟨20731289323452482917178975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13820859548968321944785983 20731289323452482917178975)
      ·
        refine ⟨31096933985178724375768463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20731289323452482917178975 31096933985178724375768463)
        ·
          refine ⟨46645400977768086563652695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31096933985178724375768463 46645400977768086563652695)
          ·
            refine ⟨69968101466652129845479043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46645400977768086563652695 69968101466652129845479043)
            ·
              refine ⟨104952152199978194768218565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69968101466652129845479043 104952152199978194768218565)
              ·
                refine ⟨19678528537495911519040981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104952152199978194768218565 19678528537495911519040981)
                ·
                  refine ⟨461215512597560426227523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19678528537495911519040981 461215512597560426227523)
                  ·
                    rfl

theorem cell23_8083926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_8083926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083926 prefixEnd_8083926 := by exact prefixLift 8083926
  have htrace : WordTrace (prefixWord ++ tailWord_8083926) baseStart_8083926 baseEnd_8083926 := by
    simpa [prefixWord, tailWord_8083926, baseEnd_8083926] using wordTrace_append hprefix tailTrace_8083926
  have hstable : (prefixWord ++ tailWord_8083926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083926).length < 2 ^ (prefixWord ++ tailWord_8083926).sum := by decide
  have hdescent : baseEnd_8083926 < baseStart_8083926 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8083976 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 1, 6, 2]
def baseStart_8083976 : Nat := 118140960795 + 8083976 * 2 ^ 59
def prefixEnd_8083976 : Nat := 4983230072969 + 3 ^ 40 * 8083976 * 2
def baseEnd_8083976 : Nat := 4150965287410768640422477

theorem tailTrace_8083976 : CollatzResearch.WordTrace tailWord_8083976 prefixEnd_8083976 4150965287410768640422477 := by
  unfold tailWord_8083976
  simp only [CollatzResearch.WordTrace]
  refine ⟨147423413680571530014043891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196564551574095373352058521 147423413680571530014043891)
  ·
    refine ⟨221135120520857295021065837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147423413680571530014043891 221135120520857295021065837)
    ·
      refine ⟨82925670195321485632899689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221135120520857295021065837 82925670195321485632899689)
      ·
        refine ⟨62194252646491114224674767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82925670195321485632899689 62194252646491114224674767)
        ·
          refine ⟨93291378969736671337012151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62194252646491114224674767 93291378969736671337012151)
          ·
            refine ⟨139937068454605007005518227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93291378969736671337012151 139937068454605007005518227)
            ·
              refine ⟨209905602681907510508277341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139937068454605007005518227 209905602681907510508277341)
              ·
                refine ⟨78714601005715316440604003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209905602681907510508277341 78714601005715316440604003)
                ·
                  refine ⟨118071901508572974660906005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78714601005715316440604003 118071901508572974660906005)
                  ·
                    refine ⟨5534620383214358187229969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118071901508572974660906005 5534620383214358187229969)
                    ·
                      refine ⟨4150965287410768640422477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5534620383214358187229969 4150965287410768640422477)
                      ·
                        rfl

theorem cell23_8083976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_8083976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8083976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8083976 prefixEnd_8083976 := by exact prefixLift 8083976
  have htrace : WordTrace (prefixWord ++ tailWord_8083976) baseStart_8083976 baseEnd_8083976 := by
    simpa [prefixWord, tailWord_8083976, baseEnd_8083976] using wordTrace_append hprefix tailTrace_8083976
  have hstable : (prefixWord ++ tailWord_8083976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8083976).length < 2 ^ (prefixWord ++ tailWord_8083976).sum := by decide
  have hdescent : baseEnd_8083976 < baseStart_8083976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8083976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084019 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 6]
def baseStart_8084019 : Nat := 118140960795 + 8084019 * 2 ^ 59
def prefixEnd_8084019 : Nat := 4983230072969 + 3 ^ 40 * 8084019 * 2
def baseEnd_8084019 : Nat := 4150987367078911972184779

theorem tailTrace_8084019 : CollatzResearch.WordTrace tailWord_8084019 prefixEnd_8084019 4150987367078911972184779 := by
  unfold tailWord_8084019
  simp only [CollatzResearch.WordTrace]
  refine ⟨294848395699987278371903111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196565597133324852247935407 294848395699987278371903111)
  ·
    refine ⟨442272593549980917557854667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294848395699987278371903111 442272593549980917557854667)
    ·
      refine ⟨663408890324971376336782001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442272593549980917557854667 663408890324971376336782001)
      ·
        refine ⟨497556667743728532252586501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 663408890324971376336782001 497556667743728532252586501)
        ·
          refine ⟨93291875201949099797359969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 497556667743728532252586501 93291875201949099797359969)
          ·
            refine ⟨69968906401461824848019977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93291875201949099797359969 69968906401461824848019977)
            ·
              refine ⟨52476679801096368636014983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69968906401461824848019977 52476679801096368636014983)
              ·
                refine ⟨78715019701644552954022475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52476679801096368636014983 78715019701644552954022475)
                ·
                  refine ⟨118072529552466829431033713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78715019701644552954022475 118072529552466829431033713)
                  ·
                    refine ⟨88554397164350122073275285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118072529552466829431033713 88554397164350122073275285)
                    ·
                      refine ⟨4150987367078911972184779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88554397164350122073275285 4150987367078911972184779)
                      ·
                        rfl

theorem cell23_8084019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_8084019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084019 prefixEnd_8084019 := by exact prefixLift 8084019
  have htrace : WordTrace (prefixWord ++ tailWord_8084019) baseStart_8084019 baseEnd_8084019 := by
    simpa [prefixWord, tailWord_8084019, baseEnd_8084019] using wordTrace_append hprefix tailTrace_8084019
  have hstable : (prefixWord ++ tailWord_8084019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084019).length < 2 ^ (prefixWord ++ tailWord_8084019).sum := by decide
  have hdescent : baseEnd_8084019 < baseStart_8084019 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084046 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_8084046 : Nat := 118140960795 + 8084046 * 2 ^ 59
def prefixEnd_8084046 : Nat := 4983230072969 + 3 ^ 40 * 8084046 * 2
def baseEnd_8084046 : Nat := 1383667077018861122182385

theorem tailTrace_8084046 : CollatzResearch.WordTrace tailWord_8084046 prefixEnd_8084046 1383667077018861122182385 := by
  unfold tailWord_8084046
  simp only [CollatzResearch.WordTrace]
  refine ⟨36856172558861182747891999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196566253647259641322090661 36856172558861182747891999)
  ·
    refine ⟨55284258838291774121837999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36856172558861182747891999 55284258838291774121837999)
    ·
      refine ⟨82926388257437661182756999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55284258838291774121837999 82926388257437661182756999)
      ·
        refine ⟨124389582386156491774135499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82926388257437661182756999 124389582386156491774135499)
        ·
          refine ⟨186584373579234737661203249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124389582386156491774135499 186584373579234737661203249)
          ·
            refine ⟨139938280184426053245902437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186584373579234737661203249 139938280184426053245902437)
            ·
              refine ⟨26238427534579884983606707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139938280184426053245902437 26238427534579884983606707)
              ·
                refine ⟨39357641301869827475410061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26238427534579884983606707 39357641301869827475410061)
                ·
                  refine ⟨14759115488201185303278773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39357641301869827475410061 14759115488201185303278773)
                  ·
                    refine ⟨1383667077018861122182385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14759115488201185303278773 1383667077018861122182385)
                    ·
                      rfl

theorem cell23_8084046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_8084046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084046 prefixEnd_8084046 := by exact prefixLift 8084046
  have htrace : WordTrace (prefixWord ++ tailWord_8084046) baseStart_8084046 baseEnd_8084046 := by
    simpa [prefixWord, tailWord_8084046, baseEnd_8084046] using wordTrace_append hprefix tailTrace_8084046
  have hstable : (prefixWord ++ tailWord_8084046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084046).length < 2 ^ (prefixWord ++ tailWord_8084046).sum := by decide
  have hdescent : baseEnd_8084046 < baseStart_8084046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084077 : List Nat := [1, 5, 1, 1, 3, 1, 2, 4, 1, 1, 3]
def baseStart_8084077 : Nat := 118140960795 + 8084077 * 2 ^ 59
def prefixEnd_8084077 : Nat := 4983230072969 + 3 ^ 40 * 8084077 * 2
def baseEnd_8084077 : Nat := 4151017148956872745259513

theorem tailTrace_8084077 : CollatzResearch.WordTrace tailWord_8084077 prefixEnd_8084077 4151017148956872745259513 := by
  unfold tailWord_8084077
  simp only [CollatzResearch.WordTrace]
  refine ⟨294850511133777154277514485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196567007422518102851676323 294850511133777154277514485)
  ·
    refine ⟨27642235418791608213516983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294850511133777154277514485 27642235418791608213516983)
    ·
      refine ⟨41463353128187412320275475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27642235418791608213516983 41463353128187412320275475)
      ·
        refine ⟨62195029692281118480413213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41463353128187412320275475 62195029692281118480413213)
        ·
          refine ⟨23323136134605419430154955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62195029692281118480413213 23323136134605419430154955)
          ·
            refine ⟨34984704201908129145232433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23323136134605419430154955 34984704201908129145232433)
            ·
              refine ⟨26238528151431096858924325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34984704201908129145232433 26238528151431096858924325)
              ·
                refine ⟨4919724028393330661048311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26238528151431096858924325 4919724028393330661048311)
                ·
                  refine ⟨7379586042589995991572467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4919724028393330661048311 7379586042589995991572467)
                  ·
                    refine ⟨11069379063884993987358701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7379586042589995991572467 11069379063884993987358701)
                    ·
                      refine ⟨4151017148956872745259513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11069379063884993987358701 4151017148956872745259513)
                      ·
                        rfl

theorem cell23_8084077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_8084077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084077 prefixEnd_8084077 := by exact prefixLift 8084077
  have htrace : WordTrace (prefixWord ++ tailWord_8084077) baseStart_8084077 baseEnd_8084077 := by
    simpa [prefixWord, tailWord_8084077, baseEnd_8084077] using wordTrace_append hprefix tailTrace_8084077
  have hstable : (prefixWord ++ tailWord_8084077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084077).length < 2 ^ (prefixWord ++ tailWord_8084077).sum := by decide
  have hdescent : baseEnd_8084077 < baseStart_8084077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084096 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 6]
def baseStart_8084096 : Nat := 118140960795 + 8084096 * 2 ^ 59
def prefixEnd_8084096 : Nat := 4983230072969 + 3 ^ 40 * 8084096 * 2
def baseEnd_8084096 : Nat := 4151026905089308170921925

theorem tailTrace_8084096 : CollatzResearch.WordTrace tailWord_8084096 prefixEnd_8084096 4151026905089308170921925 := by
  unfold tailWord_8084096
  simp only [CollatzResearch.WordTrace]
  refine ⟨147425602060354160261228071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196567469413805547014970761 147425602060354160261228071)
  ·
    refine ⟨221138403090531240391842107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147425602060354160261228071 221138403090531240391842107)
    ·
      refine ⟨331707604635796860587763161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221138403090531240391842107 331707604635796860587763161)
      ·
        refine ⟨248780703476847645440822371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331707604635796860587763161 248780703476847645440822371)
        ·
          refine ⟨373171055215271468161233557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248780703476847645440822371 373171055215271468161233557)
          ·
            refine ⟨17492393213215850070057823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 373171055215271468161233557 17492393213215850070057823)
            ·
              refine ⟨26238589819823775105086735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17492393213215850070057823 26238589819823775105086735)
              ·
                refine ⟨39357884729735662657630103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26238589819823775105086735 39357884729735662657630103)
                ·
                  refine ⟨59036827094603493986445155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39357884729735662657630103 59036827094603493986445155)
                  ·
                    refine ⟨88555240641905240979667733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59036827094603493986445155 88555240641905240979667733)
                    ·
                      refine ⟨4151026905089308170921925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88555240641905240979667733 4151026905089308170921925)
                      ·
                        rfl

theorem cell23_8084096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_8084096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084096 prefixEnd_8084096 := by exact prefixLift 8084096
  have htrace : WordTrace (prefixWord ++ tailWord_8084096) baseStart_8084096 baseEnd_8084096 := by
    simpa [prefixWord, tailWord_8084096, baseEnd_8084096] using wordTrace_append hprefix tailTrace_8084096
  have hstable : (prefixWord ++ tailWord_8084096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084096).length < 2 ^ (prefixWord ++ tailWord_8084096).sum := by decide
  have hdescent : baseEnd_8084096 < baseStart_8084096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084100 : List Nat := [2, 3, 2, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_8084100 : Nat := 118140960795 + 8084100 * 2 ^ 59
def prefixEnd_8084100 : Nat := 4983230072969 + 3 ^ 40 * 8084100 * 2
def baseEnd_8084100 : Nat := 4151028959011926155271907

theorem tailTrace_8084100 : CollatzResearch.WordTrace tailWord_8084100 prefixEnd_8084100 4151028959011926155271907 := by
  unfold tailWord_8084100
  simp only [CollatzResearch.WordTrace]
  refine ⟨147425675006346914602800877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196567566675129219470401169 147425675006346914602800877)
  ·
    refine ⟨55284628127380092976050329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147425675006346914602800877 55284628127380092976050329)
    ·
      refine ⟨41463471095535069732037747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55284628127380092976050329 41463471095535069732037747)
      ·
        refine ⟨62195206643302604598056621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41463471095535069732037747 62195206643302604598056621)
        ·
          refine ⟨23323202491238476724271233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62195206643302604598056621 23323202491238476724271233)
          ·
            refine ⟨17492401868428857543203425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23323202491238476724271233 17492401868428857543203425)
            ·
              refine ⟨13119301401321643157402569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17492401868428857543203425 13119301401321643157402569)
              ·
                refine ⟨9839476050991232368051927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13119301401321643157402569 9839476050991232368051927)
                ·
                  refine ⟨14759214076486848552077891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9839476050991232368051927 14759214076486848552077891)
                  ·
                    refine ⟨22138821114730272828116837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14759214076486848552077891 22138821114730272828116837)
                    ·
                      refine ⟨4151028959011926155271907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22138821114730272828116837 4151028959011926155271907)
                      ·
                        rfl

theorem cell23_8084100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_8084100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084100 prefixEnd_8084100 := by exact prefixLift 8084100
  have htrace : WordTrace (prefixWord ++ tailWord_8084100) baseStart_8084100 baseEnd_8084100 := by
    simpa [prefixWord, tailWord_8084100, baseEnd_8084100] using wordTrace_append hprefix tailTrace_8084100
  have hstable : (prefixWord ++ tailWord_8084100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084100).length < 2 ^ (prefixWord ++ tailWord_8084100).sum := by decide
  have hdescent : baseEnd_8084100 < baseStart_8084100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084160 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 3, 3, 2]
def baseStart_8084160 : Nat := 118140960795 + 8084160 * 2 ^ 59
def prefixEnd_8084160 : Nat := 4983230072969 + 3 ^ 40 * 8084160 * 2
def baseEnd_8084160 : Nat := 4151059767851195920521631

theorem tailTrace_8084160 : CollatzResearch.WordTrace tailWord_8084160 prefixEnd_8084160 4151059767851195920521631 := by
  unfold tailWord_8084160
  simp only [CollatzResearch.WordTrace]
  refine ⟨147426769196238229726392967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196569025594984306301857289 147426769196238229726392967)
  ·
    refine ⟨221140153794357344589589451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147426769196238229726392967 221140153794357344589589451)
    ·
      refine ⟨331710230691536016884384177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221140153794357344589589451 331710230691536016884384177)
      ·
        refine ⟨248782673018652012663288133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331710230691536016884384177 248782673018652012663288133)
        ·
          refine ⟨46646751190997252374366525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248782673018652012663288133 46646751190997252374366525)
          ·
            refine ⟨17492531696623969640387447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46646751190997252374366525 17492531696623969640387447)
            ·
              refine ⟨26238797544935954460581171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17492531696623969640387447 26238797544935954460581171)
              ·
                refine ⟨39358196317403931690871757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26238797544935954460581171 39358196317403931690871757)
                ·
                  refine ⟨14759323619026474384076909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39358196317403931690871757 14759323619026474384076909)
                  ·
                    refine ⟨5534746357134927894028841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14759323619026474384076909 5534746357134927894028841)
                    ·
                      refine ⟨4151059767851195920521631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5534746357134927894028841 4151059767851195920521631)
                      ·
                        rfl

theorem cell23_8084160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 3, 3, 2].length) (baseStart_8084160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084160 prefixEnd_8084160 := by exact prefixLift 8084160
  have htrace : WordTrace (prefixWord ++ tailWord_8084160) baseStart_8084160 baseEnd_8084160 := by
    simpa [prefixWord, tailWord_8084160, baseEnd_8084160] using wordTrace_append hprefix tailTrace_8084160
  have hstable : (prefixWord ++ tailWord_8084160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084160).length < 2 ^ (prefixWord ++ tailWord_8084160).sum := by decide
  have hdescent : baseEnd_8084160 < baseStart_8084160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084177 : List Nat := [1, 2, 2, 1, 2, 3, 5, 1, 1, 3, 2]
def baseStart_8084177 : Nat := 118140960795 + 8084177 * 2 ^ 59
def prefixEnd_8084177 : Nat := 4983230072969 + 3 ^ 40 * 8084177 * 2
def baseEnd_8084177 : Nat := 4151068497022322354009053

theorem tailTrace_8084177 : CollatzResearch.WordTrace tailWord_8084177 prefixEnd_8084177 4151068497022322354009053 := by
  unfold tailWord_8084177
  simp only [CollatzResearch.WordTrace]
  refine ⟨294854158433414871356154785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196569438955609914237436523 294854158433414871356154785)
  ·
    refine ⟨221140618825061153517116089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294854158433414871356154785 221140618825061153517116089)
    ·
      refine ⟨165855464118795865137837067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221140618825061153517116089 165855464118795865137837067)
      ·
        refine ⟨248783196178193797706755601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165855464118795865137837067 248783196178193797706755601)
        ·
          refine ⟨186587397133645348280066701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248783196178193797706755601 186587397133645348280066701)
          ·
            refine ⟨69970273925117005605025013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186587397133645348280066701 69970273925117005605025013)
            ·
              refine ⟨6559713180479719275471095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69970273925117005605025013 6559713180479719275471095)
              ·
                refine ⟨9839569770719578913206643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559713180479719275471095 9839569770719578913206643)
                ·
                  refine ⟨14759354656079368369809965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9839569770719578913206643 14759354656079368369809965)
                  ·
                    refine ⟨5534757996029763138678737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14759354656079368369809965 5534757996029763138678737)
                    ·
                      refine ⟨4151068497022322354009053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5534757996029763138678737 4151068497022322354009053)
                      ·
                        rfl

theorem cell23_8084177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 1, 3, 2].length) (baseStart_8084177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084177 prefixEnd_8084177 := by exact prefixLift 8084177
  have htrace : WordTrace (prefixWord ++ tailWord_8084177) baseStart_8084177 baseEnd_8084177 := by
    simpa [prefixWord, tailWord_8084177, baseEnd_8084177] using wordTrace_append hprefix tailTrace_8084177
  have hstable : (prefixWord ++ tailWord_8084177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084177).length < 2 ^ (prefixWord ++ tailWord_8084177).sum := by decide
  have hdescent : baseEnd_8084177 < baseStart_8084177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084193 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_8084193 : Nat := 118140960795 + 8084193 * 2 ^ 59
def prefixEnd_8084193 : Nat := 4983230072969 + 3 ^ 40 * 8084193 * 2
def baseEnd_8084193 : Nat := 4151076712712794291408979

theorem tailTrace_8084193 : CollatzResearch.WordTrace tailWord_8084193 prefixEnd_8084193 4151076712712794291408979 := by
  unfold tailWord_8084193
  simp only [CollatzResearch.WordTrace]
  refine ⟨294854742001356906088737233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196569828000904604059158155 294854742001356906088737233)
  ·
    refine ⟨221141056501017679566552925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294854742001356906088737233 221141056501017679566552925)
    ·
      refine ⟨82927896187881629837457347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221141056501017679566552925 82927896187881629837457347)
      ·
        refine ⟨124391844281822444756186021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82927896187881629837457347 124391844281822444756186021)
        ·
          refine ⟨23323470802841708391784879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124391844281822444756186021 23323470802841708391784879)
          ·
            refine ⟨34985206204262562587677319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23323470802841708391784879 34985206204262562587677319)
            ·
              refine ⟨52477809306393843881515979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34985206204262562587677319 52477809306393843881515979)
              ·
                refine ⟨78716713959590765822273969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52477809306393843881515979 78716713959590765822273969)
                ·
                  refine ⟨59037535469693074366705477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78716713959590765822273969 59037535469693074366705477)
                  ·
                    refine ⟨11069537900567451443757277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59037535469693074366705477 11069537900567451443757277)
                    ·
                      refine ⟨4151076712712794291408979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11069537900567451443757277 4151076712712794291408979)
                      ·
                        rfl

theorem cell23_8084193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_8084193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084193 prefixEnd_8084193 := by exact prefixLift 8084193
  have htrace : WordTrace (prefixWord ++ tailWord_8084193) baseStart_8084193 baseEnd_8084193 := by
    simpa [prefixWord, tailWord_8084193, baseEnd_8084193] using wordTrace_append hprefix tailTrace_8084193
  have hstable : (prefixWord ++ tailWord_8084193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084193).length < 2 ^ (prefixWord ++ tailWord_8084193).sum := by decide
  have hdescent : baseEnd_8084193 < baseStart_8084193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084207 : List Nat := [1, 1, 2, 1, 5, 2, 2, 3, 2, 2, 2]
def baseStart_8084207 : Nat := 118140960795 + 8084207 * 2 ^ 59
def prefixEnd_8084207 : Nat := 4983230072969 + 3 ^ 40 * 8084207 * 2
def baseEnd_8084207 : Nat := 4151083901441957236633915

theorem tailTrace_8084207 : CollatzResearch.WordTrace tailWord_8084207 prefixEnd_8084207 4151083901441957236633915 := by
  unfold tailWord_8084207
  simp only [CollatzResearch.WordTrace]
  refine ⟨294855252623306186479746875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196570168415537457653164583 294855252623306186479746875)
  ·
    refine ⟨442282878934959279719620313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294855252623306186479746875 442282878934959279719620313)
    ·
      refine ⟨331712159201219459789715235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442282878934959279719620313 331712159201219459789715235)
      ·
        refine ⟨497568238801829189684572853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331712159201219459789715235 497568238801829189684572853)
        ·
          refine ⟨46647022387671486532928705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 497568238801829189684572853 46647022387671486532928705)
          ·
            refine ⟨34985266790753614899696529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46647022387671486532928705 34985266790753614899696529)
            ·
              refine ⟨26238950093065211174772397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34985266790753614899696529 26238950093065211174772397)
              ·
                refine ⟨9839606284899454190539649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26238950093065211174772397 9839606284899454190539649)
                ·
                  refine ⟨7379704713674590642904737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9839606284899454190539649 7379704713674590642904737)
                  ·
                    refine ⟨5534778535255942982178553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7379704713674590642904737 5534778535255942982178553)
                    ·
                      refine ⟨4151083901441957236633915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5534778535255942982178553 4151083901441957236633915)
                      ·
                        rfl

theorem cell23_8084207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 2, 2].length) (baseStart_8084207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084207 prefixEnd_8084207 := by exact prefixLift 8084207
  have htrace : WordTrace (prefixWord ++ tailWord_8084207) baseStart_8084207 baseEnd_8084207 := by
    simpa [prefixWord, tailWord_8084207, baseEnd_8084207] using wordTrace_append hprefix tailTrace_8084207
  have hstable : (prefixWord ++ tailWord_8084207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084207).length < 2 ^ (prefixWord ++ tailWord_8084207).sum := by decide
  have hdescent : baseEnd_8084207 < baseStart_8084207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084294 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_8084294 : Nat := 118140960795 + 8084294 * 2 ^ 59
def prefixEnd_8084294 : Nat := 4983230072969 + 3 ^ 40 * 8084294 * 2
def baseEnd_8084294 : Nat := 1383709524752966132082005

theorem tailTrace_8084294 : CollatzResearch.WordTrace tailWord_8084294 prefixEnd_8084294 1383709524752966132082005 := by
  unfold tailWord_8084294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9214325805437218760567623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196572283849327333558775957 9214325805437218760567623)
  ·
    refine ⟨13821488708155828140851435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9214325805437218760567623 13821488708155828140851435)
    ·
      refine ⟨20732233062233742211277153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13821488708155828140851435 20732233062233742211277153)
      ·
        refine ⟨15549174796675306658457865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20732233062233742211277153 15549174796675306658457865)
        ·
          refine ⟨11661881097506479993843399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15549174796675306658457865 11661881097506479993843399)
          ·
            refine ⟨17492821646259719990765099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11661881097506479993843399 17492821646259719990765099)
            ·
              refine ⟨26239232469389579986147649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17492821646259719990765099 26239232469389579986147649)
              ·
                refine ⟨19679424352042184989610737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26239232469389579986147649 19679424352042184989610737)
                ·
                  refine ⟨14759568264031638742208053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19679424352042184989610737 14759568264031638742208053)
                  ·
                    refine ⟨1383709524752966132082005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14759568264031638742208053 1383709524752966132082005)
                    ·
                      rfl

theorem cell23_8084294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_8084294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084294 prefixEnd_8084294 := by exact prefixLift 8084294
  have htrace : WordTrace (prefixWord ++ tailWord_8084294) baseStart_8084294 baseEnd_8084294 := by
    simpa [prefixWord, tailWord_8084294, baseEnd_8084294] using wordTrace_append hprefix tailTrace_8084294
  have hstable : (prefixWord ++ tailWord_8084294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084294).length < 2 ^ (prefixWord ++ tailWord_8084294).sum := by decide
  have hdescent : baseEnd_8084294 < baseStart_8084294 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084300 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 4, 2, 3]
def baseStart_8084300 : Nat := 118140960795 + 8084300 * 2 ^ 59
def prefixEnd_8084300 : Nat := 4983230072969 + 3 ^ 40 * 8084300 * 2
def baseEnd_8084300 : Nat := 4151131655142825372770987

theorem tailTrace_8084300 : CollatzResearch.WordTrace tailWord_8084300 prefixEnd_8084300 4151131655142825372770987 := by
  unfold tailWord_8084300
  simp only [CollatzResearch.WordTrace]
  refine ⟨147429322305984631681441177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196572429741312842241921569 147429322305984631681441177)
  ·
    refine ⟨110571991729488473761080883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147429322305984631681441177 110571991729488473761080883)
    ·
      refine ⟨165857987594232710641621325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110571991729488473761080883 165857987594232710641621325)
      ·
        refine ⟨62196745347837266490607997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165857987594232710641621325 62196745347837266490607997)
        ·
          refine ⟨23323779505438974933977999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62196745347837266490607997 23323779505438974933977999)
          ·
            refine ⟨34985669258158462400966999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23323779505438974933977999 34985669258158462400966999)
            ·
              refine ⟨52478503887237693601450499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34985669258158462400966999 52478503887237693601450499)
              ·
                refine ⟨78717755830856540402175749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52478503887237693601450499 78717755830856540402175749)
                ·
                  refine ⟨14759579218285601325407953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78717755830856540402175749 14759579218285601325407953)
                  ·
                    refine ⟨11069684413714200994055965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14759579218285601325407953 11069684413714200994055965)
                    ·
                      refine ⟨4151131655142825372770987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11069684413714200994055965 4151131655142825372770987)
                      ·
                        rfl

theorem cell23_8084300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_8084300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084300 prefixEnd_8084300 := by exact prefixLift 8084300
  have htrace : WordTrace (prefixWord ++ tailWord_8084300) baseStart_8084300 baseEnd_8084300 := by
    simpa [prefixWord, tailWord_8084300, baseEnd_8084300] using wordTrace_append hprefix tailTrace_8084300
  have hstable : (prefixWord ++ tailWord_8084300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084300).length < 2 ^ (prefixWord ++ tailWord_8084300).sum := by decide
  have hdescent : baseEnd_8084300 < baseStart_8084300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084334 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_8084334 : Nat := 118140960795 + 8084334 * 2 ^ 59
def prefixEnd_8084334 : Nat := 4983230072969 + 3 ^ 40 * 8084334 * 2
def baseEnd_8084334 : Nat := 4151149113485078239745831

theorem tailTrace_8084334 : CollatzResearch.WordTrace tailWord_8084334 prefixEnd_8084334 4151149113485078239745831 := by
  unfold tailWord_8084334
  simp only [CollatzResearch.WordTrace]
  refine ⟨36857485586730760896202507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196573256462564058113080037 36857485586730760896202507)
  ·
    refine ⟨55286228380096141344303761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36857485586730760896202507 55286228380096141344303761)
    ·
      refine ⟨41464671285072106008227821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55286228380096141344303761 41464671285072106008227821)
      ·
        refine ⟨15549251731902039753085433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41464671285072106008227821 15549251731902039753085433)
        ·
          refine ⟨11661938798926529814814075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15549251731902039753085433 11661938798926529814814075)
          ·
            refine ⟨17492908198389794722221113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11661938798926529814814075 17492908198389794722221113)
            ·
              refine ⟨13119681148792346041665835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17492908198389794722221113 13119681148792346041665835)
              ·
                refine ⟨19679521723188519062498753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13119681148792346041665835 19679521723188519062498753)
                ·
                  refine ⟨14759641292391389296874065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19679521723188519062498753 14759641292391389296874065)
                  ·
                    refine ⟨11069730969293541972655549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14759641292391389296874065 11069730969293541972655549)
                    ·
                      refine ⟨4151149113485078239745831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11069730969293541972655549 4151149113485078239745831)
                      ·
                        rfl

theorem cell23_8084334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_8084334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084334 prefixEnd_8084334 := by exact prefixLift 8084334
  have htrace : WordTrace (prefixWord ++ tailWord_8084334) baseStart_8084334 baseEnd_8084334 := by
    simpa [prefixWord, tailWord_8084334, baseEnd_8084334] using wordTrace_append hprefix tailTrace_8084334
  have hstable : (prefixWord ++ tailWord_8084334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084334).length < 2 ^ (prefixWord ++ tailWord_8084334).sum := by decide
  have hdescent : baseEnd_8084334 < baseStart_8084334 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084357 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 2, 3, 2]
def baseStart_8084357 : Nat := 118140960795 + 8084357 * 2 ^ 59
def prefixEnd_8084357 : Nat := 4983230072969 + 3 ^ 40 * 8084357 * 2
def baseEnd_8084357 : Nat := 4151160923540131649758225

theorem tailTrace_8084357 : CollatzResearch.WordTrace tailWord_8084357 prefixEnd_8084357 4151160923540131649758225 := by
  unfold tailWord_8084357
  simp only [CollatzResearch.WordTrace]
  refine ⟨294860723572762762097707325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196573815715175174731804883 294860723572762762097707325)
  ·
    refine ⟨110572771339786035786640247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294860723572762762097707325 110572771339786035786640247)
    ·
      refine ⟨165859157009679053679960371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110572771339786035786640247 165859157009679053679960371)
      ·
        refine ⟨248788735514518580519940557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165859157009679053679960371 248788735514518580519940557)
        ·
          refine ⟨93295775817944467694977709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248788735514518580519940557 93295775817944467694977709)
          ·
            refine ⟨34985915931729175385616641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93295775817944467694977709 34985915931729175385616641)
            ·
              refine ⟨26239436948796881539212481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34985915931729175385616641 26239436948796881539212481)
              ·
                refine ⟨19679577711597661154409361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26239436948796881539212481 19679577711597661154409361)
                ·
                  refine ⟨14759683283698245865807021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19679577711597661154409361 14759683283698245865807021)
                  ·
                    refine ⟨5534881231386842199677633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14759683283698245865807021 5534881231386842199677633)
                    ·
                      refine ⟨4151160923540131649758225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5534881231386842199677633 4151160923540131649758225)
                      ·
                        rfl

theorem cell23_8084357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 3, 2].length) (baseStart_8084357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084357 prefixEnd_8084357 := by exact prefixLift 8084357
  have htrace : WordTrace (prefixWord ++ tailWord_8084357) baseStart_8084357 baseEnd_8084357 := by
    simpa [prefixWord, tailWord_8084357, baseEnd_8084357] using wordTrace_append hprefix tailTrace_8084357
  have hstable : (prefixWord ++ tailWord_8084357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084357).length < 2 ^ (prefixWord ++ tailWord_8084357).sum := by decide
  have hdescent : baseEnd_8084357 < baseStart_8084357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084387 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 5, 2, 2]
def baseStart_8084387 : Nat := 118140960795 + 8084387 * 2 ^ 59
def prefixEnd_8084387 : Nat := 4983230072969 + 3 ^ 40 * 8084387 * 2
def baseEnd_8084387 : Nat := 4151176327959766532383087

theorem tailTrace_8084387 : CollatzResearch.WordTrace tailWord_8084387 prefixEnd_8084387 4151176327959766532383087 := by
  unfold tailWord_8084387
  simp only [CollatzResearch.WordTrace]
  refine ⟨294861817762654077221299415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196574545175102718147532943 294861817762654077221299415)
  ·
    refine ⟨442292726643981115831949123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294861817762654077221299415 442292726643981115831949123)
    ·
      refine ⟨663439089965971673747923685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442292726643981115831949123 663439089965971673747923685)
      ·
        refine ⟨124394829368619688827735691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 663439089965971673747923685 124394829368619688827735691)
        ·
          refine ⟨186592244052929533241603537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124394829368619688827735691 186592244052929533241603537)
          ·
            refine ⟨139944183039697149931202653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186592244052929533241603537 139944183039697149931202653)
            ·
              refine ⟨52479068639886431224200995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139944183039697149931202653 52479068639886431224200995)
              ·
                refine ⟨78718602959829646836301493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52479068639886431224200995 78718602959829646836301493)
                ·
                  refine ⟨7379869027484029390903265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78718602959829646836301493 7379869027484029390903265)
                  ·
                    refine ⟨5534901770613022043177449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7379869027484029390903265 5534901770613022043177449)
                    ·
                      refine ⟨4151176327959766532383087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5534901770613022043177449 4151176327959766532383087)
                      ·
                        rfl

theorem cell23_8084387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_8084387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084387 prefixEnd_8084387 := by exact prefixLift 8084387
  have htrace : WordTrace (prefixWord ++ tailWord_8084387) baseStart_8084387 baseEnd_8084387 := by
    simpa [prefixWord, tailWord_8084387, baseEnd_8084387] using wordTrace_append hprefix tailTrace_8084387
  have hstable : (prefixWord ++ tailWord_8084387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084387).length < 2 ^ (prefixWord ++ tailWord_8084387).sum := by decide
  have hdescent : baseEnd_8084387 < baseStart_8084387 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084391 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_8084391 : Nat := 118140960795 + 8084391 * 2 ^ 59
def prefixEnd_8084391 : Nat := 4983230072969 + 3 ^ 40 * 8084391 * 2
def baseEnd_8084391 : Nat := 4151178381882384516733069

theorem tailTrace_8084391 : CollatzResearch.WordTrace tailWord_8084391 prefixEnd_8084391 4151178381882384516733069 := by
  unfold tailWord_8084391
  simp only [CollatzResearch.WordTrace]
  refine ⟨294861963654639585904445027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196574642436426390602963351 294861963654639585904445027)
  ·
    refine ⟨442292945481959378856667541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294861963654639585904445027 442292945481959378856667541)
    ·
      refine ⟨20732481819466845883906291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 442292945481959378856667541 20732481819466845883906291)
      ·
        refine ⟨31098722729200268825859437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20732481819466845883906291 31098722729200268825859437)
        ·
          refine ⟨11662021023450100809697289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31098722729200268825859437 11662021023450100809697289)
          ·
            refine ⟨8746515767587575607272967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11662021023450100809697289 8746515767587575607272967)
            ·
              refine ⟨13119773651381363410909451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746515767587575607272967 13119773651381363410909451)
              ·
                refine ⟨19679660477072045116364177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13119773651381363410909451 19679660477072045116364177)
                ·
                  refine ⟨14759745357804033837273133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19679660477072045116364177 14759745357804033837273133)
                  ·
                    refine ⟨5534904509176512688977425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14759745357804033837273133 5534904509176512688977425)
                    ·
                      refine ⟨4151178381882384516733069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5534904509176512688977425 4151178381882384516733069)
                      ·
                        rfl

theorem cell23_8084391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_8084391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084391 prefixEnd_8084391 := by exact prefixLift 8084391
  have htrace : WordTrace (prefixWord ++ tailWord_8084391) baseStart_8084391 baseEnd_8084391 := by
    simpa [prefixWord, tailWord_8084391, baseEnd_8084391] using wordTrace_append hprefix tailTrace_8084391
  have hstable : (prefixWord ++ tailWord_8084391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084391).length < 2 ^ (prefixWord ++ tailWord_8084391).sum := by decide
  have hdescent : baseEnd_8084391 < baseStart_8084391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084401 : List Nat := [1, 2, 2, 4, 4, 1, 2, 1, 1, 5]
def baseStart_8084401 : Nat := 118140960795 + 8084401 * 2 ^ 59
def prefixEnd_8084401 : Nat := 4983230072969 + 3 ^ 40 * 8084401 * 2
def baseEnd_8084401 : Nat := 1383727838896309825869341

theorem tailTrace_8084401 : CollatzResearch.WordTrace tailWord_8084401 prefixEnd_8084401 1383727838896309825869341 := by
  unfold tailWord_8084401
  simp only [CollatzResearch.WordTrace]
  refine ⟨294862328384603357612309057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196574885589735571741539371 294862328384603357612309057)
  ·
    refine ⟨221146746288452518209231793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294862328384603357612309057 221146746288452518209231793)
    ·
      refine ⟨165860059716339388656923845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221146746288452518209231793 165860059716339388656923845)
      ·
        refine ⟨31098761196813635373173221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165860059716339388656923845 31098761196813635373173221)
        ·
          refine ⟨5831017724402556632469979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31098761196813635373173221 5831017724402556632469979)
          ·
            refine ⟨8746526586603834948704969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831017724402556632469979 8746526586603834948704969)
            ·
              refine ⟨6559894939952876211528727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8746526586603834948704969 6559894939952876211528727)
              ·
                refine ⟨9839842409929314317293091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559894939952876211528727 9839842409929314317293091)
                ·
                  refine ⟨14759763614893971475939637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9839842409929314317293091 14759763614893971475939637)
                  ·
                    refine ⟨1383727838896309825869341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14759763614893971475939637 1383727838896309825869341)
                    ·
                      rfl

theorem cell23_8084401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_8084401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084401 prefixEnd_8084401 := by exact prefixLift 8084401
  have htrace : WordTrace (prefixWord ++ tailWord_8084401) baseStart_8084401 baseEnd_8084401 := by
    simpa [prefixWord, tailWord_8084401, baseEnd_8084401] using wordTrace_append hprefix tailTrace_8084401
  have hstable : (prefixWord ++ tailWord_8084401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084401).length < 2 ^ (prefixWord ++ tailWord_8084401).sum := by decide
  have hdescent : baseEnd_8084401 < baseStart_8084401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084423 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 1, 9]
def baseStart_8084423 : Nat := 118140960795 + 8084423 * 2 ^ 59
def prefixEnd_8084423 : Nat := 4983230072969 + 3 ^ 40 * 8084423 * 2
def baseEnd_8084423 : Nat := 1383731604421109463844307

theorem tailTrace_8084423 : CollatzResearch.WordTrace tailWord_8084423 prefixEnd_8084423 1383731604421109463844307 := by
  unfold tailWord_8084423
  simp only [CollatzResearch.WordTrace]
  refine ⟨294863130790523655369609923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196575420527015770246406615 294863130790523655369609923)
  ·
    refine ⟨442294696185785483054414885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294863130790523655369609923 442294696185785483054414885)
    ·
      refine ⟨82930255534834778072702791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 442294696185785483054414885 82930255534834778072702791)
      ·
        refine ⟨124395383302252167109054187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82930255534834778072702791 124395383302252167109054187)
        ·
          refine ⟨186593074953378250663581281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124395383302252167109054187 186593074953378250663581281)
          ·
            refine ⟨139944806215033687997685961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186593074953378250663581281 139944806215033687997685961)
            ·
              refine ⟨104958604661275265998264471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139944806215033687997685961 104958604661275265998264471)
              ·
                refine ⟨157437906991912898997396707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104958604661275265998264471 157437906991912898997396707)
                ·
                  refine ⟨236156860487869348496095061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157437906991912898997396707 236156860487869348496095061)
                  ·
                    refine ⟨1383731604421109463844307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 236156860487869348496095061 1383731604421109463844307)
                    ·
                      rfl

theorem cell23_8084423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_8084423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084423 prefixEnd_8084423 := by exact prefixLift 8084423
  have htrace : WordTrace (prefixWord ++ tailWord_8084423) baseStart_8084423 baseEnd_8084423 := by
    simpa [prefixWord, tailWord_8084423, baseEnd_8084423] using wordTrace_append hprefix tailTrace_8084423
  have hstable : (prefixWord ++ tailWord_8084423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084423).length < 2 ^ (prefixWord ++ tailWord_8084423).sum := by decide
  have hdescent : baseEnd_8084423 < baseStart_8084423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084434 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_8084434 : Nat := 118140960795 + 8084434 * 2 ^ 59
def prefixEnd_8084434 : Nat := 4983230072969 + 3 ^ 40 * 8084434 * 2
def baseEnd_8084434 : Nat := 4151200461550527848495371

theorem tailTrace_8084434 : CollatzResearch.WordTrace tailWord_8084434 prefixEnd_8084434 4151200461550527848495371 := by
  unfold tailWord_8084434
  simp only [CollatzResearch.WordTrace]
  refine ⟨73715882998370951062065089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196575687995655869498840237 73715882998370951062065089)
  ·
    refine ⟨55286912248778213296548817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73715882998370951062065089 55286912248778213296548817)
    ·
      refine ⟨41465184186583659972411613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55286912248778213296548817 41465184186583659972411613)
      ·
        refine ⟨15549444069968872489654355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41465184186583659972411613 15549444069968872489654355)
        ·
          refine ⟨23324166104953308734481533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15549444069968872489654355 23324166104953308734481533)
          ·
            refine ⟨8746562289357490775430575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23324166104953308734481533 8746562289357490775430575)
            ·
              refine ⟨13119843434036236163145863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746562289357490775430575 13119843434036236163145863)
              ·
                refine ⟨19679765151054354244718795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13119843434036236163145863 19679765151054354244718795)
                ·
                  refine ⟨29519647726581531367078193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19679765151054354244718795 29519647726581531367078193)
                  ·
                    refine ⟨22139735794936148525308645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29519647726581531367078193 22139735794936148525308645)
                    ·
                      refine ⟨4151200461550527848495371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22139735794936148525308645 4151200461550527848495371)
                      ·
                        rfl

theorem cell23_8084434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_8084434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084434 prefixEnd_8084434 := by exact prefixLift 8084434
  have htrace : WordTrace (prefixWord ++ tailWord_8084434) baseStart_8084434 baseEnd_8084434 := by
    simpa [prefixWord, tailWord_8084434, baseEnd_8084434] using wordTrace_append hprefix tailTrace_8084434
  have hstable : (prefixWord ++ tailWord_8084434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084434).length < 2 ^ (prefixWord ++ tailWord_8084434).sum := by decide
  have hdescent : baseEnd_8084434 < baseStart_8084434 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084517 : List Nat := [1, 3, 1, 2, 2, 2, 2, 5, 5]
def baseStart_8084517 : Nat := 118140960795 + 8084517 * 2 ^ 59
def prefixEnd_8084517 : Nat := 4983230072969 + 3 ^ 40 * 8084517 * 2
def baseEnd_8084517 : Nat := 461249231160539002639721

theorem tailTrace_8084517 : CollatzResearch.WordTrace tailWord_8084517 prefixEnd_8084517 461249231160539002639721 := by
  unfold tailWord_8084517
  simp only [CollatzResearch.WordTrace]
  refine ⟨294866559252183109423531805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196577706168122072949021203 294866559252183109423531805)
  ·
    refine ⟨110574959719568666033824427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294866559252183109423531805 110574959719568666033824427)
    ·
      refine ⟨165862439579352999050736641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110574959719568666033824427 165862439579352999050736641)
      ·
        refine ⟨124396829684514749288052481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165862439579352999050736641 124396829684514749288052481)
        ·
          refine ⟨93297622263386061966039361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124396829684514749288052481 93297622263386061966039361)
          ·
            refine ⟨69973216697539546474529521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93297622263386061966039361 69973216697539546474529521)
            ·
              refine ⟨52479912523154659855897141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69973216697539546474529521 52479912523154659855897141)
              ·
                refine ⟨4919991799045749361490357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52479912523154659855897141 4919991799045749361490357)
                ·
                  refine ⟨461249231160539002639721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4919991799045749361490357 461249231160539002639721)
                  ·
                    rfl

theorem cell23_8084517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 5].length) (baseStart_8084517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084517 prefixEnd_8084517 := by exact prefixLift 8084517
  have htrace : WordTrace (prefixWord ++ tailWord_8084517) baseStart_8084517 baseEnd_8084517 := by
    simpa [prefixWord, tailWord_8084517, baseEnd_8084517] using wordTrace_append hprefix tailTrace_8084517
  have hstable : (prefixWord ++ tailWord_8084517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084517).length < 2 ^ (prefixWord ++ tailWord_8084517).sum := by decide
  have hdescent : baseEnd_8084517 < baseStart_8084517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084567 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 3, 6, 2]
def baseStart_8084567 : Nat := 118140960795 + 8084567 * 2 ^ 59
def prefixEnd_8084567 : Nat := 4983230072969 + 3 ^ 40 * 8084567 * 2
def baseEnd_8084567 : Nat := 4151268754477575828132259

theorem tailTrace_8084567 : CollatzResearch.WordTrace tailWord_8084567 prefixEnd_8084567 4151268754477575828132259 := by
  unfold tailWord_8084567
  simp only [CollatzResearch.WordTrace]
  refine ⟨294868382902001967962851955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196578921934667978641901303 294868382902001967962851955)
  ·
    refine ⟨442302574353002951944277933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294868382902001967962851955 442302574353002951944277933)
    ·
      refine ⟨165863465382376106979104225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 442302574353002951944277933 165863465382376106979104225)
      ·
        refine ⟨124397599036782080234328169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165863465382376106979104225 124397599036782080234328169)
        ·
          refine ⟨93298199277586560175746127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124397599036782080234328169 93298199277586560175746127)
          ·
            refine ⟨139947298916379840263619191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93298199277586560175746127 139947298916379840263619191)
            ·
              refine ⟨209920948374569760395428787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139947298916379840263619191 209920948374569760395428787)
              ·
                refine ⟨314881422561854640593143181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209920948374569760395428787 314881422561854640593143181)
                ·
                  refine ⟨118080533460695490222428693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314881422561854640593143181 118080533460695490222428693)
                  ·
                    refine ⟨5535025005970101104176345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118080533460695490222428693 5535025005970101104176345)
                    ·
                      refine ⟨4151268754477575828132259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5535025005970101104176345 4151268754477575828132259)
                      ·
                        rfl

theorem cell23_8084567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_8084567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084567 prefixEnd_8084567 := by exact prefixLift 8084567
  have htrace : WordTrace (prefixWord ++ tailWord_8084567) baseStart_8084567 baseEnd_8084567 := by
    simpa [prefixWord, tailWord_8084567, baseEnd_8084567] using wordTrace_append hprefix tailTrace_8084567
  have hstable : (prefixWord ++ tailWord_8084567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084567).length < 2 ^ (prefixWord ++ tailWord_8084567).sum := by decide
  have hdescent : baseEnd_8084567 < baseStart_8084567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084570 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_8084570 : Nat := 118140960795 + 8084570 * 2 ^ 59
def prefixEnd_8084570 : Nat := 4983230072969 + 3 ^ 40 * 8084570 * 2
def baseEnd_8084570 : Nat := 4151270294919539316394745

theorem tailTrace_8084570 : CollatzResearch.WordTrace tailWord_8084570 prefixEnd_8084570 4151270294919539316394745 := by
  unfold tailWord_8084570
  simp only [CollatzResearch.WordTrace]
  refine ⟨73717123080247774868802791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196578994880660732983474109 73717123080247774868802791)
  ·
    refine ⟨110575684620371662303204187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73717123080247774868802791 110575684620371662303204187)
    ·
      refine ⟨165863526930557493454806281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110575684620371662303204187 165863526930557493454806281)
      ·
        refine ⟨124397645197918120091104711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165863526930557493454806281 124397645197918120091104711)
        ·
          refine ⟨186596467796877180136657067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124397645197918120091104711 186596467796877180136657067)
          ·
            refine ⟨279894701695315770204985601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186596467796877180136657067 279894701695315770204985601)
            ·
              refine ⟨209921026271486827653739201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279894701695315770204985601 209921026271486827653739201)
              ·
                refine ⟨157440769703615120740304401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209921026271486827653739201 157440769703615120740304401)
                ·
                  refine ⟨118080577277711340555228301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157440769703615120740304401 118080577277711340555228301)
                  ·
                    refine ⟨44280216479141752708210613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118080577277711340555228301 44280216479141752708210613)
                    ·
                      refine ⟨4151270294919539316394745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44280216479141752708210613 4151270294919539316394745)
                      ·
                        rfl

theorem cell23_8084570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_8084570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084570 prefixEnd_8084570 := by exact prefixLift 8084570
  have htrace : WordTrace (prefixWord ++ tailWord_8084570) baseStart_8084570 baseEnd_8084570 := by
    simpa [prefixWord, tailWord_8084570, baseEnd_8084570] using wordTrace_append hprefix tailTrace_8084570
  have hstable : (prefixWord ++ tailWord_8084570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084570).length < 2 ^ (prefixWord ++ tailWord_8084570).sum := by decide
  have hdescent : baseEnd_8084570 < baseStart_8084570 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8084594 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_8084594 : Nat := 118140960795 + 8084594 * 2 ^ 59
def prefixEnd_8084594 : Nat := 4983230072969 + 3 ^ 40 * 8084594 * 2
def baseEnd_8084594 : Nat := 1383760872818415740831545

theorem tailTrace_8084594 : CollatzResearch.WordTrace tailWord_8084594 prefixEnd_8084594 1383760872818415740831545 := by
  unfold tailWord_8084594
  simp only [CollatzResearch.WordTrace]
  refine ⟨73717341918226037893521209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196579578448602767716056557 73717341918226037893521209)
  ·
    refine ⟨55288006438669528420140907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73717341918226037893521209 55288006438669528420140907)
    ·
      refine ⟨82932009658004292630211361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55288006438669528420140907 82932009658004292630211361)
      ·
        refine ⟨62199007243503219472658521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82932009658004292630211361 62199007243503219472658521)
        ·
          refine ⟨46649255432627414604493891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62199007243503219472658521 46649255432627414604493891)
          ·
            refine ⟨69973883148941121906740837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46649255432627414604493891 69973883148941121906740837)
            ·
              refine ⟨13120103090426460357513907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69973883148941121906740837 13120103090426460357513907)
              ·
                refine ⟨19680154635639690536270861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13120103090426460357513907 19680154635639690536270861)
                ·
                  refine ⟨7380057988364883951101573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19680154635639690536270861 7380057988364883951101573)
                  ·
                    refine ⟨1383760872818415740831545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7380057988364883951101573 1383760872818415740831545)
                    ·
                      rfl

theorem cell23_8084594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_8084594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8084594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8084594 prefixEnd_8084594 := by exact prefixLift 8084594
  have htrace : WordTrace (prefixWord ++ tailWord_8084594) baseStart_8084594 baseEnd_8084594 := by
    simpa [prefixWord, tailWord_8084594, baseEnd_8084594] using wordTrace_append hprefix tailTrace_8084594
  have hstable : (prefixWord ++ tailWord_8084594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8084594).length < 2 ^ (prefixWord ++ tailWord_8084594).sum := by decide
  have hdescent : baseEnd_8084594 < baseStart_8084594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8084594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
