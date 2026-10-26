import V185TrunkScan23Chunk1235

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7322829 : List Nat := [1, 6, 2, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_7322829 : Nat := 118140960795 + 7322829 * 2 ^ 59
def prefixEnd_7322829 : Nat := 4983230072969 + 3 ^ 40 * 7322829 * 2
def baseEnd_7322829 : Nat := 3760131027683035131560429

theorem tailTrace_7322829 : CollatzResearch.WordTrace tailWord_7322829 prefixEnd_7322829 3760131027683035131560429 := by
  unfold tailWord_7322829
  simp only [CollatzResearch.WordTrace]
  refine ⟨267085515587648647469803541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178057010391765764979869027 267085515587648647469803541)
  ·
    refine ⟨12519633543171030350147041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 267085515587648647469803541 12519633543171030350147041)
    ·
      refine ⟨9389725157378272762610281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12519633543171030350147041 9389725157378272762610281)
      ·
        refine ⟨7042293868033704571957711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9389725157378272762610281 7042293868033704571957711)
        ·
          refine ⟨10563440802050556857936567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7042293868033704571957711 10563440802050556857936567)
          ·
            refine ⟨15845161203075835286904851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10563440802050556857936567 15845161203075835286904851)
            ·
              refine ⟨23767741804613752930357277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15845161203075835286904851 23767741804613752930357277)
              ·
                refine ⟨8912903176730157348883979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23767741804613752930357277 8912903176730157348883979)
                ·
                  refine ⟨13369354765095236023325969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8912903176730157348883979 13369354765095236023325969)
                  ·
                    refine ⟨10027016073821427017494477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13369354765095236023325969 10027016073821427017494477)
                    ·
                      refine ⟨3760131027683035131560429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10027016073821427017494477 3760131027683035131560429)
                      ·
                        rfl

theorem cell23_7322829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_7322829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322829 prefixEnd_7322829 := by exact prefixLift 7322829
  have htrace : WordTrace (prefixWord ++ tailWord_7322829) baseStart_7322829 baseEnd_7322829 := by
    simpa [prefixWord, tailWord_7322829, baseEnd_7322829] using wordTrace_append hprefix tailTrace_7322829
  have hstable : (prefixWord ++ tailWord_7322829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322829).length < 2 ^ (prefixWord ++ tailWord_7322829).sum := by decide
  have hdescent : baseEnd_7322829 < baseStart_7322829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7322966 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_7322966 : Nat := 118140960795 + 7322966 * 2 ^ 59
def prefixEnd_7322966 : Nat := 4983230072969 + 3 ^ 40 * 7322966 * 2
def baseEnd_7322966 : Nat := 3760201374532701095547299

theorem tailTrace_7322966 : CollatzResearch.WordTrace tailWord_7322966 prefixEnd_7322966 3760201374532701095547299 := by
  unfold tailWord_7322966
  simp only [CollatzResearch.WordTrace]
  refine ⟨16693157024259519991721297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178060341592101546578360501 16693157024259519991721297)
  ·
    refine ⟨12519867768194639993790973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16693157024259519991721297 12519867768194639993790973)
    ·
      refine ⟨4694950413072989997671615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12519867768194639993790973 4694950413072989997671615)
      ·
        refine ⟨7042425619609484996507423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4694950413072989997671615 7042425619609484996507423)
        ·
          refine ⟨10563638429414227494761135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7042425619609484996507423 10563638429414227494761135)
          ·
            refine ⟨15845457644121341242141703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10563638429414227494761135 15845457644121341242141703)
            ·
              refine ⟨23768186466182011863212555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15845457644121341242141703 23768186466182011863212555)
              ·
                refine ⟨35652279699273017794818833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23768186466182011863212555 35652279699273017794818833)
                ·
                  refine ⟨26739209774454763346114125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35652279699273017794818833 26739209774454763346114125)
                  ·
                    refine ⟨10027203665420536254792797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26739209774454763346114125 10027203665420536254792797)
                    ·
                      refine ⟨3760201374532701095547299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10027203665420536254792797 3760201374532701095547299)
                      ·
                        rfl

theorem cell23_7322966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_7322966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7322966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7322966 prefixEnd_7322966 := by exact prefixLift 7322966
  have htrace : WordTrace (prefixWord ++ tailWord_7322966) baseStart_7322966 baseEnd_7322966 := by
    simpa [prefixWord, tailWord_7322966, baseEnd_7322966] using wordTrace_append hprefix tailTrace_7322966
  have hstable : (prefixWord ++ tailWord_7322966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7322966).length < 2 ^ (prefixWord ++ tailWord_7322966).sum := by decide
  have hdescent : baseEnd_7322966 < baseStart_7322966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7322966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323005 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 5, 1, 3]
def baseStart_7323005 : Nat := 118140960795 + 7323005 * 2 ^ 59
def prefixEnd_7323005 : Nat := 4983230072969 + 3 ^ 40 * 7323005 * 2
def baseEnd_7323005 : Nat := 3760221400278226442959619

theorem tailTrace_7323005 : CollatzResearch.WordTrace tailWord_7323005 prefixEnd_7323005 3760221400278226442959619 := by
  unfold tailWord_7323005
  simp only [CollatzResearch.WordTrace]
  refine ⟨267091934835011029528210469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178061289890007353018806979 267091934835011029528210469)
  ·
    refine ⟨50079737781564568036539463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267091934835011029528210469 50079737781564568036539463)
    ·
      refine ⟨75119606672346852054809195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50079737781564568036539463 75119606672346852054809195)
      ·
        refine ⟨112679410008520278082213793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75119606672346852054809195 112679410008520278082213793)
        ·
          refine ⟨84509557506390208561660345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112679410008520278082213793 84509557506390208561660345)
          ·
            refine ⟨63382168129792656421245259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84509557506390208561660345 63382168129792656421245259)
            ·
              refine ⟨95073252194688984631867889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63382168129792656421245259 95073252194688984631867889)
              ·
                refine ⟨71304939146016738473900917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95073252194688984631867889 71304939146016738473900917)
                ·
                  refine ⟨6684838044939069231928211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71304939146016738473900917 6684838044939069231928211)
                  ·
                    refine ⟨10027257067408603847892317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6684838044939069231928211 10027257067408603847892317)
                    ·
                      refine ⟨3760221400278226442959619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10027257067408603847892317 3760221400278226442959619)
                      ·
                        rfl

theorem cell23_7323005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_7323005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323005 prefixEnd_7323005 := by exact prefixLift 7323005
  have htrace : WordTrace (prefixWord ++ tailWord_7323005) baseStart_7323005 baseEnd_7323005 := by
    simpa [prefixWord, tailWord_7323005, baseEnd_7323005] using wordTrace_append hprefix tailTrace_7323005
  have hstable : (prefixWord ++ tailWord_7323005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323005).length < 2 ^ (prefixWord ++ tailWord_7323005).sum := by decide
  have hdescent : baseEnd_7323005 < baseStart_7323005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323042 : List Nat := [3, 3, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_7323042 : Nat := 118140960795 + 7323042 * 2 ^ 59
def prefixEnd_7323042 : Nat := 4983230072969 + 3 ^ 40 * 7323042 * 2
def baseEnd_7323042 : Nat := 1253413466354147599398983

theorem tailTrace_7323042 : CollatzResearch.WordTrace tailWord_7323042 prefixEnd_7323042 1253413466354147599398983 := by
  unfold tailWord_7323042
  simp only [CollatzResearch.WordTrace]
  refine ⟨66773321083969246211826845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178062189557251323231538253 66773321083969246211826845)
  ·
    refine ⟨25039995406488467329435067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66773321083969246211826845 25039995406488467329435067)
    ·
      refine ⟨37559993109732700994152601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25039995406488467329435067 37559993109732700994152601)
      ·
        refine ⟨28169994832299525745614451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37559993109732700994152601 28169994832299525745614451)
        ·
          refine ⟨42254992248449288618421677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28169994832299525745614451 42254992248449288618421677)
          ·
            refine ⟨15845622093168483231908129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42254992248449288618421677 15845622093168483231908129)
            ·
              refine ⟨11884216569876362423931097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15845622093168483231908129 11884216569876362423931097)
              ·
                refine ⟨8913162427407271817948323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11884216569876362423931097 8913162427407271817948323)
                ·
                  refine ⟨13369743641110907726922485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8913162427407271817948323 13369743641110907726922485)
                  ·
                    refine ⟨1253413466354147599398983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13369743641110907726922485 1253413466354147599398983)
                    ·
                      rfl

theorem cell23_7323042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_7323042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323042 prefixEnd_7323042 := by exact prefixLift 7323042
  have htrace : WordTrace (prefixWord ++ tailWord_7323042) baseStart_7323042 baseEnd_7323042 := by
    simpa [prefixWord, tailWord_7323042, baseEnd_7323042] using wordTrace_append hprefix tailTrace_7323042
  have hstable : (prefixWord ++ tailWord_7323042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323042).length < 2 ^ (prefixWord ++ tailWord_7323042).sum := by decide
  have hdescent : baseEnd_7323042 < baseStart_7323042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323108 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_7323108 : Nat := 118140960795 + 7323108 * 2 ^ 59
def prefixEnd_7323108 : Nat := 4983230072969 + 3 ^ 40 * 7323108 * 2
def baseEnd_7323108 : Nat := 3760274288785639539971645

theorem tailTrace_7323108 : CollatzResearch.WordTrace tailWord_7323108 prefixEnd_7323108 3760274288785639539971645 := by
  unfold tailWord_7323108
  simp only [CollatzResearch.WordTrace]
  refine ⟨133547845776818939059604989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178063794369091918746139985 133547845776818939059604989)
  ·
    refine ⟨50080442166307102147351871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133547845776818939059604989 50080442166307102147351871)
    ·
      refine ⟨75120663249460653221027807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50080442166307102147351871 75120663249460653221027807)
      ·
        refine ⟨112680994874190979831541711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75120663249460653221027807 112680994874190979831541711)
        ·
          refine ⟨169021492311286469747312567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112680994874190979831541711 169021492311286469747312567)
          ·
            refine ⟨253532238466929704620968851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169021492311286469747312567 253532238466929704620968851)
            ·
              refine ⟨380298357700394556931453277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253532238466929704620968851 380298357700394556931453277)
              ·
                refine ⟨142611884137647958849294979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380298357700394556931453277 142611884137647958849294979)
                ·
                  refine ⟨213917826206471938273942469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142611884137647958849294979 213917826206471938273942469)
                  ·
                    refine ⟨40109592413713488426364213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 213917826206471938273942469 40109592413713488426364213)
                    ·
                      refine ⟨3760274288785639539971645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40109592413713488426364213 3760274288785639539971645)
                      ·
                        rfl

theorem cell23_7323108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_7323108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323108 prefixEnd_7323108 := by exact prefixLift 7323108
  have htrace : WordTrace (prefixWord ++ tailWord_7323108) baseStart_7323108 baseEnd_7323108 := by
    simpa [prefixWord, tailWord_7323108, baseEnd_7323108] using wordTrace_append hprefix tailTrace_7323108
  have hstable : (prefixWord ++ tailWord_7323108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323108).length < 2 ^ (prefixWord ++ tailWord_7323108).sum := by decide
  have hdescent : baseEnd_7323108 < baseStart_7323108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323165 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_7323165 : Nat := 118140960795 + 7323165 * 2 ^ 59
def prefixEnd_7323165 : Nat := 4983230072969 + 3 ^ 40 * 7323165 * 2
def baseEnd_7323165 : Nat := 3760303557182945816958883

theorem tailTrace_7323165 : CollatzResearch.WordTrace tailWord_7323165 prefixEnd_7323165 3760303557182945816958883 := by
  unfold tailWord_7323165
  simp only [CollatzResearch.WordTrace]
  refine ⟨267097770514431376854034949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178065180342954251236023299 267097770514431376854034949)
  ·
    refine ⟨50080831971455883160131553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267097770514431376854034949 50080831971455883160131553)
    ·
      refine ⟨37560623978591912370098665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50080831971455883160131553 37560623978591912370098665)
      ·
        refine ⟨28170467983943934277573999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37560623978591912370098665 28170467983943934277573999)
        ·
          refine ⟨42255701975915901416360999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28170467983943934277573999 42255701975915901416360999)
          ·
            refine ⟨63383552963873852124541499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42255701975915901416360999 63383552963873852124541499)
            ·
              refine ⟨95075329445810778186812249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63383552963873852124541499 95075329445810778186812249)
              ·
                refine ⟨71306497084358083640109187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95075329445810778186812249 71306497084358083640109187)
                ·
                  refine ⟨106959745626537125460163781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71306497084358083640109187 106959745626537125460163781)
                  ·
                    refine ⟨20054952304975711023780709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106959745626537125460163781 20054952304975711023780709)
                    ·
                      refine ⟨3760303557182945816958883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20054952304975711023780709 3760303557182945816958883)
                      ·
                        rfl

theorem cell23_7323165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_7323165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323165 prefixEnd_7323165 := by exact prefixLift 7323165
  have htrace : WordTrace (prefixWord ++ tailWord_7323165) baseStart_7323165 baseEnd_7323165 := by
    simpa [prefixWord, tailWord_7323165, baseEnd_7323165] using wordTrace_append hprefix tailTrace_7323165
  have hstable : (prefixWord ++ tailWord_7323165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323165).length < 2 ^ (prefixWord ++ tailWord_7323165).sum := by decide
  have hdescent : baseEnd_7323165 < baseStart_7323165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323182 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_7323182 : Nat := 118140960795 + 7323182 * 2 ^ 59
def prefixEnd_7323182 : Nat := 4983230072969 + 3 ^ 40 * 7323182 * 2
def baseEnd_7323182 : Nat := 3760312286354072250446305

theorem tailTrace_7323182 : CollatzResearch.WordTrace tailWord_7323182 prefixEnd_7323182 3760312286354072250446305 := by
  unfold tailWord_7323182
  simp only [CollatzResearch.WordTrace]
  refine ⟨33387298819421223594675475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178065593703579859171602533 33387298819421223594675475)
  ·
    refine ⟨50080948229131835392013213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33387298819421223594675475 50080948229131835392013213)
    ·
      refine ⟨18780355585924438272004955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50080948229131835392013213 18780355585924438272004955)
      ·
        refine ⟨28170533378886657408007433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18780355585924438272004955 28170533378886657408007433)
        ·
          refine ⟨21127900034164993056005575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28170533378886657408007433 21127900034164993056005575)
          ·
            refine ⟨31691850051247489584008363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21127900034164993056005575 31691850051247489584008363)
            ·
              refine ⟨47537775076871234376012545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31691850051247489584008363 47537775076871234376012545)
              ·
                refine ⟨35653331307653425782009409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47537775076871234376012545 35653331307653425782009409)
                ·
                  refine ⟨26739998480740069336507057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35653331307653425782009409 26739998480740069336507057)
                  ·
                    refine ⟨20054998860555052002380293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26739998480740069336507057 20054998860555052002380293)
                    ·
                      refine ⟨3760312286354072250446305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20054998860555052002380293 3760312286354072250446305)
                      ·
                        rfl

theorem cell23_7323182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_7323182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323182 prefixEnd_7323182 := by exact prefixLift 7323182
  have htrace : WordTrace (prefixWord ++ tailWord_7323182) baseStart_7323182 baseEnd_7323182 := by
    simpa [prefixWord, tailWord_7323182, baseEnd_7323182] using wordTrace_append hprefix tailTrace_7323182
  have hstable : (prefixWord ++ tailWord_7323182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323182).length < 2 ^ (prefixWord ++ tailWord_7323182).sum := by decide
  have hdescent : baseEnd_7323182 < baseStart_7323182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323192 : List Nat := [2, 1, 2, 1, 4, 2, 2, 4, 5]
def baseStart_7323192 : Nat := 118140960795 + 7323192 * 2 ^ 59
def prefixEnd_7323192 : Nat := 4983230072969 + 3 ^ 40 * 7323192 * 2
def baseEnd_7323192 : Nat := 417813046795624134591251

theorem tailTrace_7323192 : CollatzResearch.WordTrace tailWord_7323192 prefixEnd_7323192 417813046795624134591251 := by
  unfold tailWord_7323192
  simp only [CollatzResearch.WordTrace]
  refine ⟨133549377642666780232633915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178065836856889040310178553 133549377642666780232633915)
  ·
    refine ⟨200324066464000170348950873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133549377642666780232633915 200324066464000170348950873)
    ·
      refine ⟨150243049848000127761713155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200324066464000170348950873 150243049848000127761713155)
      ·
        refine ⟨225364574772000191642569733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150243049848000127761713155 225364574772000191642569733)
        ·
          refine ⟨42255857769750035932981825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225364574772000191642569733 42255857769750035932981825)
          ·
            refine ⟨31691893327312526949736369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42255857769750035932981825 31691893327312526949736369)
            ·
              refine ⟨23768919995484395212302277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31691893327312526949736369 23768919995484395212302277)
              ·
                refine ⟨4456672499153324102306677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23768919995484395212302277 4456672499153324102306677)
                ·
                  refine ⟨417813046795624134591251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4456672499153324102306677 417813046795624134591251)
                  ·
                    rfl

theorem cell23_7323192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 5].length) (baseStart_7323192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323192 prefixEnd_7323192 := by exact prefixLift 7323192
  have htrace : WordTrace (prefixWord ++ tailWord_7323192) baseStart_7323192 baseEnd_7323192 := by
    simpa [prefixWord, tailWord_7323192, baseEnd_7323192] using wordTrace_append hprefix tailTrace_7323192
  have hstable : (prefixWord ++ tailWord_7323192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323192).length < 2 ^ (prefixWord ++ tailWord_7323192).sum := by decide
  have hdescent : baseEnd_7323192 < baseStart_7323192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323225 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 6, 1, 4]
def baseStart_7323225 : Nat := 118140960795 + 7323225 * 2 ^ 59
def prefixEnd_7323225 : Nat := 4983230072969 + 3 ^ 40 * 7323225 * 2
def baseEnd_7323225 : Nat := 3760334366022215582208607

theorem tailTrace_7323225 : CollatzResearch.WordTrace tailWord_7323225 prefixEnd_7323225 3760334366022215582208607 := by
  unfold tailWord_7323225
  simp only [CollatzResearch.WordTrace]
  refine ⟨267099958894214007101219129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178066639262809338067479419 267099958894214007101219129)
  ·
    refine ⟨200324969170660505325914347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267099958894214007101219129 200324969170660505325914347)
    ·
      refine ⟨300487453755990757988871521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200324969170660505325914347 300487453755990757988871521)
      ·
        refine ⟨225365590316993068491653641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300487453755990757988871521 225365590316993068491653641)
        ·
          refine ⟨169024192737744801368740231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225365590316993068491653641 169024192737744801368740231)
          ·
            refine ⟨253536289106617202053110347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169024192737744801368740231 253536289106617202053110347)
            ·
              refine ⟨380304433659925803079665521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253536289106617202053110347 380304433659925803079665521)
              ·
                refine ⟨285228325244944352309749141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380304433659925803079665521 285228325244944352309749141)
                ·
                  refine ⟨13370077745856766514519491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 285228325244944352309749141 13370077745856766514519491)
                  ·
                    refine ⟨20055116618785149771779237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13370077745856766514519491 20055116618785149771779237)
                    ·
                      refine ⟨3760334366022215582208607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20055116618785149771779237 3760334366022215582208607)
                      ·
                        rfl

theorem cell23_7323225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_7323225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323225 prefixEnd_7323225 := by exact prefixLift 7323225
  have htrace : WordTrace (prefixWord ++ tailWord_7323225) baseStart_7323225 baseEnd_7323225 := by
    simpa [prefixWord, tailWord_7323225, baseEnd_7323225] using wordTrace_append hprefix tailTrace_7323225
  have hstable : (prefixWord ++ tailWord_7323225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323225).length < 2 ^ (prefixWord ++ tailWord_7323225).sum := by decide
  have hdescent : baseEnd_7323225 < baseStart_7323225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323242 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_7323242 : Nat := 118140960795 + 7323242 * 2 ^ 59
def prefixEnd_7323242 : Nat := 4983230072969 + 3 ^ 40 * 7323242 * 2
def baseEnd_7323242 : Nat := 3760343095193342015696029

theorem tailTrace_7323242 : CollatzResearch.WordTrace tailWord_7323242 prefixEnd_7323242 3760343095193342015696029 := by
  unfold tailWord_7323242
  simp only [CollatzResearch.WordTrace]
  refine ⟨66775144733788104751146995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178067052623434946003058653 66775144733788104751146995)
  ·
    refine ⟨100162717100682157126720493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66775144733788104751146995 100162717100682157126720493)
    ·
      refine ⟨37561018912755808922520185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100162717100682157126720493 37561018912755808922520185)
      ·
        refine ⟨28170764184566856691890139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37561018912755808922520185 28170764184566856691890139)
        ·
          refine ⟨42256146276850285037835209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28170764184566856691890139 42256146276850285037835209)
          ·
            refine ⟨31692109707637713778376407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42256146276850285037835209 31692109707637713778376407)
            ·
              refine ⟨47538164561456570667564611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31692109707637713778376407 47538164561456570667564611)
              ·
                refine ⟨71307246842184856001346917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47538164561456570667564611 71307246842184856001346917)
                ·
                  refine ⟨13370108782909660500252547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71307246842184856001346917 13370108782909660500252547)
                  ·
                    refine ⟨20055163174364490750378821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13370108782909660500252547 20055163174364490750378821)
                    ·
                      refine ⟨3760343095193342015696029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20055163174364490750378821 3760343095193342015696029)
                      ·
                        rfl

theorem cell23_7323242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_7323242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323242 prefixEnd_7323242 := by exact prefixLift 7323242
  have htrace : WordTrace (prefixWord ++ tailWord_7323242) baseStart_7323242 baseEnd_7323242 := by
    simpa [prefixWord, tailWord_7323242, baseEnd_7323242] using wordTrace_append hprefix tailTrace_7323242
  have hstable : (prefixWord ++ tailWord_7323242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323242).length < 2 ^ (prefixWord ++ tailWord_7323242).sum := by decide
  have hdescent : baseEnd_7323242 < baseStart_7323242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323326 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_7323326 : Nat := 118140960795 + 7323326 * 2 ^ 59
def prefixEnd_7323326 : Nat := 4983230072969 + 3 ^ 40 * 7323326 * 2
def baseEnd_7323326 : Nat := 3760386227568319687045643

theorem tailTrace_7323326 : CollatzResearch.WordTrace tailWord_7323326 prefixEnd_7323326 3760386227568319687045643 := by
  unfold tailWord_7323326
  simp only [CollatzResearch.WordTrace]
  refine ⟨33387955333356012668830729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178069095111232067567097221 33387955333356012668830729)
  ·
    refine ⟨25040966500017009501623047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33387955333356012668830729 25040966500017009501623047)
    ·
      refine ⟨37561449750025514252434571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25040966500017009501623047 37561449750025514252434571)
      ·
        refine ⟨56342174625038271378651857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37561449750025514252434571 56342174625038271378651857)
        ·
          refine ⟨42256630968778703533988893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56342174625038271378651857 42256630968778703533988893)
          ·
            refine ⟨15846236613292013825245835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42256630968778703533988893 15846236613292013825245835)
            ·
              refine ⟨23769354919938020737868753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15846236613292013825245835 23769354919938020737868753)
              ·
                refine ⟨17827016189953515553401565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23769354919938020737868753 17827016189953515553401565)
                ·
                  refine ⟨6685131071232568332525587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17827016189953515553401565 6685131071232568332525587)
                  ·
                    refine ⟨10027696606848852498788381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6685131071232568332525587 10027696606848852498788381)
                    ·
                      refine ⟨3760386227568319687045643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10027696606848852498788381 3760386227568319687045643)
                      ·
                        rfl

theorem cell23_7323326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_7323326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323326 prefixEnd_7323326 := by exact prefixLift 7323326
  have htrace : WordTrace (prefixWord ++ tailWord_7323326) baseStart_7323326 baseEnd_7323326 := by
    simpa [prefixWord, tailWord_7323326, baseEnd_7323326] using wordTrace_append hprefix tailTrace_7323326
  have hstable : (prefixWord ++ tailWord_7323326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323326).length < 2 ^ (prefixWord ++ tailWord_7323326).sum := by decide
  have hdescent : baseEnd_7323326 < baseStart_7323326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323342 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_7323342 : Nat := 118140960795 + 7323342 * 2 ^ 59
def prefixEnd_7323342 : Nat := 4983230072969 + 3 ^ 40 * 7323342 * 2
def baseEnd_7323342 : Nat := 1253464814419597208148523

theorem tailTrace_7323342 : CollatzResearch.WordTrace tailWord_7323342 prefixEnd_7323342 1253464814419597208148523 := by
  unfold tailWord_7323342
  simp only [CollatzResearch.WordTrace]
  refine ⟨33388028279348767010403535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178069484156526757388818853 33388028279348767010403535)
  ·
    refine ⟨50082042419023150515605303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33388028279348767010403535 50082042419023150515605303)
    ·
      refine ⟨75123063628534725773407955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50082042419023150515605303 75123063628534725773407955)
      ·
        refine ⟨112684595442802088660111933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75123063628534725773407955 112684595442802088660111933)
        ·
          refine ⟨42256723291050783247541975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112684595442802088660111933 42256723291050783247541975)
          ·
            refine ⟨63385084936576174871312963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42256723291050783247541975 63385084936576174871312963)
            ·
              refine ⟨95077627404864262306969445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63385084936576174871312963 95077627404864262306969445)
              ·
                refine ⟨17827055138412049182556771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95077627404864262306969445 17827055138412049182556771)
                ·
                  refine ⟨26740582707618073773835157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17827055138412049182556771 26740582707618073773835157)
                  ·
                    refine ⟨1253464814419597208148523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26740582707618073773835157 1253464814419597208148523)
                    ·
                      rfl

theorem cell23_7323342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_7323342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323342 prefixEnd_7323342 := by exact prefixLift 7323342
  have htrace : WordTrace (prefixWord ++ tailWord_7323342) baseStart_7323342 baseEnd_7323342 := by
    simpa [prefixWord, tailWord_7323342, baseEnd_7323342] using wordTrace_append hprefix tailTrace_7323342
  have hstable : (prefixWord ++ tailWord_7323342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323342).length < 2 ^ (prefixWord ++ tailWord_7323342).sum := by decide
  have hdescent : baseEnd_7323342 < baseStart_7323342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323346 : List Nat := [3, 2, 2, 2, 2, 1, 4, 1, 1, 5]
def baseStart_7323346 : Nat := 118140960795 + 7323346 * 2 ^ 59
def prefixEnd_7323346 : Nat := 4983230072969 + 3 ^ 40 * 7323346 * 2
def baseEnd_7323346 : Nat := 1253465499060469869598517

theorem tailTrace_7323346 : CollatzResearch.WordTrace tailWord_7323346 prefixEnd_7323346 1253465499060469869598517 := by
  unfold tailWord_7323346
  simp only [CollatzResearch.WordTrace]
  refine ⟨66776093031693911191593473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178069581417850429844249261 66776093031693911191593473)
  ·
    refine ⟨50082069773770433393695105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66776093031693911191593473 50082069773770433393695105)
    ·
      refine ⟨37561552330327825045271329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50082069773770433393695105 37561552330327825045271329)
      ·
        refine ⟨28171164247745868783953497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37561552330327825045271329 28171164247745868783953497)
        ·
          refine ⟨21128373185809401587965123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28171164247745868783953497 21128373185809401587965123)
          ·
            refine ⟨31692559778714102381947685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21128373185809401587965123 31692559778714102381947685)
            ·
              refine ⟨5942354958508894196615191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31692559778714102381947685 5942354958508894196615191)
              ·
                refine ⟨8913532437763341294922787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5942354958508894196615191 8913532437763341294922787)
                ·
                  refine ⟨13370298656645011942384181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8913532437763341294922787 13370298656645011942384181)
                  ·
                    refine ⟨1253465499060469869598517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13370298656645011942384181 1253465499060469869598517)
                    ·
                      rfl

theorem cell23_7323346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_7323346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323346 prefixEnd_7323346 := by exact prefixLift 7323346
  have htrace : WordTrace (prefixWord ++ tailWord_7323346) baseStart_7323346 baseEnd_7323346 := by
    simpa [prefixWord, tailWord_7323346, baseEnd_7323346] using wordTrace_append hprefix tailTrace_7323346
  have hstable : (prefixWord ++ tailWord_7323346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323346).length < 2 ^ (prefixWord ++ tailWord_7323346).sum := by decide
  have hdescent : baseEnd_7323346 < baseStart_7323346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323350 : List Nat := [5, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_7323350 : Nat := 118140960795 + 7323350 * 2 ^ 59
def prefixEnd_7323350 : Nat := 4983230072969 + 3 ^ 40 * 7323350 * 2
def baseEnd_7323350 : Nat := 417822061233780843682837

theorem tailTrace_7323350 : CollatzResearch.WordTrace tailWord_7323350 prefixEnd_7323350 417822061233780843682837 := by
  unfold tailWord_7323350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16694032376172572090594969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178069678679174102299679669 16694032376172572090594969)
  ·
    refine ⟨12520524282129429067946227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16694032376172572090594969 12520524282129429067946227)
    ·
      refine ⟨18780786423194143601919341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12520524282129429067946227 18780786423194143601919341)
      ·
        refine ⟨7042794908697803850719753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18780786423194143601919341 7042794908697803850719753)
        ·
          refine ⟨5282096181523352888039815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7042794908697803850719753 5282096181523352888039815)
          ·
            refine ⟨7923144272285029332059723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5282096181523352888039815 7923144272285029332059723)
            ·
              refine ⟨11884716408427543998089585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7923144272285029332059723 11884716408427543998089585)
              ·
                refine ⟨8913537306320657998567189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11884716408427543998089585 8913537306320657998567189)
                ·
                  refine ⟨417822061233780843682837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8913537306320657998567189 417822061233780843682837)
                  ·
                    rfl

theorem cell23_7323350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_7323350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323350 prefixEnd_7323350 := by exact prefixLift 7323350
  have htrace : WordTrace (prefixWord ++ tailWord_7323350) baseStart_7323350 baseEnd_7323350 := by
    simpa [prefixWord, tailWord_7323350, baseEnd_7323350] using wordTrace_append hprefix tailTrace_7323350
  have hstable : (prefixWord ++ tailWord_7323350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323350).length < 2 ^ (prefixWord ++ tailWord_7323350).sum := by decide
  have hdescent : baseEnd_7323350 < baseStart_7323350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323352 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 1, 1, 5]
def baseStart_7323352 : Nat := 118140960795 + 7323352 * 2 ^ 59
def prefixEnd_7323352 : Nat := 4983230072969 + 3 ^ 40 * 7323352 * 2
def baseEnd_7323352 : Nat := 3760399578065336585320523

theorem tailTrace_7323352 : CollatzResearch.WordTrace tailWord_7323352 prefixEnd_7323352 3760399578065336585320523 := by
  unfold tailWord_7323352
  simp only [CollatzResearch.WordTrace]
  refine ⟨133552295482376953895546155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178069727309835938527394873 133552295482376953895546155)
  ·
    refine ⟨200328443223565430843319233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133552295482376953895546155 200328443223565430843319233)
    ·
      refine ⟨150246332417674073132489425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200328443223565430843319233 150246332417674073132489425)
      ·
        refine ⟨112684749313255554849367069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150246332417674073132489425 112684749313255554849367069)
        ·
          refine ⟨42256780992470833068512651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112684749313255554849367069 42256780992470833068512651)
          ·
            refine ⟨63385171488706249602768977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42256780992470833068512651 63385171488706249602768977)
            ·
              refine ⟨47538878616529687202076733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63385171488706249602768977 47538878616529687202076733)
              ·
                refine ⟨17827079481198632700778775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47538878616529687202076733 17827079481198632700778775)
                ·
                  refine ⟨26740619221797949051168163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17827079481198632700778775 26740619221797949051168163)
                  ·
                    refine ⟨40110928832696923576752245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26740619221797949051168163 40110928832696923576752245)
                    ·
                      refine ⟨3760399578065336585320523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40110928832696923576752245 3760399578065336585320523)
                      ·
                        rfl

theorem cell23_7323352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_7323352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323352 prefixEnd_7323352 := by exact prefixLift 7323352
  have htrace : WordTrace (prefixWord ++ tailWord_7323352) baseStart_7323352 baseEnd_7323352 := by
    simpa [prefixWord, tailWord_7323352, baseEnd_7323352] using wordTrace_append hprefix tailTrace_7323352
  have hstable : (prefixWord ++ tailWord_7323352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323352).length < 2 ^ (prefixWord ++ tailWord_7323352).sum := by decide
  have hdescent : baseEnd_7323352 < baseStart_7323352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323409 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 5, 3, 2]
def baseStart_7323409 : Nat := 118140960795 + 7323409 * 2 ^ 59
def prefixEnd_7323409 : Nat := 4983230072969 + 3 ^ 40 * 7323409 * 2
def baseEnd_7323409 : Nat := 3760428846462642862307761

theorem tailTrace_7323409 : CollatzResearch.WordTrace tailWord_7323409 prefixEnd_7323409 3760428846462642862307761 := by
  unfold tailWord_7323409
  simp only [CollatzResearch.WordTrace]
  refine ⟨267106669925547406525917281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178071113283698271017278187 267106669925547406525917281)
  ·
    refine ⟨200330002444160554894437961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267106669925547406525917281 200330002444160554894437961)
    ·
      refine ⟨150247501833120416170828471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200330002444160554894437961 150247501833120416170828471)
      ·
        refine ⟨225371252749680624256242707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150247501833120416170828471 225371252749680624256242707)
        ·
          refine ⟨338056879124520936384364061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225371252749680624256242707 338056879124520936384364061)
          ·
            refine ⟨126771329671695351144136523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338056879124520936384364061 126771329671695351144136523)
            ·
              refine ⟨190156994507543026716204785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126771329671695351144136523 190156994507543026716204785)
              ·
                refine ⟨142617745880657270037153589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190156994507543026716204785 142617745880657270037153589)
                ·
                  refine ⟨13370413676311619065983149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142617745880657270037153589 13370413676311619065983149)
                  ·
                    refine ⟨5013905128616857149743681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13370413676311619065983149 5013905128616857149743681)
                    ·
                      refine ⟨3760428846462642862307761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5013905128616857149743681 3760428846462642862307761)
                      ·
                        rfl

theorem cell23_7323409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 3, 2].length) (baseStart_7323409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323409 prefixEnd_7323409 := by exact prefixLift 7323409
  have htrace : WordTrace (prefixWord ++ tailWord_7323409) baseStart_7323409 baseEnd_7323409 := by
    simpa [prefixWord, tailWord_7323409, baseEnd_7323409] using wordTrace_append hprefix tailTrace_7323409
  have hstable : (prefixWord ++ tailWord_7323409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323409).length < 2 ^ (prefixWord ++ tailWord_7323409).sum := by decide
  have hdescent : baseEnd_7323409 < baseStart_7323409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323426 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_7323426 : Nat := 118140960795 + 7323426 * 2 ^ 59
def prefixEnd_7323426 : Nat := 4983230072969 + 3 ^ 40 * 7323426 * 2
def baseEnd_7323426 : Nat := 3760437575633769295795183

theorem tailTrace_7323426 : CollatzResearch.WordTrace tailWord_7323426 prefixEnd_7323426 3760437575633769295795183 := by
  unfold tailWord_7323426
  simp only [CollatzResearch.WordTrace]
  refine ⟨66776822491621454607321533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178071526644323878952857421 66776822491621454607321533)
  ·
    refine ⟨25041308434358045477745575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66776822491621454607321533 25041308434358045477745575)
    ·
      refine ⟨37561962651537068216618363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25041308434358045477745575 37561962651537068216618363)
      ·
        refine ⟨56342943977305602324927545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37561962651537068216618363 56342943977305602324927545)
        ·
          refine ⟨42257207982979201743695659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56342943977305602324927545 42257207982979201743695659)
          ·
            refine ⟨63385811974468802615543489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42257207982979201743695659 63385811974468802615543489)
            ·
              refine ⟨47539358980851601961657617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63385811974468802615543489 47539358980851601961657617)
              ·
                refine ⟨35654519235638701471243213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47539358980851601961657617 35654519235638701471243213)
                ·
                  refine ⟨13370444713364513051716205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35654519235638701471243213 13370444713364513051716205)
                  ·
                    refine ⟨5013916767511692394393577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13370444713364513051716205 5013916767511692394393577)
                    ·
                      refine ⟨3760437575633769295795183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5013916767511692394393577 3760437575633769295795183)
                      ·
                        rfl

theorem cell23_7323426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_7323426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323426 prefixEnd_7323426 := by exact prefixLift 7323426
  have htrace : WordTrace (prefixWord ++ tailWord_7323426) baseStart_7323426 baseEnd_7323426 := by
    simpa [prefixWord, tailWord_7323426, baseEnd_7323426] using wordTrace_append hprefix tailTrace_7323426
  have hstable : (prefixWord ++ tailWord_7323426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323426).length < 2 ^ (prefixWord ++ tailWord_7323426).sum := by decide
  have hdescent : baseEnd_7323426 < baseStart_7323426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323473 : List Nat := [1, 2, 2, 1, 5, 1, 1, 4, 2, 2, 2]
def baseStart_7323473 : Nat := 118140960795 + 7323473 * 2 ^ 59
def prefixEnd_7323473 : Nat := 4983230072969 + 3 ^ 40 * 7323473 * 2
def baseEnd_7323473 : Nat := 3760461709224530611907467

theorem tailTrace_7323473 : CollatzResearch.WordTrace tailWord_7323473 prefixEnd_7323473 3760461709224530611907467 := by
  unfold tailWord_7323473
  simp only [CollatzResearch.WordTrace]
  refine ⟨267109004197315545456247073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178072669464877030304164715 267109004197315545456247073)
  ·
    refine ⟨200331753147986659092185305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267109004197315545456247073 200331753147986659092185305)
    ·
      refine ⟨150248814860989994319138979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200331753147986659092185305 150248814860989994319138979)
      ·
        refine ⟨225373222291484991478708469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150248814860989994319138979 225373222291484991478708469)
        ·
          refine ⟨21128739589826717951128919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225373222291484991478708469 21128739589826717951128919)
          ·
            refine ⟨31693109384740076926693379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21128739589826717951128919 31693109384740076926693379)
            ·
              refine ⟨47539664077110115390040069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31693109384740076926693379 47539664077110115390040069)
              ·
                refine ⟨8913687014458146635632513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47539664077110115390040069 8913687014458146635632513)
                ·
                  refine ⟨6685265260843609976724385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8913687014458146635632513 6685265260843609976724385)
                  ·
                    refine ⟨5013948945632707482543289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6685265260843609976724385 5013948945632707482543289)
                    ·
                      refine ⟨3760461709224530611907467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5013948945632707482543289 3760461709224530611907467)
                      ·
                        rfl

theorem cell23_7323473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 2, 2].length) (baseStart_7323473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323473 prefixEnd_7323473 := by exact prefixLift 7323473
  have htrace : WordTrace (prefixWord ++ tailWord_7323473) baseStart_7323473 baseEnd_7323473 := by
    simpa [prefixWord, tailWord_7323473, baseEnd_7323473] using wordTrace_append hprefix tailTrace_7323473
  have hstable : (prefixWord ++ tailWord_7323473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323473).length < 2 ^ (prefixWord ++ tailWord_7323473).sum := by decide
  have hdescent : baseEnd_7323473 < baseStart_7323473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323489 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_7323489 : Nat := 118140960795 + 7323489 * 2 ^ 59
def prefixEnd_7323489 : Nat := 4983230072969 + 3 ^ 40 * 7323489 * 2
def baseEnd_7323489 : Nat := 3760469924915002549307393

theorem tailTrace_7323489 : CollatzResearch.WordTrace tailWord_7323489 prefixEnd_7323489 3760469924915002549307393 := by
  unfold tailWord_7323489
  simp only [CollatzResearch.WordTrace]
  refine ⟨267109587765257580188829521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178073058510171720125886347 267109587765257580188829521)
  ·
    refine ⟨200332190823943185141622141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267109587765257580188829521 200332190823943185141622141)
    ·
      refine ⟨75124571558978694428108303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200332190823943185141622141 75124571558978694428108303)
      ·
        refine ⟨112686857338468041642162455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75124571558978694428108303 112686857338468041642162455)
        ·
          refine ⟨169030286007702062463243683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112686857338468041642162455 169030286007702062463243683)
          ·
            refine ⟨253545429011553093694865525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169030286007702062463243683 253545429011553093694865525)
            ·
              refine ⟨23769883969833102533893643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253545429011553093694865525 23769883969833102533893643)
              ·
                refine ⟨35654825954749653800840465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23769883969833102533893643 35654825954749653800840465)
                ·
                  refine ⟨26741119466062240350630349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35654825954749653800840465 26741119466062240350630349)
                  ·
                    refine ⟨10027919799773340131486381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26741119466062240350630349 10027919799773340131486381)
                    ·
                      refine ⟨3760469924915002549307393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10027919799773340131486381 3760469924915002549307393)
                      ·
                        rfl

theorem cell23_7323489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_7323489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323489 prefixEnd_7323489 := by exact prefixLift 7323489
  have htrace : WordTrace (prefixWord ++ tailWord_7323489) baseStart_7323489 baseEnd_7323489 := by
    simpa [prefixWord, tailWord_7323489, baseEnd_7323489] using wordTrace_append hprefix tailTrace_7323489
  have hstable : (prefixWord ++ tailWord_7323489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323489).length < 2 ^ (prefixWord ++ tailWord_7323489).sum := by decide
  have hdescent : baseEnd_7323489 < baseStart_7323489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323490 : List Nat := [3, 3, 2, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_7323490 : Nat := 118140960795 + 7323490 * 2 ^ 59
def prefixEnd_7323490 : Nat := 4983230072969 + 3 ^ 40 * 7323490 * 2
def baseEnd_7323490 : Nat := 3760470438395657045394889

theorem tailTrace_7323490 : CollatzResearch.WordTrace tailWord_7323490 prefixEnd_7323490 3760470438395657045394889 := by
  unfold tailWord_7323490
  simp only [CollatzResearch.WordTrace]
  refine ⟨66777406059563489339903981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178073082825502638239743949 66777406059563489339903981)
  ·
    refine ⟨25041527272336308502463993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66777406059563489339903981 25041527272336308502463993)
    ·
      refine ⟨18781145454252231376847995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25041527272336308502463993 18781145454252231376847995)
      ·
        refine ⟨28171718181378347065271993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18781145454252231376847995 28171718181378347065271993)
        ·
          refine ⟨21128788636033760298953995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28171718181378347065271993 21128788636033760298953995)
          ·
            refine ⟨31693182954050640448430993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21128788636033760298953995 31693182954050640448430993)
            ·
              refine ⟨23769887215537980336323245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31693182954050640448430993 23769887215537980336323245)
              ·
                refine ⟨8913707705826742626121217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23769887215537980336323245 8913707705826742626121217)
                ·
                  refine ⟨6685280779370056969590913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8913707705826742626121217 6685280779370056969590913)
                  ·
                    refine ⟨5013960584527542727193185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6685280779370056969590913 5013960584527542727193185)
                    ·
                      refine ⟨3760470438395657045394889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5013960584527542727193185 3760470438395657045394889)
                      ·
                        rfl

theorem cell23_7323490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_7323490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323490 prefixEnd_7323490 := by exact prefixLift 7323490
  have htrace : WordTrace (prefixWord ++ tailWord_7323490) baseStart_7323490 baseEnd_7323490 := by
    simpa [prefixWord, tailWord_7323490, baseEnd_7323490] using wordTrace_append hprefix tailTrace_7323490
  have hstable : (prefixWord ++ tailWord_7323490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323490).length < 2 ^ (prefixWord ++ tailWord_7323490).sum := by decide
  have hdescent : baseEnd_7323490 < baseStart_7323490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323499 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 4, 5, 2]
def baseStart_7323499 : Nat := 118140960795 + 7323499 * 2 ^ 59
def prefixEnd_7323499 : Nat := 4983230072969 + 3 ^ 40 * 7323499 * 2
def baseEnd_7323499 : Nat := 3760475059721547510182347

theorem tailTrace_7323499 : CollatzResearch.WordTrace tailWord_7323499 prefixEnd_7323499 3760475059721547510182347 := by
  unfold tailWord_7323499
  simp only [CollatzResearch.WordTrace]
  refine ⟨267109952495221351896693551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178073301663480901264462367 267109952495221351896693551)
  ·
    refine ⟨400664928742832027845040327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267109952495221351896693551 400664928742832027845040327)
    ·
      refine ⟨600997393114248041767560491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400664928742832027845040327 600997393114248041767560491)
      ·
        refine ⟨901496089671372062651340737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600997393114248041767560491 901496089671372062651340737)
        ·
          refine ⟨676122067253529046988505553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 901496089671372062651340737 676122067253529046988505553)
          ·
            refine ⟨507091550440146785241379165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 676122067253529046988505553 507091550440146785241379165)
            ·
              refine ⟨190159331415055044465517187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507091550440146785241379165 190159331415055044465517187)
              ·
                refine ⟨285238997122582566698275781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190159331415055044465517187 285238997122582566698275781)
                ·
                  refine ⟨53482311960484231255926709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285238997122582566698275781 53482311960484231255926709)
                  ·
                    refine ⟨5013966746295396680243129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53482311960484231255926709 5013966746295396680243129)
                    ·
                      refine ⟨3760475059721547510182347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5013966746295396680243129 3760475059721547510182347)
                      ·
                        rfl

theorem cell23_7323499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 5, 2].length) (baseStart_7323499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323499 prefixEnd_7323499 := by exact prefixLift 7323499
  have htrace : WordTrace (prefixWord ++ tailWord_7323499) baseStart_7323499 baseEnd_7323499 := by
    simpa [prefixWord, tailWord_7323499, baseEnd_7323499] using wordTrace_append hprefix tailTrace_7323499
  have hstable : (prefixWord ++ tailWord_7323499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323499).length < 2 ^ (prefixWord ++ tailWord_7323499).sum := by decide
  have hdescent : baseEnd_7323499 < baseStart_7323499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323509 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 1, 7]
def baseStart_7323509 : Nat := 118140960795 + 7323509 * 2 ^ 59
def prefixEnd_7323509 : Nat := 4983230072969 + 3 ^ 40 * 7323509 * 2
def baseEnd_7323509 : Nat := 1253493398176030823685767

theorem tailTrace_7323509 : CollatzResearch.WordTrace tailWord_7323509 prefixEnd_7323509 1253493398176030823685767 := by
  unfold tailWord_7323509
  simp only [CollatzResearch.WordTrace]
  refine ⟨267110317225185123604557581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178073544816790082403038387 267110317225185123604557581)
  ·
    refine ⟨100166368959444421351709093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267110317225185123604557581 100166368959444421351709093)
    ·
      refine ⟨18781194179895829003445455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100166368959444421351709093 18781194179895829003445455)
      ·
        refine ⟨28171791269843743505168183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18781194179895829003445455 28171791269843743505168183)
        ·
          refine ⟨42257686904765615257752275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28171791269843743505168183 42257686904765615257752275)
          ·
            refine ⟨63386530357148422886628413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42257686904765615257752275 63386530357148422886628413)
            ·
              refine ⟨23769948883930658582485655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63386530357148422886628413 23769948883930658582485655)
              ·
                refine ⟨35654923325895987873728483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23769948883930658582485655 35654923325895987873728483)
                ·
                  refine ⟨53482384988843981810592725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35654923325895987873728483 53482384988843981810592725)
                  ·
                    refine ⟨1253493398176030823685767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53482384988843981810592725 1253493398176030823685767)
                    ·
                      rfl

theorem cell23_7323509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_7323509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323509 prefixEnd_7323509 := by exact prefixLift 7323509
  have htrace : WordTrace (prefixWord ++ tailWord_7323509) baseStart_7323509 baseEnd_7323509 := by
    simpa [prefixWord, tailWord_7323509, baseEnd_7323509] using wordTrace_append hprefix tailTrace_7323509
  have hstable : (prefixWord ++ tailWord_7323509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323509).length < 2 ^ (prefixWord ++ tailWord_7323509).sum := by decide
  have hdescent : baseEnd_7323509 < baseStart_7323509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323529 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 4, 1, 4]
def baseStart_7323529 : Nat := 118140960795 + 7323529 * 2 ^ 59
def prefixEnd_7323529 : Nat := 4983230072969 + 3 ^ 40 * 7323529 * 2
def baseEnd_7323529 : Nat := 3760490464141182392807209

theorem tailTrace_7323529 : CollatzResearch.WordTrace tailWord_7323529 prefixEnd_7323529 3760490464141182392807209 := by
  unfold tailWord_7323529
  simp only [CollatzResearch.WordTrace]
  refine ⟨267111046685112667020285641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178074031123408444680190427 267111046685112667020285641)
  ·
    refine ⟨200333285013834500265214231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267111046685112667020285641 200333285013834500265214231)
    ·
      refine ⟨300499927520751750397821347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200333285013834500265214231 300499927520751750397821347)
      ·
        refine ⟨450749891281127625596732021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300499927520751750397821347 450749891281127625596732021)
        ·
          refine ⟨42257802307605714899693627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 450749891281127625596732021 42257802307605714899693627)
          ·
            refine ⟨63386703461408572349540441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42257802307605714899693627 63386703461408572349540441)
            ·
              refine ⟨47540027596056429262155331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63386703461408572349540441 47540027596056429262155331)
              ·
                refine ⟨71310041394084643893232997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47540027596056429262155331 71310041394084643893232997)
                ·
                  refine ⟨13370632761390870729981187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71310041394084643893232997 13370632761390870729981187)
                  ·
                    refine ⟨20055949142086306094971781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13370632761390870729981187 20055949142086306094971781)
                    ·
                      refine ⟨3760490464141182392807209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20055949142086306094971781 3760490464141182392807209)
                      ·
                        rfl

theorem cell23_7323529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_7323529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323529 prefixEnd_7323529 := by exact prefixLift 7323529
  have htrace : WordTrace (prefixWord ++ tailWord_7323529) baseStart_7323529 baseEnd_7323529 := by
    simpa [prefixWord, tailWord_7323529, baseEnd_7323529] using wordTrace_append hprefix tailTrace_7323529
  have hstable : (prefixWord ++ tailWord_7323529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323529).length < 2 ^ (prefixWord ++ tailWord_7323529).sum := by decide
  have hdescent : baseEnd_7323529 < baseStart_7323529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323556 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_7323556 : Nat := 118140960795 + 7323556 * 2 ^ 59
def prefixEnd_7323556 : Nat := 4983230072969 + 3 ^ 40 * 7323556 * 2
def baseEnd_7323556 : Nat := 1253501442706284595723195

theorem tailTrace_7323556 : CollatzResearch.WordTrace tailWord_7323556 prefixEnd_7323556 1253501442706284595723195 := by
  unfold tailWord_7323556
  simp only [CollatzResearch.WordTrace]
  refine ⟨133556015728007425315759261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178074687637343233754345681 133556015728007425315759261)
  ·
    refine ⟨50083505898002784493409723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133556015728007425315759261 50083505898002784493409723)
    ·
      refine ⟨75125258847004176740114585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50083505898002784493409723 75125258847004176740114585)
      ·
        refine ⟨56343944135253132555085939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75125258847004176740114585 56343944135253132555085939)
        ·
          refine ⟨84515916202879698832628909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56343944135253132555085939 84515916202879698832628909)
          ·
            refine ⟨31693468576079887062235841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84515916202879698832628909 31693468576079887062235841)
            ·
              refine ⟨23770101432059915296676881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31693468576079887062235841 23770101432059915296676881)
              ·
                refine ⟨17827576074044936472507661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23770101432059915296676881 17827576074044936472507661)
                ·
                  refine ⟨6685341027766851177190373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17827576074044936472507661 6685341027766851177190373)
                  ·
                    refine ⟨1253501442706284595723195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6685341027766851177190373 1253501442706284595723195)
                    ·
                      rfl

theorem cell23_7323556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_7323556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323556 prefixEnd_7323556 := by exact prefixLift 7323556
  have htrace : WordTrace (prefixWord ++ tailWord_7323556) baseStart_7323556 baseEnd_7323556 := by
    simpa [prefixWord, tailWord_7323556, baseEnd_7323556] using wordTrace_append hprefix tailTrace_7323556
  have hstable : (prefixWord ++ tailWord_7323556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323556).length < 2 ^ (prefixWord ++ tailWord_7323556).sum := by decide
  have hdescent : baseEnd_7323556 < baseStart_7323556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323569 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 8]
def baseStart_7323569 : Nat := 118140960795 + 7323569 * 2 ^ 59
def prefixEnd_7323569 : Nat := 4983230072969 + 3 ^ 40 * 7323569 * 2
def baseEnd_7323569 : Nat := 417834555929706915145225

theorem tailTrace_7323569 : CollatzResearch.WordTrace tailWord_7323569 prefixEnd_7323569 417834555929706915145225 := by
  unfold tailWord_7323569
  simp only [CollatzResearch.WordTrace]
  refine ⟨267112505604967753851741761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178075003736645169234494507 267112505604967753851741761)
  ·
    refine ⟨200334379203725815388806321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267112505604967753851741761 200334379203725815388806321)
    ·
      refine ⟨150250784402794361541604741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200334379203725815388806321 150250784402794361541604741)
      ·
        refine ⟨28172022075523942789050889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150250784402794361541604741 28172022075523942789050889)
        ·
          refine ⟨21129016556642957091788167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28172022075523942789050889 21129016556642957091788167)
          ·
            refine ⟨31693524834964435637682251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21129016556642957091788167 31693524834964435637682251)
            ·
              refine ⟨47540287252446653456523377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31693524834964435637682251 47540287252446653456523377)
              ·
                refine ⟨35655215439334990092392533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47540287252446653456523377 35655215439334990092392533)
                ·
                  refine ⟨417834555929706915145225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35655215439334990092392533 417834555929706915145225)
                  ·
                    rfl

theorem cell23_7323569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 8].length) (baseStart_7323569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323569 prefixEnd_7323569 := by exact prefixLift 7323569
  have htrace : WordTrace (prefixWord ++ tailWord_7323569) baseStart_7323569 baseEnd_7323569 := by
    simpa [prefixWord, tailWord_7323569, baseEnd_7323569] using wordTrace_append hprefix tailTrace_7323569
  have hstable : (prefixWord ++ tailWord_7323569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323569).length < 2 ^ (prefixWord ++ tailWord_7323569).sum := by decide
  have hdescent : baseEnd_7323569 < baseStart_7323569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323599 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 3, 5]
def baseStart_7323599 : Nat := 118140960795 + 7323599 * 2 ^ 59
def prefixEnd_7323599 : Nat := 4983230072969 + 3 ^ 40 * 7323599 * 2
def baseEnd_7323599 : Nat := 1253508802595665706310629

theorem tailTrace_7323599 : CollatzResearch.WordTrace tailWord_7323599 prefixEnd_7323599 1253508802595665706310629 := by
  unfold tailWord_7323599
  simp only [CollatzResearch.WordTrace]
  refine ⟨267113599794859068975333851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178075733196572712650222567 267113599794859068975333851)
  ·
    refine ⟨400670399692288603463000777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267113599794859068975333851 400670399692288603463000777)
    ·
      refine ⟨300502799769216452597250583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400670399692288603463000777 300502799769216452597250583)
      ·
        refine ⟨450754199653824678895875875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300502799769216452597250583 450754199653824678895875875)
        ·
          refine ⟨676131299480737018343813813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450754199653824678895875875 676131299480737018343813813)
          ·
            refine ⟨63387309326319095469732545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 676131299480737018343813813 63387309326319095469732545)
            ·
              refine ⟨47540481994739321602299409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63387309326319095469732545 47540481994739321602299409)
              ·
                refine ⟨35655361496054491201724557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47540481994739321602299409 35655361496054491201724557)
                ·
                  refine ⟨13370760561020434200646709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35655361496054491201724557 13370760561020434200646709)
                  ·
                    refine ⟨1253508802595665706310629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13370760561020434200646709 1253508802595665706310629)
                    ·
                      rfl

theorem cell23_7323599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 5].length) (baseStart_7323599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323599 prefixEnd_7323599 := by exact prefixLift 7323599
  have htrace : WordTrace (prefixWord ++ tailWord_7323599) baseStart_7323599 baseEnd_7323599 := by
    simpa [prefixWord, tailWord_7323599, baseEnd_7323599] using wordTrace_append hprefix tailTrace_7323599
  have hstable : (prefixWord ++ tailWord_7323599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323599).length < 2 ^ (prefixWord ++ tailWord_7323599).sum := by decide
  have hdescent : baseEnd_7323599 < baseStart_7323599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323656 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_7323656 : Nat := 118140960795 + 7323656 * 2 ^ 59
def prefixEnd_7323656 : Nat := 4983230072969 + 3 ^ 40 * 7323656 * 2
def baseEnd_7323656 : Nat := 3760555676184303395919125

theorem tailTrace_7323656 : CollatzResearch.WordTrace tailWord_7323656 prefixEnd_7323656 3760555676184303395919125 := by
  unfold tailWord_7323656
  simp only [CollatzResearch.WordTrace]
  refine ⟨133557839377826283855079411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178077119170435045140105881 133557839377826283855079411)
  ·
    refine ⟨200336759066739425782619117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133557839377826283855079411 200336759066739425782619117)
    ·
      refine ⟨75126284650027284668482169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200336759066739425782619117 75126284650027284668482169)
      ·
        refine ⟨56344713487520463501361627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75126284650027284668482169 56344713487520463501361627)
        ·
          refine ⟨84517070231280695252042441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56344713487520463501361627 84517070231280695252042441)
          ·
            refine ⟨63387802673460521439031831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84517070231280695252042441 63387802673460521439031831)
            ·
              refine ⟨95081704010190782158547747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63387802673460521439031831 95081704010190782158547747)
              ·
                refine ⟨142622556015286173237821621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95081704010190782158547747 142622556015286173237821621)
                ·
                  refine ⟨13370864626433078741045777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142622556015286173237821621 13370864626433078741045777)
                  ·
                    refine ⟨10028148469824809055784333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13370864626433078741045777 10028148469824809055784333)
                    ·
                      refine ⟨3760555676184303395919125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10028148469824809055784333 3760555676184303395919125)
                      ·
                        rfl

theorem cell23_7323656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_7323656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323656 prefixEnd_7323656 := by exact prefixLift 7323656
  have htrace : WordTrace (prefixWord ++ tailWord_7323656) baseStart_7323656 baseEnd_7323656 := by
    simpa [prefixWord, tailWord_7323656, baseEnd_7323656] using wordTrace_append hprefix tailTrace_7323656
  have hstable : (prefixWord ++ tailWord_7323656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323656).length < 2 ^ (prefixWord ++ tailWord_7323656).sum := by decide
  have hdescent : baseEnd_7323656 < baseStart_7323656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323690 : List Nat := [3, 1, 4, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_7323690 : Nat := 118140960795 + 7323690 * 2 ^ 59
def prefixEnd_7323690 : Nat := 4983230072969 + 3 ^ 40 * 7323690 * 2
def baseEnd_7323690 : Nat := 3760573134526556262893969

theorem tailTrace_7323690 : CollatzResearch.WordTrace tailWord_7323690 prefixEnd_7323690 3760573134526556262893969 := by
  unfold tailWord_7323690
  simp only [CollatzResearch.WordTrace]
  refine ⟨66779229709382347879224131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178077945891686261011264349 66779229709382347879224131)
  ·
    refine ⟨100168844564073521818836197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66779229709382347879224131 100168844564073521818836197)
    ·
      refine ⟨18781658355763785341031787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100168844564073521818836197 18781658355763785341031787)
      ·
        refine ⟨28172487533645678011547681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18781658355763785341031787 28172487533645678011547681)
        ·
          refine ⟨21129365650234258508660761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28172487533645678011547681 21129365650234258508660761)
          ·
            refine ⟨15847024237675693881495571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21129365650234258508660761 15847024237675693881495571)
            ·
              refine ⟨23770536356513540822243357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15847024237675693881495571 23770536356513540822243357)
              ·
                refine ⟨8913951133692577808341259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23770536356513540822243357 8913951133692577808341259)
                ·
                  refine ⟨13370926700538866712511889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8913951133692577808341259 13370926700538866712511889)
                  ·
                    refine ⟨10028195025404150034383917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13370926700538866712511889 10028195025404150034383917)
                    ·
                      refine ⟨3760573134526556262893969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10028195025404150034383917 3760573134526556262893969)
                      ·
                        rfl

theorem cell23_7323690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_7323690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323690 prefixEnd_7323690 := by exact prefixLift 7323690
  have htrace : WordTrace (prefixWord ++ tailWord_7323690) baseStart_7323690 baseEnd_7323690 := by
    simpa [prefixWord, tailWord_7323690, baseEnd_7323690] using wordTrace_append hprefix tailTrace_7323690
  have hstable : (prefixWord ++ tailWord_7323690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323690).length < 2 ^ (prefixWord ++ tailWord_7323690).sum := by decide
  have hdescent : baseEnd_7323690 < baseStart_7323690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323760 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 4, 2, 2]
def baseStart_7323760 : Nat := 118140960795 + 7323760 * 2 ^ 59
def prefixEnd_7323760 : Nat := 4983230072969 + 3 ^ 40 * 7323760 * 2
def baseEnd_7323760 : Nat := 3760609078172370989018647

theorem tailTrace_7323760 : CollatzResearch.WordTrace tailWord_7323760 prefixEnd_7323760 3760609078172370989018647 := by
  unfold tailWord_7323760
  simp only [CollatzResearch.WordTrace]
  refine ⟨133559735973637896735972367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178079647964850528981296489 133559735973637896735972367)
  ·
    refine ⟨200339603960456845103958551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133559735973637896735972367 200339603960456845103958551)
    ·
      refine ⟨300509405940685267655937827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200339603960456845103958551 300509405940685267655937827)
      ·
        refine ⟨450764108911027901483906741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300509405940685267655937827 450764108911027901483906741)
        ·
          refine ⟨42259135210408865764116257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 450764108911027901483906741 42259135210408865764116257)
          ·
            refine ⟨31694351407806649323087193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42259135210408865764116257 31694351407806649323087193)
            ·
              refine ⟨23770763555854986992315395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31694351407806649323087193 23770763555854986992315395)
              ·
                refine ⟨35656145333782480488473093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23770763555854986992315395 35656145333782480488473093)
                ·
                  refine ⟨6685527250084215091588705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35656145333782480488473093 6685527250084215091588705)
                  ·
                    refine ⟨5014145437563161318691529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6685527250084215091588705 5014145437563161318691529)
                    ·
                      refine ⟨3760609078172370989018647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5014145437563161318691529 3760609078172370989018647)
                      ·
                        rfl

theorem cell23_7323760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 4, 2, 2].length) (baseStart_7323760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323760 prefixEnd_7323760 := by exact prefixLift 7323760
  have htrace : WordTrace (prefixWord ++ tailWord_7323760) baseStart_7323760 baseEnd_7323760 := by
    simpa [prefixWord, tailWord_7323760, baseEnd_7323760] using wordTrace_append hprefix tailTrace_7323760
  have hstable : (prefixWord ++ tailWord_7323760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323760).length < 2 ^ (prefixWord ++ tailWord_7323760).sum := by decide
  have hdescent : baseEnd_7323760 < baseStart_7323760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323776 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 3]
def baseStart_7323776 : Nat := 118140960795 + 7323776 * 2 ^ 59
def prefixEnd_7323776 : Nat := 4983230072969 + 3 ^ 40 * 7323776 * 2
def baseEnd_7323776 : Nat := 3760617293862842926418573

theorem tailTrace_7323776 : CollatzResearch.WordTrace tailWord_7323776 prefixEnd_7323776 3760617293862842926418573 := by
  unfold tailWord_7323776
  simp only [CollatzResearch.WordTrace]
  refine ⟨133560027757608914102263591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178080037010145218803018121 133560027757608914102263591)
  ·
    refine ⟨200340041636413371153395387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133560027757608914102263591 200340041636413371153395387)
    ·
      refine ⟨300510062454620056730093081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200340041636413371153395387 300510062454620056730093081)
      ·
        refine ⟨225382546840965042547569811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300510062454620056730093081 225382546840965042547569811)
        ·
          refine ⟨338073820261447563821354717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225382546840965042547569811 338073820261447563821354717)
          ·
            refine ⟨126777682598042836433008019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338073820261447563821354717 126777682598042836433008019)
            ·
              refine ⟨190166523897064254649512029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126777682598042836433008019 190166523897064254649512029)
              ·
                refine ⟨71312446461399095493567011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190166523897064254649512029 71312446461399095493567011)
                ·
                  refine ⟨106968669692098643240350517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71312446461399095493567011 106968669692098643240350517)
                  ·
                    refine ⟨10028312783634247803782861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106968669692098643240350517 10028312783634247803782861)
                    ·
                      refine ⟨3760617293862842926418573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10028312783634247803782861 3760617293862842926418573)
                      ·
                        rfl

theorem cell23_7323776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_7323776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323776 prefixEnd_7323776 := by exact prefixLift 7323776
  have htrace : WordTrace (prefixWord ++ tailWord_7323776) baseStart_7323776 baseEnd_7323776 := by
    simpa [prefixWord, tailWord_7323776, baseEnd_7323776] using wordTrace_append hprefix tailTrace_7323776
  have hstable : (prefixWord ++ tailWord_7323776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323776).length < 2 ^ (prefixWord ++ tailWord_7323776).sum := by decide
  have hdescent : baseEnd_7323776 < baseStart_7323776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323877 : List Nat := [1, 3, 1, 4, 2, 1, 2, 4, 1, 4]
def baseStart_7323877 : Nat := 118140960795 + 7323877 * 2 ^ 59
def prefixEnd_7323877 : Nat := 4983230072969 + 3 ^ 40 * 7323877 * 2
def baseEnd_7323877 : Nat := 1253556385136315677085203

theorem tailTrace_7323877 : CollatzResearch.WordTrace tailWord_7323877 prefixEnd_7323877 1253556385136315677085203 := by
  unfold tailWord_7323877
  simp only [CollatzResearch.WordTrace]
  refine ⟨267123739287851922453953885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178082492858567948302635923 267123739287851922453953885)
  ·
    refine ⟨100171402232944470920232707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267123739287851922453953885 100171402232944470920232707)
    ·
      refine ⟨150257103349416706380349061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100171402232944470920232707 150257103349416706380349061)
      ·
        refine ⟨28173206878015632446315449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150257103349416706380349061 28173206878015632446315449)
        ·
          refine ⟨21129905158511724334736587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28173206878015632446315449 21129905158511724334736587)
          ·
            refine ⟨31694857737767586502104881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21129905158511724334736587 31694857737767586502104881)
            ·
              refine ⟨23771143303325689876578661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31694857737767586502104881 23771143303325689876578661)
              ·
                refine ⟨4457089369373566851858499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23771143303325689876578661 4457089369373566851858499)
                ·
                  refine ⟨6685634054060350277787749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4457089369373566851858499 6685634054060350277787749)
                  ·
                    refine ⟨1253556385136315677085203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6685634054060350277787749 1253556385136315677085203)
                    ·
                      rfl

theorem cell23_7323877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_7323877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323877 prefixEnd_7323877 := by exact prefixLift 7323877
  have htrace : WordTrace (prefixWord ++ tailWord_7323877) baseStart_7323877 baseEnd_7323877 := by
    simpa [prefixWord, tailWord_7323877, baseEnd_7323877] using wordTrace_append hprefix tailTrace_7323877
  have hstable : (prefixWord ++ tailWord_7323877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323877).length < 2 ^ (prefixWord ++ tailWord_7323877).sum := by decide
  have hdescent : baseEnd_7323877 < baseStart_7323877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323896 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_7323896 : Nat := 118140960795 + 7323896 * 2 ^ 59
def prefixEnd_7323896 : Nat := 4983230072969 + 3 ^ 40 * 7323896 * 2
def baseEnd_7323896 : Nat := 3760678911541382456918021

theorem tailTrace_7323896 : CollatzResearch.WordTrace tailWord_7323896 prefixEnd_7323896 3760678911541382456918021 := by
  unfold tailWord_7323896
  simp only [CollatzResearch.WordTrace]
  refine ⟨133562216137391544349447771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178082954849855392465930361 133562216137391544349447771)
  ·
    refine ⟨200343324206087316524171657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133562216137391544349447771 200343324206087316524171657)
    ·
      refine ⟨150257493154565487393128743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200343324206087316524171657 150257493154565487393128743)
      ·
        refine ⟨225386239731848231089693115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150257493154565487393128743 225386239731848231089693115)
        ·
          refine ⟨338079359597772346634539673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225386239731848231089693115 338079359597772346634539673)
          ·
            refine ⟨253559519698329259975904755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338079359597772346634539673 253559519698329259975904755)
            ·
              refine ⟨380339279547493889963857133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253559519698329259975904755 380339279547493889963857133)
              ·
                refine ⟨142627229830310208736446425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380339279547493889963857133 142627229830310208736446425)
                ·
                  refine ⟨106970422372732656552334819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142627229830310208736446425 106970422372732656552334819)
                  ·
                    refine ⟨160455633559098984828502229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106970422372732656552334819 160455633559098984828502229)
                    ·
                      refine ⟨3760678911541382456918021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160455633559098984828502229 3760678911541382456918021)
                      ·
                        rfl

theorem cell23_7323896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_7323896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323896 prefixEnd_7323896 := by exact prefixLift 7323896
  have htrace : WordTrace (prefixWord ++ tailWord_7323896) baseStart_7323896 baseEnd_7323896 := by
    simpa [prefixWord, tailWord_7323896, baseEnd_7323896] using wordTrace_append hprefix tailTrace_7323896
  have hstable : (prefixWord ++ tailWord_7323896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323896).length < 2 ^ (prefixWord ++ tailWord_7323896).sum := by decide
  have hdescent : baseEnd_7323896 < baseStart_7323896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323911 : List Nat := [1, 1, 4, 5, 1, 2, 1, 3, 1, 4]
def baseStart_7323911 : Nat := 118140960795 + 7323911 * 2 ^ 59
def prefixEnd_7323911 : Nat := 4983230072969 + 3 ^ 40 * 7323911 * 2
def baseEnd_7323911 : Nat := 1253562204583733299410151

theorem tailTrace_7323911 : CollatzResearch.WordTrace tailWord_7323911 prefixEnd_7323911 1253562204583733299410151 := by
  unfold tailWord_7323911
  simp only [CollatzResearch.WordTrace]
  refine ⟨267124979369728746260691587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178083319579819164173794391 267124979369728746260691587)
  ·
    refine ⟨400687469054593119391037381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267124979369728746260691587 400687469054593119391037381)
    ·
      refine ⟨75128900447736209885819509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400687469054593119391037381 75128900447736209885819509)
      ·
        refine ⟨7043334416975269676795579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75128900447736209885819509 7043334416975269676795579)
        ·
          refine ⟨10565001625462904515193369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7043334416975269676795579 10565001625462904515193369)
          ·
            refine ⟨7923751219097178386395027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10565001625462904515193369 7923751219097178386395027)
            ·
              refine ⟨11885626828645767579592541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7923751219097178386395027 11885626828645767579592541)
              ·
                refine ⟨4457110060742162842347203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11885626828645767579592541 4457110060742162842347203)
                ·
                  refine ⟨6685665091113244263520805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4457110060742162842347203 6685665091113244263520805)
                  ·
                    refine ⟨1253562204583733299410151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6685665091113244263520805 1253562204583733299410151)
                    ·
                      rfl

theorem cell23_7323911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_7323911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323911 prefixEnd_7323911 := by exact prefixLift 7323911
  have htrace : WordTrace (prefixWord ++ tailWord_7323911) baseStart_7323911 baseEnd_7323911 := by
    simpa [prefixWord, tailWord_7323911, baseEnd_7323911] using wordTrace_append hprefix tailTrace_7323911
  have hstable : (prefixWord ++ tailWord_7323911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323911).length < 2 ^ (prefixWord ++ tailWord_7323911).sum := by decide
  have hdescent : baseEnd_7323911 < baseStart_7323911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323927 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 2, 3, 2]
def baseStart_7323927 : Nat := 118140960795 + 7323927 * 2 ^ 59
def prefixEnd_7323927 : Nat := 4983230072969 + 3 ^ 40 * 7323927 * 2
def baseEnd_7323927 : Nat := 3760694829441671835630379

theorem tailTrace_7323927 : CollatzResearch.WordTrace tailWord_7323927 prefixEnd_7323927 3760694829441671835630379 := by
  unfold tailWord_7323927
  simp only [CollatzResearch.WordTrace]
  refine ⟨267125562937670780993274035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178083708625113853995516023 267125562937670780993274035)
  ·
    refine ⟨400688344406506171489911053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267125562937670780993274035 400688344406506171489911053)
    ·
      refine ⟨150258129152439814308716645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400688344406506171489911053 150258129152439814308716645)
      ·
        refine ⟨28173399216082465182884371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150258129152439814308716645 28173399216082465182884371)
        ·
          refine ⟨42260098824123697774326557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28173399216082465182884371 42260098824123697774326557)
          ·
            refine ⟨15847537059046386665372459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42260098824123697774326557 15847537059046386665372459)
            ·
              refine ⟨23771305588569579998058689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15847537059046386665372459 23771305588569579998058689)
              ·
                refine ⟨17828479191427184998544017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23771305588569579998058689 17828479191427184998544017)
                ·
                  refine ⟨13371359393570388748908013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17828479191427184998544017 13371359393570388748908013)
                  ·
                    refine ⟨5014259772588895780840505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13371359393570388748908013 5014259772588895780840505)
                    ·
                      refine ⟨3760694829441671835630379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5014259772588895780840505 3760694829441671835630379)
                      ·
                        rfl

theorem cell23_7323927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_7323927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323927 prefixEnd_7323927 := by exact prefixLift 7323927
  have htrace : WordTrace (prefixWord ++ tailWord_7323927) baseStart_7323927 baseEnd_7323927 := by
    simpa [prefixWord, tailWord_7323927, baseEnd_7323927] using wordTrace_append hprefix tailTrace_7323927
  have hstable : (prefixWord ++ tailWord_7323927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323927).length < 2 ^ (prefixWord ++ tailWord_7323927).sum := by decide
  have hdescent : baseEnd_7323927 < baseStart_7323927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323954 : List Nat := [3, 2, 1, 1, 6, 1, 1, 2, 1, 5]
def baseStart_7323954 : Nat := 118140960795 + 7323954 * 2 ^ 59
def prefixEnd_7323954 : Nat := 4983230072969 + 3 ^ 40 * 7323954 * 2
def baseEnd_7323954 : Nat := 1253569564473114409997585

theorem tailTrace_7323954 : CollatzResearch.WordTrace tailWord_7323954 prefixEnd_7323954 1253569564473114409997585 := by
  unfold tailWord_7323954
  simp only [CollatzResearch.WordTrace]
  refine ⟨66781636927143241151126729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178084365139048643069671277 66781636927143241151126729)
  ·
    refine ⟨50086227695357430863345047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66781636927143241151126729 50086227695357430863345047)
    ·
      refine ⟨75129341543036146295017571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50086227695357430863345047 75129341543036146295017571)
      ·
        refine ⟨112694012314554219442526357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75129341543036146295017571 112694012314554219442526357)
        ·
          refine ⟨5282531827244729036368423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112694012314554219442526357 5282531827244729036368423)
          ·
            refine ⟨7923797740867093554552635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5282531827244729036368423 7923797740867093554552635)
            ·
              refine ⟨11885696611300640331828953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7923797740867093554552635 11885696611300640331828953)
              ·
                refine ⟨8914272458475480248871715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11885696611300640331828953 8914272458475480248871715)
                ·
                  refine ⟨13371408687713220373307573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8914272458475480248871715 13371408687713220373307573)
                  ·
                    refine ⟨1253569564473114409997585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13371408687713220373307573 1253569564473114409997585)
                    ·
                      rfl

theorem cell23_7323954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_7323954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323954 prefixEnd_7323954 := by exact prefixLift 7323954
  have htrace : WordTrace (prefixWord ++ tailWord_7323954) baseStart_7323954 baseEnd_7323954 := by
    simpa [prefixWord, tailWord_7323954, baseEnd_7323954] using wordTrace_append hprefix tailTrace_7323954
  have hstable : (prefixWord ++ tailWord_7323954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323954).length < 2 ^ (prefixWord ++ tailWord_7323954).sum := by decide
  have hdescent : baseEnd_7323954 < baseStart_7323954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7323957 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_7323957 : Nat := 118140960795 + 7323957 * 2 ^ 59
def prefixEnd_7323957 : Nat := 4983230072969 + 3 ^ 40 * 7323957 * 2
def baseEnd_7323957 : Nat := 3760710233861306718255241

theorem tailTrace_7323957 : CollatzResearch.WordTrace tailWord_7323957 prefixEnd_7323957 3760710233861306718255241 := by
  unfold tailWord_7323957
  simp only [CollatzResearch.WordTrace]
  refine ⟨267126657127562096116866125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178084438085041397411244083 267126657127562096116866125)
  ·
    refine ⟨100172496422835786043824797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267126657127562096116866125 100172496422835786043824797)
    ·
      refine ⟨37564686158563419766434299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100172496422835786043824797 37564686158563419766434299)
      ·
        refine ⟨56347029237845129649651449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37564686158563419766434299 56347029237845129649651449)
        ·
          refine ⟨42260271928383847237238587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56347029237845129649651449 42260271928383847237238587)
          ·
            refine ⟨63390407892575770855857881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42260271928383847237238587 63390407892575770855857881)
            ·
              refine ⟨47542805919431828141893411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63390407892575770855857881 47542805919431828141893411)
              ·
                refine ⟨71314208879147742212840117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47542805919431828141893411 71314208879147742212840117)
                ·
                  refine ⟨6685707082420100832453761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71314208879147742212840117 6685707082420100832453761)
                  ·
                    refine ⟨5014280311815075624340321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6685707082420100832453761 5014280311815075624340321)
                    ·
                      refine ⟨3760710233861306718255241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5014280311815075624340321 3760710233861306718255241)
                      ·
                        rfl

theorem cell23_7323957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_7323957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7323957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7323957 prefixEnd_7323957 := by exact prefixLift 7323957
  have htrace : WordTrace (prefixWord ++ tailWord_7323957) baseStart_7323957 baseEnd_7323957 := by
    simpa [prefixWord, tailWord_7323957, baseEnd_7323957] using wordTrace_append hprefix tailTrace_7323957
  have hstable : (prefixWord ++ tailWord_7323957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7323957).length < 2 ^ (prefixWord ++ tailWord_7323957).sum := by decide
  have hdescent : baseEnd_7323957 < baseStart_7323957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7323957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324007 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_7324007 : Nat := 118140960795 + 7324007 * 2 ^ 59
def prefixEnd_7324007 : Nat := 4983230072969 + 3 ^ 40 * 7324007 * 2
def baseEnd_7324007 : Nat := 3760735907894031522630011

theorem tailTrace_7324007 : CollatzResearch.WordTrace tailWord_7324007 prefixEnd_7324007 3760735907894031522630011 := by
  unfold tailWord_7324007
  simp only [CollatzResearch.WordTrace]
  refine ⟨267128480777380954656186275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178085653851587303104124183 267128480777380954656186275)
  ·
    refine ⟨400692721166071431984279413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267128480777380954656186275 400692721166071431984279413)
    ·
      refine ⟨37564942609319196748526195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 400692721166071431984279413 37564942609319196748526195)
      ·
        refine ⟨56347413913978795122789293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37564942609319196748526195 56347413913978795122789293)
        ·
          refine ⟨21130280217742048171045985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56347413913978795122789293 21130280217742048171045985)
          ·
            refine ⟨15847710163306536128284489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21130280217742048171045985 15847710163306536128284489)
            ·
              refine ⟨11885782622479902096213367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15847710163306536128284489 11885782622479902096213367)
              ·
                refine ⟨17828673933719853144320051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11885782622479902096213367 17828673933719853144320051)
                ·
                  refine ⟨26743010900579779716480077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17828673933719853144320051 26743010900579779716480077)
                  ·
                    refine ⟨10028629087717417393680029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26743010900579779716480077 10028629087717417393680029)
                    ·
                      refine ⟨3760735907894031522630011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10028629087717417393680029 3760735907894031522630011)
                      ·
                        rfl

theorem cell23_7324007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_7324007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324007 prefixEnd_7324007 := by exact prefixLift 7324007
  have htrace : WordTrace (prefixWord ++ tailWord_7324007) baseStart_7324007 baseEnd_7324007 := by
    simpa [prefixWord, tailWord_7324007, baseEnd_7324007] using wordTrace_append hprefix tailTrace_7324007
  have hstable : (prefixWord ++ tailWord_7324007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324007).length < 2 ^ (prefixWord ++ tailWord_7324007).sum := by decide
  have hdescent : baseEnd_7324007 < baseStart_7324007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324017 : List Nat := [1, 2, 2, 2, 1, 2, 1, 6, 1, 3, 2]
def baseStart_7324017 : Nat := 118140960795 + 7324017 * 2 ^ 59
def prefixEnd_7324017 : Nat := 4983230072969 + 3 ^ 40 * 7324017 * 2
def baseEnd_7324017 : Nat := 3760741042700576483504965

theorem tailTrace_7324017 : CollatzResearch.WordTrace tailWord_7324017 prefixEnd_7324017 3760741042700576483504965 := by
  unfold tailWord_7324017
  simp only [CollatzResearch.WordTrace]
  refine ⟨267128845507344726364050305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178085897004896484242700203 267128845507344726364050305)
  ·
    refine ⟨200346634130508544773037729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267128845507344726364050305 200346634130508544773037729)
    ·
      refine ⟨150259975597881408579778297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200346634130508544773037729 150259975597881408579778297)
      ·
        refine ⟨112694981698411056434833723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150259975597881408579778297 112694981698411056434833723)
        ·
          refine ⟨169042472547616584652250585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112694981698411056434833723 169042472547616584652250585)
          ·
            refine ⟨126781854410712438489187939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169042472547616584652250585 126781854410712438489187939)
            ·
              refine ⟨190172781616068657733781909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126781854410712438489187939 190172781616068657733781909)
              ·
                refine ⟨8914349138253218331271027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 190172781616068657733781909 8914349138253218331271027)
                ·
                  refine ⟨13371523707379827496906541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8914349138253218331271027 13371523707379827496906541)
                  ·
                    refine ⟨5014321390267435311339953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13371523707379827496906541 5014321390267435311339953)
                    ·
                      refine ⟨3760741042700576483504965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5014321390267435311339953 3760741042700576483504965)
                      ·
                        rfl

theorem cell23_7324017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_7324017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324017 prefixEnd_7324017 := by exact prefixLift 7324017
  have htrace : WordTrace (prefixWord ++ tailWord_7324017) baseStart_7324017 baseEnd_7324017 := by
    simpa [prefixWord, tailWord_7324017, baseEnd_7324017] using wordTrace_append hprefix tailTrace_7324017
  have hstable : (prefixWord ++ tailWord_7324017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324017).length < 2 ^ (prefixWord ++ tailWord_7324017).sum := by decide
  have hdescent : baseEnd_7324017 < baseStart_7324017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324064 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 1, 4, 2]
def baseStart_7324064 : Nat := 118140960795 + 7324064 * 2 ^ 59
def prefixEnd_7324064 : Nat := 4983230072969 + 3 ^ 40 * 7324064 * 2
def baseEnd_7324064 : Nat := 3760765176291337799617249

theorem tailTrace_7324064 : CollatzResearch.WordTrace tailWord_7324064 prefixEnd_7324064 3760765176291337799617249 := by
  unfold tailWord_7324064
  simp only [CollatzResearch.WordTrace]
  refine ⟨133565279869087226695505623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178087039825449635594007497 133565279869087226695505623)
  ·
    refine ⟨200347919803630840043258435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133565279869087226695505623 200347919803630840043258435)
    ·
      refine ⟨300521879705446260064887653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200347919803630840043258435 300521879705446260064887653)
      ·
        refine ⟨56347852444771173762166435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300521879705446260064887653 56347852444771173762166435)
        ·
          refine ⟨84521778667156760643249653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56347852444771173762166435 84521778667156760643249653)
          ·
            refine ⟨7923916750045946310304655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84521778667156760643249653 7923916750045946310304655)
            ·
              refine ⟨11885875125068919465456983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7923916750045946310304655 11885875125068919465456983)
              ·
                refine ⟨17828812687603379198185475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11885875125068919465456983 17828812687603379198185475)
                ·
                  refine ⟨26743219031405068797278213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17828812687603379198185475 26743219031405068797278213)
                  ·
                    refine ⟨5014353568388450399489665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26743219031405068797278213 5014353568388450399489665)
                    ·
                      refine ⟨3760765176291337799617249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5014353568388450399489665 3760765176291337799617249)
                      ·
                        rfl

theorem cell23_7324064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_7324064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324064 prefixEnd_7324064 := by exact prefixLift 7324064
  have htrace : WordTrace (prefixWord ++ tailWord_7324064) baseStart_7324064 baseEnd_7324064 := by
    simpa [prefixWord, tailWord_7324064, baseEnd_7324064] using wordTrace_append hprefix tailTrace_7324064
  have hstable : (prefixWord ++ tailWord_7324064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324064).length < 2 ^ (prefixWord ++ tailWord_7324064).sum := by decide
  have hdescent : baseEnd_7324064 < baseStart_7324064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324087 : List Nat := [1, 1, 3, 1, 3, 3, 3, 3, 5]
def baseStart_7324087 : Nat := 118140960795 + 7324087 * 2 ^ 59
def prefixEnd_7324087 : Nat := 4983230072969 + 3 ^ 40 * 7324087 * 2
def baseEnd_7324087 : Nat := 417864109594043467736627

theorem tailTrace_7324087 : CollatzResearch.WordTrace tailWord_7324087 prefixEnd_7324087 417864109594043467736627 := by
  unfold tailWord_7324087
  simp only [CollatzResearch.WordTrace]
  refine ⟨267131398617091128319098515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178087599078060752212732343 267131398617091128319098515)
  ·
    refine ⟨400697097925636692478647773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267131398617091128319098515 400697097925636692478647773)
    ·
      refine ⟨150261411722113759679492915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400697097925636692478647773 150261411722113759679492915)
      ·
        refine ⟨225392117583170639519239373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150261411722113759679492915 225392117583170639519239373)
        ·
          refine ⟨84522044093688989819714765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225392117583170639519239373 84522044093688989819714765)
          ·
            refine ⟨31695766535133371182393037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84522044093688989819714765 31695766535133371182393037)
            ·
              refine ⟨11885912450675014193397389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31695766535133371182393037 11885912450675014193397389)
              ·
                refine ⟨4457217169003130322524021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11885912450675014193397389 4457217169003130322524021)
                ·
                  refine ⟨417864109594043467736627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4457217169003130322524021 417864109594043467736627)
                  ·
                    rfl

theorem cell23_7324087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 5].length) (baseStart_7324087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324087 prefixEnd_7324087 := by exact prefixLift 7324087
  have htrace : WordTrace (prefixWord ++ tailWord_7324087) baseStart_7324087 baseEnd_7324087 := by
    simpa [prefixWord, tailWord_7324087, baseEnd_7324087] using wordTrace_append hprefix tailTrace_7324087
  have hstable : (prefixWord ++ tailWord_7324087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324087).length < 2 ^ (prefixWord ++ tailWord_7324087).sum := by decide
  have hdescent : baseEnd_7324087 < baseStart_7324087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324104 : List Nat := [2, 1, 3, 1, 3, 3, 3, 2, 5]
def baseStart_7324104 : Nat := 118140960795 + 7324104 * 2 ^ 59
def prefixEnd_7324104 : Nat := 4983230072969 + 3 ^ 40 * 7324104 * 2
def baseEnd_7324104 : Nat := 417865079501946404790785

theorem tailTrace_7324104 : CollatzResearch.WordTrace tailWord_7324104 prefixEnd_7324104 417865079501946404790785 := by
  unfold tailWord_7324104
  simp only [CollatzResearch.WordTrace]
  refine ⟨133566009329014770111233683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178088012438686360148311577 133566009329014770111233683)
  ·
    refine ⟨200349013993522155166850525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133566009329014770111233683 200349013993522155166850525)
    ·
      refine ⟨75130880247570808187568947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200349013993522155166850525 75130880247570808187568947)
      ·
        refine ⟨112696320371356212281353421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75130880247570808187568947 112696320371356212281353421)
        ·
          refine ⟨42261120139258579605507533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112696320371356212281353421 42261120139258579605507533)
          ·
            refine ⟨15847920052221967352065325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42261120139258579605507533 15847920052221967352065325)
            ·
              refine ⟨5942970019583237757024497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15847920052221967352065325 5942970019583237757024497)
              ·
                refine ⟨4457227514687428317768373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5942970019583237757024497 4457227514687428317768373)
                ·
                  refine ⟨417865079501946404790785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4457227514687428317768373 417865079501946404790785)
                  ·
                    rfl

theorem cell23_7324104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 5].length) (baseStart_7324104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324104 prefixEnd_7324104 := by exact prefixLift 7324104
  have htrace : WordTrace (prefixWord ++ tailWord_7324104) baseStart_7324104 baseEnd_7324104 := by
    simpa [prefixWord, tailWord_7324104, baseEnd_7324104] using wordTrace_append hprefix tailTrace_7324104
  have hstable : (prefixWord ++ tailWord_7324104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324104).length < 2 ^ (prefixWord ++ tailWord_7324104).sum := by decide
  have hdescent : baseEnd_7324104 < baseStart_7324104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324120 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 6, 1, 4]
def baseStart_7324120 : Nat := 118140960795 + 7324120 * 2 ^ 59
def prefixEnd_7324120 : Nat := 4983230072969 + 3 ^ 40 * 7324120 * 2
def baseEnd_7324120 : Nat := 3760793931207989580516991

theorem tailTrace_7324120 : CollatzResearch.WordTrace tailWord_7324120 prefixEnd_7324120 3760793931207989580516991 := by
  unfold tailWord_7324120
  simp only [CollatzResearch.WordTrace]
  refine ⟨133566301112985787477524907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178088401483981049970033209 133566301112985787477524907)
  ·
    refine ⟨200349451669478681216287361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133566301112985787477524907 200349451669478681216287361)
    ·
      refine ⟨150262088752109010912215521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200349451669478681216287361 150262088752109010912215521)
      ·
        refine ⟨112696566564081758184161641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150262088752109010912215521 112696566564081758184161641)
        ·
          refine ⟨84522424923061318638121231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112696566564081758184161641 84522424923061318638121231)
          ·
            refine ⟨126783637384591977957181847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84522424923061318638121231 126783637384591977957181847)
            ·
              refine ⟨190175456076887966935772771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126783637384591977957181847 190175456076887966935772771)
              ·
                refine ⟨285263184115331950403659157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190175456076887966935772771 285263184115331950403659157)
                ·
                  refine ⟨13371711755406185175171523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 285263184115331950403659157 13371711755406185175171523)
                  ·
                    refine ⟨20057567633109277762757285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13371711755406185175171523 20057567633109277762757285)
                    ·
                      refine ⟨3760793931207989580516991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20057567633109277762757285 3760793931207989580516991)
                      ·
                        rfl

theorem cell23_7324120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_7324120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324120 prefixEnd_7324120 := by exact prefixLift 7324120
  have htrace : WordTrace (prefixWord ++ tailWord_7324120) baseStart_7324120 baseEnd_7324120 := by
    simpa [prefixWord, tailWord_7324120, baseEnd_7324120] using wordTrace_append hprefix tailTrace_7324120
  have hstable : (prefixWord ++ tailWord_7324120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324120).length < 2 ^ (prefixWord ++ tailWord_7324120).sum := by decide
  have hdescent : baseEnd_7324120 < baseStart_7324120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324157 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_7324157 : Nat := 118140960795 + 7324157 * 2 ^ 59
def prefixEnd_7324157 : Nat := 4983230072969 + 3 ^ 40 * 7324157 * 2
def baseEnd_7324157 : Nat := 3760812929992205935754321

theorem tailTrace_7324157 : CollatzResearch.WordTrace tailWord_7324157 prefixEnd_7324157 3760812929992205935754321 := by
  unfold tailWord_7324157
  simp only [CollatzResearch.WordTrace]
  refine ⟨267133951726837530274146725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178089301151225020182764483 267133951726837530274146725)
  ·
    refine ⟨50087615948782036926402511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267133951726837530274146725 50087615948782036926402511)
    ·
      refine ⟨75131423923173055389603767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50087615948782036926402511 75131423923173055389603767)
      ·
        refine ⟨112697135884759583084405651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75131423923173055389603767 112697135884759583084405651)
        ·
          refine ⟨169045703827139374626608477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112697135884759583084405651 169045703827139374626608477)
          ·
            refine ⟨63392138935177265484978179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169045703827139374626608477 63392138935177265484978179)
            ·
              refine ⟨95088208402765898227467269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63392138935177265484978179 95088208402765898227467269)
              ·
                refine ⟨17829039075518605917650113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95088208402765898227467269 17829039075518605917650113)
                ·
                  refine ⟨13371779306638954438237585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17829039075518605917650113 13371779306638954438237585)
                  ·
                    refine ⟨10028834479979215828678189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13371779306638954438237585 10028834479979215828678189)
                    ·
                      refine ⟨3760812929992205935754321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10028834479979215828678189 3760812929992205935754321)
                      ·
                        rfl

theorem cell23_7324157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_7324157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324157 prefixEnd_7324157 := by exact prefixLift 7324157
  have htrace : WordTrace (prefixWord ++ tailWord_7324157) baseStart_7324157 baseEnd_7324157 := by
    simpa [prefixWord, tailWord_7324157, baseEnd_7324157] using wordTrace_append hprefix tailTrace_7324157
  have hstable : (prefixWord ++ tailWord_7324157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324157).length < 2 ^ (prefixWord ++ tailWord_7324157).sum := by decide
  have hdescent : baseEnd_7324157 < baseStart_7324157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324221 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 3, 1, 3]
def baseStart_7324221 : Nat := 118140960795 + 7324221 * 2 ^ 59
def prefixEnd_7324221 : Nat := 4983230072969 + 3 ^ 40 * 7324221 * 2
def baseEnd_7324221 : Nat := 3760845792754093685354027

theorem tailTrace_7324221 : CollatzResearch.WordTrace tailWord_7324221 prefixEnd_7324221 3760845792754093685354027 := by
  unfold tailWord_7324221
  simp only [CollatzResearch.WordTrace]
  refine ⟨267136285998605669204476517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178090857332403779469651011 267136285998605669204476517)
  ·
    refine ⟨50088053624738562975839347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267136285998605669204476517 50088053624738562975839347)
    ·
      refine ⟨75132080437107844463759021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50088053624738562975839347 75132080437107844463759021)
      ·
        refine ⟨28174530163915441673909633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75132080437107844463759021 28174530163915441673909633)
        ·
          refine ⟨21130897622936581255432225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28174530163915441673909633 21130897622936581255432225)
          ·
            refine ⟨15848173217202435941574169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21130897622936581255432225 15848173217202435941574169)
            ·
              refine ⟨11886129912901826956180627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15848173217202435941574169 11886129912901826956180627)
              ·
                refine ⟨17829194869352740434270941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11886129912901826956180627 17829194869352740434270941)
                ·
                  refine ⟨6685948076007277662851603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17829194869352740434270941 6685948076007277662851603)
                  ·
                    refine ⟨10028922114010916494277405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6685948076007277662851603 10028922114010916494277405)
                    ·
                      refine ⟨3760845792754093685354027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10028922114010916494277405 3760845792754093685354027)
                      ·
                        rfl

theorem cell23_7324221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_7324221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324221 prefixEnd_7324221 := by exact prefixLift 7324221
  have htrace : WordTrace (prefixWord ++ tailWord_7324221) baseStart_7324221 baseEnd_7324221 := by
    simpa [prefixWord, tailWord_7324221, baseEnd_7324221] using wordTrace_append hprefix tailTrace_7324221
  have hstable : (prefixWord ++ tailWord_7324221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324221).length < 2 ^ (prefixWord ++ tailWord_7324221).sum := by decide
  have hdescent : baseEnd_7324221 < baseStart_7324221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324244 : List Nat := [2, 4, 1, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_7324244 : Nat := 118140960795 + 7324244 * 2 ^ 59
def prefixEnd_7324244 : Nat := 4983230072969 + 3 ^ 40 * 7324244 * 2
def baseEnd_7324244 : Nat := 3760857602809147095366421

theorem tailTrace_7324244 : CollatzResearch.WordTrace tailWord_7324244 prefixEnd_7324244 3760857602809147095366421 := by
  unfold tailWord_7324244
  simp only [CollatzResearch.WordTrace]
  refine ⟨133568562438761172066281893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178091416585014896088375857 133568562438761172066281893)
  ·
    refine ⟨25044105457267719762427855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133568562438761172066281893 25044105457267719762427855)
    ·
      refine ⟨37566158185901579643641783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25044105457267719762427855 37566158185901579643641783)
      ·
        refine ⟨56349237278852369465462675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37566158185901579643641783 56349237278852369465462675)
        ·
          refine ⟨84523855918278554198194013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56349237278852369465462675 84523855918278554198194013)
          ·
            refine ⟨31696445969354457824322755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84523855918278554198194013 31696445969354457824322755)
            ·
              refine ⟨47544668954031686736484133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31696445969354457824322755 47544668954031686736484133)
              ·
                refine ⟨8914625428880941263090775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47544668954031686736484133 8914625428880941263090775)
                ·
                  refine ⟨13371938143321411894636163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8914625428880941263090775 13371938143321411894636163)
                  ·
                    refine ⟨20057907214982117841954245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13371938143321411894636163 20057907214982117841954245)
                    ·
                      refine ⟨3760857602809147095366421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20057907214982117841954245 3760857602809147095366421)
                      ·
                        rfl

theorem cell23_7324244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_7324244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324244 prefixEnd_7324244 := by exact prefixLift 7324244
  have htrace : WordTrace (prefixWord ++ tailWord_7324244) baseStart_7324244 baseEnd_7324244 := by
    simpa [prefixWord, tailWord_7324244, baseEnd_7324244] using wordTrace_append hprefix tailTrace_7324244
  have hstable : (prefixWord ++ tailWord_7324244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324244).length < 2 ^ (prefixWord ++ tailWord_7324244).sum := by decide
  have hdescent : baseEnd_7324244 < baseStart_7324244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324280 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 1, 9]
def baseStart_7324280 : Nat := 118140960795 + 7324280 * 2 ^ 59
def prefixEnd_7324280 : Nat := 4983230072969 + 3 ^ 40 * 7324280 * 2
def baseEnd_7324280 : Nat := 1253625362704236318172085

theorem tailTrace_7324280 : CollatzResearch.WordTrace tailWord_7324280 prefixEnd_7324280 1253625362704236318172085 := by
  unfold tailWord_7324280
  simp only [CollatzResearch.WordTrace]
  refine ⟨133569218952695961140437147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178092291936927948187249529 133569218952695961140437147)
  ·
    refine ⟨200353828429043941710655721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133569218952695961140437147 200353828429043941710655721)
    ·
      refine ⟨150265371321782956282991791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200353828429043941710655721 150265371321782956282991791)
      ·
        refine ⟨225398056982674434424487687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150265371321782956282991791 225398056982674434424487687)
        ·
          refine ⟨338097085474011651636731531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225398056982674434424487687 338097085474011651636731531)
          ·
            refine ⟨507145628211017477455097297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338097085474011651636731531 507145628211017477455097297)
            ·
              refine ⟨380359221158263108091322973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507145628211017477455097297 380359221158263108091322973)
              ·
                refine ⟨142634707934348665534246115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380359221158263108091322973 142634707934348665534246115)
                ·
                  refine ⟨213952061901522998301369173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142634707934348665534246115 213952061901522998301369173)
                  ·
                    refine ⟨1253625362704236318172085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 213952061901522998301369173 1253625362704236318172085)
                    ·
                      rfl

theorem cell23_7324280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_7324280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324280 prefixEnd_7324280 := by exact prefixLift 7324280
  have htrace : WordTrace (prefixWord ++ tailWord_7324280) baseStart_7324280 baseEnd_7324280 := by
    simpa [prefixWord, tailWord_7324280, baseEnd_7324280] using wordTrace_append hprefix tailTrace_7324280
  have hstable : (prefixWord ++ tailWord_7324280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324280).length < 2 ^ (prefixWord ++ tailWord_7324280).sum := by decide
  have hdescent : baseEnd_7324280 < baseStart_7324280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324298 : List Nat := [3, 1, 2, 3, 3, 2, 1, 2, 1, 2, 3]
def baseStart_7324298 : Nat := 118140960795 + 7324298 * 2 ^ 59
def prefixEnd_7324298 : Nat := 4983230072969 + 3 ^ 40 * 7324298 * 2
def baseEnd_7324298 : Nat := 3760885330764489884091173

theorem tailTrace_7324298 : CollatzResearch.WordTrace tailWord_7324298 prefixEnd_7324298 3760885330764489884091173 := by
  unfold tailWord_7324298
  simp only [CollatzResearch.WordTrace]
  refine ⟨66784773604831677838757387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178092729612884474236686365 66784773604831677838757387)
  ·
    refine ⟨100177160407247516758136081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66784773604831677838757387 100177160407247516758136081)
    ·
      refine ⟨75132870305435637568602061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100177160407247516758136081 75132870305435637568602061)
      ·
        refine ⟨28174826364538364088225773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75132870305435637568602061 28174826364538364088225773)
        ·
          refine ⟨10565559886701886533084665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28174826364538364088225773 10565559886701886533084665)
          ·
            refine ⟨7924169915026414899813499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10565559886701886533084665 7924169915026414899813499)
            ·
              refine ⟨11886254872539622349720249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7924169915026414899813499 11886254872539622349720249)
              ·
                refine ⟨8914691154404716762290187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11886254872539622349720249 8914691154404716762290187)
                ·
                  refine ⟨13372036731607075143435281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8914691154404716762290187 13372036731607075143435281)
                  ·
                    refine ⟨10029027548705306357576461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13372036731607075143435281 10029027548705306357576461)
                    ·
                      refine ⟨3760885330764489884091173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10029027548705306357576461 3760885330764489884091173)
                      ·
                        rfl

theorem cell23_7324298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_7324298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324298 prefixEnd_7324298 := by exact prefixLift 7324298
  have htrace : WordTrace (prefixWord ++ tailWord_7324298) baseStart_7324298 baseEnd_7324298 := by
    simpa [prefixWord, tailWord_7324298, baseEnd_7324298] using wordTrace_append hprefix tailTrace_7324298
  have hstable : (prefixWord ++ tailWord_7324298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324298).length < 2 ^ (prefixWord ++ tailWord_7324298).sum := by decide
  have hdescent : baseEnd_7324298 < baseStart_7324298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324351 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 1, 4, 2]
def baseStart_7324351 : Nat := 118140960795 + 7324351 * 2 ^ 59
def prefixEnd_7324351 : Nat := 4983230072969 + 3 ^ 40 * 7324351 * 2
def baseEnd_7324351 : Nat := 3760912545239178176728429

theorem tailTrace_7324351 : CollatzResearch.WordTrace tailWord_7324351 prefixEnd_7324351 3760912545239178176728429 := by
  unfold tailWord_7324351
  simp only [CollatzResearch.WordTrace]
  refine ⟨267141027488134701406708907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178094018325423134271139271 267141027488134701406708907)
  ·
    refine ⟨400711541232202052110063361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267141027488134701406708907 400711541232202052110063361)
    ·
      refine ⟨300533655924151539082547521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400711541232202052110063361 300533655924151539082547521)
      ·
        refine ⟨225400241943113654311910641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300533655924151539082547521 225400241943113654311910641)
        ·
          refine ⟨169050181457335240733932981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225400241943113654311910641 169050181457335240733932981)
          ·
            refine ⟨15848454511625178818806217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169050181457335240733932981 15848454511625178818806217)
            ·
              refine ⟨11886340883718884114104663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15848454511625178818806217 11886340883718884114104663)
              ·
                refine ⟨17829511325578326171156995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11886340883718884114104663 17829511325578326171156995)
                ·
                  refine ⟨26744266988367489256735493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17829511325578326171156995 26744266988367489256735493)
                  ·
                    refine ⟨5014550060318904235637905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26744266988367489256735493 5014550060318904235637905)
                    ·
                      refine ⟨3760912545239178176728429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5014550060318904235637905 3760912545239178176728429)
                      ·
                        rfl

theorem cell23_7324351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 4, 2].length) (baseStart_7324351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324351 prefixEnd_7324351 := by exact prefixLift 7324351
  have htrace : WordTrace (prefixWord ++ tailWord_7324351) baseStart_7324351 baseEnd_7324351 := by
    simpa [prefixWord, tailWord_7324351, baseEnd_7324351] using wordTrace_append hprefix tailTrace_7324351
  have hstable : (prefixWord ++ tailWord_7324351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324351).length < 2 ^ (prefixWord ++ tailWord_7324351).sum := by decide
  have hdescent : baseEnd_7324351 < baseStart_7324351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324372 : List Nat := [2, 4, 1, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_7324372 : Nat := 118140960795 + 7324372 * 2 ^ 59
def prefixEnd_7324372 : Nat := 4983230072969 + 3 ^ 40 * 7324372 * 2
def baseEnd_7324372 : Nat := 3760923328332922594565833

theorem tailTrace_7324372 : CollatzResearch.WordTrace tailWord_7324372 prefixEnd_7324372 3760923328332922594565833 := by
  unfold tailWord_7324372
  simp only [CollatzResearch.WordTrace]
  refine ⟨133570896710529310996611685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178094528947372414662148913 133570896710529310996611685)
  ·
    refine ⟨25044543133224245811864691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133570896710529310996611685 25044543133224245811864691)
    ·
      refine ⟨37566814699836368717797037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25044543133224245811864691 37566814699836368717797037)
      ·
        refine ⟨14087555512438638269173889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37566814699836368717797037 14087555512438638269173889)
        ·
          refine ⟨10565666634328978701880417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14087555512438638269173889 10565666634328978701880417)
          ·
            refine ⟨7924249975746734026410313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10565666634328978701880417 7924249975746734026410313)
            ·
              refine ⟨5943187481810050519807735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7924249975746734026410313 5943187481810050519807735)
              ·
                refine ⟨8914781222715075779711603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5943187481810050519807735 8914781222715075779711603)
                ·
                  refine ⟨13372171834072613669567405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8914781222715075779711603 13372171834072613669567405)
                  ·
                    refine ⟨5014564437777230126087777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13372171834072613669567405 5014564437777230126087777)
                    ·
                      refine ⟨3760923328332922594565833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5014564437777230126087777 3760923328332922594565833)
                      ·
                        rfl

theorem cell23_7324372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_7324372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324372 prefixEnd_7324372 := by exact prefixLift 7324372
  have htrace : WordTrace (prefixWord ++ tailWord_7324372) baseStart_7324372 baseEnd_7324372 := by
    simpa [prefixWord, tailWord_7324372, baseEnd_7324372] using wordTrace_append hprefix tailTrace_7324372
  have hstable : (prefixWord ++ tailWord_7324372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324372).length < 2 ^ (prefixWord ++ tailWord_7324372).sum := by decide
  have hdescent : baseEnd_7324372 < baseStart_7324372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324385 : List Nat := [1, 2, 3, 1, 4, 3, 1, 2, 2, 2, 2]
def baseStart_7324385 : Nat := 118140960795 + 7324385 * 2 ^ 59
def prefixEnd_7324385 : Nat := 4983230072969 + 3 ^ 40 * 7324385 * 2
def baseEnd_7324385 : Nat := 3760930003581431043703273

theorem tailTrace_7324385 : CollatzResearch.WordTrace tailWord_7324385 prefixEnd_7324385 3760930003581431043703273 := by
  unfold tailWord_7324385
  simp only [CollatzResearch.WordTrace]
  refine ⟨267142267570011525213446609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178094845046674350142297739 267142267570011525213446609)
  ·
    refine ⟨200356700677508643910084957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267142267570011525213446609 200356700677508643910084957)
    ·
      refine ⟨75133762754065741466281859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200356700677508643910084957 75133762754065741466281859)
      ·
        refine ⟨112700644131098612199422789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75133762754065741466281859 112700644131098612199422789)
        ·
          refine ⟨21131370774580989787391773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112700644131098612199422789 21131370774580989787391773)
          ·
            refine ⟨7924264040467871170271915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21131370774580989787391773 7924264040467871170271915)
            ·
              refine ⟨11886396060701806755407873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7924264040467871170271915 11886396060701806755407873)
              ·
                refine ⟨8914797045526355066555905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11886396060701806755407873 8914797045526355066555905)
                ·
                  refine ⟨6686097784144766299916929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8914797045526355066555905 6686097784144766299916929)
                  ·
                    refine ⟨5014573338108574724937697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6686097784144766299916929 5014573338108574724937697)
                    ·
                      refine ⟨3760930003581431043703273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5014573338108574724937697 3760930003581431043703273)
                      ·
                        rfl

theorem cell23_7324385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_7324385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324385 prefixEnd_7324385 := by exact prefixLift 7324385
  have htrace : WordTrace (prefixWord ++ tailWord_7324385) baseStart_7324385 baseEnd_7324385 := by
    simpa [prefixWord, tailWord_7324385, baseEnd_7324385] using wordTrace_append hprefix tailTrace_7324385
  have hstable : (prefixWord ++ tailWord_7324385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324385).length < 2 ^ (prefixWord ++ tailWord_7324385).sum := by decide
  have hdescent : baseEnd_7324385 < baseStart_7324385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324417 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 1, 10]
def baseStart_7324417 : Nat := 118140960795 + 7324417 * 2 ^ 59
def prefixEnd_7324417 : Nat := 4983230072969 + 3 ^ 40 * 7324417 * 2
def baseEnd_7324417 : Nat := 1253648811654124972834375

theorem tailTrace_7324417 : CollatzResearch.WordTrace tailWord_7324417 prefixEnd_7324417 1253648811654124972834375 := by
  unfold tailWord_7324417
  simp only [CollatzResearch.WordTrace]
  refine ⟨267143434705895594678611505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178095623137263729785741003 267143434705895594678611505)
  ·
    refine ⟨200357576029421696008958629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267143434705895594678611505 200357576029421696008958629)
    ·
      refine ⟨37567045505516568001679743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200357576029421696008958629 37567045505516568001679743)
      ·
        refine ⟨56350568258274852002519615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37567045505516568001679743 56350568258274852002519615)
        ·
          refine ⟨84525852387412278003779423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56350568258274852002519615 84525852387412278003779423)
          ·
            refine ⟨126788778581118417005669135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84525852387412278003779423 126788778581118417005669135)
            ·
              refine ⟨190183167871677625508503703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126788778581118417005669135 190183167871677625508503703)
              ·
                refine ⟨285274751807516438262755555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190183167871677625508503703 285274751807516438262755555)
                ·
                  refine ⟨427912127711274657394133333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285274751807516438262755555 427912127711274657394133333)
                  ·
                    refine ⟨1253648811654124972834375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 427912127711274657394133333 1253648811654124972834375)
                    ·
                      rfl

theorem cell23_7324417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_7324417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324417 prefixEnd_7324417 := by exact prefixLift 7324417
  have htrace : WordTrace (prefixWord ++ tailWord_7324417) baseStart_7324417 baseEnd_7324417 := by
    simpa [prefixWord, tailWord_7324417, baseEnd_7324417] using wordTrace_append hprefix tailTrace_7324417
  have hstable : (prefixWord ++ tailWord_7324417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324417).length < 2 ^ (prefixWord ++ tailWord_7324417).sum := by decide
  have hdescent : baseEnd_7324417 < baseStart_7324417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324424 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_7324424 : Nat := 118140960795 + 7324424 * 2 ^ 59
def prefixEnd_7324424 : Nat := 4983230072969 + 3 ^ 40 * 7324424 * 2
def baseEnd_7324424 : Nat := 3760950029326956391115593

theorem tailTrace_7324424 : CollatzResearch.WordTrace tailWord_7324424 prefixEnd_7324424 3760950029326956391115593 := by
  unfold tailWord_7324424
  simp only [CollatzResearch.WordTrace]
  refine ⟨133571845008435117437058163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178095793344580156582744217 133571845008435117437058163)
  ·
    refine ⟨200357767512652676155587245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133571845008435117437058163 200357767512652676155587245)
    ·
      refine ⟨75134162817244753558345217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200357767512652676155587245 75134162817244753558345217)
      ·
        refine ⟨56350622112933565168758913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75134162817244753558345217 56350622112933565168758913)
        ·
          refine ⟨42262966584700173876569185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56350622112933565168758913 42262966584700173876569185)
          ·
            refine ⟨31697224938525130407426889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42262966584700173876569185 31697224938525130407426889)
            ·
              refine ⟨23772918703893847805570167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31697224938525130407426889 23772918703893847805570167)
              ·
                refine ⟨35659378055840771708355251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23772918703893847805570167 35659378055840771708355251)
                ·
                  refine ⟨53489067083761157562532877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35659378055840771708355251 53489067083761157562532877)
                  ·
                    refine ⟨20058400156410434085949829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53489067083761157562532877 20058400156410434085949829)
                    ·
                      refine ⟨3760950029326956391115593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20058400156410434085949829 3760950029326956391115593)
                      ·
                        rfl

theorem cell23_7324424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_7324424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324424 prefixEnd_7324424 := by exact prefixLift 7324424
  have htrace : WordTrace (prefixWord ++ tailWord_7324424) baseStart_7324424 baseEnd_7324424 := by
    simpa [prefixWord, tailWord_7324424, baseEnd_7324424] using wordTrace_append hprefix tailTrace_7324424
  have hstable : (prefixWord ++ tailWord_7324424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324424).length < 2 ^ (prefixWord ++ tailWord_7324424).sum := by decide
  have hdescent : baseEnd_7324424 < baseStart_7324424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324427 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 5]
def baseStart_7324427 : Nat := 118140960795 + 7324427 * 2 ^ 59
def prefixEnd_7324427 : Nat := 4983230072969 + 3 ^ 40 * 7324427 * 2
def baseEnd_7324427 : Nat := 3760951569768919879378079

theorem tailTrace_7324427 : CollatzResearch.WordTrace tailWord_7324427 prefixEnd_7324427 3760951569768919879378079 := by
  unfold tailWord_7324427
  simp only [CollatzResearch.WordTrace]
  refine ⟨267143799435859366386475535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178095866290572910924317023 267143799435859366386475535)
  ·
    refine ⟨400715699153789049579713303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267143799435859366386475535 400715699153789049579713303)
    ·
      refine ⟨601073548730683574369569955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400715699153789049579713303 601073548730683574369569955)
      ·
        refine ⟨901610323096025361554354933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601073548730683574369569955 901610323096025361554354933)
        ·
          refine ⟨84525967790252377645720775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 901610323096025361554354933 84525967790252377645720775)
          ·
            refine ⟨126788951685378566468581163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84525967790252377645720775 126788951685378566468581163)
            ·
              refine ⟨190183427528067849702871745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126788951685378566468581163 190183427528067849702871745)
              ·
                refine ⟨142637570646050887277153809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190183427528067849702871745 142637570646050887277153809)
                ·
                  refine ⟨106978177984538165457865357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142637570646050887277153809 106978177984538165457865357)
                  ·
                    refine ⟨40116816744201812046699509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106978177984538165457865357 40116816744201812046699509)
                    ·
                      refine ⟨3760951569768919879378079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40116816744201812046699509 3760951569768919879378079)
                      ·
                        rfl

theorem cell23_7324427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 5].length) (baseStart_7324427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324427 prefixEnd_7324427 := by exact prefixLift 7324427
  have htrace : WordTrace (prefixWord ++ tailWord_7324427) baseStart_7324427 baseEnd_7324427 := by
    simpa [prefixWord, tailWord_7324427, baseEnd_7324427] using wordTrace_append hprefix tailTrace_7324427
  have hstable : (prefixWord ++ tailWord_7324427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324427).length < 2 ^ (prefixWord ++ tailWord_7324427).sum := by decide
  have hdescent : baseEnd_7324427 < baseStart_7324427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324544 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 4]
def baseStart_7324544 : Nat := 118140960795 + 7324544 * 2 ^ 59
def prefixEnd_7324544 : Nat := 4983230072969 + 3 ^ 40 * 7324544 * 2
def baseEnd_7324544 : Nat := 3761011647005495921615041

theorem tailTrace_7324544 : CollatzResearch.WordTrace tailWord_7324544 prefixEnd_7324544 3761011647005495921615041 := by
  unfold tailWord_7324544
  simp only [CollatzResearch.WordTrace]
  refine ⟨133574033388217747684242343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178098711184290330245656457 133574033388217747684242343)
  ·
    refine ⟨200361050082326621526363515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133574033388217747684242343 200361050082326621526363515)
    ·
      refine ⟨300541575123489932289545273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200361050082326621526363515 300541575123489932289545273)
      ·
        refine ⟨225406181342617449217158955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300541575123489932289545273 225406181342617449217158955)
        ·
          refine ⟨338109272013926173825738433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225406181342617449217158955 338109272013926173825738433)
          ·
            refine ⟨253581954010444630369303825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338109272013926173825738433 253581954010444630369303825)
            ·
              refine ⟨190186465507833472776977869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253581954010444630369303825 190186465507833472776977869)
              ·
                refine ⟨71319924565437552291366701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190186465507833472776977869 71319924565437552291366701)
                ·
                  refine ⟨26744971712039082109262513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71319924565437552291366701 26744971712039082109262513)
                  ·
                    refine ⟨20058728784029311581946885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26744971712039082109262513 20058728784029311581946885)
                    ·
                      refine ⟨3761011647005495921615041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20058728784029311581946885 3761011647005495921615041)
                      ·
                        rfl

theorem cell23_7324544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_7324544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324544 prefixEnd_7324544 := by exact prefixLift 7324544
  have htrace : WordTrace (prefixWord ++ tailWord_7324544) baseStart_7324544 baseEnd_7324544 := by
    simpa [prefixWord, tailWord_7324544, baseEnd_7324544] using wordTrace_append hprefix tailTrace_7324544
  have hstable : (prefixWord ++ tailWord_7324544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324544).length < 2 ^ (prefixWord ++ tailWord_7324544).sum := by decide
  have hdescent : baseEnd_7324544 < baseStart_7324544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324548 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_7324548 : Nat := 118140960795 + 7324548 * 2 ^ 59
def prefixEnd_7324548 : Nat := 4983230072969 + 3 ^ 40 * 7324548 * 2
def baseEnd_7324548 : Nat := 3761013700928113905965023

theorem tailTrace_7324548 : CollatzResearch.WordTrace tailWord_7324548 prefixEnd_7324548 3761013700928113905965023 := by
  unfold tailWord_7324548
  simp only [CollatzResearch.WordTrace]
  refine ⟨133574106334210502025815149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178098808445614002701086865 133574106334210502025815149)
  ·
    refine ⟨50090289875328938259680681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133574106334210502025815149 50090289875328938259680681)
    ·
      refine ⟨37567717406496703694760511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50090289875328938259680681 37567717406496703694760511)
      ·
        refine ⟨56351576109745055542140767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37567717406496703694760511 56351576109745055542140767)
        ·
          refine ⟨84527364164617583313211151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56351576109745055542140767 84527364164617583313211151)
          ·
            refine ⟨126791046246926374969816727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84527364164617583313211151 126791046246926374969816727)
            ·
              refine ⟨190186569370389562454725091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126791046246926374969816727 190186569370389562454725091)
              ·
                refine ⟨285279854055584343682087637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190186569370389562454725091 285279854055584343682087637)
                ·
                  refine ⟨6686246579427758055048929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 285279854055584343682087637 6686246579427758055048929)
                  ·
                    refine ⟨5014684934570818541286697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6686246579427758055048929 5014684934570818541286697)
                    ·
                      refine ⟨3761013700928113905965023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5014684934570818541286697 3761013700928113905965023)
                      ·
                        rfl

theorem cell23_7324548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_7324548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324548 prefixEnd_7324548 := by exact prefixLift 7324548
  have htrace : WordTrace (prefixWord ++ tailWord_7324548) baseStart_7324548 baseEnd_7324548 := by
    simpa [prefixWord, tailWord_7324548, baseEnd_7324548] using wordTrace_append hprefix tailTrace_7324548
  have hstable : (prefixWord ++ tailWord_7324548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324548).length < 2 ^ (prefixWord ++ tailWord_7324548).sum := by decide
  have hdescent : baseEnd_7324548 < baseStart_7324548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324565 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 3, 2, 2]
def baseStart_7324565 : Nat := 118140960795 + 7324565 * 2 ^ 59
def prefixEnd_7324565 : Nat := 4983230072969 + 3 ^ 40 * 7324565 * 2
def baseEnd_7324565 : Nat := 3761022430099240339452445

theorem tailTrace_7324565 : CollatzResearch.WordTrace tailWord_7324565 prefixEnd_7324565 3761022430099240339452445 := by
  unfold tailWord_7324565
  simp only [CollatzResearch.WordTrace]
  refine ⟨267148832709359415954999149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178099221806239610636666099 267148832709359415954999149)
  ·
    refine ⟨100180812266009780983124681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267148832709359415954999149 100180812266009780983124681)
    ·
      refine ⟨75135609199507335737343511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100180812266009780983124681 75135609199507335737343511)
      ·
        refine ⟨112703413799261003606015267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75135609199507335737343511 112703413799261003606015267)
        ·
          refine ⟨169055120698891505409022901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112703413799261003606015267 169055120698891505409022901)
          ·
            refine ⟨15848917565521078632095897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169055120698891505409022901 15848917565521078632095897)
            ·
              refine ⟨11886688174140808974071923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15848917565521078632095897 11886688174140808974071923)
              ·
                refine ⟨17830032261211213461107885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11886688174140808974071923 17830032261211213461107885)
                ·
                  refine ⟨6686262097954205047915457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17830032261211213461107885 6686262097954205047915457)
                  ·
                    refine ⟨5014696573465653785936593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6686262097954205047915457 5014696573465653785936593)
                    ·
                      refine ⟨3761022430099240339452445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5014696573465653785936593 3761022430099240339452445)
                      ·
                        rfl

theorem cell23_7324565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_7324565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324565 prefixEnd_7324565 := by exact prefixLift 7324565
  have htrace : WordTrace (prefixWord ++ tailWord_7324565) baseStart_7324565 baseEnd_7324565 := by
    simpa [prefixWord, tailWord_7324565, baseEnd_7324565] using wordTrace_append hprefix tailTrace_7324565
  have hstable : (prefixWord ++ tailWord_7324565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324565).length < 2 ^ (prefixWord ++ tailWord_7324565).sum := by decide
  have hdescent : baseEnd_7324565 < baseStart_7324565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324575 : List Nat := [1, 1, 2, 5, 2, 2, 3, 1, 2, 4]
def baseStart_7324575 : Nat := 118140960795 + 7324575 * 2 ^ 59
def prefixEnd_7324575 : Nat := 4983230072969 + 3 ^ 40 * 7324575 * 2
def baseEnd_7324575 : Nat := 1253675854968595100109133

theorem tailTrace_7324575 : CollatzResearch.WordTrace tailWord_7324575 prefixEnd_7324575 1253675854968595100109133 := by
  unfold tailWord_7324575
  simp only [CollatzResearch.WordTrace]
  refine ⟨267149197439323187662863179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178099464959548791775242119 267149197439323187662863179)
  ·
    refine ⟨400723796158984781494294769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267149197439323187662863179 400723796158984781494294769)
    ·
      refine ⟨300542847119238586120721077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400723796158984781494294769 300542847119238586120721077)
      ·
        refine ⟨28175891917428617448817601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 300542847119238586120721077 28175891917428617448817601)
        ·
          refine ⟨21131918938071463086613201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28175891917428617448817601 21131918938071463086613201)
          ·
            refine ⟨15848939203553597314959901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21131918938071463086613201 15848939203553597314959901)
            ·
              refine ⟨5943352201332598993109963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15848939203553597314959901 5943352201332598993109963)
              ·
                refine ⟨8915028301998898489664945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5943352201332598993109963 8915028301998898489664945)
                ·
                  refine ⟨6686271226499173867248709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8915028301998898489664945 6686271226499173867248709)
                  ·
                    refine ⟨1253675854968595100109133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6686271226499173867248709 1253675854968595100109133)
                    ·
                      rfl

theorem cell23_7324575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 1, 2, 4].length) (baseStart_7324575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324575 prefixEnd_7324575 := by exact prefixLift 7324575
  have htrace : WordTrace (prefixWord ++ tailWord_7324575) baseStart_7324575 baseEnd_7324575 := by
    simpa [prefixWord, tailWord_7324575, baseEnd_7324575] using wordTrace_append hprefix tailTrace_7324575
  have hstable : (prefixWord ++ tailWord_7324575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324575).length < 2 ^ (prefixWord ++ tailWord_7324575).sum := by decide
  have hdescent : baseEnd_7324575 < baseStart_7324575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324578 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_7324578 : Nat := 118140960795 + 7324578 * 2 ^ 59
def prefixEnd_7324578 : Nat := 4983230072969 + 3 ^ 40 * 7324578 * 2
def baseEnd_7324578 : Nat := 3761029105347748788589885

theorem tailTrace_7324578 : CollatzResearch.WordTrace tailWord_7324578 prefixEnd_7324578 3761029105347748788589885 := by
  unfold tailWord_7324578
  simp only [CollatzResearch.WordTrace]
  refine ⟨66787326714578079793805597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178099537905541546116814925 66787326714578079793805597)
  ·
    refine ⟨25045247517966779922677099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66787326714578079793805597 25045247517966779922677099)
    ·
      refine ⟨37567871276950169884015649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25045247517966779922677099 37567871276950169884015649)
      ·
        refine ⟨28175903457712627413011737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37567871276950169884015649 28175903457712627413011737)
        ·
          refine ⟨21131927593284470559758803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28175903457712627413011737 21131927593284470559758803)
          ·
            refine ⟨31697891389926705839638205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21131927593284470559758803 31697891389926705839638205)
            ·
              refine ⟨11886709271222514689864327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31697891389926705839638205 11886709271222514689864327)
              ·
                refine ⟨17830063906833772034796491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11886709271222514689864327 17830063906833772034796491)
                ·
                  refine ⟨26745095860250658052194737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17830063906833772034796491 26745095860250658052194737)
                  ·
                    refine ⟨20058821895187993539146053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26745095860250658052194737 20058821895187993539146053)
                    ·
                      refine ⟨3761029105347748788589885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20058821895187993539146053 3761029105347748788589885)
                      ·
                        rfl

theorem cell23_7324578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_7324578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324578 prefixEnd_7324578 := by exact prefixLift 7324578
  have htrace : WordTrace (prefixWord ++ tailWord_7324578) baseStart_7324578 baseEnd_7324578 := by
    simpa [prefixWord, tailWord_7324578, baseEnd_7324578] using wordTrace_append hprefix tailTrace_7324578
  have hstable : (prefixWord ++ tailWord_7324578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324578).length < 2 ^ (prefixWord ++ tailWord_7324578).sum := by decide
  have hdescent : baseEnd_7324578 < baseStart_7324578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324624 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 5]
def baseStart_7324624 : Nat := 118140960795 + 7324624 * 2 ^ 59
def prefixEnd_7324624 : Nat := 4983230072969 + 3 ^ 40 * 7324624 * 2
def baseEnd_7324624 : Nat := 3761052725457855608614673

theorem tailTrace_7324624 : CollatzResearch.WordTrace tailWord_7324624 prefixEnd_7324624 3761052725457855608614673 := by
  unfold tailWord_7324624
  simp only [CollatzResearch.WordTrace]
  refine ⟨133575492308072834515698463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178100656410763779354264617 133575492308072834515698463)
  ·
    refine ⟨200363238462109251773547695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133575492308072834515698463 200363238462109251773547695)
    ·
      refine ⟨300544857693163877660321543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200363238462109251773547695 300544857693163877660321543)
      ·
        refine ⟨450817286539745816490482315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300544857693163877660321543 450817286539745816490482315)
        ·
          refine ⟨676225929809618724735723473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450817286539745816490482315 676225929809618724735723473)
          ·
            refine ⟨507169447357214043551792605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 676225929809618724735723473 507169447357214043551792605)
            ·
              refine ⟨190188542758955266331922227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507169447357214043551792605 190188542758955266331922227)
              ·
                refine ⟨285282814138432899497883341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190188542758955266331922227 285282814138432899497883341)
                ·
                  refine ⟨106981055301912337311706253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285282814138432899497883341 106981055301912337311706253)
                  ·
                    refine ⟨40117895738217126491889845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106981055301912337311706253 40117895738217126491889845)
                    ·
                      refine ⟨3761052725457855608614673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40117895738217126491889845 3761052725457855608614673)
                      ·
                        rfl

theorem cell23_7324624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_7324624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324624 prefixEnd_7324624 := by exact prefixLift 7324624
  have htrace : WordTrace (prefixWord ++ tailWord_7324624) baseStart_7324624 baseEnd_7324624 := by
    simpa [prefixWord, tailWord_7324624, baseEnd_7324624] using wordTrace_append hprefix tailTrace_7324624
  have hstable : (prefixWord ++ tailWord_7324624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324624).length < 2 ^ (prefixWord ++ tailWord_7324624).sum := by decide
  have hdescent : baseEnd_7324624 < baseStart_7324624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324632 : List Nat := [2, 1, 2, 2, 2, 5, 2, 1, 2, 1, 3]
def baseStart_7324632 : Nat := 118140960795 + 7324632 * 2 ^ 59
def prefixEnd_7324632 : Nat := 4983230072969 + 3 ^ 40 * 7324632 * 2
def baseEnd_7324632 : Nat := 3761056833303091577314637

theorem tailTrace_7324632 : CollatzResearch.WordTrace tailWord_7324632 prefixEnd_7324632 3761056833303091577314637 := by
  unfold tailWord_7324632
  simp only [CollatzResearch.WordTrace]
  refine ⟨133575638200058343198844075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178100850933411124265125433 133575638200058343198844075)
  ·
    refine ⟨200363457300087514798266113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133575638200058343198844075 200363457300087514798266113)
    ·
      refine ⟨150272592975065636098699585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200363457300087514798266113 150272592975065636098699585)
      ·
        refine ⟨112704444731299227074024689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150272592975065636098699585 112704444731299227074024689)
        ·
          refine ⟨84528333548474420305518517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112704444731299227074024689 84528333548474420305518517)
          ·
            refine ⟨7924531270169476903642361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84528333548474420305518517 7924531270169476903642361)
            ·
              refine ⟨5943398452627107677731771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7924531270169476903642361 5943398452627107677731771)
              ·
                refine ⟨8915097678940661516597657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5943398452627107677731771 8915097678940661516597657)
                ·
                  refine ⟨6686323259205496137448243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8915097678940661516597657 6686323259205496137448243)
                  ·
                    refine ⟨10029484888808244206172365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6686323259205496137448243 10029484888808244206172365)
                    ·
                      refine ⟨3761056833303091577314637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10029484888808244206172365 3761056833303091577314637)
                      ·
                        rfl

theorem cell23_7324632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_7324632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324632 prefixEnd_7324632 := by exact prefixLift 7324632
  have htrace : WordTrace (prefixWord ++ tailWord_7324632) baseStart_7324632 baseEnd_7324632 := by
    simpa [prefixWord, tailWord_7324632, baseEnd_7324632] using wordTrace_append hprefix tailTrace_7324632
  have hstable : (prefixWord ++ tailWord_7324632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324632).length < 2 ^ (prefixWord ++ tailWord_7324632).sum := by decide
  have hdescent : baseEnd_7324632 < baseStart_7324632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324642 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_7324642 : Nat := 118140960795 + 7324642 * 2 ^ 59
def prefixEnd_7324642 : Nat := 4983230072969 + 3 ^ 40 * 7324642 * 2
def baseEnd_7324642 : Nat := 3761061968109636538189591

theorem tailTrace_7324642 : CollatzResearch.WordTrace tailWord_7324642 prefixEnd_7324642 3761061968109636538189591 := by
  unfold tailWord_7324642
  simp only [CollatzResearch.WordTrace]
  refine ⟨66787910282520114526388045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178101094086720305403701453 66787910282520114526388045)
  ·
    refine ⟨25045466355945042947395517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66787910282520114526388045 25045466355945042947395517)
    ·
      refine ⟨9392049883479391105273319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25045466355945042947395517 9392049883479391105273319)
      ·
        refine ⟨14088074825219086657909979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9392049883479391105273319 14088074825219086657909979)
        ·
          refine ⟨21132112237828629986864969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14088074825219086657909979 21132112237828629986864969)
          ·
            refine ⟨15849084178371472490148727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21132112237828629986864969 15849084178371472490148727)
            ·
              refine ⟨23773626267557208735223091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15849084178371472490148727 23773626267557208735223091)
              ·
                refine ⟨35660439401335813102834637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23773626267557208735223091 35660439401335813102834637)
                ·
                  refine ⟨13372664775500929913562989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35660439401335813102834637 13372664775500929913562989)
                  ·
                    refine ⟨5014749290812848717586121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13372664775500929913562989 5014749290812848717586121)
                    ·
                      refine ⟨3761061968109636538189591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5014749290812848717586121 3761061968109636538189591)
                      ·
                        rfl

theorem cell23_7324642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_7324642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324642 prefixEnd_7324642 := by exact prefixLift 7324642
  have htrace : WordTrace (prefixWord ++ tailWord_7324642) baseStart_7324642 baseEnd_7324642 := by
    simpa [prefixWord, tailWord_7324642, baseEnd_7324642] using wordTrace_append hprefix tailTrace_7324642
  have hstable : (prefixWord ++ tailWord_7324642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324642).length < 2 ^ (prefixWord ++ tailWord_7324642).sum := by decide
  have hdescent : baseEnd_7324642 < baseStart_7324642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324698 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2]
def baseStart_7324698 : Nat := 118140960795 + 7324698 * 2 ^ 59
def prefixEnd_7324698 : Nat := 4983230072969 + 3 ^ 40 * 7324698 * 2
def baseEnd_7324698 : Nat := 3761090723026288319089333

theorem tailTrace_7324698 : CollatzResearch.WordTrace tailWord_7324698 prefixEnd_7324698 3761090723026288319089333 := by
  unfold tailWord_7324698
  simp only [CollatzResearch.WordTrace]
  refine ⟨66788420904469394917397687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178102455745251719779727165 66788420904469394917397687)
  ·
    refine ⟨100182631356704092376096531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66788420904469394917397687 100182631356704092376096531)
    ·
      refine ⟨150273947035056138564144797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100182631356704092376096531 150273947035056138564144797)
      ·
        refine ⟨56352730138146051961554299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150273947035056138564144797 56352730138146051961554299)
        ·
          refine ⟨84529095207219077942331449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56352730138146051961554299 84529095207219077942331449)
          ·
            refine ⟨63396821405414308456748587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84529095207219077942331449 63396821405414308456748587)
            ·
              refine ⟨95095232108121462685122881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63396821405414308456748587 95095232108121462685122881)
              ·
                refine ⟨71321424081091097013842161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95095232108121462685122881 71321424081091097013842161)
                ·
                  refine ⟨53491068060818322760381621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71321424081091097013842161 53491068060818322760381621)
                  ·
                    refine ⟨5014787630701717758785777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53491068060818322760381621 5014787630701717758785777)
                    ·
                      refine ⟨3761090723026288319089333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5014787630701717758785777 3761090723026288319089333)
                      ·
                        rfl

theorem cell23_7324698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_7324698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324698 prefixEnd_7324698 := by exact prefixLift 7324698
  have htrace : WordTrace (prefixWord ++ tailWord_7324698) baseStart_7324698 baseEnd_7324698 := by
    simpa [prefixWord, tailWord_7324698, baseEnd_7324698] using wordTrace_append hprefix tailTrace_7324698
  have hstable : (prefixWord ++ tailWord_7324698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324698).length < 2 ^ (prefixWord ++ tailWord_7324698).sum := by decide
  have hdescent : baseEnd_7324698 < baseStart_7324698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324708 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_7324708 : Nat := 118140960795 + 7324708 * 2 ^ 59
def prefixEnd_7324708 : Nat := 4983230072969 + 3 ^ 40 * 7324708 * 2
def baseEnd_7324708 : Nat := 1253698619277611093321429

theorem tailTrace_7324708 : CollatzResearch.WordTrace tailWord_7324708 prefixEnd_7324708 1253698619277611093321429 := by
  unfold tailWord_7324708
  simp only [CollatzResearch.WordTrace]
  refine ⟨133577024173920675688727389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178102698898560900918303185 133577024173920675688727389)
  ·
    refine ⟨50091384065220253383272771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133577024173920675688727389 50091384065220253383272771)
    ·
      refine ⟨75137076097830380074909157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50091384065220253383272771 75137076097830380074909157)
      ·
        refine ⟨14088201768343196264045467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75137076097830380074909157 14088201768343196264045467)
        ·
          refine ⟨21132302652514794396068201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14088201768343196264045467 21132302652514794396068201)
          ·
            refine ⟨15849226989386095797051151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21132302652514794396068201 15849226989386095797051151)
            ·
              refine ⟨23773840484079143695576727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15849226989386095797051151 23773840484079143695576727)
              ·
                refine ⟨35660760726118715543365091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23773840484079143695576727 35660760726118715543365091)
                ·
                  refine ⟨53491141089178073315047637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35660760726118715543365091 53491141089178073315047637)
                  ·
                    refine ⟨1253698619277611093321429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53491141089178073315047637 1253698619277611093321429)
                    ·
                      rfl

theorem cell23_7324708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_7324708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324708 prefixEnd_7324708 := by exact prefixLift 7324708
  have htrace : WordTrace (prefixWord ++ tailWord_7324708) baseStart_7324708 baseEnd_7324708 := by
    simpa [prefixWord, tailWord_7324708, baseEnd_7324708] using wordTrace_append hprefix tailTrace_7324708
  have hstable : (prefixWord ++ tailWord_7324708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324708).length < 2 ^ (prefixWord ++ tailWord_7324708).sum := by decide
  have hdescent : baseEnd_7324708 < baseStart_7324708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324731 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 3]
def baseStart_7324731 : Nat := 118140960795 + 7324731 * 2 ^ 59
def prefixEnd_7324731 : Nat := 4983230072969 + 3 ^ 40 * 7324731 * 2
def baseEnd_7324731 : Nat := 3761107667887886689976681

theorem tailTrace_7324731 : CollatzResearch.WordTrace tailWord_7324731 prefixEnd_7324731 3761107667887886689976681 := by
  unfold tailWord_7324731
  simp only [CollatzResearch.WordTrace]
  refine ⟨267154887226758026305542047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178103258151172017537028031 267154887226758026305542047)
  ·
    refine ⟨400732330840137039458313071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267154887226758026305542047 400732330840137039458313071)
    ·
      refine ⟨601098496260205559187469607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400732330840137039458313071 601098496260205559187469607)
      ·
        refine ⟨901647744390308338781204411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601098496260205559187469607 901647744390308338781204411)
        ·
          refine ⟨1352471616585462508171806617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901647744390308338781204411 1352471616585462508171806617)
          ·
            refine ⟨1014353712439096881128854963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1352471616585462508171806617 1014353712439096881128854963)
            ·
              refine ⟨1521530568658645321693282445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014353712439096881128854963 1521530568658645321693282445)
              ·
                refine ⟨570573963246991995634980917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1521530568658645321693282445 570573963246991995634980917)
                ·
                  refine ⟨53491309054405499590779461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 570573963246991995634980917 53491309054405499590779461)
                  ·
                    refine ⟨10029620447701031173271149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53491309054405499590779461 10029620447701031173271149)
                    ·
                      refine ⟨3761107667887886689976681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10029620447701031173271149 3761107667887886689976681)
                      ·
                        rfl

theorem cell23_7324731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 3].length) (baseStart_7324731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324731 prefixEnd_7324731 := by exact prefixLift 7324731
  have htrace : WordTrace (prefixWord ++ tailWord_7324731) baseStart_7324731 baseEnd_7324731 := by
    simpa [prefixWord, tailWord_7324731, baseEnd_7324731] using wordTrace_append hprefix tailTrace_7324731
  have hstable : (prefixWord ++ tailWord_7324731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324731).length < 2 ^ (prefixWord ++ tailWord_7324731).sum := by decide
  have hdescent : baseEnd_7324731 < baseStart_7324731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324789 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 3, 4]
def baseStart_7324789 : Nat := 118140960795 + 7324789 * 2 ^ 59
def prefixEnd_7324789 : Nat := 4983230072969 + 3 ^ 40 * 7324789 * 2
def baseEnd_7324789 : Nat := 1253712483255282487683805

theorem tailTrace_7324789 : CollatzResearch.WordTrace tailWord_7324789 prefixEnd_7324789 1253712483255282487683805 := by
  unfold tailWord_7324789
  simp only [CollatzResearch.WordTrace]
  refine ⟨267157002660547902211153421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178104668440365268140768947 267157002660547902211153421)
  ·
    refine ⟨100183875997705463329182533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267157002660547902211153421 100183875997705463329182533)
    ·
      refine ⟨18784476749569774374221725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100183875997705463329182533 18784476749569774374221725)
      ·
        refine ⟨7044178781088665390333147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18784476749569774374221725 7044178781088665390333147)
        ·
          refine ⟨10566268171632998085499721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7044178781088665390333147 10566268171632998085499721)
          ·
            refine ⟨7924701128724748564124791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10566268171632998085499721 7924701128724748564124791)
            ·
              refine ⟨11887051693087122846187187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7924701128724748564124791 11887051693087122846187187)
              ·
                refine ⟨17830577539630684269280781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11887051693087122846187187 17830577539630684269280781)
                ·
                  refine ⟨6686466577361506600980293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17830577539630684269280781 6686466577361506600980293)
                  ·
                    refine ⟨1253712483255282487683805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6686466577361506600980293 1253712483255282487683805)
                    ·
                      rfl

theorem cell23_7324789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_7324789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324789 prefixEnd_7324789 := by exact prefixLift 7324789
  have htrace : WordTrace (prefixWord ++ tailWord_7324789) baseStart_7324789 baseEnd_7324789 := by
    simpa [prefixWord, tailWord_7324789, baseEnd_7324789] using wordTrace_append hprefix tailTrace_7324789
  have hstable : (prefixWord ++ tailWord_7324789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324789).length < 2 ^ (prefixWord ++ tailWord_7324789).sum := by decide
  have hdescent : baseEnd_7324789 < baseStart_7324789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324811 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 5, 6]
def baseStart_7324811 : Nat := 118140960795 + 7324811 * 2 ^ 59
def prefixEnd_7324811 : Nat := 4983230072969 + 3 ^ 40 * 7324811 * 2
def baseEnd_7324811 : Nat := 1253716248780082125658771

theorem tailTrace_7324811 : CollatzResearch.WordTrace tailWord_7324811 prefixEnd_7324811 1253716248780082125658771 := by
  unfold tailWord_7324811
  simp only [CollatzResearch.WordTrace]
  refine ⟨267157805066468199968454287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178105203377645466645636191 267157805066468199968454287)
  ·
    refine ⟨400736707599702299952681431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267157805066468199968454287 400736707599702299952681431)
    ·
      refine ⟨601105061399553449929022147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400736707599702299952681431 601105061399553449929022147)
      ·
        refine ⟨901657592099330174893533221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601105061399553449929022147 901657592099330174893533221)
        ·
          refine ⟨169060798518624407792537479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 901657592099330174893533221 169060798518624407792537479)
          ·
            refine ⟨253591197777936611688806219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169060798518624407792537479 253591197777936611688806219)
            ·
              refine ⟨380386796666904917533209329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253591197777936611688806219 380386796666904917533209329)
              ·
                refine ⟨285290097500178688149906997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380386796666904917533209329 285290097500178688149906997)
                ·
                  refine ⟨26745946640641752014053781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 285290097500178688149906997 26745946640641752014053781)
                  ·
                    refine ⟨1253716248780082125658771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26745946640641752014053781 1253716248780082125658771)
                    ·
                      rfl

theorem cell23_7324811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 6].length) (baseStart_7324811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324811 prefixEnd_7324811 := by exact prefixLift 7324811
  have htrace : WordTrace (prefixWord ++ tailWord_7324811) baseStart_7324811 baseEnd_7324811 := by
    simpa [prefixWord, tailWord_7324811, baseEnd_7324811] using wordTrace_append hprefix tailTrace_7324811
  have hstable : (prefixWord ++ tailWord_7324811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324811).length < 2 ^ (prefixWord ++ tailWord_7324811).sum := by decide
  have hdescent : baseEnd_7324811 < baseStart_7324811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324828 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 3, 6]
def baseStart_7324828 : Nat := 118140960795 + 7324828 * 2 ^ 59
def prefixEnd_7324828 : Nat := 4983230072969 + 3 ^ 40 * 7324828 * 2
def baseEnd_7324828 : Nat := 1253719158503790936821245

theorem tailTrace_7324828 : CollatzResearch.WordTrace tailWord_7324828 prefixEnd_7324828 1253719158503790936821245 := by
  unfold tailWord_7324828
  simp only [CollatzResearch.WordTrace]
  refine ⟨133579212553703305935911569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178105616738271074581215425 133579212553703305935911569)
  ·
    refine ⟨100184409415277479451933677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133579212553703305935911569 100184409415277479451933677)
    ·
      refine ⟨37569153530729054794475129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100184409415277479451933677 37569153530729054794475129)
      ·
        refine ⟨28176865148046791095856347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37569153530729054794475129 28176865148046791095856347)
        ·
          refine ⟨42265297722070186643784521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28176865148046791095856347 42265297722070186643784521)
          ·
            refine ⟨31698973291552639982838391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42265297722070186643784521 31698973291552639982838391)
            ·
              refine ⟨47548459937328959974257587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31698973291552639982838391 47548459937328959974257587)
              ·
                refine ⟨71322689905993439961386381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47548459937328959974257587 71322689905993439961386381)
                ·
                  refine ⟨26746008714747539985519893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71322689905993439961386381 26746008714747539985519893)
                  ·
                    refine ⟨1253719158503790936821245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26746008714747539985519893 1253719158503790936821245)
                    ·
                      rfl

theorem cell23_7324828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_7324828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324828 prefixEnd_7324828 := by exact prefixLift 7324828
  have htrace : WordTrace (prefixWord ++ tailWord_7324828) baseStart_7324828 baseEnd_7324828 := by
    simpa [prefixWord, tailWord_7324828, baseEnd_7324828] using wordTrace_append hprefix tailTrace_7324828
  have hstable : (prefixWord ++ tailWord_7324828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324828).length < 2 ^ (prefixWord ++ tailWord_7324828).sum := by decide
  have hdescent : baseEnd_7324828 < baseStart_7324828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324862 : List Nat := [4, 2, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_7324862 : Nat := 118140960795 + 7324862 * 2 ^ 59
def prefixEnd_7324862 : Nat := 4983230072969 + 3 ^ 40 * 7324862 * 2
def baseEnd_7324862 : Nat := 1253724977951208559146193

theorem tailTrace_7324862 : CollatzResearch.WordTrace tailWord_7324862 prefixEnd_7324862 1253724977951208559146193 := by
  unfold tailWord_7324862
  simp only [CollatzResearch.WordTrace]
  refine ⟨33394958148660429459820105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178106443459522290452373893 33394958148660429459820105)
  ·
    refine ⟨25046218611495322094865079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33394958148660429459820105 25046218611495322094865079)
    ·
      refine ⟨37569327917242983142297619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25046218611495322094865079 37569327917242983142297619)
      ·
        refine ⟨56353991875864474713446429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37569327917242983142297619 56353991875864474713446429)
        ·
          refine ⟨21132746953449178017542411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56353991875864474713446429 21132746953449178017542411)
          ·
            refine ⟨31699120430173767026313617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21132746953449178017542411 31699120430173767026313617)
            ·
              refine ⟨23774340322630325269735213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31699120430173767026313617 23774340322630325269735213)
              ·
                refine ⟨8915377620986371976150705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23774340322630325269735213 8915377620986371976150705)
                ·
                  refine ⟨6686533215739778982113029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8915377620986371976150705 6686533215739778982113029)
                  ·
                    refine ⟨1253724977951208559146193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6686533215739778982113029 1253724977951208559146193)
                    ·
                      rfl

theorem cell23_7324862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_7324862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324862 prefixEnd_7324862 := by exact prefixLift 7324862
  have htrace : WordTrace (prefixWord ++ tailWord_7324862) baseStart_7324862 baseEnd_7324862 := by
    simpa [prefixWord, tailWord_7324862, baseEnd_7324862] using wordTrace_append hprefix tailTrace_7324862
  have hstable : (prefixWord ++ tailWord_7324862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324862).length < 2 ^ (prefixWord ++ tailWord_7324862).sum := by decide
  have hdescent : baseEnd_7324862 < baseStart_7324862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324928 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 5]
def baseStart_7324928 : Nat := 118140960795 + 7324928 * 2 ^ 59
def prefixEnd_7324928 : Nat := 4983230072969 + 3 ^ 40 * 7324928 * 2
def baseEnd_7324928 : Nat := 3761208823576822419213275

theorem tailTrace_7324928 : CollatzResearch.WordTrace tailWord_7324928 prefixEnd_7324928 3761208823576822419213275 := by
  unfold tailWord_7324928
  simp only [CollatzResearch.WordTrace]
  refine ⟨133581036203522164475231719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178108048271362885966975625 133581036203522164475231719)
  ·
    refine ⟨200371554305283246712847579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133581036203522164475231719 200371554305283246712847579)
    ·
      refine ⟨300557331457924870069271369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200371554305283246712847579 300557331457924870069271369)
      ·
        refine ⟨225417998593443652551953527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300557331457924870069271369 225417998593443652551953527)
        ·
          refine ⟨338126997890165478827930291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225417998593443652551953527 338126997890165478827930291)
          ·
            refine ⟨507190496835248218241895437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338126997890165478827930291 507190496835248218241895437)
            ·
              refine ⟨190196436313218081840710789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507190496835248218241895437 190196436313218081840710789)
              ·
                refine ⟨35661831808728390345133273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190196436313218081840710789 35661831808728390345133273)
                ·
                  refine ⟨26746373856546292758849955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35661831808728390345133273 26746373856546292758849955)
                  ·
                    refine ⟨40119560784819439138274933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26746373856546292758849955 40119560784819439138274933)
                    ·
                      refine ⟨3761208823576822419213275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40119560784819439138274933 3761208823576822419213275)
                      ·
                        rfl

theorem cell23_7324928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_7324928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324928 prefixEnd_7324928 := by exact prefixLift 7324928
  have htrace : WordTrace (prefixWord ++ tailWord_7324928) baseStart_7324928 baseEnd_7324928 := by
    simpa [prefixWord, tailWord_7324928, baseEnd_7324928] using wordTrace_append hprefix tailTrace_7324928
  have hstable : (prefixWord ++ tailWord_7324928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324928).length < 2 ^ (prefixWord ++ tailWord_7324928).sum := by decide
  have hdescent : baseEnd_7324928 < baseStart_7324928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324929 : List Nat := [1, 2, 4, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_7324929 : Nat := 118140960795 + 7324929 * 2 ^ 59
def prefixEnd_7324929 : Nat := 4983230072969 + 3 ^ 40 * 7324929 * 2
def baseEnd_7324929 : Nat := 3761209337057476915300771

theorem tailTrace_7324929 : CollatzResearch.WordTrace tailWord_7324929 prefixEnd_7324929 3761209337057476915300771 := by
  unfold tailWord_7324929
  simp only [CollatzResearch.WordTrace]
  refine ⟨267162108880040706121249841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178108072586693804080833227 267162108880040706121249841)
  ·
    refine ⟨200371581660030529590937381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267162108880040706121249841 200371581660030529590937381)
    ·
      refine ⟨37569671561255724298300759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200371581660030529590937381 37569671561255724298300759)
      ·
        refine ⟨56354507341883586447451139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37569671561255724298300759 56354507341883586447451139)
        ·
          refine ⟨84531761012825379671176709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56354507341883586447451139 84531761012825379671176709)
          ·
            refine ⟨15849705189904758688345633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84531761012825379671176709 15849705189904758688345633)
            ·
              refine ⟨11887278892428569016259225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15849705189904758688345633 11887278892428569016259225)
              ·
                refine ⟨8915459169321426762194419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11887278892428569016259225 8915459169321426762194419)
                ·
                  refine ⟨13373188753982140143291629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8915459169321426762194419 13373188753982140143291629)
                  ·
                    refine ⟨5014945782743302553734361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13373188753982140143291629 5014945782743302553734361)
                    ·
                      refine ⟨3761209337057476915300771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5014945782743302553734361 3761209337057476915300771)
                      ·
                        rfl

theorem cell23_7324929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_7324929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324929 prefixEnd_7324929 := by exact prefixLift 7324929
  have htrace : WordTrace (prefixWord ++ tailWord_7324929) baseStart_7324929 baseEnd_7324929 := by
    simpa [prefixWord, tailWord_7324929, baseEnd_7324929] using wordTrace_append hprefix tailTrace_7324929
  have hstable : (prefixWord ++ tailWord_7324929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324929).length < 2 ^ (prefixWord ++ tailWord_7324929).sum := by decide
  have hdescent : baseEnd_7324929 < baseStart_7324929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7324965 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 7]
def baseStart_7324965 : Nat := 118140960795 + 7324965 * 2 ^ 59
def prefixEnd_7324965 : Nat := 4983230072969 + 3 ^ 40 * 7324965 * 2
def baseEnd_7324965 : Nat := 417914202484559863827845

theorem tailTrace_7324965 : CollatzResearch.WordTrace tailWord_7324965 prefixEnd_7324965 417914202484559863827845 := by
  unfold tailWord_7324965
  simp only [CollatzResearch.WordTrace]
  refine ⟨267163421907910284269560349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178108947938606856179706899 267163421907910284269560349)
  ·
    refine ⟨100186283215466356601085131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267163421907910284269560349 100186283215466356601085131)
    ·
      refine ⟨150279424823199534901627697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100186283215466356601085131 150279424823199534901627697)
      ·
        refine ⟨112709568617399651176220773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150279424823199534901627697 112709568617399651176220773)
        ·
          refine ⟨21133044115762434595541395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112709568617399651176220773 21133044115762434595541395)
          ·
            refine ⟨31699566173643651893312093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21133044115762434595541395 31699566173643651893312093)
            ·
              refine ⟨11887337315116369459992035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31699566173643651893312093 11887337315116369459992035)
              ·
                refine ⟨17831005972674554189988053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11887337315116369459992035 17831005972674554189988053)
                ·
                  refine ⟨417914202484559863827845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17831005972674554189988053 417914202484559863827845)
                  ·
                    rfl

theorem cell23_7324965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 7].length) (baseStart_7324965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7324965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7324965 prefixEnd_7324965 := by exact prefixLift 7324965
  have htrace : WordTrace (prefixWord ++ tailWord_7324965) baseStart_7324965 baseEnd_7324965 := by
    simpa [prefixWord, tailWord_7324965, baseEnd_7324965] using wordTrace_append hprefix tailTrace_7324965
  have hstable : (prefixWord ++ tailWord_7324965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7324965).length < 2 ^ (prefixWord ++ tailWord_7324965).sum := by decide
  have hdescent : baseEnd_7324965 < baseStart_7324965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7324965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325025 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 7, 4]
def baseStart_7325025 : Nat := 118140960795 + 7325025 * 2 ^ 59
def prefixEnd_7325025 : Nat := 4983230072969 + 3 ^ 40 * 7325025 * 2
def baseEnd_7325025 : Nat := 1253752877066769513233443

theorem tailTrace_7325025 : CollatzResearch.WordTrace tailWord_7325025 prefixEnd_7325025 1253752877066769513233443 := by
  unfold tailWord_7325025
  simp only [CollatzResearch.WordTrace]
  refine ⟨267165610287692914516744529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178110406858461943011163019 267165610287692914516744529)
  ·
    refine ⟨200374207715769685887558397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267165610287692914516744529 200374207715769685887558397)
    ·
      refine ⟨75140327893413632207834399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200374207715769685887558397 75140327893413632207834399)
      ·
        refine ⟨112710491840120448311751599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75140327893413632207834399 112710491840120448311751599)
        ·
          refine ⟨169065737760180672467627399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112710491840120448311751599 169065737760180672467627399)
          ·
            refine ⟨253598606640271008701441099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169065737760180672467627399 253598606640271008701441099)
            ·
              refine ⟨380397909960406513052161649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253598606640271008701441099 380397909960406513052161649)
              ·
                refine ⟨285298432470304884789121237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380397909960406513052161649 285298432470304884789121237)
                ·
                  refine ⟨6686682011022770737245029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 285298432470304884789121237 6686682011022770737245029)
                  ·
                    refine ⟨1253752877066769513233443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6686682011022770737245029 1253752877066769513233443)
                    ·
                      rfl

theorem cell23_7325025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_7325025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325025 prefixEnd_7325025 := by exact prefixLift 7325025
  have htrace : WordTrace (prefixWord ++ tailWord_7325025) baseStart_7325025 baseEnd_7325025 := by
    simpa [prefixWord, tailWord_7325025, baseEnd_7325025] using wordTrace_append hprefix tailTrace_7325025
  have hstable : (prefixWord ++ tailWord_7325025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325025).length < 2 ^ (prefixWord ++ tailWord_7325025).sum := by decide
  have hdescent : baseEnd_7325025 < baseStart_7325025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325042 : List Nat := [3, 2, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_7325042 : Nat := 118140960795 + 7325042 * 2 ^ 59
def prefixEnd_7325042 : Nat := 4983230072969 + 3 ^ 40 * 7325042 * 2
def baseEnd_7325042 : Nat := 1253755786790478324395917

theorem tailTrace_7325042 : CollatzResearch.WordTrace tailWord_7325042 prefixEnd_7325042 1253755786790478324395917 := by
  unfold tailWord_7325042
  simp only [CollatzResearch.WordTrace]
  refine ⟨66791557582157831605028345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178110820219087550946742253 66791557582157831605028345)
  ·
    refine ⟨50093668186618373703771259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66791557582157831605028345 50093668186618373703771259)
    ·
      refine ⟨75140502279927560555656889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50093668186618373703771259 75140502279927560555656889)
      ·
        refine ⟨56355376709945670416742667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75140502279927560555656889 56355376709945670416742667)
        ·
          refine ⟨84533065064918505625114001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56355376709945670416742667 84533065064918505625114001)
          ·
            refine ⟨63399798798688879218835501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84533065064918505625114001 63399798798688879218835501)
            ·
              refine ⟨23774924549508329707063313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63399798798688879218835501 23774924549508329707063313)
              ·
                refine ⟨17831193412131247280297485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23774924549508329707063313 17831193412131247280297485)
                ·
                  refine ⟨6686697529549217730111557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17831193412131247280297485 6686697529549217730111557)
                  ·
                    refine ⟨1253755786790478324395917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6686697529549217730111557 1253755786790478324395917)
                    ·
                      rfl

theorem cell23_7325042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_7325042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325042 prefixEnd_7325042 := by exact prefixLift 7325042
  have htrace : WordTrace (prefixWord ++ tailWord_7325042) baseStart_7325042 baseEnd_7325042 := by
    simpa [prefixWord, tailWord_7325042, baseEnd_7325042] using wordTrace_append hprefix tailTrace_7325042
  have hstable : (prefixWord ++ tailWord_7325042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325042).length < 2 ^ (prefixWord ++ tailWord_7325042).sum := by decide
  have hdescent : baseEnd_7325042 < baseStart_7325042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325059 : List Nat := [1, 1, 1, 3, 5, 1, 1, 5, 1, 4]
def baseStart_7325059 : Nat := 118140960795 + 7325059 * 2 ^ 59
def prefixEnd_7325059 : Nat := 4983230072969 + 3 ^ 40 * 7325059 * 2
def baseEnd_7325059 : Nat := 1253758696514187135558391

theorem tailTrace_7325059 : CollatzResearch.WordTrace tailWord_7325059 prefixEnd_7325059 1253758696514187135558391 := by
  unfold tailWord_7325059
  simp only [CollatzResearch.WordTrace]
  refine ⟨267166850369569738323482231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178111233579713158882321487 267166850369569738323482231)
  ·
    refine ⟨400750275554354607485223347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267166850369569738323482231 400750275554354607485223347)
    ·
      refine ⟨601125413331531911227835021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400750275554354607485223347 601125413331531911227835021)
      ·
        refine ⟨225422029999324466710438133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 601125413331531911227835021 225422029999324466710438133)
        ·
          refine ⟨21133315312436668754103575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225422029999324466710438133 21133315312436668754103575)
          ·
            refine ⟨31699972968655003131155363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21133315312436668754103575 31699972968655003131155363)
            ·
              refine ⟨47549959452982504696733045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31699972968655003131155363 47549959452982504696733045)
              ·
                refine ⟨4457808698717109815318723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47549959452982504696733045 4457808698717109815318723)
                ·
                  refine ⟨6686713048075664722978085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4457808698717109815318723 6686713048075664722978085)
                  ·
                    refine ⟨1253758696514187135558391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6686713048075664722978085 1253758696514187135558391)
                    ·
                      rfl

theorem cell23_7325059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 5, 1, 4].length) (baseStart_7325059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325059 prefixEnd_7325059 := by exact prefixLift 7325059
  have htrace : WordTrace (prefixWord ++ tailWord_7325059) baseStart_7325059 baseEnd_7325059 := by
    simpa [prefixWord, tailWord_7325059, baseEnd_7325059] using wordTrace_append hprefix tailTrace_7325059
  have hstable : (prefixWord ++ tailWord_7325059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325059).length < 2 ^ (prefixWord ++ tailWord_7325059).sum := by decide
  have hdescent : baseEnd_7325059 < baseStart_7325059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325076 : List Nat := [2, 4, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_7325076 : Nat := 118140960795 + 7325076 * 2 ^ 59
def prefixEnd_7325076 : Nat := 4983230072969 + 3 ^ 40 * 7325076 * 2
def baseEnd_7325076 : Nat := 1253761606237895946720865

theorem tailTrace_7325076 : CollatzResearch.WordTrace tailWord_7325076 prefixEnd_7325076 1253761606237895946720865 := by
  unfold tailWord_7325076
  simp only [CollatzResearch.WordTrace]
  refine ⟨133583735205254075113425541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178111646940338766817900721 133583735205254075113425541)
  ·
    refine ⟨25046950350985139083767289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133583735205254075113425541 25046950350985139083767289)
    ·
      refine ⟨18785212763238854312825467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25046950350985139083767289 18785212763238854312825467)
      ·
        refine ⟨28177819144858281469238201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18785212763238854312825467 28177819144858281469238201)
        ·
          refine ⟨21133364358643711101928651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28177819144858281469238201 21133364358643711101928651)
          ·
            refine ⟨31700046537965566652892977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21133364358643711101928651 31700046537965566652892977)
            ·
              refine ⟨23775034903474174989669733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31700046537965566652892977 23775034903474174989669733)
              ·
                refine ⟨4457819044401407810563075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23775034903474174989669733 4457819044401407810563075)
                ·
                  refine ⟨6686728566602111715844613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4457819044401407810563075 6686728566602111715844613)
                  ·
                    refine ⟨1253761606237895946720865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6686728566602111715844613 1253761606237895946720865)
                    ·
                      rfl

theorem cell23_7325076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_7325076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325076 prefixEnd_7325076 := by exact prefixLift 7325076
  have htrace : WordTrace (prefixWord ++ tailWord_7325076) baseStart_7325076 baseEnd_7325076 := by
    simpa [prefixWord, tailWord_7325076, baseEnd_7325076] using wordTrace_append hprefix tailTrace_7325076
  have hstable : (prefixWord ++ tailWord_7325076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325076).length < 2 ^ (prefixWord ++ tailWord_7325076).sum := by decide
  have hdescent : baseEnd_7325076 < baseStart_7325076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325109 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_7325109 : Nat := 118140960795 + 7325109 * 2 ^ 59
def prefixEnd_7325109 : Nat := 4983230072969 + 3 ^ 40 * 7325109 * 2
def baseEnd_7325109 : Nat := 3761301763575286211049943

theorem tailTrace_7325109 : CollatzResearch.WordTrace tailWord_7325109 prefixEnd_7325109 3761301763575286211049943 := by
  unfold tailWord_7325109
  simp only [CollatzResearch.WordTrace]
  refine ⟨267168674019388596862802381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178112449346259064575201587 267168674019388596862802381)
  ·
    refine ⟨100188252757270723823550893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267168674019388596862802381 100188252757270723823550893)
    ·
      refine ⟨37570594783976521433831585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100188252757270723823550893 37570594783976521433831585)
      ·
        refine ⟨28177946087982391075373689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37570594783976521433831585 28177946087982391075373689)
        ·
          refine ⟨21133459565986793306530267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28177946087982391075373689 21133459565986793306530267)
          ·
            refine ⟨31700189348980189959795401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21133459565986793306530267 31700189348980189959795401)
            ·
              refine ⟨23775142011735142469846551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31700189348980189959795401 23775142011735142469846551)
              ·
                refine ⟨35662713017602713704769827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23775142011735142469846551 35662713017602713704769827)
                ·
                  refine ⟨53494069526404070557154741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35662713017602713704769827 53494069526404070557154741)
                  ·
                    refine ⟨5015069018100381614733257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53494069526404070557154741 5015069018100381614733257)
                    ·
                      refine ⟨3761301763575286211049943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015069018100381614733257 3761301763575286211049943)
                      ·
                        rfl

theorem cell23_7325109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_7325109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325109 prefixEnd_7325109 := by exact prefixLift 7325109
  have htrace : WordTrace (prefixWord ++ tailWord_7325109) baseStart_7325109 baseEnd_7325109 := by
    simpa [prefixWord, tailWord_7325109, baseEnd_7325109] using wordTrace_append hprefix tailTrace_7325109
  have hstable : (prefixWord ++ tailWord_7325109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325109).length < 2 ^ (prefixWord ++ tailWord_7325109).sum := by decide
  have hdescent : baseEnd_7325109 < baseStart_7325109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325135 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 6]
def baseStart_7325135 : Nat := 118140960795 + 7325135 * 2 ^ 59
def prefixEnd_7325135 : Nat := 4983230072969 + 3 ^ 40 * 7325135 * 2
def baseEnd_7325135 : Nat := 3761315114072303109324823

theorem tailTrace_7325135 : CollatzResearch.WordTrace tailWord_7325135 prefixEnd_7325135 3761315114072303109324823 := by
  unfold tailWord_7325135
  simp only [CollatzResearch.WordTrace]
  refine ⟨267169622317294403303248859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178113081544862935535499239 267169622317294403303248859)
  ·
    refine ⟨400754433475941604954873289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267169622317294403303248859 400754433475941604954873289)
    ·
      refine ⟨300565825106956203716154967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400754433475941604954873289 300565825106956203716154967)
      ·
        refine ⟨450848737660434305574232451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300565825106956203716154967 450848737660434305574232451)
        ·
          refine ⟨676273106490651458361348677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450848737660434305574232451 676273106490651458361348677)
          ·
            refine ⟨126801207466997148442752877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 676273106490651458361348677 126801207466997148442752877)
            ·
              refine ⟨47550452800123930666032329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126801207466997148442752877 47550452800123930666032329)
              ·
                refine ⟨35662839600092947999524247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47550452800123930666032329 35662839600092947999524247)
                ·
                  refine ⟨53494259400139421999286371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35662839600092947999524247 53494259400139421999286371)
                  ·
                    refine ⟨80241389100209132998929557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53494259400139421999286371 80241389100209132998929557)
                    ·
                      refine ⟨3761315114072303109324823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80241389100209132998929557 3761315114072303109324823)
                      ·
                        rfl

theorem cell23_7325135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_7325135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325135 prefixEnd_7325135 := by exact prefixLift 7325135
  have htrace : WordTrace (prefixWord ++ tailWord_7325135) baseStart_7325135 baseEnd_7325135 := by
    simpa [prefixWord, tailWord_7325135, baseEnd_7325135] using wordTrace_append hprefix tailTrace_7325135
  have hstable : (prefixWord ++ tailWord_7325135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325135).length < 2 ^ (prefixWord ++ tailWord_7325135).sum := by decide
  have hdescent : baseEnd_7325135 < baseStart_7325135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325145 : List Nat := [1, 2, 1, 2, 4, 2, 1, 10]
def baseStart_7325145 : Nat := 118140960795 + 7325145 * 2 ^ 59
def prefixEnd_7325145 : Nat := 4983230072969 + 3 ^ 40 * 7325145 * 2
def baseEnd_7325145 : Nat := 139308157365883261859251

theorem tailTrace_7325145 : CollatzResearch.WordTrace tailWord_7325145 prefixEnd_7325145 139308157365883261859251 := by
  unfold tailWord_7325145
  simp only [CollatzResearch.WordTrace]
  refine ⟨267169987047258175011112889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178113324698172116674075259 267169987047258175011112889)
  ·
    refine ⟨200377490285443631258334667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267169987047258175011112889 200377490285443631258334667)
    ·
      refine ⟨300566235428165446887502001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200377490285443631258334667 300566235428165446887502001)
      ·
        refine ⟨225424676571124085165626501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300566235428165446887502001 225424676571124085165626501)
        ·
          refine ⟨42267126857085765968554969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225424676571124085165626501 42267126857085765968554969)
          ·
            refine ⟨31700345142814324476416227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42267126857085765968554969 31700345142814324476416227)
            ·
              refine ⟨47550517714221486714624341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31700345142814324476416227 47550517714221486714624341)
              ·
                refine ⟨139308157365883261859251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47550517714221486714624341 139308157365883261859251)
                ·
                  rfl

theorem cell23_7325145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 10].length) (baseStart_7325145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325145 prefixEnd_7325145 := by exact prefixLift 7325145
  have htrace : WordTrace (prefixWord ++ tailWord_7325145) baseStart_7325145 baseEnd_7325145 := by
    simpa [prefixWord, tailWord_7325145, baseEnd_7325145] using wordTrace_append hprefix tailTrace_7325145
  have hstable : (prefixWord ++ tailWord_7325145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325145).length < 2 ^ (prefixWord ++ tailWord_7325145).sum := by decide
  have hdescent : baseEnd_7325145 < baseStart_7325145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325159 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_7325159 : Nat := 118140960795 + 7325159 * 2 ^ 59
def prefixEnd_7325159 : Nat := 4983230072969 + 3 ^ 40 * 7325159 * 2
def baseEnd_7325159 : Nat := 3761327437608011015424713

theorem tailTrace_7325159 : CollatzResearch.WordTrace tailWord_7325159 prefixEnd_7325159 3761327437608011015424713 := by
  unfold tailWord_7325159
  simp only [CollatzResearch.WordTrace]
  refine ⟨267170497669207455402122531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178113665112804970268081687 267170497669207455402122531)
  ·
    refine ⟨400755746503811183103183797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267170497669207455402122531 400755746503811183103183797)
    ·
      refine ⟨37570851234732298415923481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 400755746503811183103183797 37570851234732298415923481)
      ·
        refine ⟨28178138426049223811942611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37570851234732298415923481 28178138426049223811942611)
        ·
          refine ⟨42267207639073835717913917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28178138426049223811942611 42267207639073835717913917)
          ·
            refine ⟨15850202864652688394217719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42267207639073835717913917 15850202864652688394217719)
            ·
              refine ⟨23775304296979032591326579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15850202864652688394217719 23775304296979032591326579)
              ·
                refine ⟨35662956445468548886989869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23775304296979032591326579 35662956445468548886989869)
                ·
                  refine ⟨13373608667050705832621201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35662956445468548886989869 13373608667050705832621201)
                  ·
                    refine ⟨10030206500288029374465901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13373608667050705832621201 10030206500288029374465901)
                    ·
                      refine ⟨3761327437608011015424713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10030206500288029374465901 3761327437608011015424713)
                      ·
                        rfl

theorem cell23_7325159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_7325159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325159 prefixEnd_7325159 := by exact prefixLift 7325159
  have htrace : WordTrace (prefixWord ++ tailWord_7325159) baseStart_7325159 baseEnd_7325159 := by
    simpa [prefixWord, tailWord_7325159, baseEnd_7325159] using wordTrace_append hprefix tailTrace_7325159
  have hstable : (prefixWord ++ tailWord_7325159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325159).length < 2 ^ (prefixWord ++ tailWord_7325159).sum := by decide
  have hdescent : baseEnd_7325159 < baseStart_7325159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325173 : List Nat := [1, 3, 5, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_7325173 : Nat := 118140960795 + 7325173 * 2 ^ 59
def prefixEnd_7325173 : Nat := 4983230072969 + 3 ^ 40 * 7325173 * 2
def baseEnd_7325173 : Nat := 3761334626337173960649649

theorem tailTrace_7325173 : CollatzResearch.WordTrace tailWord_7325173 prefixEnd_7325173 3761334626337173960649649 := by
  unfold tailWord_7325173
  simp only [CollatzResearch.WordTrace]
  refine ⟨267171008291156735793132173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178114005527437823862088115 267171008291156735793132173)
  ·
    refine ⟨100189128109183775922424565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267171008291156735793132173 100189128109183775922424565)
    ·
      refine ⟨9392730760235978992727303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100189128109183775922424565 9392730760235978992727303)
      ·
        refine ⟨14089096140353968489090955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9392730760235978992727303 14089096140353968489090955)
        ·
          refine ⟨21133644210530952733636433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14089096140353968489090955 21133644210530952733636433)
          ·
            refine ⟨15850233157898214550227325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21133644210530952733636433 15850233157898214550227325)
            ·
              refine ⟨5943837434211830456335247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15850233157898214550227325 5943837434211830456335247)
              ·
                refine ⟨8915756151317745684502871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5943837434211830456335247 8915756151317745684502871)
                ·
                  refine ⟨13373634226976618526754307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8915756151317745684502871 13373634226976618526754307)
                  ·
                    refine ⟨20060451340464927790131461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13373634226976618526754307 20060451340464927790131461)
                    ·
                      refine ⟨3761334626337173960649649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20060451340464927790131461 3761334626337173960649649)
                      ·
                        rfl

theorem cell23_7325173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_7325173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325173 prefixEnd_7325173 := by exact prefixLift 7325173
  have htrace : WordTrace (prefixWord ++ tailWord_7325173) baseStart_7325173 baseEnd_7325173 := by
    simpa [prefixWord, tailWord_7325173, baseEnd_7325173] using wordTrace_append hprefix tailTrace_7325173
  have hstable : (prefixWord ++ tailWord_7325173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325173).length < 2 ^ (prefixWord ++ tailWord_7325173).sum := by decide
  have hdescent : baseEnd_7325173 < baseStart_7325173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325176 : List Nat := [2, 1, 2, 1, 1, 6, 3, 1, 1, 2, 3]
def baseStart_7325176 : Nat := 118140960795 + 7325176 * 2 ^ 59
def prefixEnd_7325176 : Nat := 4983230072969 + 3 ^ 40 * 7325176 * 2
def baseEnd_7325176 : Nat := 3761336166779137448912135

theorem tailTrace_7325176 : CollatzResearch.WordTrace tailWord_7325176 prefixEnd_7325176 3761336166779137448912135 := by
  unfold tailWord_7325176
  simp only [CollatzResearch.WordTrace]
  refine ⟨133585558855072933652745691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178114078473430578203660921 133585558855072933652745691)
  ·
    refine ⟨200378338282609400479118537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133585558855072933652745691 200378338282609400479118537)
    ·
      refine ⟨150283753711957050359338903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200378338282609400479118537 150283753711957050359338903)
      ·
        refine ⟨225425630567935575539008355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150283753711957050359338903 225425630567935575539008355)
        ·
          refine ⟨338138445851903363308512533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225425630567935575539008355 338138445851903363308512533)
          ·
            refine ⟨15850239649307970155086525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 338138445851903363308512533 15850239649307970155086525)
            ·
              refine ⟨5943839868490488808157447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15850239649307970155086525 5943839868490488808157447)
              ·
                refine ⟨8915759802735733212236171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5943839868490488808157447 8915759802735733212236171)
                ·
                  refine ⟨13373639704103599818354257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8915759802735733212236171 13373639704103599818354257)
                  ·
                    refine ⟨10030229778077699863765693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13373639704103599818354257 10030229778077699863765693)
                    ·
                      refine ⟨3761336166779137448912135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10030229778077699863765693 3761336166779137448912135)
                      ·
                        rfl

theorem cell23_7325176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 1, 2, 3].length) (baseStart_7325176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325176 prefixEnd_7325176 := by exact prefixLift 7325176
  have htrace : WordTrace (prefixWord ++ tailWord_7325176) baseStart_7325176 baseEnd_7325176 := by
    simpa [prefixWord, tailWord_7325176, baseEnd_7325176] using wordTrace_append hprefix tailTrace_7325176
  have hstable : (prefixWord ++ tailWord_7325176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325176).length < 2 ^ (prefixWord ++ tailWord_7325176).sum := by decide
  have hdescent : baseEnd_7325176 < baseStart_7325176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325212 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_7325212 : Nat := 118140960795 + 7325212 * 2 ^ 59
def prefixEnd_7325212 : Nat := 4983230072969 + 3 ^ 40 * 7325212 * 2
def baseEnd_7325212 : Nat := 3761354652082699308061969

theorem tailTrace_7325212 : CollatzResearch.WordTrace tailWord_7325212 prefixEnd_7325212 3761354652082699308061969 := by
  unfold tailWord_7325212
  simp only [CollatzResearch.WordTrace]
  refine ⟨133586215369007722726900945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178114953825343630302534593 133586215369007722726900945)
  ·
    refine ⟨100189661526755792045175709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133586215369007722726900945 100189661526755792045175709)
    ·
      refine ⟨37571123072533422016940891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100189661526755792045175709 37571123072533422016940891)
      ·
        refine ⟨56356684608800133025411337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37571123072533422016940891 56356684608800133025411337)
        ·
          refine ⟨42267513456600099769058503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56356684608800133025411337 42267513456600099769058503)
          ·
            refine ⟨63401270184900149653587755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42267513456600099769058503 63401270184900149653587755)
            ·
              refine ⟨95101905277350224480381633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63401270184900149653587755 95101905277350224480381633)
              ·
                refine ⟨71326428958012668360286225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95101905277350224480381633 71326428958012668360286225)
                ·
                  refine ⟨53494821718509501270214669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71326428958012668360286225 53494821718509501270214669)
                  ·
                    refine ⟨20060558144441062976330501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53494821718509501270214669 20060558144441062976330501)
                    ·
                      refine ⟨3761354652082699308061969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20060558144441062976330501 3761354652082699308061969)
                      ·
                        rfl

theorem cell23_7325212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_7325212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325212 prefixEnd_7325212 := by exact prefixLift 7325212
  have htrace : WordTrace (prefixWord ++ tailWord_7325212) baseStart_7325212 baseEnd_7325212 := by
    simpa [prefixWord, tailWord_7325212, baseEnd_7325212] using wordTrace_append hprefix tailTrace_7325212
  have hstable : (prefixWord ++ tailWord_7325212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325212).length < 2 ^ (prefixWord ++ tailWord_7325212).sum := by decide
  have hdescent : baseEnd_7325212 < baseStart_7325212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325216 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 3, 3, 2]
def baseStart_7325216 : Nat := 118140960795 + 7325216 * 2 ^ 59
def prefixEnd_7325216 : Nat := 4983230072969 + 3 ^ 40 * 7325216 * 2
def baseEnd_7325216 : Nat := 3761356706005317292411951

theorem tailTrace_7325216 : CollatzResearch.WordTrace tailWord_7325216 prefixEnd_7325216 3761356706005317292411951 := by
  unfold tailWord_7325216
  simp only [CollatzResearch.WordTrace]
  refine ⟨133586288315000477068473751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178115051086667302757965001 133586288315000477068473751)
  ·
    refine ⟨200379432472500715602710627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133586288315000477068473751 200379432472500715602710627)
    ·
      refine ⟨300569148708751073404065941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200379432472500715602710627 300569148708751073404065941)
      ·
        refine ⟨14089178845722706565815591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 300569148708751073404065941 14089178845722706565815591)
        ·
          refine ⟨21133768268584059848723387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14089178845722706565815591 21133768268584059848723387)
          ·
            refine ⟨31700652402876089773085081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21133768268584059848723387 31700652402876089773085081)
            ·
              refine ⟨23775489302157067329813811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31700652402876089773085081 23775489302157067329813811)
              ·
                refine ⟨35663233953235600994720717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23775489302157067329813811 35663233953235600994720717)
                ·
                  refine ⟨13373712732463350373020269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35663233953235600994720717 13373712732463350373020269)
                  ·
                    refine ⟨5015142274673756389882601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13373712732463350373020269 5015142274673756389882601)
                    ·
                      refine ⟨3761356706005317292411951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015142274673756389882601 3761356706005317292411951)
                      ·
                        rfl

theorem cell23_7325216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_7325216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325216 prefixEnd_7325216 := by exact prefixLift 7325216
  have htrace : WordTrace (prefixWord ++ tailWord_7325216) baseStart_7325216 baseEnd_7325216 := by
    simpa [prefixWord, tailWord_7325216, baseEnd_7325216] using wordTrace_append hprefix tailTrace_7325216
  have hstable : (prefixWord ++ tailWord_7325216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325216).length < 2 ^ (prefixWord ++ tailWord_7325216).sum := by decide
  have hdescent : baseEnd_7325216 < baseStart_7325216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325242 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_7325242 : Nat := 118140960795 + 7325242 * 2 ^ 59
def prefixEnd_7325242 : Nat := 4983230072969 + 3 ^ 40 * 7325242 * 2
def baseEnd_7325242 : Nat := 3761370056502334190686831

theorem tailTrace_7325242 : CollatzResearch.WordTrace tailWord_7325242 prefixEnd_7325242 3761370056502334190686831 := by
  unfold tailWord_7325242
  simp only [CollatzResearch.WordTrace]
  refine ⟨66793381231976690144348495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178115683285271173718262653 66793381231976690144348495)
  ·
    refine ⟨100190071847965035216522743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66793381231976690144348495 100190071847965035216522743)
    ·
      refine ⟨150285107771947552824784115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100190071847965035216522743 150285107771947552824784115)
      ·
        refine ⟨225427661657921329237176173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150285107771947552824784115 225427661657921329237176173)
        ·
          refine ⟨84535373121720498463941065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225427661657921329237176173 84535373121720498463941065)
          ·
            refine ⟨63401529841290373847955799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84535373121720498463941065 63401529841290373847955799)
            ·
              refine ⟨95102294761935560771933699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63401529841290373847955799 95102294761935560771933699)
              ·
                refine ⟨142653442142903341157900549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95102294761935560771933699 142653442142903341157900549)
                ·
                  refine ⟨26747520401794376467106353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142653442142903341157900549 26747520401794376467106353)
                  ·
                    refine ⟨20060640301345782350329765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26747520401794376467106353 20060640301345782350329765)
                    ·
                      refine ⟨3761370056502334190686831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20060640301345782350329765 3761370056502334190686831)
                      ·
                        rfl

theorem cell23_7325242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_7325242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325242 prefixEnd_7325242 := by exact prefixLift 7325242
  have htrace : WordTrace (prefixWord ++ tailWord_7325242) baseStart_7325242 baseEnd_7325242 := by
    simpa [prefixWord, tailWord_7325242, baseEnd_7325242] using wordTrace_append hprefix tailTrace_7325242
  have hstable : (prefixWord ++ tailWord_7325242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325242).length < 2 ^ (prefixWord ++ tailWord_7325242).sum := by decide
  have hdescent : baseEnd_7325242 < baseStart_7325242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325292 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_7325292 : Nat := 118140960795 + 7325292 * 2 ^ 59
def prefixEnd_7325292 : Nat := 4983230072969 + 3 ^ 40 * 7325292 * 2
def baseEnd_7325292 : Nat := 3761395730535058995061601

theorem tailTrace_7325292 : CollatzResearch.WordTrace tailWord_7325292 prefixEnd_7325292 3761395730535058995061601 := by
  unfold tailWord_7325292
  simp only [CollatzResearch.WordTrace]
  refine ⟨133587674288862809558357065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178116899051817079411142753 133587674288862809558357065)
  ·
    refine ⟨100190755716647107168767799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133587674288862809558357065 100190755716647107168767799)
    ·
      refine ⟨150286133574970660753151699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100190755716647107168767799 150286133574970660753151699)
      ·
        refine ⟨225429200362455991129727549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150286133574970660753151699 225429200362455991129727549)
        ·
          refine ⟨84535950135920996673647831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225429200362455991129727549 84535950135920996673647831)
          ·
            refine ⟨126803925203881495010471747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84535950135920996673647831 126803925203881495010471747)
            ·
              refine ⟨190205887805822242515707621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126803925203881495010471747 190205887805822242515707621)
              ·
                refine ⟨35663603963591670471695179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190205887805822242515707621 35663603963591670471695179)
                ·
                  refine ⟨53495405945387505707542769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35663603963591670471695179 53495405945387505707542769)
                  ·
                    refine ⟨40121554459040629280657077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53495405945387505707542769 40121554459040629280657077)
                    ·
                      refine ⟨3761395730535058995061601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40121554459040629280657077 3761395730535058995061601)
                      ·
                        rfl

theorem cell23_7325292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_7325292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325292 prefixEnd_7325292 := by exact prefixLift 7325292
  have htrace : WordTrace (prefixWord ++ tailWord_7325292) baseStart_7325292 baseEnd_7325292 := by
    simpa [prefixWord, tailWord_7325292, baseEnd_7325292] using wordTrace_append hprefix tailTrace_7325292
  have hstable : (prefixWord ++ tailWord_7325292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325292).length < 2 ^ (prefixWord ++ tailWord_7325292).sum := by decide
  have hdescent : baseEnd_7325292 < baseStart_7325292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325309 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_7325309 : Nat := 118140960795 + 7325309 * 2 ^ 59
def prefixEnd_7325309 : Nat := 4983230072969 + 3 ^ 40 * 7325309 * 2
def baseEnd_7325309 : Nat := 3761404459706185428549023

theorem tailTrace_7325309 : CollatzResearch.WordTrace tailWord_7325309 prefixEnd_7325309 3761404459706185428549023 := by
  unfold tailWord_7325309
  simp only [CollatzResearch.WordTrace]
  refine ⟨267175968618664031020082981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178117312412442687346721987 267175968618664031020082981)
  ·
    refine ⟨50095494115999505816265559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267175968618664031020082981 50095494115999505816265559)
    ·
      refine ⟨75143241173999258724398339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50095494115999505816265559 75143241173999258724398339)
      ·
        refine ⟨112714861760998888086597509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75143241173999258724398339 112714861760998888086597509)
        ·
          refine ⟨21134036580187291516237033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112714861760998888086597509 21134036580187291516237033)
          ·
            refine ⟨15850527435140468637177775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21134036580187291516237033 15850527435140468637177775)
            ·
              refine ⟨23775791152710702955766663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15850527435140468637177775 23775791152710702955766663)
              ·
                refine ⟨35663686729066054433649995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23775791152710702955766663 35663686729066054433649995)
                ·
                  refine ⟨53495530093599081650474993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35663686729066054433649995 53495530093599081650474993)
                  ·
                    refine ⟨40121647570199311237856245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53495530093599081650474993 40121647570199311237856245)
                    ·
                      refine ⟨3761404459706185428549023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40121647570199311237856245 3761404459706185428549023)
                      ·
                        rfl

theorem cell23_7325309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_7325309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325309 prefixEnd_7325309 := by exact prefixLift 7325309
  have htrace : WordTrace (prefixWord ++ tailWord_7325309) baseStart_7325309 baseEnd_7325309 := by
    simpa [prefixWord, tailWord_7325309, baseEnd_7325309] using wordTrace_append hprefix tailTrace_7325309
  have hstable : (prefixWord ++ tailWord_7325309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325309).length < 2 ^ (prefixWord ++ tailWord_7325309).sum := by decide
  have hdescent : baseEnd_7325309 < baseStart_7325309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325336 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 2, 1, 4]
def baseStart_7325336 : Nat := 118140960795 + 7325336 * 2 ^ 59
def prefixEnd_7325336 : Nat := 4983230072969 + 3 ^ 40 * 7325336 * 2
def baseEnd_7325336 : Nat := 3761418323683856822911399

theorem tailTrace_7325336 : CollatzResearch.WordTrace tailWord_7325336 prefixEnd_7325336 3761418323683856822911399 := by
  unfold tailWord_7325336
  simp only [CollatzResearch.WordTrace]
  refine ⟨133588476694783107315657931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178117968926377476420877241 133588476694783107315657931)
  ·
    refine ⟨200382715042174660973486897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133588476694783107315657931 200382715042174660973486897)
    ·
      refine ⟨150287036281630995730115173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200382715042174660973486897 150287036281630995730115173)
      ·
        refine ⟨28178819302805811699396595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150287036281630995730115173 28178819302805811699396595)
        ·
          refine ⟨42268228954208717549094893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28178819302805811699396595 42268228954208717549094893)
          ·
            refine ⟨15850585857828269080910585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42268228954208717549094893 15850585857828269080910585)
            ·
              refine ⟨11887939393371201810682939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15850585857828269080910585 11887939393371201810682939)
              ·
                refine ⟨17831909090056802716024409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11887939393371201810682939 17831909090056802716024409)
                ·
                  refine ⟨13373931817542602037018307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17831909090056802716024409 13373931817542602037018307)
                  ·
                    refine ⟨20060897726313903055527461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13373931817542602037018307 20060897726313903055527461)
                    ·
                      refine ⟨3761418323683856822911399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20060897726313903055527461 3761418323683856822911399)
                      ·
                        rfl

theorem cell23_7325336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_7325336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325336 prefixEnd_7325336 := by exact prefixLift 7325336
  have htrace : WordTrace (prefixWord ++ tailWord_7325336) baseStart_7325336 baseEnd_7325336 := by
    simpa [prefixWord, tailWord_7325336, baseEnd_7325336] using wordTrace_append hprefix tailTrace_7325336
  have hstable : (prefixWord ++ tailWord_7325336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325336).length < 2 ^ (prefixWord ++ tailWord_7325336).sum := by decide
  have hdescent : baseEnd_7325336 < baseStart_7325336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325359 : List Nat := [1, 1, 2, 1, 2, 4, 4, 2, 6]
def baseStart_7325359 : Nat := 118140960795 + 7325359 * 2 ^ 59
def prefixEnd_7325359 : Nat := 4983230072969 + 3 ^ 40 * 7325359 * 2
def baseEnd_7325359 : Nat := 417936681526545581435977

theorem tailTrace_7325359 : CollatzResearch.WordTrace tailWord_7325359 prefixEnd_7325359 417936681526545581435977 := by
  unfold tailWord_7325359
  simp only [CollatzResearch.WordTrace]
  refine ⟨267177792268482889559403131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178118528178988593039602087 267177792268482889559403131)
  ·
    refine ⟨400766688402724334339104697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267177792268482889559403131 400766688402724334339104697)
    ·
      refine ⟨300575016302043250754328523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400766688402724334339104697 300575016302043250754328523)
      ·
        refine ⟨450862524453064876131492785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300575016302043250754328523 450862524453064876131492785)
        ·
          refine ⟨338146893339798657098619589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450862524453064876131492785 338146893339798657098619589)
          ·
            refine ⟨63402542501212248205991173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338146893339798657098619589 63402542501212248205991173)
            ·
              refine ⟨11887976718977296538623345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63402542501212248205991173 11887976718977296538623345)
              ·
                refine ⟨8915982539232972403967509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11887976718977296538623345 8915982539232972403967509)
                ·
                  refine ⟨417936681526545581435977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8915982539232972403967509 417936681526545581435977)
                  ·
                    rfl

theorem cell23_7325359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 6].length) (baseStart_7325359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325359 prefixEnd_7325359 := by exact prefixLift 7325359
  have htrace : WordTrace (prefixWord ++ tailWord_7325359) baseStart_7325359 baseEnd_7325359 := by
    simpa [prefixWord, tailWord_7325359, baseEnd_7325359] using wordTrace_append hprefix tailTrace_7325359
  have hstable : (prefixWord ++ tailWord_7325359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325359).length < 2 ^ (prefixWord ++ tailWord_7325359).sum := by decide
  have hdescent : baseEnd_7325359 < baseStart_7325359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325443 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 3, 2, 2]
def baseStart_7325443 : Nat := 118140960795 + 7325443 * 2 ^ 59
def prefixEnd_7325443 : Nat := 4983230072969 + 3 ^ 40 * 7325443 * 2
def baseEnd_7325443 : Nat := 3761473266113887904273407

theorem tailTrace_7325443 : CollatzResearch.WordTrace tailWord_7325443 prefixEnd_7325443 3761473266113887904273407 := by
  unfold tailWord_7325443
  simp only [CollatzResearch.WordTrace]
  refine ⟨267180856000178571905460983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178120570666785714603640655 267180856000178571905460983)
  ·
    refine ⟨400771284000267857858191475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267180856000178571905460983 400771284000267857858191475)
    ·
      refine ⟨601156926000401786787287213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400771284000267857858191475 601156926000401786787287213)
      ·
        refine ⟨225433847250150670045232705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 601156926000401786787287213 225433847250150670045232705)
        ·
          refine ⟨169075385437613002533924529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225433847250150670045232705 169075385437613002533924529)
          ·
            refine ⟨126806539078209751900443397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169075385437613002533924529 126806539078209751900443397)
            ·
              refine ⟨23776226077164328481333137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126806539078209751900443397 23776226077164328481333137)
              ·
                refine ⟨17832169557873246360999853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23776226077164328481333137 17832169557873246360999853)
                ·
                  refine ⟨6687063584202467385374945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17832169557873246360999853 6687063584202467385374945)
                  ·
                    refine ⟨5015297688151850539031209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6687063584202467385374945 5015297688151850539031209)
                    ·
                      refine ⟨3761473266113887904273407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015297688151850539031209 3761473266113887904273407)
                      ·
                        rfl

theorem cell23_7325443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 2, 2].length) (baseStart_7325443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325443 prefixEnd_7325443 := by exact prefixLift 7325443
  have htrace : WordTrace (prefixWord ++ tailWord_7325443) baseStart_7325443 baseEnd_7325443 := by
    simpa [prefixWord, tailWord_7325443, baseEnd_7325443] using wordTrace_append hprefix tailTrace_7325443
  have hstable : (prefixWord ++ tailWord_7325443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325443).length < 2 ^ (prefixWord ++ tailWord_7325443).sum := by decide
  have hdescent : baseEnd_7325443 < baseStart_7325443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325463 : List Nat := [1, 1, 3, 4, 2, 1, 2, 3, 1, 2, 3]
def baseStart_7325463 : Nat := 118140960795 + 7325463 * 2 ^ 59
def prefixEnd_7325463 : Nat := 4983230072969 + 3 ^ 40 * 7325463 * 2
def baseEnd_7325463 : Nat := 3761483535726977826023315

theorem tailTrace_7325463 : CollatzResearch.WordTrace tailWord_7325463 prefixEnd_7325463 3761483535726977826023315 := by
  unfold tailWord_7325463
  simp only [CollatzResearch.WordTrace]
  refine ⟨267181585460106115321189043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178121056973404076880792695 267181585460106115321189043)
  ·
    refine ⟨400772378190159172981783565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267181585460106115321189043 400772378190159172981783565)
    ·
      refine ⟨150289641821309689868168837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400772378190159172981783565 150289641821309689868168837)
      ·
        refine ⟨28179307841495566850281657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150289641821309689868168837 28179307841495566850281657)
        ·
          refine ⟨21134480881121675137711243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28179307841495566850281657 21134480881121675137711243)
          ·
            refine ⟨31701721321682512706566865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21134480881121675137711243 31701721321682512706566865)
            ·
              refine ⟨23776290991261884529925149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31701721321682512706566865 23776290991261884529925149)
              ·
                refine ⟨8916109121723206698721931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23776290991261884529925149 8916109121723206698721931)
                ·
                  refine ⟨13374163682584810048082897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8916109121723206698721931 13374163682584810048082897)
                  ·
                    refine ⟨10030622761938607536062173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13374163682584810048082897 10030622761938607536062173)
                    ·
                      refine ⟨3761483535726977826023315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10030622761938607536062173 3761483535726977826023315)
                      ·
                        rfl

theorem cell23_7325463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_7325463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325463 prefixEnd_7325463 := by exact prefixLift 7325463
  have htrace : WordTrace (prefixWord ++ tailWord_7325463) baseStart_7325463 baseEnd_7325463 := by
    simpa [prefixWord, tailWord_7325463, baseEnd_7325463] using wordTrace_append hprefix tailTrace_7325463
  have hstable : (prefixWord ++ tailWord_7325463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325463).length < 2 ^ (prefixWord ++ tailWord_7325463).sum := by decide
  have hdescent : baseEnd_7325463 < baseStart_7325463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325497 : List Nat := [1, 2, 1, 7, 1, 2, 1, 2, 1, 2, 3]
def baseStart_7325497 : Nat := 118140960795 + 7325497 * 2 ^ 59
def prefixEnd_7325497 : Nat := 4983230072969 + 3 ^ 40 * 7325497 * 2
def baseEnd_7325497 : Nat := 3761500994069230692998159

theorem tailTrace_7325497 : CollatzResearch.WordTrace tailWord_7325497 prefixEnd_7325497 3761500994069230692998159 := by
  unfold tailWord_7325497
  simp only [CollatzResearch.WordTrace]
  refine ⟨267182825541982939127926745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178121883694655292751951163 267182825541982939127926745)
  ·
    refine ⟨200387119156487204345945059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267182825541982939127926745 200387119156487204345945059)
    ·
      refine ⟨300580678734730806518917589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200387119156487204345945059 300580678734730806518917589)
      ·
        refine ⟨7044859657845253277787131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 300580678734730806518917589 7044859657845253277787131)
        ·
          refine ⟨10567289486767879916680697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7044859657845253277787131 10567289486767879916680697)
          ·
            refine ⟨7925467115075909937510523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10567289486767879916680697 7925467115075909937510523)
            ·
              refine ⟨11888200672613864906265785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7925467115075909937510523 11888200672613864906265785)
              ·
                refine ⟨8916150504460398679699339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11888200672613864906265785 8916150504460398679699339)
                ·
                  refine ⟨13374225756690598019549009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8916150504460398679699339 13374225756690598019549009)
                  ·
                    refine ⟨10030669317517948514661757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13374225756690598019549009 10030669317517948514661757)
                    ·
                      refine ⟨3761500994069230692998159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10030669317517948514661757 3761500994069230692998159)
                      ·
                        rfl

theorem cell23_7325497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_7325497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325497 prefixEnd_7325497 := by exact prefixLift 7325497
  have htrace : WordTrace (prefixWord ++ tailWord_7325497) baseStart_7325497 baseEnd_7325497 := by
    simpa [prefixWord, tailWord_7325497, baseEnd_7325497] using wordTrace_append hprefix tailTrace_7325497
  have hstable : (prefixWord ++ tailWord_7325497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325497).length < 2 ^ (prefixWord ++ tailWord_7325497).sum := by decide
  have hdescent : baseEnd_7325497 < baseStart_7325497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325510 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_7325510 : Nat := 118140960795 + 7325510 * 2 ^ 59
def prefixEnd_7325510 : Nat := 4983230072969 + 3 ^ 40 * 7325510 * 2
def baseEnd_7325510 : Nat := 3761507669317739142135599

theorem tailTrace_7325510 : CollatzResearch.WordTrace tailWord_7325510 prefixEnd_7325510 3761507669317739142135599 := by
  unfold tailWord_7325510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8349478115341745073379687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178122199793957228232099989 8349478115341745073379687)
  ·
    refine ⟨12524217173012617610069531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8349478115341745073379687 12524217173012617610069531)
    ·
      refine ⟨18786325759518926415104297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12524217173012617610069531 18786325759518926415104297)
      ·
        refine ⟨14089744319639194811328223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18786325759518926415104297 14089744319639194811328223)
        ·
          refine ⟨21134616479458792216992335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14089744319639194811328223 21134616479458792216992335)
          ·
            refine ⟨31701924719188188325488503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21134616479458792216992335 31701924719188188325488503)
            ·
              refine ⟨47552887078782282488232755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31701924719188188325488503 47552887078782282488232755)
              ·
                refine ⟨71329330618173423732349133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47552887078782282488232755 71329330618173423732349133)
                ·
                  refine ⟨26748498981815033899630925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71329330618173423732349133 26748498981815033899630925)
                  ·
                    refine ⟨10030687118180637712361597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26748498981815033899630925 10030687118180637712361597)
                    ·
                      refine ⟨3761507669317739142135599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10030687118180637712361597 3761507669317739142135599)
                      ·
                        rfl

theorem cell23_7325510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_7325510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325510 prefixEnd_7325510 := by exact prefixLift 7325510
  have htrace : WordTrace (prefixWord ++ tailWord_7325510) baseStart_7325510 baseEnd_7325510 := by
    simpa [prefixWord, tailWord_7325510, baseEnd_7325510] using wordTrace_append hprefix tailTrace_7325510
  have hstable : (prefixWord ++ tailWord_7325510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325510).length < 2 ^ (prefixWord ++ tailWord_7325510).sum := by decide
  have hdescent : baseEnd_7325510 < baseStart_7325510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325536 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 3]
def baseStart_7325536 : Nat := 118140960795 + 7325536 * 2 ^ 59
def prefixEnd_7325536 : Nat := 4983230072969 + 3 ^ 40 * 7325536 * 2
def baseEnd_7325536 : Nat := 3761521019814756040410479

theorem tailTrace_7325536 : CollatzResearch.WordTrace tailWord_7325536 prefixEnd_7325536 3761521019814756040410479 := by
  unfold tailWord_7325536
  simp only [CollatzResearch.WordTrace]
  refine ⟨133592123994420824394298231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178122831992561099192397641 133592123994420824394298231)
  ·
    refine ⟨200388185991631236591447347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133592123994420824394298231 200388185991631236591447347)
    ·
      refine ⟨300582278987446854887171021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200388185991631236591447347 300582278987446854887171021)
      ·
        refine ⟨112718354620292570582689133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300582278987446854887171021 112718354620292570582689133)
        ·
          refine ⟨42269382982609713968508425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112718354620292570582689133 42269382982609713968508425)
          ·
            refine ⟨31702037236957285476381319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42269382982609713968508425 31702037236957285476381319)
            ·
              refine ⟨47553055855435928214571979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31702037236957285476381319 47553055855435928214571979)
              ·
                refine ⟨71329583783153892321857969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47553055855435928214571979 71329583783153892321857969)
                ·
                  refine ⟨53497187837365419241393477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71329583783153892321857969 53497187837365419241393477)
                  ·
                    refine ⟨10030722719506016107761277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53497187837365419241393477 10030722719506016107761277)
                    ·
                      refine ⟨3761521019814756040410479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10030722719506016107761277 3761521019814756040410479)
                      ·
                        rfl

theorem cell23_7325536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_7325536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325536 prefixEnd_7325536 := by exact prefixLift 7325536
  have htrace : WordTrace (prefixWord ++ tailWord_7325536) baseStart_7325536 baseEnd_7325536 := by
    simpa [prefixWord, tailWord_7325536, baseEnd_7325536] using wordTrace_append hprefix tailTrace_7325536
  have hstable : (prefixWord ++ tailWord_7325536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325536).length < 2 ^ (prefixWord ++ tailWord_7325536).sum := by decide
  have hdescent : baseEnd_7325536 < baseStart_7325536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325550 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_7325550 : Nat := 118140960795 + 7325550 * 2 ^ 59
def prefixEnd_7325550 : Nat := 4983230072969 + 3 ^ 40 * 7325550 * 2
def baseEnd_7325550 : Nat := 3761528208543918985635415

theorem tailTrace_7325550 : CollatzResearch.WordTrace tailWord_7325550 prefixEnd_7325550 3761528208543918985635415 := by
  unfold tailWord_7325550
  simp only [CollatzResearch.WordTrace]
  refine ⟨33398094826348866147450763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178123172407193952786404069 33398094826348866147450763)
  ·
    refine ⟨50097142239523299221176145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33398094826348866147450763 50097142239523299221176145)
    ·
      refine ⟨37572856679642474415882109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50097142239523299221176145 37572856679642474415882109)
      ·
        refine ⟨14089821254865927905955791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37572856679642474415882109 14089821254865927905955791)
        ·
          refine ⟨21134731882298891858933687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14089821254865927905955791 21134731882298891858933687)
          ·
            refine ⟨31702097823448337788400531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21134731882298891858933687 31702097823448337788400531)
            ·
              refine ⟨47553146735172506682600797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31702097823448337788400531 47553146735172506682600797)
              ·
                refine ⟨17832430025689690005975299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47553146735172506682600797 17832430025689690005975299)
                ·
                  refine ⟨26748645038534535008962949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17832430025689690005975299 26748645038534535008962949)
                  ·
                    refine ⟨5015370944725225314180553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26748645038534535008962949 5015370944725225314180553)
                    ·
                      refine ⟨3761528208543918985635415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015370944725225314180553 3761528208543918985635415)
                      ·
                        rfl

theorem cell23_7325550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_7325550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325550 prefixEnd_7325550 := by exact prefixLift 7325550
  have htrace : WordTrace (prefixWord ++ tailWord_7325550) baseStart_7325550 baseEnd_7325550 := by
    simpa [prefixWord, tailWord_7325550, baseEnd_7325550] using wordTrace_append hprefix tailTrace_7325550
  have hstable : (prefixWord ++ tailWord_7325550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325550).length < 2 ^ (prefixWord ++ tailWord_7325550).sum := by decide
  have hdescent : baseEnd_7325550 < baseStart_7325550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325573 : List Nat := [1, 3, 1, 1, 3, 2, 4, 3, 5]
def baseStart_7325573 : Nat := 118140960795 + 7325573 * 2 ^ 59
def prefixEnd_7325573 : Nat := 4983230072969 + 3 ^ 40 * 7325573 * 2
def baseEnd_7325573 : Nat := 417948890955441377294201

theorem tailTrace_7325573 : CollatzResearch.WordTrace tailWord_7325573 prefixEnd_7325573 417948890955441377294201 := by
  unfold tailWord_7325573
  simp only [CollatzResearch.WordTrace]
  refine ⟨267185597489707604107693373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178123731659805069405128915 267185597489707604107693373)
  ·
    refine ⟨100194599058640351540385015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267185597489707604107693373 100194599058640351540385015)
    ·
      refine ⟨150291898587960527310577523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100194599058640351540385015 150291898587960527310577523)
      ·
        refine ⟨225437847881940790965866285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150291898587960527310577523 225437847881940790965866285)
        ·
          refine ⟨84539192955727796612199857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225437847881940790965866285 84539192955727796612199857)
          ·
            refine ⟨63404394716795847459149893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84539192955727796612199857 63404394716795847459149893)
            ·
              refine ⟨11888324009399221398590605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63404394716795847459149893 11888324009399221398590605)
              ·
                refine ⟨4458121503524708024471477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11888324009399221398590605 4458121503524708024471477)
                ·
                  refine ⟨417948890955441377294201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4458121503524708024471477 417948890955441377294201)
                  ·
                    rfl

theorem cell23_7325573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 5].length) (baseStart_7325573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325573 prefixEnd_7325573 := by exact prefixLift 7325573
  have htrace : WordTrace (prefixWord ++ tailWord_7325573) baseStart_7325573 baseEnd_7325573 := by
    simpa [prefixWord, tailWord_7325573, baseEnd_7325573] using wordTrace_append hprefix tailTrace_7325573
  have hstable : (prefixWord ++ tailWord_7325573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325573).length < 2 ^ (prefixWord ++ tailWord_7325573).sum := by decide
  have hdescent : baseEnd_7325573 < baseStart_7325573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325643 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 3]
def baseStart_7325643 : Nat := 118140960795 + 7325643 * 2 ^ 59
def prefixEnd_7325643 : Nat := 4983230072969 + 3 ^ 40 * 7325643 * 2
def baseEnd_7325643 : Nat := 3761575962244787121772487

theorem tailTrace_7325643 : CollatzResearch.WordTrace tailWord_7325643 prefixEnd_7325643 3761575962244787121772487 := by
  unfold tailWord_7325643
  simp only [CollatzResearch.WordTrace]
  refine ⟨267188150599454006062741583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178125433732969337375161055 267188150599454006062741583)
  ·
    refine ⟨400782225899181009094112375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267188150599454006062741583 400782225899181009094112375)
    ·
      refine ⟨601173338848771513641168563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400782225899181009094112375 601173338848771513641168563)
      ·
        refine ⟨901760008273157270461752845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601173338848771513641168563 901760008273157270461752845)
        ·
          refine ⟨338160003102433976423157317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 901760008273157270461752845 338160003102433976423157317)
          ·
            refine ⟨63405000581706370579341997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338160003102433976423157317 63405000581706370579341997)
            ·
              refine ⟨23776875218139888967253249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63405000581706370579341997 23776875218139888967253249)
              ·
                refine ⟨17832656413604916725439937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23776875218139888967253249 17832656413604916725439937)
                ·
                  refine ⟨13374492310203687544079953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17832656413604916725439937 13374492310203687544079953)
                  ·
                    refine ⟨10030869232652765658059965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13374492310203687544079953 10030869232652765658059965)
                    ·
                      refine ⟨3761575962244787121772487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10030869232652765658059965 3761575962244787121772487)
                      ·
                        rfl

theorem cell23_7325643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 3].length) (baseStart_7325643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325643 prefixEnd_7325643 := by exact prefixLift 7325643
  have htrace : WordTrace (prefixWord ++ tailWord_7325643) baseStart_7325643 baseEnd_7325643 := by
    simpa [prefixWord, tailWord_7325643, baseEnd_7325643] using wordTrace_append hprefix tailTrace_7325643
  have hstable : (prefixWord ++ tailWord_7325643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325643).length < 2 ^ (prefixWord ++ tailWord_7325643).sum := by decide
  have hdescent : baseEnd_7325643 < baseStart_7325643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325646 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 8]
def baseStart_7325646 : Nat := 118140960795 + 7325646 * 2 ^ 59
def prefixEnd_7325646 : Nat := 4983230072969 + 3 ^ 40 * 7325646 * 2
def baseEnd_7325646 : Nat := 417953055854083401114997

theorem tailTrace_7325646 : CollatzResearch.WordTrace tailWord_7325646 prefixEnd_7325646 417953055854083401114997 := by
  unfold tailWord_7325646
  simp only [CollatzResearch.WordTrace]
  refine ⟨33398532502305392196887599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178125506678962091716733861 33398532502305392196887599)
  ·
    refine ⟨50097798753458088295331399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33398532502305392196887599 50097798753458088295331399)
    ·
      refine ⟨75146698130187132442997099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50097798753458088295331399 75146698130187132442997099)
      ·
        refine ⟨112720047195280698664495649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75146698130187132442997099 112720047195280698664495649)
        ·
          refine ⟨84540035396460523998371737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112720047195280698664495649 84540035396460523998371737)
          ·
            refine ⟨63405026547345392998778803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84540035396460523998371737 63405026547345392998778803)
            ·
              refine ⟨95107539821018089498168205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63405026547345392998778803 95107539821018089498168205)
              ·
                refine ⟨35665327432881783561813077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95107539821018089498168205 35665327432881783561813077)
                ·
                  refine ⟨417953055854083401114997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35665327432881783561813077 417953055854083401114997)
                  ·
                    rfl

theorem cell23_7325646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_7325646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325646 prefixEnd_7325646 := by exact prefixLift 7325646
  have htrace : WordTrace (prefixWord ++ tailWord_7325646) baseStart_7325646 baseEnd_7325646 := by
    simpa [prefixWord, tailWord_7325646, baseEnd_7325646] using wordTrace_append hprefix tailTrace_7325646
  have hstable : (prefixWord ++ tailWord_7325646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325646).length < 2 ^ (prefixWord ++ tailWord_7325646).sum := by decide
  have hdescent : baseEnd_7325646 < baseStart_7325646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325663 : List Nat := [1, 1, 2, 3, 4, 2, 1, 3, 6]
def baseStart_7325663 : Nat := 118140960795 + 7325663 * 2 ^ 59
def prefixEnd_7325663 : Nat := 4983230072969 + 3 ^ 40 * 7325663 * 2
def baseEnd_7325663 : Nat := 417954025761986338169155

theorem tailTrace_7325663 : CollatzResearch.WordTrace tailWord_7325663 prefixEnd_7325663 417954025761986338169155 := by
  unfold tailWord_7325663
  simp only [CollatzResearch.WordTrace]
  refine ⟨267188880059381549478469643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178125920039587699652313095 267188880059381549478469643)
  ·
    refine ⟨400783320089072324217704465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267188880059381549478469643 400783320089072324217704465)
    ·
      refine ⟨300587490066804243163278349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400783320089072324217704465 300587490066804243163278349)
      ·
        refine ⟨112720308775051591186229381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300587490066804243163278349 112720308775051591186229381)
        ·
          refine ⟨21135057895322173347418009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112720308775051591186229381 21135057895322173347418009)
          ·
            refine ⟨15851293421491630010563507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21135057895322173347418009 15851293421491630010563507)
            ·
              refine ⟨23776940132237445015845261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15851293421491630010563507 23776940132237445015845261)
              ·
                refine ⟨8916352549589041880941973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23776940132237445015845261 8916352549589041880941973)
                ·
                  refine ⟨417954025761986338169155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8916352549589041880941973 417954025761986338169155)
                  ·
                    rfl

theorem cell23_7325663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 6].length) (baseStart_7325663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325663 prefixEnd_7325663 := by exact prefixLift 7325663
  have htrace : WordTrace (prefixWord ++ tailWord_7325663) baseStart_7325663 baseEnd_7325663 := by
    simpa [prefixWord, tailWord_7325663, baseEnd_7325663] using wordTrace_append hprefix tailTrace_7325663
  have hstable : (prefixWord ++ tailWord_7325663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325663).length < 2 ^ (prefixWord ++ tailWord_7325663).sum := by decide
  have hdescent : baseEnd_7325663 < baseStart_7325663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325683 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 1, 5, 2]
def baseStart_7325683 : Nat := 118140960795 + 7325683 * 2 ^ 59
def prefixEnd_7325683 : Nat := 4983230072969 + 3 ^ 40 * 7325683 * 2
def baseEnd_7325683 : Nat := 3761596501470966965272303

theorem tailTrace_7325683 : CollatzResearch.WordTrace tailWord_7325683 prefixEnd_7325683 3761596501470966965272303 := by
  unfold tailWord_7325683
  simp only [CollatzResearch.WordTrace]
  refine ⟨267189609519309092894197703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178126406346206061929465135 267189609519309092894197703)
  ·
    refine ⟨400784414278963639341296555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267189609519309092894197703 400784414278963639341296555)
    ·
      refine ⟨601176621418445459011944833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400784414278963639341296555 601176621418445459011944833)
      ·
        refine ⟨450882466063834094258958625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601176621418445459011944833 450882466063834094258958625)
        ·
          refine ⟨338161849547875570694218969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450882466063834094258958625 338161849547875570694218969)
          ·
            refine ⟨253621387160906678020664227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338161849547875570694218969 253621387160906678020664227)
            ·
              refine ⟨380432080741360017030996341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253621387160906678020664227 380432080741360017030996341)
              ·
                refine ⟨35665507569502501596655907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 380432080741360017030996341 35665507569502501596655907)
                ·
                  refine ⟨53498261354253752394983861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35665507569502501596655907 53498261354253752394983861)
                  ·
                    refine ⟨5015462001961289287029737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53498261354253752394983861 5015462001961289287029737)
                    ·
                      refine ⟨3761596501470966965272303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015462001961289287029737 3761596501470966965272303)
                      ·
                        rfl

theorem cell23_7325683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 5, 2].length) (baseStart_7325683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325683 prefixEnd_7325683 := by exact prefixLift 7325683
  have htrace : WordTrace (prefixWord ++ tailWord_7325683) baseStart_7325683 baseEnd_7325683 := by
    simpa [prefixWord, tailWord_7325683, baseEnd_7325683] using wordTrace_append hprefix tailTrace_7325683
  have hstable : (prefixWord ++ tailWord_7325683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325683).length < 2 ^ (prefixWord ++ tailWord_7325683).sum := by decide
  have hdescent : baseEnd_7325683 < baseStart_7325683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325693 : List Nat := [1, 4, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_7325693 : Nat := 118140960795 + 7325693 * 2 ^ 59
def prefixEnd_7325693 : Nat := 4983230072969 + 3 ^ 40 * 7325693 * 2
def baseEnd_7325693 : Nat := 1253867212092503975382419

theorem tailTrace_7325693 : CollatzResearch.WordTrace tailWord_7325693 prefixEnd_7325693 1253867212092503975382419 := by
  unfold tailWord_7325693
  simp only [CollatzResearch.WordTrace]
  refine ⟨267189974249272864602061733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178126649499515243068041155 267189974249272864602061733)
  ·
    refine ⟨50098120171738662112886575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267189974249272864602061733 50098120171738662112886575)
    ·
      refine ⟨75147180257607993169329863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50098120171738662112886575 75147180257607993169329863)
      ·
        refine ⟨112720770386411989753994795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75147180257607993169329863 112720770386411989753994795)
        ·
          refine ⟨169081155579617984630992193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112720770386411989753994795 169081155579617984630992193)
          ·
            refine ⟨126810866684713488473244145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169081155579617984630992193 126810866684713488473244145)
            ·
              refine ⟨95108150013535116354933109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126810866684713488473244145 95108150013535116354933109)
              ·
                refine ⟨8916389063768917158274979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95108150013535116354933109 8916389063768917158274979)
                ·
                  refine ⟨13374583595653375737412469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8916389063768917158274979 13374583595653375737412469)
                  ·
                    refine ⟨1253867212092503975382419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13374583595653375737412469 1253867212092503975382419)
                    ·
                      rfl

theorem cell23_7325693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_7325693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325693 prefixEnd_7325693 := by exact prefixLift 7325693
  have htrace : WordTrace (prefixWord ++ tailWord_7325693) baseStart_7325693 baseEnd_7325693 := by
    simpa [prefixWord, tailWord_7325693, baseEnd_7325693] using wordTrace_append hprefix tailTrace_7325693
  have hstable : (prefixWord ++ tailWord_7325693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325693).length < 2 ^ (prefixWord ++ tailWord_7325693).sum := by decide
  have hdescent : baseEnd_7325693 < baseStart_7325693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325707 : List Nat := [1, 1, 1, 1, 6, 1, 3, 4, 1, 1, 3]
def baseStart_7325707 : Nat := 118140960795 + 7325707 * 2 ^ 59
def prefixEnd_7325707 : Nat := 4983230072969 + 3 ^ 40 * 7325707 * 2
def baseEnd_7325707 : Nat := 3761608825006674871372193

theorem tailTrace_7325707 : CollatzResearch.WordTrace tailWord_7325707 prefixEnd_7325707 3761608825006674871372193 := by
  unfold tailWord_7325707
  simp only [CollatzResearch.WordTrace]
  refine ⟨267190484871222144993071375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178126989914148096662047583 267190484871222144993071375)
  ·
    refine ⟨400785727306833217489607063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267190484871222144993071375 400785727306833217489607063)
    ·
      refine ⟨601178590960249826234410595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400785727306833217489607063 601178590960249826234410595)
      ·
        refine ⟨901767886440374739351615893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601178590960249826234410595 901767886440374739351615893)
        ·
          refine ⟨42270369676892565907106995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 901767886440374739351615893 42270369676892565907106995)
          ·
            refine ⟨63405554515338848860660493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42270369676892565907106995 63405554515338848860660493)
            ·
              refine ⟨23777082943252068322747685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63405554515338848860660493 23777082943252068322747685)
              ·
                refine ⟨4458203051859762810515191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23777082943252068322747685 4458203051859762810515191)
                ·
                  refine ⟨6687304577789644215772787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4458203051859762810515191 6687304577789644215772787)
                  ·
                    refine ⟨10030956866684466323659181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6687304577789644215772787 10030956866684466323659181)
                    ·
                      refine ⟨3761608825006674871372193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10030956866684466323659181 3761608825006674871372193)
                      ·
                        rfl

theorem cell23_7325707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 1, 1, 3].length) (baseStart_7325707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325707 prefixEnd_7325707 := by exact prefixLift 7325707
  have htrace : WordTrace (prefixWord ++ tailWord_7325707) baseStart_7325707 baseEnd_7325707 := by
    simpa [prefixWord, tailWord_7325707, baseEnd_7325707] using wordTrace_append hprefix tailTrace_7325707
  have hstable : (prefixWord ++ tailWord_7325707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325707).length < 2 ^ (prefixWord ++ tailWord_7325707).sum := by decide
  have hdescent : baseEnd_7325707 < baseStart_7325707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325713 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 4, 6, 2]
def baseStart_7325713 : Nat := 118140960795 + 7325713 * 2 ^ 59
def prefixEnd_7325713 : Nat := 4983230072969 + 3 ^ 40 * 7325713 * 2
def baseEnd_7325713 : Nat := 3761611905890601847897165

theorem tailTrace_7325713 : CollatzResearch.WordTrace tailWord_7325713 prefixEnd_7325713 3761611905890601847897165 := by
  unfold tailWord_7325713
  simp only [CollatzResearch.WordTrace]
  refine ⟨267190703709200408017789793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178127135806133605345193195 267190703709200408017789793)
  ·
    refine ⟨200393027781900306013342345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267190703709200408017789793 200393027781900306013342345)
    ·
      refine ⟨150294770836425229510006759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200393027781900306013342345 150294770836425229510006759)
      ·
        refine ⟨225442156254637844265010139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150294770836425229510006759 225442156254637844265010139)
        ·
          refine ⟨338163234381956766397515209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225442156254637844265010139 338163234381956766397515209)
          ·
            refine ⟨253622425786467574798136407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338163234381956766397515209 253622425786467574798136407)
            ·
              refine ⟨380433638679701362197204611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253622425786467574798136407 380433638679701362197204611)
              ·
                refine ⟨570650458019552043295806917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380433638679701362197204611 570650458019552043295806917)
                ·
                  refine ⟨106996960878666008117963797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 570650458019552043295806917 106996960878666008117963797)
                  ·
                    refine ⟨5015482541187469130529553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106996960878666008117963797 5015482541187469130529553)
                    ·
                      refine ⟨3761611905890601847897165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015482541187469130529553 3761611905890601847897165)
                      ·
                        rfl

theorem cell23_7325713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 6, 2].length) (baseStart_7325713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325713 prefixEnd_7325713 := by exact prefixLift 7325713
  have htrace : WordTrace (prefixWord ++ tailWord_7325713) baseStart_7325713 baseEnd_7325713 := by
    simpa [prefixWord, tailWord_7325713, baseEnd_7325713] using wordTrace_append hprefix tailTrace_7325713
  have hstable : (prefixWord ++ tailWord_7325713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325713).length < 2 ^ (prefixWord ++ tailWord_7325713).sum := by decide
  have hdescent : baseEnd_7325713 < baseStart_7325713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325730 : List Nat := [3, 3, 1, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_7325730 : Nat := 118140960795 + 7325730 * 2 ^ 59
def prefixEnd_7325730 : Nat := 4983230072969 + 3 ^ 40 * 7325730 * 2
def baseEnd_7325730 : Nat := 3761620635061728281384587

theorem tailTrace_7325730 : CollatzResearch.WordTrace tailWord_7325730 prefixEnd_7325730 3761620635061728281384587 := by
  unfold tailWord_7325730
  simp only [CollatzResearch.WordTrace]
  refine ⟨66797830937534704980289661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178127549166759213280772429 66797830937534704980289661)
  ·
    refine ⟨25049186601575514367608623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66797830937534704980289661 25049186601575514367608623)
    ·
      refine ⟨37573779902363271551412935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25049186601575514367608623 37573779902363271551412935)
      ·
        refine ⟨56360669853544907327119403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37573779902363271551412935 56360669853544907327119403)
        ·
          refine ⟨84541004780317360990679105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56360669853544907327119403 84541004780317360990679105)
          ·
            refine ⟨63405753585238020743009329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84541004780317360990679105 63405753585238020743009329)
            ·
              refine ⟨47554315188928515557256997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63405753585238020743009329 47554315188928515557256997)
              ·
                refine ⟨8916434097924096666985687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47554315188928515557256997 8916434097924096666985687)
                ·
                  refine ⟨13374651146886145000478531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8916434097924096666985687 13374651146886145000478531)
                  ·
                    refine ⟨20061976720329217500717797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13374651146886145000478531 20061976720329217500717797)
                    ·
                      refine ⟨3761620635061728281384587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20061976720329217500717797 3761620635061728281384587)
                      ·
                        rfl

theorem cell23_7325730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_7325730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325730 prefixEnd_7325730 := by exact prefixLift 7325730
  have htrace : WordTrace (prefixWord ++ tailWord_7325730) baseStart_7325730 baseEnd_7325730 := by
    simpa [prefixWord, tailWord_7325730, baseEnd_7325730] using wordTrace_append hprefix tailTrace_7325730
  have hstable : (prefixWord ++ tailWord_7325730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325730).length < 2 ^ (prefixWord ++ tailWord_7325730).sum := by decide
  have hdescent : baseEnd_7325730 < baseStart_7325730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325750 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_7325750 : Nat := 118140960795 + 7325750 * 2 ^ 59
def prefixEnd_7325750 : Nat := 4983230072969 + 3 ^ 40 * 7325750 * 2
def baseEnd_7325750 : Nat := 3761630904674818203134495

theorem tailTrace_7325750 : CollatzResearch.WordTrace tailWord_7325750 prefixEnd_7325750 3761630904674818203134495 := by
  unfold tailWord_7325750
  simp only [CollatzResearch.WordTrace]
  refine ⟨16699503325629147708555419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178128035473377575557924469 16699503325629147708555419)
  ·
    refine ⟨25049254988443721562833129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16699503325629147708555419 25049254988443721562833129)
    ·
      refine ⟨18786941241332791172124847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25049254988443721562833129 18786941241332791172124847)
      ·
        refine ⟨28180411861999186758187271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18786941241332791172124847 28180411861999186758187271)
        ·
          refine ⟨42270617792998780137280907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28180411861999186758187271 42270617792998780137280907)
          ·
            refine ⟨63405926689498170205921361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42270617792998780137280907 63405926689498170205921361)
            ·
              refine ⟨47554445017123627654441021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63405926689498170205921361 47554445017123627654441021)
              ·
                refine ⟨17832916881421360370415383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47554445017123627654441021 17832916881421360370415383)
                ·
                  refine ⟨26749375322132040555623075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17832916881421360370415383 26749375322132040555623075)
                  ·
                    refine ⟨40124062983198060833434613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26749375322132040555623075 40124062983198060833434613)
                    ·
                      refine ⟨3761630904674818203134495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40124062983198060833434613 3761630904674818203134495)
                      ·
                        rfl

theorem cell23_7325750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_7325750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325750 prefixEnd_7325750 := by exact prefixLift 7325750
  have htrace : WordTrace (prefixWord ++ tailWord_7325750) baseStart_7325750 baseEnd_7325750 := by
    simpa [prefixWord, tailWord_7325750, baseEnd_7325750] using wordTrace_append hprefix tailTrace_7325750
  have hstable : (prefixWord ++ tailWord_7325750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325750).length < 2 ^ (prefixWord ++ tailWord_7325750).sum := by decide
  have hdescent : baseEnd_7325750 < baseStart_7325750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325753 : List Nat := [1, 2, 1, 5, 3, 1, 10]
def baseStart_7325753 : Nat := 118140960795 + 7325753 * 2 ^ 59
def prefixEnd_7325753 : Nat := 4983230072969 + 3 ^ 40 * 7325753 * 2
def baseEnd_7325753 : Nat := 46439906729836811004901

theorem tailTrace_7325753 : CollatzResearch.WordTrace tailWord_7325753 prefixEnd_7325753 46439906729836811004901 := by
  unfold tailWord_7325753
  simp only [CollatzResearch.WordTrace]
  refine ⟨267192162629055494849245913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178128108419370329899497275 267192162629055494849245913)
  ·
    refine ⟨200394121971791621136934435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267192162629055494849245913 200394121971791621136934435)
    ·
      refine ⟨300591182957687431705401653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200394121971791621136934435 300591182957687431705401653)
      ·
        refine ⟨28180423402283196722381405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 300591182957687431705401653 28180423402283196722381405)
        ·
          refine ⟨10567658775856198770893027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28180423402283196722381405 10567658775856198770893027)
          ·
            refine ⟨15851488163784298156339541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10567658775856198770893027 15851488163784298156339541)
            ·
              refine ⟨46439906729836811004901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15851488163784298156339541 46439906729836811004901)
              ·
                rfl

theorem cell23_7325753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 10].length) (baseStart_7325753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325753 prefixEnd_7325753 := by exact prefixLift 7325753
  have htrace : WordTrace (prefixWord ++ tailWord_7325753) baseStart_7325753 baseEnd_7325753 := by
    simpa [prefixWord, tailWord_7325753, baseEnd_7325753] using wordTrace_append hprefix tailTrace_7325753
  have hstable : (prefixWord ++ tailWord_7325753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325753).length < 2 ^ (prefixWord ++ tailWord_7325753).sum := by decide
  have hdescent : baseEnd_7325753 < baseStart_7325753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325807 : List Nat := [1, 1, 2, 1, 3, 4, 2, 3, 1, 3, 2]
def baseStart_7325807 : Nat := 118140960795 + 7325807 * 2 ^ 59
def prefixEnd_7325807 : Nat := 4983230072969 + 3 ^ 40 * 7325807 * 2
def baseEnd_7325807 : Nat := 3761660173072124480121733

theorem tailTrace_7325807 : CollatzResearch.WordTrace tailWord_7325807 prefixEnd_7325807 3761660173072124480121733 := by
  unfold tailWord_7325807
  simp only [CollatzResearch.WordTrace]
  refine ⟨267194132170859862071711675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178129421447239908047807783 267194132170859862071711675)
  ·
    refine ⟨400791198256289793107567513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267194132170859862071711675 400791198256289793107567513)
    ·
      refine ⟨300593398692217344830675635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400791198256289793107567513 300593398692217344830675635)
      ·
        refine ⟨450890098038326017246013453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300593398692217344830675635 450890098038326017246013453)
        ·
          refine ⟨169083786764372256467255045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450890098038326017246013453 169083786764372256467255045)
          ·
            refine ⟨31703210018319798087610321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169083786764372256467255045 31703210018319798087610321)
            ·
              refine ⟨23777407513739848565707741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31703210018319798087610321 23777407513739848565707741)
              ·
                refine ⟨8916527817652443212140403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23777407513739848565707741 8916527817652443212140403)
                ·
                  refine ⟨13374791726478664818210605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8916527817652443212140403 13374791726478664818210605)
                  ·
                    refine ⟨5015546897429499306828977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13374791726478664818210605 5015546897429499306828977)
                    ·
                      refine ⟨3761660173072124480121733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015546897429499306828977 3761660173072124480121733)
                      ·
                        rfl

theorem cell23_7325807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 3, 2].length) (baseStart_7325807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325807 prefixEnd_7325807 := by exact prefixLift 7325807
  have htrace : WordTrace (prefixWord ++ tailWord_7325807) baseStart_7325807 baseEnd_7325807 := by
    simpa [prefixWord, tailWord_7325807, baseEnd_7325807] using wordTrace_append hprefix tailTrace_7325807
  have hstable : (prefixWord ++ tailWord_7325807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325807).length < 2 ^ (prefixWord ++ tailWord_7325807).sum := by decide
  have hdescent : baseEnd_7325807 < baseStart_7325807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325833 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 1, 4, 4]
def baseStart_7325833 : Nat := 118140960795 + 7325833 * 2 ^ 59
def prefixEnd_7325833 : Nat := 4983230072969 + 3 ^ 40 * 7325833 * 2
def baseEnd_7325833 : Nat := 3761673523569141378396613

theorem tailTrace_7325833 : CollatzResearch.WordTrace tailWord_7325833 prefixEnd_7325833 3761673523569141378396613 := by
  unfold tailWord_7325833
  simp only [CollatzResearch.WordTrace]
  refine ⟨267195080468765668512158153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178130053645843779008105435 267195080468765668512158153)
  ·
    refine ⟨200396310351574251384118615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267195080468765668512158153 200396310351574251384118615)
    ·
      refine ⟨300594465527361377076177923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200396310351574251384118615 300594465527361377076177923)
      ·
        refine ⟨450891698291042065614266885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300594465527361377076177923 450891698291042065614266885)
        ·
          refine ⟨84542193429570387302675041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 450891698291042065614266885 84542193429570387302675041)
          ·
            refine ⟨63406645072177790477006281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84542193429570387302675041 63406645072177790477006281)
            ·
              refine ⟨47554983804133342857754711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63406645072177790477006281 47554983804133342857754711)
              ·
                refine ⟨71332475706200014286632067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47554983804133342857754711 71332475706200014286632067)
                ·
                  refine ⟨106998713559300021429948101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71332475706200014286632067 106998713559300021429948101)
                  ·
                    refine ⟨20062258792368754018115269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106998713559300021429948101 20062258792368754018115269)
                    ·
                      refine ⟨3761673523569141378396613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20062258792368754018115269 3761673523569141378396613)
                      ·
                        rfl

theorem cell23_7325833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_7325833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325833 prefixEnd_7325833 := by exact prefixLift 7325833
  have htrace : WordTrace (prefixWord ++ tailWord_7325833) baseStart_7325833 baseEnd_7325833 := by
    simpa [prefixWord, tailWord_7325833, baseEnd_7325833] using wordTrace_append hprefix tailTrace_7325833
  have hstable : (prefixWord ++ tailWord_7325833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325833).length < 2 ^ (prefixWord ++ tailWord_7325833).sum := by decide
  have hdescent : baseEnd_7325833 < baseStart_7325833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325880 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 1, 7, 2]
def baseStart_7325880 : Nat := 118140960795 + 7325880 * 2 ^ 59
def prefixEnd_7325880 : Nat := 4983230072969 + 3 ^ 40 * 7325880 * 2
def baseEnd_7325880 : Nat := 3761697657159902694508897

theorem tailTrace_7325880 : CollatzResearch.WordTrace tailWord_7325880 prefixEnd_7325880 3761697657159902694508897 := by
  unfold tailWord_7325880
  simp only [CollatzResearch.WordTrace]
  refine ⟨133598397349797697769559547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178131196466396930359412729 133598397349797697769559547)
  ·
    refine ⟨200397596024696546654339321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133598397349797697769559547 200397596024696546654339321)
    ·
      refine ⟨150298197018522409990754491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200397596024696546654339321 150298197018522409990754491)
      ·
        refine ⟨225447295527783614986131737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150298197018522409990754491 225447295527783614986131737)
        ·
          refine ⟨169085471645837711239598803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225447295527783614986131737 169085471645837711239598803)
          ·
            refine ⟨253628207468756566859398205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169085471645837711239598803 253628207468756566859398205)
            ·
              refine ⟨95110577800783712572274327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253628207468756566859398205 95110577800783712572274327)
              ·
                refine ⟨142665866701175568858411491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95110577800783712572274327 142665866701175568858411491)
                ·
                  refine ⟨213998800051763353287617237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142665866701175568858411491 213998800051763353287617237)
                  ·
                    refine ⟨5015596876213203592678529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 213998800051763353287617237 5015596876213203592678529)
                    ·
                      refine ⟨3761697657159902694508897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015596876213203592678529 3761697657159902694508897)
                      ·
                        rfl

theorem cell23_7325880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 7, 2].length) (baseStart_7325880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325880 prefixEnd_7325880 := by exact prefixLift 7325880
  have htrace : WordTrace (prefixWord ++ tailWord_7325880) baseStart_7325880 baseEnd_7325880 := by
    simpa [prefixWord, tailWord_7325880, baseEnd_7325880] using wordTrace_append hprefix tailTrace_7325880
  have hstable : (prefixWord ++ tailWord_7325880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325880).length < 2 ^ (prefixWord ++ tailWord_7325880).sum := by decide
  have hdescent : baseEnd_7325880 < baseStart_7325880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325883 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 5]
def baseStart_7325883 : Nat := 118140960795 + 7325883 * 2 ^ 59
def prefixEnd_7325883 : Nat := 4983230072969 + 3 ^ 40 * 7325883 * 2
def baseEnd_7325883 : Nat := 3761699197601866182771383

theorem tailTrace_7325883 : CollatzResearch.WordTrace tailWord_7325883 prefixEnd_7325883 3761699197601866182771383 := by
  unfold tailWord_7325883
  simp only [CollatzResearch.WordTrace]
  refine ⟨267196904118584527051478303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178131269412389684700985535 267196904118584527051478303)
  ·
    refine ⟨400795356177876790577217455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267196904118584527051478303 400795356177876790577217455)
    ·
      refine ⟨601193034266815185865826183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400795356177876790577217455 601193034266815185865826183)
      ·
        refine ⟨901789551400222778798739275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601193034266815185865826183 901789551400222778798739275)
        ·
          refine ⟨1352684327100334168198108913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901789551400222778798739275 1352684327100334168198108913)
          ·
            refine ⟨1014513245325250626148581685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1352684327100334168198108913 1014513245325250626148581685)
            ·
              refine ⟨95110616749242246201429533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1014513245325250626148581685 95110616749242246201429533)
              ·
                refine ⟨35666481280965842325536075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95110616749242246201429533 35666481280965842325536075)
                ·
                  refine ⟨53499721921448763488304113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35666481280965842325536075 53499721921448763488304113)
                  ·
                    refine ⟨40124791441086572616228085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53499721921448763488304113 40124791441086572616228085)
                    ·
                      refine ⟨3761699197601866182771383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40124791441086572616228085 3761699197601866182771383)
                      ·
                        rfl

theorem cell23_7325883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 5].length) (baseStart_7325883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325883 prefixEnd_7325883 := by exact prefixLift 7325883
  have htrace : WordTrace (prefixWord ++ tailWord_7325883) baseStart_7325883 baseEnd_7325883 := by
    simpa [prefixWord, tailWord_7325883, baseEnd_7325883] using wordTrace_append hprefix tailTrace_7325883
  have hstable : (prefixWord ++ tailWord_7325883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325883).length < 2 ^ (prefixWord ++ tailWord_7325883).sum := by decide
  have hdescent : baseEnd_7325883 < baseStart_7325883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325920 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 5, 4]
def baseStart_7325920 : Nat := 118140960795 + 7325920 * 2 ^ 59
def prefixEnd_7325920 : Nat := 4983230072969 + 3 ^ 40 * 7325920 * 2
def baseEnd_7325920 : Nat := 1253906065462027512669571

theorem tailTrace_7325920 : CollatzResearch.WordTrace tailWord_7325920 prefixEnd_7325920 1253906065462027512669571 := by
  unfold tailWord_7325920
  simp only [CollatzResearch.WordTrace]
  refine ⟨133599126809725241185287607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178132169079633654913716809 133599126809725241185287607)
  ·
    refine ⟨200398690214587861777931411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133599126809725241185287607 200398690214587861777931411)
    ·
      refine ⟨300598035321881792666897117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200398690214587861777931411 300598035321881792666897117)
      ·
        refine ⟨112724263245705672250086419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300598035321881792666897117 112724263245705672250086419)
        ·
          refine ⟨169086394868558508375129629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112724263245705672250086419 169086394868558508375129629)
          ·
            refine ⟨63407398075709440640673611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169086394868558508375129629 63407398075709440640673611)
            ·
              refine ⟨95111097113564160961010417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63407398075709440640673611 95111097113564160961010417)
              ·
                refine ⟨71333322835173120720757813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95111097113564160961010417 71333322835173120720757813)
                ·
                  refine ⟨6687499015797480067571045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71333322835173120720757813 6687499015797480067571045)
                  ·
                    refine ⟨1253906065462027512669571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6687499015797480067571045 1253906065462027512669571)
                    ·
                      rfl

theorem cell23_7325920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 5, 4].length) (baseStart_7325920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325920 prefixEnd_7325920 := by exact prefixLift 7325920
  have htrace : WordTrace (prefixWord ++ tailWord_7325920) baseStart_7325920 baseEnd_7325920 := by
    simpa [prefixWord, tailWord_7325920, baseEnd_7325920] using wordTrace_append hprefix tailTrace_7325920
  have hstable : (prefixWord ++ tailWord_7325920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325920).length < 2 ^ (prefixWord ++ tailWord_7325920).sum := by decide
  have hdescent : baseEnd_7325920 < baseStart_7325920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325922 : List Nat := [3, 3, 4, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7325922 : Nat := 118140960795 + 7325922 * 2 ^ 59
def prefixEnd_7325922 : Nat := 4983230072969 + 3 ^ 40 * 7325922 * 2
def baseEnd_7325922 : Nat := 3761719223347391530183705

theorem tailTrace_7325922 : CollatzResearch.WordTrace tailWord_7325922 prefixEnd_7325922 3761719223347391530183705 := by
  unfold tailWord_7325922
  simp only [CollatzResearch.WordTrace]
  refine ⟨66799581641360809178037005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178132217710295491141432013 66799581641360809178037005)
  ·
    refine ⟨25049843115510303441763877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66799581641360809178037005 25049843115510303441763877)
    ·
      refine ⟨4696845584158181895330727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25049843115510303441763877 4696845584158181895330727)
      ·
        refine ⟨7045268376237272842996091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4696845584158181895330727 7045268376237272842996091)
        ·
          refine ⟨10567902564355909264494137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7045268376237272842996091 10567902564355909264494137)
          ·
            refine ⟨7925926923266931948370603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10567902564355909264494137 7925926923266931948370603)
            ·
              refine ⟨11888890384900397922555905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7925926923266931948370603 11888890384900397922555905)
              ·
                refine ⟨8916667788675298441916929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11888890384900397922555905 8916667788675298441916929)
                ·
                  refine ⟨6687500841506473831437697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8916667788675298441916929 6687500841506473831437697)
                  ·
                    refine ⟨5015625631129855373578273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6687500841506473831437697 5015625631129855373578273)
                    ·
                      refine ⟨3761719223347391530183705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015625631129855373578273 3761719223347391530183705)
                      ·
                        rfl

theorem cell23_7325922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7325922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325922 prefixEnd_7325922 := by exact prefixLift 7325922
  have htrace : WordTrace (prefixWord ++ tailWord_7325922) baseStart_7325922 baseEnd_7325922 := by
    simpa [prefixWord, tailWord_7325922, baseEnd_7325922] using wordTrace_append hprefix tailTrace_7325922
  have hstable : (prefixWord ++ tailWord_7325922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325922).length < 2 ^ (prefixWord ++ tailWord_7325922).sum := by decide
  have hdescent : baseEnd_7325922 < baseStart_7325922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325954 : List Nat := [3, 4, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_7325954 : Nat := 118140960795 + 7325954 * 2 ^ 59
def prefixEnd_7325954 : Nat := 4983230072969 + 3 ^ 40 * 7325954 * 2
def baseEnd_7325954 : Nat := 1253911884909445134994519

theorem tailTrace_7325954 : CollatzResearch.WordTrace tailWord_7325954 prefixEnd_7325954 1253911884909445134994519 := by
  unfold tailWord_7325954
  simp only [CollatzResearch.WordTrace]
  refine ⟨66799873425331826544328229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178132995800884870784875277 66799873425331826544328229)
  ·
    refine ⟨12524976267249717477061543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66799873425331826544328229 12524976267249717477061543)
    ·
      refine ⟨18787464400874576215592315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12524976267249717477061543 18787464400874576215592315)
      ·
        refine ⟨28181196601311864323388473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18787464400874576215592315 28181196601311864323388473)
        ·
          refine ⟨21135897450983898242541355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28181196601311864323388473 21135897450983898242541355)
          ·
            refine ⟨31703846176475847363812033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21135897450983898242541355 31703846176475847363812033)
            ·
              refine ⟨23777884632356885522859025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31703846176475847363812033 23777884632356885522859025)
              ·
                refine ⟨17833413474267664142144269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23777884632356885522859025 17833413474267664142144269)
                ·
                  refine ⟨6687530052850374053304101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17833413474267664142144269 6687530052850374053304101)
                  ·
                    refine ⟨1253911884909445134994519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6687530052850374053304101 1253911884909445134994519)
                    ·
                      rfl

theorem cell23_7325954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_7325954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325954 prefixEnd_7325954 := by exact prefixLift 7325954
  have htrace : WordTrace (prefixWord ++ tailWord_7325954) baseStart_7325954 baseEnd_7325954 := by
    simpa [prefixWord, tailWord_7325954, baseEnd_7325954] using wordTrace_append hprefix tailTrace_7325954
  have hstable : (prefixWord ++ tailWord_7325954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325954).length < 2 ^ (prefixWord ++ tailWord_7325954).sum := by decide
  have hdescent : baseEnd_7325954 < baseStart_7325954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325980 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 5, 5]
def baseStart_7325980 : Nat := 118140960795 + 7325980 * 2 ^ 59
def prefixEnd_7325980 : Nat := 4983230072969 + 3 ^ 40 * 7325980 * 2
def baseEnd_7325980 : Nat := 1253916335075117434419479

theorem tailTrace_7325980 : CollatzResearch.WordTrace tailWord_7325980 prefixEnd_7325980 1253916335075117434419479 := by
  unfold tailWord_7325980
  simp only [CollatzResearch.WordTrace]
  refine ⟨133600220999616556308879697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178133627999488741745172929 133600220999616556308879697)
  ·
    refine ⟨100200165749712417231659773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133600220999616556308879697 100200165749712417231659773)
    ·
      refine ⟨37575062156142156461872415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100200165749712417231659773 37575062156142156461872415)
      ·
        refine ⟨56362593234213234692808623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37575062156142156461872415 56362593234213234692808623)
        ·
          refine ⟨84543889851319852039212935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56362593234213234692808623 84543889851319852039212935)
          ·
            refine ⟨126815834776979778058819403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84543889851319852039212935 126815834776979778058819403)
            ·
              refine ⟨190223752165469667088229105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126815834776979778058819403 190223752165469667088229105)
              ·
                refine ⟨142667814124102250316171829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190223752165469667088229105 142667814124102250316171829)
                ·
                  refine ⟨13375107574134585967141109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142667814124102250316171829 13375107574134585967141109)
                  ·
                    refine ⟨1253916335075117434419479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13375107574134585967141109 1253916335075117434419479)
                    ·
                      rfl

theorem cell23_7325980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_7325980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7325980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7325980 prefixEnd_7325980 := by exact prefixLift 7325980
  have htrace : WordTrace (prefixWord ++ tailWord_7325980) baseStart_7325980 baseEnd_7325980 := by
    simpa [prefixWord, tailWord_7325980, baseEnd_7325980] using wordTrace_append hprefix tailTrace_7325980
  have hstable : (prefixWord ++ tailWord_7325980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325980).length < 2 ^ (prefixWord ++ tailWord_7325980).sum := by decide
  have hdescent : baseEnd_7325980 < baseStart_7325980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326001 : List Nat := [1, 2, 2, 3, 5, 1, 2, 1, 6]
def baseStart_7326001 : Nat := 118140960795 + 7326001 * 2 ^ 59
def prefixEnd_7326001 : Nat := 4983230072969 + 3 ^ 40 * 7326001 * 2
def baseEnd_7326001 : Nat := 417973309813232969010649

theorem tailTrace_7326001 : CollatzResearch.WordTrace tailWord_7326001 prefixEnd_7326001 417973309813232969010649 := by
  unfold tailWord_7326001
  simp only [CollatzResearch.WordTrace]
  refine ⟨267201207932157033204273857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178134138621438022136182571 267201207932157033204273857)
  ·
    refine ⟨200400905949117774903205393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267201207932157033204273857 200400905949117774903205393)
    ·
      refine ⟨150300679461838331177404045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200400905949117774903205393 150300679461838331177404045)
      ·
        refine ⟨56362754798189374191526517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150300679461838331177404045 56362754798189374191526517)
        ·
          refine ⟨5284008262330253830455611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56362754798189374191526517 5284008262330253830455611)
          ·
            refine ⟨7926012393495380745683417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5284008262330253830455611 7926012393495380745683417)
            ·
              refine ⟨5944509295121535559262563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7926012393495380745683417 5944509295121535559262563)
              ·
                refine ⟨8916763942682303338893845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5944509295121535559262563 8916763942682303338893845)
                ·
                  refine ⟨417973309813232969010649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8916763942682303338893845 417973309813232969010649)
                  ·
                    rfl

theorem cell23_7326001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 6].length) (baseStart_7326001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326001 prefixEnd_7326001 := by exact prefixLift 7326001
  have htrace : WordTrace (prefixWord ++ tailWord_7326001) baseStart_7326001 baseEnd_7326001 := by
    simpa [prefixWord, tailWord_7326001, baseEnd_7326001] using wordTrace_append hprefix tailTrace_7326001
  have hstable : (prefixWord ++ tailWord_7326001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326001).length < 2 ^ (prefixWord ++ tailWord_7326001).sum := by decide
  have hdescent : baseEnd_7326001 < baseStart_7326001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326014 : List Nat := [4, 2, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_7326014 : Nat := 118140960795 + 7326014 * 2 ^ 59
def prefixEnd_7326014 : Nat := 4983230072969 + 3 ^ 40 * 7326014 * 2
def baseEnd_7326014 : Nat := 1253922154522535056744427

theorem tailTrace_7326014 : CollatzResearch.WordTrace tailWord_7326014 prefixEnd_7326014 1253922154522535056744427 := by
  unfold tailWord_7326014
  simp only [CollatzResearch.WordTrace]
  refine ⟨33400210260138742053062137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178134454720739957616331397 33400210260138742053062137)
  ·
    refine ⟨25050157695104056539796603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33400210260138742053062137 25050157695104056539796603)
    ·
      refine ⟨37575236542656084809694905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25050157695104056539796603 37575236542656084809694905)
      ·
        refine ⟨28181427406992063607271179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37575236542656084809694905 28181427406992063607271179)
        ·
          refine ⟨42272141110488095410906769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28181427406992063607271179 42272141110488095410906769)
          ·
            refine ⟨31704105832866071558180077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42272141110488095410906769 31704105832866071558180077)
            ·
              refine ⟨11889039687324776834317529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31704105832866071558180077 11889039687324776834317529)
              ·
                refine ⟨8916779765493582625738147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11889039687324776834317529 8916779765493582625738147)
                ·
                  refine ⟨13375169648240373938607221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8916779765493582625738147 13375169648240373938607221)
                  ·
                    refine ⟨1253922154522535056744427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13375169648240373938607221 1253922154522535056744427)
                    ·
                      rfl

theorem cell23_7326014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_7326014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326014 prefixEnd_7326014 := by exact prefixLift 7326014
  have htrace : WordTrace (prefixWord ++ tailWord_7326014) baseStart_7326014 baseEnd_7326014 := by
    simpa [prefixWord, tailWord_7326014, baseEnd_7326014] using wordTrace_append hprefix tailTrace_7326014
  have hstable : (prefixWord ++ tailWord_7326014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326014).length < 2 ^ (prefixWord ++ tailWord_7326014).sum := by decide
  have hdescent : baseEnd_7326014 < baseStart_7326014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326030 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_7326030 : Nat := 118140960795 + 7326030 * 2 ^ 59
def prefixEnd_7326030 : Nat := 4983230072969 + 3 ^ 40 * 7326030 * 2
def baseEnd_7326030 : Nat := 3761774679258077107633207

theorem tailTrace_7326030 : CollatzResearch.WordTrace tailWord_7326030 prefixEnd_7326030 3761774679258077107633207 := by
  unfold tailWord_7326030
  simp only [CollatzResearch.WordTrace]
  refine ⟨33400283206131496394634943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178134843766034647438053029 33400283206131496394634943)
  ·
    refine ⟨50100424809197244591952415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33400283206131496394634943 50100424809197244591952415)
    ·
      refine ⟨75150637213795866887928623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50100424809197244591952415 75150637213795866887928623)
      ·
        refine ⟨112725955820693800331892935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75150637213795866887928623 112725955820693800331892935)
        ·
          refine ⟨169088933731040700497839403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112725955820693800331892935 169088933731040700497839403)
          ·
            refine ⟨253633400596561050746759105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169088933731040700497839403 253633400596561050746759105)
            ·
              refine ⟨190225050447420788060069329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253633400596561050746759105 190225050447420788060069329)
              ·
                refine ⟨142668787835565591045051997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190225050447420788060069329 142668787835565591045051997)
                ·
                  refine ⟨53500795438337096641894499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142668787835565591045051997 53500795438337096641894499)
                  ·
                    refine ⟨80251193157505644962841749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53500795438337096641894499 80251193157505644962841749)
                    ·
                      refine ⟨3761774679258077107633207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80251193157505644962841749 3761774679258077107633207)
                      ·
                        rfl

theorem cell23_7326030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_7326030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326030 prefixEnd_7326030 := by exact prefixLift 7326030
  have htrace : WordTrace (prefixWord ++ tailWord_7326030) baseStart_7326030 baseEnd_7326030 := by
    simpa [prefixWord, tailWord_7326030, baseEnd_7326030] using wordTrace_append hprefix tailTrace_7326030
  have hstable : (prefixWord ++ tailWord_7326030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326030).length < 2 ^ (prefixWord ++ tailWord_7326030).sum := by decide
  have hdescent : baseEnd_7326030 < baseStart_7326030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326084 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_7326084 : Nat := 118140960795 + 7326084 * 2 ^ 59
def prefixEnd_7326084 : Nat := 4983230072969 + 3 ^ 40 * 7326084 * 2
def baseEnd_7326084 : Nat := 3761802407213419896357959

theorem tailTrace_7326084 : CollatzResearch.WordTrace tailWord_7326084 prefixEnd_7326084 3761802407213419896357959 := by
  unfold tailWord_7326084
  simp only [CollatzResearch.WordTrace]
  refine ⟨133602117595428169189772653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178136156793904225586363537 133602117595428169189772653)
  ·
    refine ⟨50100794098285563446164745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133602117595428169189772653 50100794098285563446164745)
    ·
      refine ⟨37575595573714172584623559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50100794098285563446164745 37575595573714172584623559)
      ·
        refine ⟨56363393360571258876935339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37575595573714172584623559 56363393360571258876935339)
        ·
          refine ⟨84545090040856888315403009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56363393360571258876935339 84545090040856888315403009)
          ·
            refine ⟨63408817530642666236552257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84545090040856888315403009 63408817530642666236552257)
            ·
              refine ⟨47556613147981999677414193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63408817530642666236552257 47556613147981999677414193)
              ·
                refine ⟨35667459860986499758060645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47556613147981999677414193 35667459860986499758060645)
                ·
                  refine ⟨6687648723934968704636371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35667459860986499758060645 6687648723934968704636371)
                  ·
                    refine ⟨10031473085902453056954557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6687648723934968704636371 10031473085902453056954557)
                    ·
                      refine ⟨3761802407213419896357959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10031473085902453056954557 3761802407213419896357959)
                      ·
                        rfl

theorem cell23_7326084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_7326084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326084 prefixEnd_7326084 := by exact prefixLift 7326084
  have htrace : WordTrace (prefixWord ++ tailWord_7326084) baseStart_7326084 baseEnd_7326084 := by
    simpa [prefixWord, tailWord_7326084, baseEnd_7326084] using wordTrace_append hprefix tailTrace_7326084
  have hstable : (prefixWord ++ tailWord_7326084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326084).length < 2 ^ (prefixWord ++ tailWord_7326084).sum := by decide
  have hdescent : baseEnd_7326084 < baseStart_7326084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326141 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 4, 2, 2]
def baseStart_7326141 : Nat := 118140960795 + 7326141 * 2 ^ 59
def prefixEnd_7326141 : Nat := 4983230072969 + 3 ^ 40 * 7326141 * 2
def baseEnd_7326141 : Nat := 3761831675610726173345197

theorem tailTrace_7326141 : CollatzResearch.WordTrace tailWord_7326141 prefixEnd_7326141 3761831675610726173345197 := by
  unfold tailWord_7326141
  simp only [CollatzResearch.WordTrace]
  refine ⟨267206314151649837114370277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178137542767766558076246851 267206314151649837114370277)
  ·
    refine ⟨50101183903434344458944427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267206314151649837114370277 50101183903434344458944427)
    ·
      refine ⟨75151775855151516688416641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50101183903434344458944427 75151775855151516688416641)
      ·
        refine ⟨56363831891363637516312481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75151775855151516688416641 56363831891363637516312481)
        ·
          refine ⟨42272873918522728137234361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56363831891363637516312481 42272873918522728137234361)
          ·
            refine ⟨31704655438892046102925771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42272873918522728137234361 31704655438892046102925771)
            ·
              refine ⟨47556983158338069154388657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31704655438892046102925771 47556983158338069154388657)
              ·
                refine ⟨35667737368753551865791493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47556983158338069154388657 35667737368753551865791493)
                ·
                  refine ⟨6687700756641290974835905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35667737368753551865791493 6687700756641290974835905)
                  ·
                    refine ⟨5015775567480968231126929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6687700756641290974835905 5015775567480968231126929)
                    ·
                      refine ⟨3761831675610726173345197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015775567480968231126929 3761831675610726173345197)
                      ·
                        rfl

theorem cell23_7326141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_7326141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326141 prefixEnd_7326141 := by exact prefixLift 7326141
  have htrace : WordTrace (prefixWord ++ tailWord_7326141) baseStart_7326141 baseEnd_7326141 := by
    simpa [prefixWord, tailWord_7326141, baseEnd_7326141] using wordTrace_append hprefix tailTrace_7326141
  have hstable : (prefixWord ++ tailWord_7326141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326141).length < 2 ^ (prefixWord ++ tailWord_7326141).sum := by decide
  have hdescent : baseEnd_7326141 < baseStart_7326141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326164 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 7]
def baseStart_7326164 : Nat := 118140960795 + 7326164 * 2 ^ 59
def prefixEnd_7326164 : Nat := 4983230072969 + 3 ^ 40 * 7326164 * 2
def baseEnd_7326164 : Nat := 417982609518419953706399

theorem tailTrace_7326164 : CollatzResearch.WordTrace tailWord_7326164 prefixEnd_7326164 417982609518419953706399 := by
  unfold tailWord_7326164
  simp only [CollatzResearch.WordTrace]
  refine ⟨133603576515283256021228773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178138102020377674694971697 133603576515283256021228773)
  ·
    refine ⟨25050670596615610503980395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133603576515283256021228773 25050670596615610503980395)
    ·
      refine ⟨37576005894923415755970593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25050670596615610503980395 37576005894923415755970593)
      ·
        refine ⟨28182004421192561816977945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37576005894923415755970593 28182004421192561816977945)
        ·
          refine ⟨21136503315894421362733459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28182004421192561816977945 21136503315894421362733459)
          ·
            refine ⟨31704754973841632044100189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21136503315894421362733459 31704754973841632044100189)
            ·
              refine ⟨11889283115190612016537571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31704754973841632044100189 11889283115190612016537571)
              ·
                refine ⟨17833924672785918024806357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11889283115190612016537571 17833924672785918024806357)
                ·
                  refine ⟨417982609518419953706399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17833924672785918024806357 417982609518419953706399)
                  ·
                    rfl

theorem cell23_7326164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_7326164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326164 prefixEnd_7326164 := by exact prefixLift 7326164
  have htrace : WordTrace (prefixWord ++ tailWord_7326164) baseStart_7326164 baseEnd_7326164 := by
    simpa [prefixWord, tailWord_7326164, baseEnd_7326164] using wordTrace_append hprefix tailTrace_7326164
  have hstable : (prefixWord ++ tailWord_7326164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326164).length < 2 ^ (prefixWord ++ tailWord_7326164).sum := by decide
  have hdescent : baseEnd_7326164 < baseStart_7326164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326175 : List Nat := [1, 1, 2, 3, 3, 4, 2, 1, 2, 2, 2]
def baseStart_7326175 : Nat := 118140960795 + 7326175 * 2 ^ 59
def prefixEnd_7326175 : Nat := 4983230072969 + 3 ^ 40 * 7326175 * 2
def baseEnd_7326175 : Nat := 3761849133952979040320041

theorem tailTrace_7326175 : CollatzResearch.WordTrace tailWord_7326175 prefixEnd_7326175 3761849133952979040320041 := by
  unfold tailWord_7326175
  simp only [CollatzResearch.WordTrace]
  refine ⟨267207554233526660921107979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178138369489017773947405319 267207554233526660921107979)
  ·
    refine ⟨400811331350289991381661969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267207554233526660921107979 400811331350289991381661969)
    ·
      refine ⟨300608498512717493536246477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400811331350289991381661969 300608498512717493536246477)
      ·
        refine ⟨112728186942269060076092429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300608498512717493536246477 112728186942269060076092429)
        ·
          refine ⟨42273070103350897528534661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112728186942269060076092429 42273070103350897528534661)
          ·
            refine ⟨7926200644378293286600249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42273070103350897528534661 7926200644378293286600249)
            ·
              refine ⟨5944650483283719964950187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7926200644378293286600249 5944650483283719964950187)
              ·
                refine ⟨8916975724925579947425281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5944650483283719964950187 8916975724925579947425281)
                ·
                  refine ⟨6687731793694184960568961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8916975724925579947425281 6687731793694184960568961)
                  ·
                    refine ⟨5015798845270638720426721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6687731793694184960568961 5015798845270638720426721)
                    ·
                      refine ⟨3761849133952979040320041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015798845270638720426721 3761849133952979040320041)
                      ·
                        rfl

theorem cell23_7326175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_7326175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326175 prefixEnd_7326175 := by exact prefixLift 7326175
  have htrace : WordTrace (prefixWord ++ tailWord_7326175) baseStart_7326175 baseEnd_7326175 := by
    simpa [prefixWord, tailWord_7326175, baseEnd_7326175] using wordTrace_append hprefix tailTrace_7326175
  have hstable : (prefixWord ++ tailWord_7326175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326175).length < 2 ^ (prefixWord ++ tailWord_7326175).sum := by decide
  have hdescent : baseEnd_7326175 < baseStart_7326175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326177 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 4, 5]
def baseStart_7326177 : Nat := 118140960795 + 7326177 * 2 ^ 59
def prefixEnd_7326177 : Nat := 4983230072969 + 3 ^ 40 * 7326177 * 2
def baseEnd_7326177 : Nat := 1253950053638096010831677

theorem tailTrace_7326177 : CollatzResearch.WordTrace tailWord_7326177 prefixEnd_7326177 1253950053638096010831677 := by
  unfold tailWord_7326177
  simp only [CollatzResearch.WordTrace]
  refine ⟨267207627179519415262680785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178138418119679610175120523 267207627179519415262680785)
  ·
    refine ⟨200405720384639561447010589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267207627179519415262680785 200405720384639561447010589)
    ·
      refine ⟨75152145144239835542628971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200405720384639561447010589 75152145144239835542628971)
      ·
        refine ⟨112728217716359753313943457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75152145144239835542628971 112728217716359753313943457)
        ·
          refine ⟨84546163287269814985457593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112728217716359753313943457 84546163287269814985457593)
          ·
            refine ⟨63409622465452361239093195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84546163287269814985457593 63409622465452361239093195)
            ·
              refine ⟨95114433698178541858639793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63409622465452361239093195 95114433698178541858639793)
              ·
                refine ⟨71335825273633906393979845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95114433698178541858639793 71335825273633906393979845)
                ·
                  refine ⟨13375467238806357448871221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71335825273633906393979845 13375467238806357448871221)
                  ·
                    refine ⟨1253950053638096010831677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13375467238806357448871221 1253950053638096010831677)
                    ·
                      rfl

theorem cell23_7326177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_7326177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326177 prefixEnd_7326177 := by exact prefixLift 7326177
  have htrace : WordTrace (prefixWord ++ tailWord_7326177) baseStart_7326177 baseEnd_7326177 := by
    simpa [prefixWord, tailWord_7326177, baseEnd_7326177] using wordTrace_append hprefix tailTrace_7326177
  have hstable : (prefixWord ++ tailWord_7326177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326177).length < 2 ^ (prefixWord ++ tailWord_7326177).sum := by decide
  have hdescent : baseEnd_7326177 < baseStart_7326177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326215 : List Nat := [1, 1, 4, 3, 4, 1, 2, 2, 5]
def baseStart_7326215 : Nat := 118140960795 + 7326215 * 2 ^ 59
def prefixEnd_7326215 : Nat := 4983230072969 + 3 ^ 40 * 7326215 * 2
def baseEnd_7326215 : Nat := 417985519242128764868873

theorem tailTrace_7326215 : CollatzResearch.WordTrace tailWord_7326215 prefixEnd_7326215 417985519242128764868873 := by
  unfold tailWord_7326215
  simp only [CollatzResearch.WordTrace]
  refine ⟨267209013153381747752564099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178139342102254498501709399 267209013153381747752564099)
  ·
    refine ⟨400813519730072621628846149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267209013153381747752564099 400813519730072621628846149)
    ·
      refine ⟨75152534949388616555408653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 400813519730072621628846149 75152534949388616555408653)
      ·
        refine ⟨28182200606020731208278245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75152534949388616555408653 28182200606020731208278245)
        ·
          refine ⟨5284162613628887101552171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28182200606020731208278245 5284162613628887101552171)
          ·
            refine ⟨7926243920443330652328257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5284162613628887101552171 7926243920443330652328257)
            ·
              refine ⟨5944682940332497989246193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7926243920443330652328257 5944682940332497989246193)
              ·
                refine ⟨4458512205249373491934645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5944682940332497989246193 4458512205249373491934645)
                ·
                  refine ⟨417985519242128764868873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4458512205249373491934645 417985519242128764868873)
                  ·
                    rfl

theorem cell23_7326215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 5].length) (baseStart_7326215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326215 prefixEnd_7326215 := by exact prefixLift 7326215
  have htrace : WordTrace (prefixWord ++ tailWord_7326215) baseStart_7326215 baseEnd_7326215 := by
    simpa [prefixWord, tailWord_7326215, baseEnd_7326215] using wordTrace_append hprefix tailTrace_7326215
  have hstable : (prefixWord ++ tailWord_7326215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326215).length < 2 ^ (prefixWord ++ tailWord_7326215).sum := by decide
  have hdescent : baseEnd_7326215 < baseStart_7326215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326234 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3]
def baseStart_7326234 : Nat := 118140960795 + 7326234 * 2 ^ 59
def prefixEnd_7326234 : Nat := 4983230072969 + 3 ^ 40 * 7326234 * 2
def baseEnd_7326234 : Nat := 3761879429311594309482269

theorem tailTrace_7326234 : CollatzResearch.WordTrace tailWord_7326234 prefixEnd_7326234 3761879429311594309482269 := by
  unfold tailWord_7326234
  simp only [CollatzResearch.WordTrace]
  refine ⟨66802426535078228499376439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178139804093541942665003837 66802426535078228499376439)
  ·
    refine ⟨100203639802617342749064659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66802426535078228499376439 100203639802617342749064659)
    ·
      refine ⟨150305459703926014123596989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100203639802617342749064659 150305459703926014123596989)
      ·
        refine ⟨56364547388972255296348871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150305459703926014123596989 56364547388972255296348871)
        ·
          refine ⟨84546821083458382944523307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56364547388972255296348871 84546821083458382944523307)
          ·
            refine ⟨126820231625187574416784961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84546821083458382944523307 126820231625187574416784961)
            ·
              refine ⟨95115173718890680812588721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126820231625187574416784961 95115173718890680812588721)
              ·
                refine ⟨71336380289168010609441541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95115173718890680812588721 71336380289168010609441541)
                ·
                  refine ⟨13375571304219001989270289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71336380289168010609441541 13375571304219001989270289)
                  ·
                    refine ⟨10031678478164251491952717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13375571304219001989270289 10031678478164251491952717)
                    ·
                      refine ⟨3761879429311594309482269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10031678478164251491952717 3761879429311594309482269)
                      ·
                        rfl

theorem cell23_7326234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_7326234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326234 prefixEnd_7326234 := by exact prefixLift 7326234
  have htrace : WordTrace (prefixWord ++ tailWord_7326234) baseStart_7326234 baseEnd_7326234 := by
    simpa [prefixWord, tailWord_7326234, baseEnd_7326234] using wordTrace_append hprefix tailTrace_7326234
  have hstable : (prefixWord ++ tailWord_7326234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326234).length < 2 ^ (prefixWord ++ tailWord_7326234).sum := by decide
  have hdescent : baseEnd_7326234 < baseStart_7326234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326248 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_7326248 : Nat := 118140960795 + 7326248 * 2 ^ 59
def prefixEnd_7326248 : Nat := 4983230072969 + 3 ^ 40 * 7326248 * 2
def baseEnd_7326248 : Nat := 3761886618040757254707205

theorem tailTrace_7326248 : CollatzResearch.WordTrace tailWord_7326248 prefixEnd_7326248 3761886618040757254707205 := by
  unfold tailWord_7326248
  simp only [CollatzResearch.WordTrace]
  refine ⟨133605108381131097194257699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178140144508174796259010265 133605108381131097194257699)
  ·
    refine ⟨200407662571696645791386549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133605108381131097194257699 200407662571696645791386549)
    ·
      refine ⟨18788218366096560542942489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200407662571696645791386549 18788218366096560542942489)
      ·
        refine ⟨14091163774572420407206867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18788218366096560542942489 14091163774572420407206867)
        ·
          refine ⟨21136745661858630610810301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14091163774572420407206867 21136745661858630610810301)
          ·
            refine ⟨7926279623196986479053863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21136745661858630610810301 7926279623196986479053863)
            ·
              refine ⟨11889419434795479718580795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7926279623196986479053863 11889419434795479718580795)
              ·
                refine ⟨17834129152193219577871193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11889419434795479718580795 17834129152193219577871193)
                ·
                  refine ⟨13375596864144914683403395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17834129152193219577871193 13375596864144914683403395)
                  ·
                    refine ⟨20063395296217372025105093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13375596864144914683403395 20063395296217372025105093)
                    ·
                      refine ⟨3761886618040757254707205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20063395296217372025105093 3761886618040757254707205)
                      ·
                        rfl

theorem cell23_7326248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_7326248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326248 prefixEnd_7326248 := by exact prefixLift 7326248
  have htrace : WordTrace (prefixWord ++ tailWord_7326248) baseStart_7326248 baseEnd_7326248 := by
    simpa [prefixWord, tailWord_7326248, baseEnd_7326248] using wordTrace_append hprefix tailTrace_7326248
  have hstable : (prefixWord ++ tailWord_7326248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326248).length < 2 ^ (prefixWord ++ tailWord_7326248).sum := by decide
  have hdescent : baseEnd_7326248 < baseStart_7326248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326304 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 4]
def baseStart_7326304 : Nat := 118140960795 + 7326304 * 2 ^ 59
def prefixEnd_7326304 : Nat := 4983230072969 + 3 ^ 40 * 7326304 * 2
def baseEnd_7326304 : Nat := 3761915372957409035606947

theorem tailTrace_7326304 : CollatzResearch.WordTrace tailWord_7326304 prefixEnd_7326304 3761915372957409035606947 := by
  unfold tailWord_7326304
  simp only [CollatzResearch.WordTrace]
  refine ⟨133606129625029657976276983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178141506166706210635035977 133606129625029657976276983)
  ·
    refine ⟨200409194437544486964415475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133606129625029657976276983 200409194437544486964415475)
    ·
      refine ⟨300613791656316730446623213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200409194437544486964415475 300613791656316730446623213)
      ·
        refine ⟨112730171871118773917483705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300613791656316730446623213 112730171871118773917483705)
        ·
          refine ⟨84547628903339080438112779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112730171871118773917483705 84547628903339080438112779)
          ·
            refine ⟨126821443355008620657169169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84547628903339080438112779 126821443355008620657169169)
            ·
              refine ⟨95116082516256465492876877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126821443355008620657169169 95116082516256465492876877)
              ·
                refine ⟨35668530943596174559828829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95116082516256465492876877 35668530943596174559828829)
                ·
                  refine ⟨13375699103848565459935811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35668530943596174559828829 13375699103848565459935811)
                  ·
                    refine ⟨20063548655772848189903717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13375699103848565459935811 20063548655772848189903717)
                    ·
                      refine ⟨3761915372957409035606947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20063548655772848189903717 3761915372957409035606947)
                      ·
                        rfl

theorem cell23_7326304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_7326304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326304 prefixEnd_7326304 := by exact prefixLift 7326304
  have htrace : WordTrace (prefixWord ++ tailWord_7326304) baseStart_7326304 baseEnd_7326304 := by
    simpa [prefixWord, tailWord_7326304, baseEnd_7326304] using wordTrace_append hprefix tailTrace_7326304
  have hstable : (prefixWord ++ tailWord_7326304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326304).length < 2 ^ (prefixWord ++ tailWord_7326304).sum := by decide
  have hdescent : baseEnd_7326304 < baseStart_7326304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326314 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 3, 6]
def baseStart_7326314 : Nat := 118140960795 + 7326314 * 2 ^ 59
def prefixEnd_7326314 : Nat := 4983230072969 + 3 ^ 40 * 7326314 * 2
def baseEnd_7326314 : Nat := 1253973502587984665493967

theorem tailTrace_7326314 : CollatzResearch.WordTrace tailWord_7326314 prefixEnd_7326314 1253973502587984665493967 := by
  unfold tailWord_7326314
  simp only [CollatzResearch.WordTrace]
  refine ⟨66803155995005771915104499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178141749320015391773611997 66803155995005771915104499)
  ·
    refine ⟨100204733992508657872656749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66803155995005771915104499 100204733992508657872656749)
    ·
      refine ⟨37576775247190746702246281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100204733992508657872656749 37576775247190746702246281)
      ·
        refine ⟨28182581435393060026684711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37576775247190746702246281 28182581435393060026684711)
        ·
          refine ⟨42273872153089590040027067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28182581435393060026684711 42273872153089590040027067)
          ·
            refine ⟨63410808229634385060040601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42273872153089590040027067 63410808229634385060040601)
            ·
              refine ⟨47558106172225788795030451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63410808229634385060040601 47558106172225788795030451)
              ·
                refine ⟨71337159258338683192545677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47558106172225788795030451 71337159258338683192545677)
                ·
                  refine ⟨26751434721877006197204629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71337159258338683192545677 26751434721877006197204629)
                  ·
                    refine ⟨1253973502587984665493967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26751434721877006197204629 1253973502587984665493967)
                    ·
                      rfl

theorem cell23_7326314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_7326314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326314 prefixEnd_7326314 := by exact prefixLift 7326314
  have htrace : WordTrace (prefixWord ++ tailWord_7326314) baseStart_7326314 baseEnd_7326314 := by
    simpa [prefixWord, tailWord_7326314, baseEnd_7326314] using wordTrace_append hprefix tailTrace_7326314
  have hstable : (prefixWord ++ tailWord_7326314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326314).length < 2 ^ (prefixWord ++ tailWord_7326314).sum := by decide
  have hdescent : baseEnd_7326314 < baseStart_7326314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326325 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_7326325 : Nat := 118140960795 + 7326325 * 2 ^ 59
def prefixEnd_7326325 : Nat := 4983230072969 + 3 ^ 40 * 7326325 * 2
def baseEnd_7326325 : Nat := 3761926156051153453444351

theorem tailTrace_7326325 : CollatzResearch.WordTrace tailWord_7326325 prefixEnd_7326325 3761926156051153453444351 := by
  unfold tailWord_7326325
  simp only [CollatzResearch.WordTrace]
  refine ⟨267213025182983236539068429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178142016788655491026045619 267213025182983236539068429)
  ·
    refine ⟨100204884443618713702150661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267213025182983236539068429 100204884443618713702150661)
    ·
      refine ⟨18788415833178508819153249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100204884443618713702150661 18788415833178508819153249)
      ·
        refine ⟨14091311874883881614364937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18788415833178508819153249 14091311874883881614364937)
        ·
          refine ⟨10568483906162911210773703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14091311874883881614364937 10568483906162911210773703)
          ·
            refine ⟨15852725859244366816160555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10568483906162911210773703 15852725859244366816160555)
            ·
              refine ⟨23779088788866550224240833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15852725859244366816160555 23779088788866550224240833)
              ·
                refine ⟨17834316591649912668180625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23779088788866550224240833 17834316591649912668180625)
                ·
                  refine ⟨13375737443737434501135469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17834316591649912668180625 13375737443737434501135469)
                  ·
                    refine ⟨5015901541401537937925801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13375737443737434501135469 5015901541401537937925801)
                    ·
                      refine ⟨3761926156051153453444351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015901541401537937925801 3761926156051153453444351)
                      ·
                        rfl

theorem cell23_7326325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_7326325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326325 prefixEnd_7326325 := by exact prefixLift 7326325
  have htrace : WordTrace (prefixWord ++ tailWord_7326325) baseStart_7326325 baseEnd_7326325 := by
    simpa [prefixWord, tailWord_7326325, baseEnd_7326325] using wordTrace_append hprefix tailTrace_7326325
  have hstable : (prefixWord ++ tailWord_7326325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326325).length < 2 ^ (prefixWord ++ tailWord_7326325).sum := by decide
  have hdescent : baseEnd_7326325 < baseStart_7326325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326327 : List Nat := [1, 1, 3, 1, 1, 3, 13]
def baseStart_7326327 : Nat := 118140960795 + 7326327 * 2 ^ 59
def prefixEnd_7326327 : Nat := 4983230072969 + 3 ^ 40 * 7326327 * 2
def baseEnd_7326327 : Nat := 46443545469289659822461

theorem tailTrace_7326327 : CollatzResearch.WordTrace tailWord_7326327 prefixEnd_7326327 46443545469289659822461 := by
  unfold tailWord_7326327
  simp only [CollatzResearch.WordTrace]
  refine ⟨267213098128975990880641235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178142065419317327253760823 267213098128975990880641235)
  ·
    refine ⟨400819647193463986320961853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267213098128975990880641235 400819647193463986320961853)
    ·
      refine ⟨150307367697548994870360695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400819647193463986320961853 150307367697548994870360695)
      ·
        refine ⟨225461051546323492305541043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150307367697548994870360695 225461051546323492305541043)
        ·
          refine ⟨338191577319485238458311565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225461051546323492305541043 338191577319485238458311565)
          ·
            refine ⟨126821841494806964421866837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338191577319485238458311565 126821841494806964421866837)
            ·
              refine ⟨46443545469289659822461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 126821841494806964421866837 46443545469289659822461)
              ·
                rfl

theorem cell23_7326327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 13].length) (baseStart_7326327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326327 prefixEnd_7326327 := by exact prefixLift 7326327
  have htrace : WordTrace (prefixWord ++ tailWord_7326327) baseStart_7326327 baseEnd_7326327 := by
    simpa [prefixWord, tailWord_7326327, baseEnd_7326327] using wordTrace_append hprefix tailTrace_7326327
  have hstable : (prefixWord ++ tailWord_7326327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326327).length < 2 ^ (prefixWord ++ tailWord_7326327).sum := by decide
  have hdescent : baseEnd_7326327 < baseStart_7326327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326371 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 4, 1, 3]
def baseStart_7326371 : Nat := 118140960795 + 7326371 * 2 ^ 59
def prefixEnd_7326371 : Nat := 4983230072969 + 3 ^ 40 * 7326371 * 2
def baseEnd_7326371 : Nat := 3761949776161260273469139

theorem tailTrace_7326371 : CollatzResearch.WordTrace tailWord_7326371 prefixEnd_7326371 3761949776161260273469139 := by
  unfold tailWord_7326371
  simp only [CollatzResearch.WordTrace]
  refine ⟨267214702940816586395242967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178143135293877724263495311 267214702940816586395242967)
  ·
    refine ⟨400822054411224879592864451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267214702940816586395242967 400822054411224879592864451)
    ·
      refine ⟨601233081616837319389296677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400822054411224879592864451 601233081616837319389296677)
      ·
        refine ⟨112731202803156997385493127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 601233081616837319389296677 112731202803156997385493127)
        ·
          refine ⟨169096804204735496078239691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112731202803156997385493127 169096804204735496078239691)
          ·
            refine ⟨253645206307103244117359537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169096804204735496078239691 253645206307103244117359537)
            ·
              refine ⟨190233904730327433088019653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253645206307103244117359537 190233904730327433088019653)
              ·
                refine ⟨35668857136936393704003685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190233904730327433088019653 35668857136936393704003685)
                ·
                  refine ⟨6687910713175573819500691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35668857136936393704003685 6687910713175573819500691)
                  ·
                    refine ⟨10031866069763360729251037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6687910713175573819500691 10031866069763360729251037)
                    ·
                      refine ⟨3761949776161260273469139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10031866069763360729251037 3761949776161260273469139)
                      ·
                        rfl

theorem cell23_7326371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_7326371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326371 prefixEnd_7326371 := by exact prefixLift 7326371
  have htrace : WordTrace (prefixWord ++ tailWord_7326371) baseStart_7326371 baseEnd_7326371 := by
    simpa [prefixWord, tailWord_7326371, baseEnd_7326371] using wordTrace_append hprefix tailTrace_7326371
  have hstable : (prefixWord ++ tailWord_7326371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326371).length < 2 ^ (prefixWord ++ tailWord_7326371).sum := by decide
  have hdescent : baseEnd_7326371 < baseStart_7326371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326375 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_7326375 : Nat := 118140960795 + 7326375 * 2 ^ 59
def prefixEnd_7326375 : Nat := 4983230072969 + 3 ^ 40 * 7326375 * 2
def baseEnd_7326375 : Nat := 3761951830083878257819121

theorem tailTrace_7326375 : CollatzResearch.WordTrace tailWord_7326375 prefixEnd_7326375 3761951830083878257819121 := by
  unfold tailWord_7326375
  simp only [CollatzResearch.WordTrace]
  refine ⟨267214848832802095078388579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178143232555201396718925719 267214848832802095078388579)
  ·
    refine ⟨400822273249203142617582869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267214848832802095078388579 400822273249203142617582869)
    ·
      refine ⟨18788544058556397310199197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 400822273249203142617582869 18788544058556397310199197)
      ·
        refine ⟨7045704021958648991324699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18788544058556397310199197 7045704021958648991324699)
        ·
          refine ⟨10568556032937973486987049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7045704021958648991324699 10568556032937973486987049)
          ·
            refine ⟨7926417024703480115240287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10568556032937973486987049 7926417024703480115240287)
            ·
              refine ⟨11889625537055220172860431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7926417024703480115240287 11889625537055220172860431)
              ·
                refine ⟨17834438305582830259290647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11889625537055220172860431 17834438305582830259290647)
                ·
                  refine ⟨26751657458374245388935971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17834438305582830259290647 26751657458374245388935971)
                  ·
                    refine ⟨40127486187561368083403957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26751657458374245388935971 40127486187561368083403957)
                    ·
                      refine ⟨3761951830083878257819121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40127486187561368083403957 3761951830083878257819121)
                      ·
                        rfl

theorem cell23_7326375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_7326375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326375 prefixEnd_7326375 := by exact prefixLift 7326375
  have htrace : WordTrace (prefixWord ++ tailWord_7326375) baseStart_7326375 baseEnd_7326375 := by
    simpa [prefixWord, tailWord_7326375, baseEnd_7326375] using wordTrace_append hprefix tailTrace_7326375
  have hstable : (prefixWord ++ tailWord_7326375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326375).length < 2 ^ (prefixWord ++ tailWord_7326375).sum := by decide
  have hdescent : baseEnd_7326375 < baseStart_7326375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326378 : List Nat := [3, 1, 5, 2, 2, 10]
def baseStart_7326378 : Nat := 118140960795 + 7326378 * 2 ^ 59
def prefixEnd_7326378 : Nat := 4983230072969 + 3 ^ 40 * 7326378 * 2
def baseEnd_7326378 : Nat := 15481289590641324057949

theorem tailTrace_7326378 : CollatzResearch.WordTrace tailWord_7326378 prefixEnd_7326378 15481289590641324057949 := by
  unfold tailWord_7326378
  simp only [CollatzResearch.WordTrace]
  refine ⟨66803739562947806647686947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178143305501194151060498525 66803739562947806647686947)
  ·
    refine ⟨100205609344421709971530421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66803739562947806647686947 100205609344421709971530421)
    ·
      refine ⟨9394275876039535309830977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100205609344421709971530421 9394275876039535309830977)
      ·
        refine ⟨7045706907029651482373233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9394275876039535309830977 7045706907029651482373233)
        ·
          refine ⟨5284280180272238611779925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7045706907029651482373233 5284280180272238611779925)
          ·
            refine ⟨15481289590641324057949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5284280180272238611779925 15481289590641324057949)
            ·
              rfl

theorem cell23_7326378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 10].length) (baseStart_7326378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326378 prefixEnd_7326378 := by exact prefixLift 7326378
  have htrace : WordTrace (prefixWord ++ tailWord_7326378) baseStart_7326378 baseEnd_7326378 := by
    simpa [prefixWord, tailWord_7326378, baseEnd_7326378] using wordTrace_append hprefix tailTrace_7326378
  have hstable : (prefixWord ++ tailWord_7326378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326378).length < 2 ^ (prefixWord ++ tailWord_7326378).sum := by decide
  have hdescent : baseEnd_7326378 < baseStart_7326378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326389 : List Nat := [1, 3, 3, 3, 1, 1, 4, 2, 1, 2, 2]
def baseStart_7326389 : Nat := 118140960795 + 7326389 * 2 ^ 59
def prefixEnd_7326389 : Nat := 4983230072969 + 3 ^ 40 * 7326389 * 2
def baseEnd_7326389 : Nat := 3761959018813041203044057

theorem tailTrace_7326389 : CollatzResearch.WordTrace tailWord_7326389 prefixEnd_7326389 3761959018813041203044057 := by
  unfold tailWord_7326389
  simp only [CollatzResearch.WordTrace]
  refine ⟨267215359454751375469398221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178143572969834250312932147 267215359454751375469398221)
  ·
    refine ⟨100205759795531765801024333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267215359454751375469398221 100205759795531765801024333)
    ·
      refine ⟨37577159923324412175384125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100205759795531765801024333 37577159923324412175384125)
      ·
        refine ⟨14091434971246654565769047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37577159923324412175384125 14091434971246654565769047)
        ·
          refine ⟨21137152456869981848653571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14091434971246654565769047 21137152456869981848653571)
          ·
            refine ⟨31705728685304972772980357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21137152456869981848653571 31705728685304972772980357)
            ·
              refine ⟨5944824128494682394933817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31705728685304972772980357 5944824128494682394933817)
              ·
                refine ⟨4458618096371011796200363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5944824128494682394933817 4458618096371011796200363)
                ·
                  refine ⟨6687927144556517694300545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4458618096371011796200363 6687927144556517694300545)
                  ·
                    refine ⟨5015945358417388270725409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6687927144556517694300545 5015945358417388270725409)
                    ·
                      refine ⟨3761959018813041203044057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015945358417388270725409 3761959018813041203044057)
                      ·
                        rfl

theorem cell23_7326389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_7326389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326389 prefixEnd_7326389 := by exact prefixLift 7326389
  have htrace : WordTrace (prefixWord ++ tailWord_7326389) baseStart_7326389 baseEnd_7326389 := by
    simpa [prefixWord, tailWord_7326389, baseEnd_7326389] using wordTrace_append hprefix tailTrace_7326389
  have hstable : (prefixWord ++ tailWord_7326389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326389).length < 2 ^ (prefixWord ++ tailWord_7326389).sum := by decide
  have hdescent : baseEnd_7326389 < baseStart_7326389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326394 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_7326394 : Nat := 118140960795 + 7326394 * 2 ^ 59
def prefixEnd_7326394 : Nat := 4983230072969 + 3 ^ 40 * 7326394 * 2
def baseEnd_7326394 : Nat := 3761961586216313683481533

theorem tailTrace_7326394 : CollatzResearch.WordTrace tailWord_7326394 prefixEnd_7326394 3761961586216313683481533 := by
  unfold tailWord_7326394
  simp only [CollatzResearch.WordTrace]
  refine ⟨66803885454933315330832559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178143694546488840882220157 66803885454933315330832559)
  ·
    refine ⟨100205828182399972996248839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66803885454933315330832559 100205828182399972996248839)
    ·
      refine ⟨150308742273599959494373259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100205828182399972996248839 150308742273599959494373259)
      ·
        refine ⟨225463113410399939241559889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150308742273599959494373259 225463113410399939241559889)
        ·
          refine ⟨169097335057799954431169917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225463113410399939241559889 169097335057799954431169917)
          ·
            refine ⟨63411500646674982911688719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169097335057799954431169917 63411500646674982911688719)
            ·
              refine ⟨95117250970012474367533079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63411500646674982911688719 95117250970012474367533079)
              ·
                refine ⟨142675876455018711551299619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95117250970012474367533079 142675876455018711551299619)
                ·
                  refine ⟨214013814682528067326949429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142675876455018711551299619 214013814682528067326949429)
                  ·
                    refine ⟨20063795126487006311901509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 214013814682528067326949429 20063795126487006311901509)
                    ·
                      refine ⟨3761961586216313683481533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20063795126487006311901509 3761961586216313683481533)
                      ·
                        rfl

theorem cell23_7326394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_7326394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326394 prefixEnd_7326394 := by exact prefixLift 7326394
  have htrace : WordTrace (prefixWord ++ tailWord_7326394) baseStart_7326394 baseEnd_7326394 := by
    simpa [prefixWord, tailWord_7326394, baseEnd_7326394] using wordTrace_append hprefix tailTrace_7326394
  have hstable : (prefixWord ++ tailWord_7326394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326394).length < 2 ^ (prefixWord ++ tailWord_7326394).sum := by decide
  have hdescent : baseEnd_7326394 < baseStart_7326394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326398 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_7326398 : Nat := 118140960795 + 7326398 * 2 ^ 59
def prefixEnd_7326398 : Nat := 4983230072969 + 3 ^ 40 * 7326398 * 2
def baseEnd_7326398 : Nat := 3761963640138931667831515

theorem tailTrace_7326398 : CollatzResearch.WordTrace tailWord_7326398 prefixEnd_7326398 3761963640138931667831515 := by
  unfold tailWord_7326398
  simp only [CollatzResearch.WordTrace]
  refine ⟨33401960963964846250809481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178143791807812513337650565 33401960963964846250809481)
  ·
    refine ⟨25051470722973634688107111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33401960963964846250809481 25051470722973634688107111)
    ·
      refine ⟨37577206084460452032160667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25051470722973634688107111 37577206084460452032160667)
      ·
        refine ⟨56365809126690678048241001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37577206084460452032160667 56365809126690678048241001)
        ·
          refine ⟨42274356845018008536180751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56365809126690678048241001 42274356845018008536180751)
          ·
            refine ⟨63411535267527012804271127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42274356845018008536180751 63411535267527012804271127)
            ·
              refine ⟨95117302901290519206406691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63411535267527012804271127 95117302901290519206406691)
              ·
                refine ⟨142675954351935778809610037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95117302901290519206406691 142675954351935778809610037)
                ·
                  refine ⟨13375870720493979263400941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142675954351935778809610037 13375870720493979263400941)
                  ·
                    refine ⟨5015951520185242223775353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13375870720493979263400941 5015951520185242223775353)
                    ·
                      refine ⟨3761963640138931667831515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015951520185242223775353 3761963640138931667831515)
                      ·
                        rfl

theorem cell23_7326398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_7326398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326398 prefixEnd_7326398 := by exact prefixLift 7326398
  have htrace : WordTrace (prefixWord ++ tailWord_7326398) baseStart_7326398 baseEnd_7326398 := by
    simpa [prefixWord, tailWord_7326398, baseEnd_7326398] using wordTrace_append hprefix tailTrace_7326398
  have hstable : (prefixWord ++ tailWord_7326398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326398).length < 2 ^ (prefixWord ++ tailWord_7326398).sum := by decide
  have hdescent : baseEnd_7326398 < baseStart_7326398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326445 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_7326445 : Nat := 118140960795 + 7326445 * 2 ^ 59
def prefixEnd_7326445 : Nat := 4983230072969 + 3 ^ 40 * 7326445 * 2
def baseEnd_7326445 : Nat := 3761987773729692983943799

theorem tailTrace_7326445 : CollatzResearch.WordTrace tailWord_7326445 prefixEnd_7326445 3761987773729692983943799 := by
  unfold tailWord_7326445
  simp only [CollatzResearch.WordTrace]
  refine ⟨267217401942548497033436789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178144934628365664688957859 267217401942548497033436789)
  ·
    refine ⟨25051631432113921596884699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267217401942548497033436789 25051631432113921596884699)
    ·
      refine ⟨37577447148170882395327049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25051631432113921596884699 37577447148170882395327049)
      ·
        refine ⟨28183085361128161796495287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37577447148170882395327049 28183085361128161796495287)
        ·
          refine ⟨42274628041692242694742931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28183085361128161796495287 42274628041692242694742931)
          ·
            refine ⟨63411942062538364042114397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42274628041692242694742931 63411942062538364042114397)
            ·
              refine ⟨23779478273451886515792899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63411942062538364042114397 23779478273451886515792899)
              ·
                refine ⟨35669217410177829773689349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23779478273451886515792899 35669217410177829773689349)
                ·
                  refine ⟨6687978264408343082566753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35669217410177829773689349 6687978264408343082566753)
                  ·
                    refine ⟨5015983698306257311925065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6687978264408343082566753 5015983698306257311925065)
                    ·
                      refine ⟨3761987773729692983943799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015983698306257311925065 3761987773729692983943799)
                      ·
                        rfl

theorem cell23_7326445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_7326445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326445 prefixEnd_7326445 := by exact prefixLift 7326445
  have htrace : WordTrace (prefixWord ++ tailWord_7326445) baseStart_7326445 baseEnd_7326445 := by
    simpa [prefixWord, tailWord_7326445, baseEnd_7326445] using wordTrace_append hprefix tailTrace_7326445
  have hstable : (prefixWord ++ tailWord_7326445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326445).length < 2 ^ (prefixWord ++ tailWord_7326445).sum := by decide
  have hdescent : baseEnd_7326445 < baseStart_7326445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326461 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_7326461 : Nat := 118140960795 + 7326461 * 2 ^ 59
def prefixEnd_7326461 : Nat := 4983230072969 + 3 ^ 40 * 7326461 * 2
def baseEnd_7326461 : Nat := 3761995989420164921343725

theorem tailTrace_7326461 : CollatzResearch.WordTrace tailWord_7326461 prefixEnd_7326461 3761995989420164921343725 := by
  unfold tailWord_7326461
  simp only [CollatzResearch.WordTrace]
  refine ⟨267217985510490531766019237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178145323673660354510679491 267217985510490531766019237)
  ·
    refine ⟨50103372283216974706128607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267217985510490531766019237 50103372283216974706128607)
    ·
      refine ⟨75155058424825462059192911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50103372283216974706128607 75155058424825462059192911)
      ·
        refine ⟨112732587637238193088789367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75155058424825462059192911 112732587637238193088789367)
        ·
          refine ⟨169098881455857289633184051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112732587637238193088789367 169098881455857289633184051)
          ·
            refine ⟨253648322183785934449776077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169098881455857289633184051 253648322183785934449776077)
            ·
              refine ⟨95118120818919725418666029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253648322183785934449776077 95118120818919725418666029)
              ·
                refine ⟨35669295307094897031999761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95118120818919725418666029 35669295307094897031999761)
                ·
                  refine ⟨26751971480321172773999821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35669295307094897031999761 26751971480321172773999821)
                  ·
                    refine ⟨10031989305120439790249933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26751971480321172773999821 10031989305120439790249933)
                    ·
                      refine ⟨3761995989420164921343725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10031989305120439790249933 3761995989420164921343725)
                      ·
                        rfl

theorem cell23_7326461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_7326461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326461 prefixEnd_7326461 := by exact prefixLift 7326461
  have htrace : WordTrace (prefixWord ++ tailWord_7326461) baseStart_7326461 baseEnd_7326461 := by
    simpa [prefixWord, tailWord_7326461, baseEnd_7326461] using wordTrace_append hprefix tailTrace_7326461
  have hstable : (prefixWord ++ tailWord_7326461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326461).length < 2 ^ (prefixWord ++ tailWord_7326461).sum := by decide
  have hdescent : baseEnd_7326461 < baseStart_7326461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326462 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_7326462 : Nat := 118140960795 + 7326462 * 2 ^ 59
def prefixEnd_7326462 : Nat := 4983230072969 + 3 ^ 40 * 7326462 * 2
def baseEnd_7326462 : Nat := 3761996502900819417431221

theorem tailTrace_7326462 : CollatzResearch.WordTrace tailWord_7326462 prefixEnd_7326462 3761996502900819417431221 := by
  unfold tailWord_7326462
  simp only [CollatzResearch.WordTrace]
  refine ⟨33402252747935863617100705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178145347988991272624537093 33402252747935863617100705)
  ·
    refine ⟨25051689560951897712825529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33402252747935863617100705 25051689560951897712825529)
    ·
      refine ⟨18788767170713923284619147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25051689560951897712825529 18788767170713923284619147)
      ·
        refine ⟨28183150756070884926928721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18788767170713923284619147 28183150756070884926928721)
        ·
          refine ⟨21137363067053163695196541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28183150756070884926928721 21137363067053163695196541)
          ·
            refine ⟨7926511150144936385698703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21137363067053163695196541 7926511150144936385698703)
            ·
              refine ⟨11889766725217404578548055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7926511150144936385698703 11889766725217404578548055)
              ·
                refine ⟨17834650087826106867822083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11889766725217404578548055 17834650087826106867822083)
                ·
                  refine ⟨26751975131739160301733125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17834650087826106867822083 26751975131739160301733125)
                  ·
                    refine ⟨5015995337201092556574961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26751975131739160301733125 5015995337201092556574961)
                    ·
                      refine ⟨3761996502900819417431221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5015995337201092556574961 3761996502900819417431221)
                      ·
                        rfl

theorem cell23_7326462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_7326462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326462 prefixEnd_7326462 := by exact prefixLift 7326462
  have htrace : WordTrace (prefixWord ++ tailWord_7326462) baseStart_7326462 baseEnd_7326462 := by
    simpa [prefixWord, tailWord_7326462, baseEnd_7326462] using wordTrace_append hprefix tailTrace_7326462
  have hstable : (prefixWord ++ tailWord_7326462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326462).length < 2 ^ (prefixWord ++ tailWord_7326462).sum := by decide
  have hdescent : baseEnd_7326462 < baseStart_7326462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326498 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_7326498 : Nat := 118140960795 + 7326498 * 2 ^ 59
def prefixEnd_7326498 : Nat := 4983230072969 + 3 ^ 40 * 7326498 * 2
def baseEnd_7326498 : Nat := 1254004996068127092193685

theorem tailTrace_7326498 : CollatzResearch.WordTrace tailWord_7326498 prefixEnd_7326498 1254004996068127092193685 := by
  unfold tailWord_7326498
  simp only [CollatzResearch.WordTrace]
  refine ⟨66804833752839121771279037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178146223340904324723410765 66804833752839121771279037)
  ·
    refine ⟨25051812657314670664229639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66804833752839121771279037 25051812657314670664229639)
    ·
      refine ⟨37577718985972005996344459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25051812657314670664229639 37577718985972005996344459)
      ·
        refine ⟨56366578478958008994516689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37577718985972005996344459 56366578478958008994516689)
        ·
          refine ⟨42274933859218506745887517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56366578478958008994516689 42274933859218506745887517)
          ·
            refine ⟨15853100197206940029707819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42274933859218506745887517 15853100197206940029707819)
            ·
              refine ⟨23779650295810410044561729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15853100197206940029707819 23779650295810410044561729)
              ·
                refine ⟨17834737721857807533421297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23779650295810410044561729 17834737721857807533421297)
                ·
                  refine ⟨13376053291393355650065973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17834737721857807533421297 13376053291393355650065973)
                  ·
                    refine ⟨1254004996068127092193685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13376053291393355650065973 1254004996068127092193685)
                    ·
                      rfl

theorem cell23_7326498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_7326498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326498 prefixEnd_7326498 := by exact prefixLift 7326498
  have htrace : WordTrace (prefixWord ++ tailWord_7326498) baseStart_7326498 baseEnd_7326498 := by
    simpa [prefixWord, tailWord_7326498, baseEnd_7326498] using wordTrace_append hprefix tailTrace_7326498
  have hstable : (prefixWord ++ tailWord_7326498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326498).length < 2 ^ (prefixWord ++ tailWord_7326498).sum := by decide
  have hdescent : baseEnd_7326498 < baseStart_7326498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326532 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_7326532 : Nat := 118140960795 + 7326532 * 2 ^ 59
def prefixEnd_7326532 : Nat := 4983230072969 + 3 ^ 40 * 7326532 * 2
def baseEnd_7326532 : Nat := 1254010815515544714518633

theorem tailTrace_7326532 : CollatzResearch.WordTrace tailWord_7326532 prefixEnd_7326532 1254010815515544714518633 := by
  unfold tailWord_7326532
  simp only [CollatzResearch.WordTrace]
  refine ⟨133610287546616655445926925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178147050062155540594569233 133610287546616655445926925)
  ·
    refine ⟨50103857829981245792222597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133610287546616655445926925 50103857829981245792222597)
    ·
      refine ⟨9394473343121483586041737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50103857829981245792222597 9394473343121483586041737)
      ·
        refine ⟨7045855007341112689531303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9394473343121483586041737 7045855007341112689531303)
        ·
          refine ⟨10568782511011669034296955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7045855007341112689531303 10568782511011669034296955)
          ·
            refine ⟨15853173766517503551445433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10568782511011669034296955 15853173766517503551445433)
            ·
              refine ⟨11889880324888127663584075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15853173766517503551445433 11889880324888127663584075)
              ·
                refine ⟨17834820487332191495376113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11889880324888127663584075 17834820487332191495376113)
                ·
                  refine ⟨13376115365499143621532085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17834820487332191495376113 13376115365499143621532085)
                  ·
                    refine ⟨1254010815515544714518633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13376115365499143621532085 1254010815515544714518633)
                    ·
                      rfl

theorem cell23_7326532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_7326532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326532 prefixEnd_7326532 := by exact prefixLift 7326532
  have htrace : WordTrace (prefixWord ++ tailWord_7326532) baseStart_7326532 baseEnd_7326532 := by
    simpa [prefixWord, tailWord_7326532, baseEnd_7326532] using wordTrace_append hprefix tailTrace_7326532
  have hstable : (prefixWord ++ tailWord_7326532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326532).length < 2 ^ (prefixWord ++ tailWord_7326532).sum := by decide
  have hdescent : baseEnd_7326532 < baseStart_7326532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326571 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 3, 5]
def baseStart_7326571 : Nat := 118140960795 + 7326571 * 2 ^ 59
def prefixEnd_7326571 : Nat := 4983230072969 + 3 ^ 40 * 7326571 * 2
def baseEnd_7326571 : Nat := 1254017490764053163656073

theorem tailTrace_7326571 : CollatzResearch.WordTrace tailWord_7326571 prefixEnd_7326571 1254017490764053163656073 := by
  unfold tailWord_7326571
  simp only [CollatzResearch.WordTrace]
  refine ⟨267221997540092020552523567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178147998360061347035015711 267221997540092020552523567)
  ·
    refine ⟨400832996310138030828785351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267221997540092020552523567 400832996310138030828785351)
    ·
      refine ⟨601249494465207046243178027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400832996310138030828785351 601249494465207046243178027)
      ·
        refine ⟨901874241697810569364767041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601249494465207046243178027 901874241697810569364767041)
        ·
          refine ⟨676405681273357927023575281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 901874241697810569364767041 676405681273357927023575281)
          ·
            refine ⟨507304260955018445267681461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 676405681273357927023575281 507304260955018445267681461)
            ·
              refine ⟨47559774464532979243845137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 507304260955018445267681461 47559774464532979243845137)
              ·
                refine ⟨35669830848399734432883853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47559774464532979243845137 35669830848399734432883853)
                ·
                  refine ⟨13376186568149900412331445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35669830848399734432883853 13376186568149900412331445)
                  ·
                    refine ⟨1254017490764053163656073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13376186568149900412331445 1254017490764053163656073)
                    ·
                      rfl

theorem cell23_7326571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 5].length) (baseStart_7326571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326571 prefixEnd_7326571 := by exact prefixLift 7326571
  have htrace : WordTrace (prefixWord ++ tailWord_7326571) baseStart_7326571 baseEnd_7326571 := by
    simpa [prefixWord, tailWord_7326571, baseEnd_7326571] using wordTrace_append hprefix tailTrace_7326571
  have hstable : (prefixWord ++ tailWord_7326571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326571).length < 2 ^ (prefixWord ++ tailWord_7326571).sum := by decide
  have hdescent : baseEnd_7326571 < baseStart_7326571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326585 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 3, 1, 3]
def baseStart_7326585 : Nat := 118140960795 + 7326585 * 2 ^ 59
def prefixEnd_7326585 : Nat := 4983230072969 + 3 ^ 40 * 7326585 * 2
def baseEnd_7326585 : Nat := 3762059661021322436193155

theorem tailTrace_7326585 : CollatzResearch.WordTrace tailWord_7326585 prefixEnd_7326585 3762059661021322436193155 := by
  unfold tailWord_7326585
  simp only [CollatzResearch.WordTrace]
  refine ⟨267222508162041300943533209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178148338774694200629022139 267222508162041300943533209)
  ·
    refine ⟨200416881121530975707649907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267222508162041300943533209 200416881121530975707649907)
    ·
      refine ⟨300625321682296463561474861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200416881121530975707649907 300625321682296463561474861)
      ·
        refine ⟨112734495630861173835553073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300625321682296463561474861 112734495630861173835553073)
        ·
          refine ⟨84550871723145880376664805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112734495630861173835553073 84550871723145880376664805)
          ·
            refine ⟨15853288448089852570624651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84550871723145880376664805 15853288448089852570624651)
            ·
              refine ⟨23779932672134778855936977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15853288448089852570624651 23779932672134778855936977)
              ·
                refine ⟨17834949504101084141952733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23779932672134778855936977 17834949504101084141952733)
                ·
                  refine ⟨6688106064037906553232275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17834949504101084141952733 6688106064037906553232275)
                  ·
                    refine ⟨10032159096056859829848413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6688106064037906553232275 10032159096056859829848413)
                    ·
                      refine ⟨3762059661021322436193155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10032159096056859829848413 3762059661021322436193155)
                      ·
                        rfl

theorem cell23_7326585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_7326585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326585 prefixEnd_7326585 := by exact prefixLift 7326585
  have htrace : WordTrace (prefixWord ++ tailWord_7326585) baseStart_7326585 baseEnd_7326585 := by
    simpa [prefixWord, tailWord_7326585, baseEnd_7326585] using wordTrace_append hprefix tailTrace_7326585
  have hstable : (prefixWord ++ tailWord_7326585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326585).length < 2 ^ (prefixWord ++ tailWord_7326585).sum := by decide
  have hdescent : baseEnd_7326585 < baseStart_7326585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326628 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_7326628 : Nat := 118140960795 + 7326628 * 2 ^ 59
def prefixEnd_7326628 : Nat := 4983230072969 + 3 ^ 40 * 7326628 * 2
def baseEnd_7326628 : Nat := 3762081740689465767955457

theorem tailTrace_7326628 : CollatzResearch.WordTrace tailWord_7326628 prefixEnd_7326628 3762081740689465767955457 := by
  unfold tailWord_7326628
  simp only [CollatzResearch.WordTrace]
  refine ⟨133612038250442759643674269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178149384333923679524899025 133612038250442759643674269)
  ·
    refine ⟨50104514343916034866377851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133612038250442759643674269 50104514343916034866377851)
    ·
      refine ⟨75156771515874052299566777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50104514343916034866377851 75156771515874052299566777)
      ·
        refine ⟨56367578636905539224675083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75156771515874052299566777 56367578636905539224675083)
        ·
          refine ⟨84551367955358308837012625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56367578636905539224675083 84551367955358308837012625)
          ·
            refine ⟨63413525966518731627759469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84551367955358308837012625 63413525966518731627759469)
            ·
              refine ⟨23780072237444524360409801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63413525966518731627759469 23780072237444524360409801)
              ·
                refine ⟨17835054178083393270307351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23780072237444524360409801 17835054178083393270307351)
                ·
                  refine ⟨26752581267125089905461027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17835054178083393270307351 26752581267125089905461027)
                  ·
                    refine ⟨40128871900687634858191541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26752581267125089905461027 40128871900687634858191541)
                    ·
                      refine ⟨3762081740689465767955457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40128871900687634858191541 3762081740689465767955457)
                      ·
                        rfl

theorem cell23_7326628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_7326628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326628 prefixEnd_7326628 := by exact prefixLift 7326628
  have htrace : WordTrace (prefixWord ++ tailWord_7326628) baseStart_7326628 baseEnd_7326628 := by
    simpa [prefixWord, tailWord_7326628, baseEnd_7326628] using wordTrace_append hprefix tailTrace_7326628
  have hstable : (prefixWord ++ tailWord_7326628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326628).length < 2 ^ (prefixWord ++ tailWord_7326628).sum := by decide
  have hdescent : baseEnd_7326628 < baseStart_7326628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326648 : List Nat := [2, 1, 2, 1, 2, 4, 4, 7]
def baseStart_7326648 : Nat := 118140960795 + 7326648 * 2 ^ 59
def prefixEnd_7326648 : Nat := 4983230072969 + 3 ^ 40 * 7326648 * 2
def baseEnd_7326648 : Nat := 139336741122316877396495

theorem tailTrace_7326648 : CollatzResearch.WordTrace tailWord_7326648 prefixEnd_7326648 139336741122316877396495 := by
  unfold tailWord_7326648
  simp only [CollatzResearch.WordTrace]
  refine ⟨133612402980406531351538299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178149870640542041802051065 133612402980406531351538299)
  ·
    refine ⟨200418604470609797027307449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133612402980406531351538299 200418604470609797027307449)
    ·
      refine ⟨150313953352957347770480587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200418604470609797027307449 150313953352957347770480587)
      ·
        refine ⟨225470930029436021655720881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150313953352957347770480587 225470930029436021655720881)
        ·
          refine ⟨169103197522077016241790661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225470930029436021655720881 169103197522077016241790661)
          ·
            refine ⟨31706849535389440545335749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169103197522077016241790661 31706849535389440545335749)
            ·
              refine ⟨5945034287885520102250453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31706849535389440545335749 5945034287885520102250453)
              ·
                refine ⟨139336741122316877396495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5945034287885520102250453 139336741122316877396495)
                ·
                  rfl

theorem cell23_7326648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 7].length) (baseStart_7326648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326648 prefixEnd_7326648 := by exact prefixLift 7326648
  have htrace : WordTrace (prefixWord ++ tailWord_7326648) baseStart_7326648 baseEnd_7326648 := by
    simpa [prefixWord, tailWord_7326648, baseEnd_7326648] using wordTrace_append hprefix tailTrace_7326648
  have hstable : (prefixWord ++ tailWord_7326648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326648).length < 2 ^ (prefixWord ++ tailWord_7326648).sum := by decide
  have hdescent : baseEnd_7326648 < baseStart_7326648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326709 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7326709 : Nat := 118140960795 + 7326709 * 2 ^ 59
def prefixEnd_7326709 : Nat := 4983230072969 + 3 ^ 40 * 7326709 * 2
def baseEnd_7326709 : Nat := 3762123332622479951042585

theorem tailTrace_7326709 : CollatzResearch.WordTrace tailWord_7326709 prefixEnd_7326709 3762123332622479951042585 := by
  unfold tailWord_7326709
  simp only [CollatzResearch.WordTrace]
  refine ⟨267227030813592070121047181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178151353875728046747364787 267227030813592070121047181)
  ·
    refine ⟨100210136555097026295392693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267227030813592070121047181 100210136555097026295392693)
    ·
      refine ⟨9394700302040346215193065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100210136555097026295392693 9394700302040346215193065)
      ·
        refine ⟨7046025226530259661394799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9394700302040346215193065 7046025226530259661394799)
        ·
          refine ⟨10569037839795389492092199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7046025226530259661394799 10569037839795389492092199)
          ·
            refine ⟨15853556759693084238138299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10569037839795389492092199 15853556759693084238138299)
            ·
              refine ⟨23780335139539626357207449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15853556759693084238138299 23780335139539626357207449)
              ·
                refine ⟨17835251354654719767905587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23780335139539626357207449 17835251354654719767905587)
                ·
                  refine ⟨26752877031982079651858381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17835251354654719767905587 26752877031982079651858381)
                  ·
                    refine ⟨10032328886993279869446893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26752877031982079651858381 10032328886993279869446893)
                    ·
                      refine ⟨3762123332622479951042585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10032328886993279869446893 3762123332622479951042585)
                      ·
                        rfl

theorem cell23_7326709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7326709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326709 prefixEnd_7326709 := by exact prefixLift 7326709
  have htrace : WordTrace (prefixWord ++ tailWord_7326709) baseStart_7326709 baseEnd_7326709 := by
    simpa [prefixWord, tailWord_7326709, baseEnd_7326709] using wordTrace_append hprefix tailTrace_7326709
  have hstable : (prefixWord ++ tailWord_7326709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326709).length < 2 ^ (prefixWord ++ tailWord_7326709).sum := by decide
  have hdescent : baseEnd_7326709 < baseStart_7326709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326749 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_7326749 : Nat := 118140960795 + 7326749 * 2 ^ 59
def prefixEnd_7326749 : Nat := 4983230072969 + 3 ^ 40 * 7326749 * 2
def baseEnd_7326749 : Nat := 3762143871848659794542401

theorem tailTrace_7326749 : CollatzResearch.WordTrace tailWord_7326749 prefixEnd_7326749 3762143871848659794542401 := by
  unfold tailWord_7326749
  simp only [CollatzResearch.WordTrace]
  refine ⟨267228489733447156952503301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178152326488964771301668867 267228489733447156952503301)
  ·
    refine ⟨50105341825021341928594369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267228489733447156952503301 50105341825021341928594369)
    ·
      refine ⟨37579006368766006446445777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50105341825021341928594369 37579006368766006446445777)
      ·
        refine ⟨28184254776574504834834333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37579006368766006446445777 28184254776574504834834333)
        ·
          refine ⟨10569095541215439313062875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28184254776574504834834333 10569095541215439313062875)
          ·
            refine ⟨15853643311823158969594313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10569095541215439313062875 15853643311823158969594313)
            ·
              refine ⟨11890232483867369227195735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15853643311823158969594313 11890232483867369227195735)
              ·
                refine ⟨17835348725801053840793603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11890232483867369227195735 17835348725801053840793603)
                ·
                  refine ⟨26753023088701580761190405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17835348725801053840793603 26753023088701580761190405)
                  ·
                    refine ⟨5016191829131546392723201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26753023088701580761190405 5016191829131546392723201)
                    ·
                      refine ⟨3762143871848659794542401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5016191829131546392723201 3762143871848659794542401)
                      ·
                        rfl

theorem cell23_7326749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_7326749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326749 prefixEnd_7326749 := by exact prefixLift 7326749
  have htrace : WordTrace (prefixWord ++ tailWord_7326749) baseStart_7326749 baseEnd_7326749 := by
    simpa [prefixWord, tailWord_7326749, baseEnd_7326749] using wordTrace_append hprefix tailTrace_7326749
  have hstable : (prefixWord ++ tailWord_7326749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326749).length < 2 ^ (prefixWord ++ tailWord_7326749).sum := by decide
  have hdescent : baseEnd_7326749 < baseStart_7326749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326768 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 1, 7]
def baseStart_7326768 : Nat := 118140960795 + 7326768 * 2 ^ 59
def prefixEnd_7326768 : Nat := 4983230072969 + 3 ^ 40 * 7326768 * 2
def baseEnd_7326768 : Nat := 1254051209327031740068271

theorem tailTrace_7326768 : CollatzResearch.WordTrace tailWord_7326768 prefixEnd_7326768 1254051209327031740068271 := by
  unfold tailWord_7326768
  simp only [CollatzResearch.WordTrace]
  refine ⟨133614591360189161598722479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178152788480252215464963305 133614591360189161598722479)
  ·
    refine ⟨200421887040283742398083719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133614591360189161598722479 200421887040283742398083719)
    ·
      refine ⟨300632830560425613597125579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200421887040283742398083719 300632830560425613597125579)
      ·
        refine ⟨450949245840638420395688369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300632830560425613597125579 450949245840638420395688369)
        ·
          refine ⟨338211934380478815296766277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450949245840638420395688369 338211934380478815296766277)
          ·
            refine ⟨63414737696339777868143677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338211934380478815296766277 63414737696339777868143677)
            ·
              refine ⟨23780526636127416700553879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63414737696339777868143677 23780526636127416700553879)
              ·
                refine ⟨35670789954191125050830819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23780526636127416700553879 35670789954191125050830819)
                ·
                  refine ⟨53506184931286687576246229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35670789954191125050830819 53506184931286687576246229)
                  ·
                    refine ⟨1254051209327031740068271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53506184931286687576246229 1254051209327031740068271)
                    ·
                      rfl

theorem cell23_7326768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 1, 7].length) (baseStart_7326768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326768 prefixEnd_7326768 := by exact prefixLift 7326768
  have htrace : WordTrace (prefixWord ++ tailWord_7326768) baseStart_7326768 baseEnd_7326768 := by
    simpa [prefixWord, tailWord_7326768, baseEnd_7326768] using wordTrace_append hprefix tailTrace_7326768
  have hstable : (prefixWord ++ tailWord_7326768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326768).length < 2 ^ (prefixWord ++ tailWord_7326768).sum := by decide
  have hdescent : baseEnd_7326768 < baseStart_7326768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326778 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_7326778 : Nat := 118140960795 + 7326778 * 2 ^ 59
def prefixEnd_7326778 : Nat := 4983230072969 + 3 ^ 40 * 7326778 * 2
def baseEnd_7326778 : Nat := 3762158762787640181079767

theorem tailTrace_7326778 : CollatzResearch.WordTrace tailWord_7326778 prefixEnd_7326778 3762158762787640181079767 := by
  unfold tailWord_7326778
  simp only [CollatzResearch.WordTrace]
  refine ⟨66807386862585523726327247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178153031633561396603539325 66807386862585523726327247)
  ·
    refine ⟨100211080293878285589490871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66807386862585523726327247 100211080293878285589490871)
    ·
      refine ⟨150316620440817428384236307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100211080293878285589490871 150316620440817428384236307)
      ·
        refine ⟨225474930661226142576354461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150316620440817428384236307 225474930661226142576354461)
        ·
          refine ⟨84553098997959803466132923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225474930661226142576354461 84553098997959803466132923)
          ·
            refine ⟨126829648496939705199199385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84553098997959803466132923 126829648496939705199199385)
            ·
              refine ⟨95122236372704778899399539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126829648496939705199199385 95122236372704778899399539)
              ·
                refine ⟨142683354559057168349099309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95122236372704778899399539 142683354559057168349099309)
                ·
                  refine ⟨53506257959646438130912241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142683354559057168349099309 53506257959646438130912241)
                  ·
                    refine ⟨40129693469734828598184181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53506257959646438130912241 40129693469734828598184181)
                    ·
                      refine ⟨3762158762787640181079767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40129693469734828598184181 3762158762787640181079767)
                      ·
                        rfl

theorem cell23_7326778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_7326778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326778 prefixEnd_7326778 := by exact prefixLift 7326778
  have htrace : WordTrace (prefixWord ++ tailWord_7326778) baseStart_7326778 baseEnd_7326778 := by
    simpa [prefixWord, tailWord_7326778, baseEnd_7326778] using wordTrace_append hprefix tailTrace_7326778
  have hstable : (prefixWord ++ tailWord_7326778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326778).length < 2 ^ (prefixWord ++ tailWord_7326778).sum := by decide
  have hdescent : baseEnd_7326778 < baseStart_7326778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326782 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_7326782 : Nat := 118140960795 + 7326782 * 2 ^ 59
def prefixEnd_7326782 : Nat := 4983230072969 + 3 ^ 40 * 7326782 * 2
def baseEnd_7326782 : Nat := 3762160816710258165429749

theorem tailTrace_7326782 : CollatzResearch.WordTrace tailWord_7326782 prefixEnd_7326782 3762160816710258165429749 := by
  unfold tailWord_7326782
  simp only [CollatzResearch.WordTrace]
  refine ⟨33403711667790950448556825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178153128894885069058969733 33403711667790950448556825)
  ·
    refine ⟨25052783750843212836417619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33403711667790950448556825 25052783750843212836417619)
    ·
      refine ⟨37579175626264819254626429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25052783750843212836417619 37579175626264819254626429)
      ·
        refine ⟨14092190859849307220484911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37579175626264819254626429 14092190859849307220484911)
        ·
          refine ⟨21138286289773960830727367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14092190859849307220484911 21138286289773960830727367)
          ·
            refine ⟨31707429434660941246091051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21138286289773960830727367 31707429434660941246091051)
            ·
              refine ⟨47561144151991411869136577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31707429434660941246091051 47561144151991411869136577)
              ·
                refine ⟨35670858113993558901852433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47561144151991411869136577 35670858113993558901852433)
                ·
                  refine ⟨26753143585495169176389325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35670858113993558901852433 26753143585495169176389325)
                  ·
                    refine ⟨10032428844560688441145997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26753143585495169176389325 10032428844560688441145997)
                    ·
                      refine ⟨3762160816710258165429749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10032428844560688441145997 3762160816710258165429749)
                      ·
                        rfl

theorem cell23_7326782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_7326782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326782 prefixEnd_7326782 := by exact prefixLift 7326782
  have htrace : WordTrace (prefixWord ++ tailWord_7326782) baseStart_7326782 baseEnd_7326782 := by
    simpa [prefixWord, tailWord_7326782, baseEnd_7326782] using wordTrace_append hprefix tailTrace_7326782
  have hstable : (prefixWord ++ tailWord_7326782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326782).length < 2 ^ (prefixWord ++ tailWord_7326782).sum := by decide
  have hdescent : baseEnd_7326782 < baseStart_7326782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326815 : List Nat := [1, 1, 2, 3, 1, 1, 3, 4, 3, 4]
def baseStart_7326815 : Nat := 118140960795 + 7326815 * 2 ^ 59
def prefixEnd_7326815 : Nat := 4983230072969 + 3 ^ 40 * 7326815 * 2
def baseEnd_7326815 : Nat := 1254059253857285512105699

theorem tailTrace_7326815 : CollatzResearch.WordTrace tailWord_7326815 prefixEnd_7326815 1254059253857285512105699 := by
  unfold tailWord_7326815
  simp only [CollatzResearch.WordTrace]
  refine ⟨267230896951208050224405899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178153931300805366816270599 267230896951208050224405899)
  ·
    refine ⟨400846345426812075336608849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267230896951208050224405899 400846345426812075336608849)
    ·
      refine ⟨300634759070109056502456637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400846345426812075336608849 300634759070109056502456637)
      ·
        refine ⟨112738034651290896188421239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300634759070109056502456637 112738034651290896188421239)
        ·
          refine ⟨169107051976936344282631859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112738034651290896188421239 169107051976936344282631859)
          ·
            refine ⟨253660577965404516423947789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169107051976936344282631859 253660577965404516423947789)
            ·
              refine ⟨95122716737026693658980421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253660577965404516423947789 95122716737026693658980421)
              ·
                refine ⟨17835509388192505061058829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95122716737026693658980421 17835509388192505061058829)
                ·
                  refine ⟨6688316020572189397897061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17835509388192505061058829 6688316020572189397897061)
                  ·
                    refine ⟨1254059253857285512105699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6688316020572189397897061 1254059253857285512105699)
                    ·
                      rfl

theorem cell23_7326815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 4].length) (baseStart_7326815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326815 prefixEnd_7326815 := by exact prefixLift 7326815
  have htrace : WordTrace (prefixWord ++ tailWord_7326815) baseStart_7326815 baseEnd_7326815 := by
    simpa [prefixWord, tailWord_7326815, baseEnd_7326815] using wordTrace_append hprefix tailTrace_7326815
  have hstable : (prefixWord ++ tailWord_7326815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326815).length < 2 ^ (prefixWord ++ tailWord_7326815).sum := by decide
  have hdescent : baseEnd_7326815 < baseStart_7326815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326825 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 1, 4, 3]
def baseStart_7326825 : Nat := 118140960795 + 7326825 * 2 ^ 59
def prefixEnd_7326825 : Nat := 4983230072969 + 3 ^ 40 * 7326825 * 2
def baseEnd_7326825 : Nat := 3762182896378401497192051

theorem tailTrace_7326825 : CollatzResearch.WordTrace tailWord_7326825 prefixEnd_7326825 3762182896378401497192051 := by
  unfold tailWord_7326825
  simp only [CollatzResearch.WordTrace]
  refine ⟨267231261681171821932269929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178154174454114547954846619 267231261681171821932269929)
  ·
    refine ⟨200423446260878866449202447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267231261681171821932269929 200423446260878866449202447)
    ·
      refine ⟨300635169391318299673803671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200423446260878866449202447 300635169391318299673803671)
      ·
        refine ⟨450952754086977449510705507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300635169391318299673803671 450952754086977449510705507)
        ·
          refine ⟨676429131130466174266058261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450952754086977449510705507 676429131130466174266058261)
          ·
            refine ⟨31707615521740601918721481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 676429131130466174266058261 31707615521740601918721481)
            ·
              refine ⟨23780711641305451439041111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31707615521740601918721481 23780711641305451439041111)
              ·
                refine ⟨35671067461958177158561667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23780711641305451439041111 35671067461958177158561667)
                ·
                  refine ⟨53506601192937265737842501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35671067461958177158561667 53506601192937265737842501)
                  ·
                    refine ⟨10032487723675737325845469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53506601192937265737842501 10032487723675737325845469)
                    ·
                      refine ⟨3762182896378401497192051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10032487723675737325845469 3762182896378401497192051)
                      ·
                        rfl

theorem cell23_7326825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 4, 3].length) (baseStart_7326825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326825 prefixEnd_7326825 := by exact prefixLift 7326825
  have htrace : WordTrace (prefixWord ++ tailWord_7326825) baseStart_7326825 baseEnd_7326825 := by
    simpa [prefixWord, tailWord_7326825, baseEnd_7326825] using wordTrace_append hprefix tailTrace_7326825
  have hstable : (prefixWord ++ tailWord_7326825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326825).length < 2 ^ (prefixWord ++ tailWord_7326825).sum := by decide
  have hdescent : baseEnd_7326825 < baseStart_7326825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326828 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 10]
def baseStart_7326828 : Nat := 118140960795 + 7326828 * 2 ^ 59
def prefixEnd_7326828 : Nat := 4983230072969 + 3 ^ 40 * 7326828 * 2
def baseEnd_7326828 : Nat := 418020492980040553939393

theorem tailTrace_7326828 : CollatzResearch.WordTrace tailWord_7326828 prefixEnd_7326828 418020492980040553939393 := by
  unfold tailWord_7326828
  simp only [CollatzResearch.WordTrace]
  refine ⟨133615685550080476722314569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178154247400107302296419425 133615685550080476722314569)
  ·
    refine ⟨100211764162560357541735927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133615685550080476722314569 100211764162560357541735927)
    ·
      refine ⟨150317646243840536312603891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100211764162560357541735927 150317646243840536312603891)
      ·
        refine ⟨225476469365760804468905837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150317646243840536312603891 225476469365760804468905837)
        ·
          refine ⟨84553676012160301675839689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225476469365760804468905837 84553676012160301675839689)
          ·
            refine ⟨63415257009120226256879767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84553676012160301675839689 63415257009120226256879767)
            ·
              refine ⟨95122885513680339385319651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63415257009120226256879767 95122885513680339385319651)
              ·
                refine ⟨142684328270520509077979477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95122885513680339385319651 142684328270520509077979477)
                ·
                  refine ⟨418020492980040553939393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 142684328270520509077979477 418020492980040553939393)
                  ·
                    rfl

theorem cell23_7326828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_7326828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326828 prefixEnd_7326828 := by exact prefixLift 7326828
  have htrace : WordTrace (prefixWord ++ tailWord_7326828) baseStart_7326828 baseEnd_7326828 := by
    simpa [prefixWord, tailWord_7326828, baseEnd_7326828] using wordTrace_append hprefix tailTrace_7326828
  have hstable : (prefixWord ++ tailWord_7326828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326828).length < 2 ^ (prefixWord ++ tailWord_7326828).sum := by decide
  have hdescent : baseEnd_7326828 < baseStart_7326828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326845 : List Nat := [1, 4, 1, 1, 3, 1, 2, 4, 6]
def baseStart_7326845 : Nat := 118140960795 + 7326845 * 2 ^ 59
def prefixEnd_7326845 : Nat := 4983230072969 + 3 ^ 40 * 7326845 * 2
def baseEnd_7326845 : Nat := 418021462887943490993551

theorem tailTrace_7326845 : CollatzResearch.WordTrace tailWord_7326845 prefixEnd_7326845 418021462887943490993551 := by
  unfold tailWord_7326845
  simp only [CollatzResearch.WordTrace]
  refine ⟨267231991141099365347997989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178154660760732910231998659 267231991141099365347997989)
  ·
    refine ⟨50105998338956131002749623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267231991141099365347997989 50105998338956131002749623)
    ·
      refine ⟨75158997508434196504124435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50105998338956131002749623 75158997508434196504124435)
      ·
        refine ⟨112738496262651294756186653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75158997508434196504124435 112738496262651294756186653)
        ·
          refine ⟨42276936098494235533569995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112738496262651294756186653 42276936098494235533569995)
          ·
            refine ⟨63415404147741353300354993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42276936098494235533569995 63415404147741353300354993)
            ·
              refine ⟨47561553110806014975266245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63415404147741353300354993 47561553110806014975266245)
              ·
                refine ⟨8917791208276127807862421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47561553110806014975266245 8917791208276127807862421)
                ·
                  refine ⟨418021462887943490993551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8917791208276127807862421 418021462887943490993551)
                  ·
                    rfl

theorem cell23_7326845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_7326845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326845 prefixEnd_7326845 := by exact prefixLift 7326845
  have htrace : WordTrace (prefixWord ++ tailWord_7326845) baseStart_7326845 baseEnd_7326845 := by
    simpa [prefixWord, tailWord_7326845, baseEnd_7326845] using wordTrace_append hprefix tailTrace_7326845
  have hstable : (prefixWord ++ tailWord_7326845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326845).length < 2 ^ (prefixWord ++ tailWord_7326845).sum := by decide
  have hdescent : baseEnd_7326845 < baseStart_7326845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326846 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_7326846 : Nat := 118140960795 + 7326846 * 2 ^ 59
def prefixEnd_7326846 : Nat := 4983230072969 + 3 ^ 40 * 7326846 * 2
def baseEnd_7326846 : Nat := 3762193679472145915029455

theorem tailTrace_7326846 : CollatzResearch.WordTrace tailWord_7326846 prefixEnd_7326846 3762193679472145915029455 := by
  unfold tailWord_7326846
  simp only [CollatzResearch.WordTrace]
  refine ⟨33404003451761967814848049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178154685076063828345856261 33404003451761967814848049)
  ·
    refine ⟨25053002588821475861136037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33404003451761967814848049 25053002588821475861136037)
    ·
      refine ⟨4697437985404026723963007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25053002588821475861136037 4697437985404026723963007)
      ·
        refine ⟨7046156978106040085944511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4697437985404026723963007 7046156978106040085944511)
        ·
          refine ⟨10569235467159060128916767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7046156978106040085944511 10569235467159060128916767)
          ·
            refine ⟨15853853200738590193375151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10569235467159060128916767 15853853200738590193375151)
            ·
              refine ⟨23780779801107885290062727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15853853200738590193375151 23780779801107885290062727)
              ·
                refine ⟨35671169701661827935094091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23780779801107885290062727 35671169701661827935094091)
                ·
                  refine ⟨53506754552492741902641137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35671169701661827935094091 53506754552492741902641137)
                  ·
                    refine ⟨40130065914369556426980853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53506754552492741902641137 40130065914369556426980853)
                    ·
                      refine ⟨3762193679472145915029455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40130065914369556426980853 3762193679472145915029455)
                      ·
                        rfl

theorem cell23_7326846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_7326846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326846 prefixEnd_7326846 := by exact prefixLift 7326846
  have htrace : WordTrace (prefixWord ++ tailWord_7326846) baseStart_7326846 baseEnd_7326846 := by
    simpa [prefixWord, tailWord_7326846, baseEnd_7326846] using wordTrace_append hprefix tailTrace_7326846
  have hstable : (prefixWord ++ tailWord_7326846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326846).length < 2 ^ (prefixWord ++ tailWord_7326846).sum := by decide
  have hdescent : baseEnd_7326846 < baseStart_7326846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326848 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 8]
def baseStart_7326848 : Nat := 118140960795 + 7326848 * 2 ^ 59
def prefixEnd_7326848 : Nat := 4983230072969 + 3 ^ 40 * 7326848 * 2
def baseEnd_7326848 : Nat := 3762194706433454907204445

theorem tailTrace_7326848 : CollatzResearch.WordTrace tailWord_7326848 prefixEnd_7326848 3762194706433454907204445 := by
  unfold tailWord_7326848
  simp only [CollatzResearch.WordTrace]
  refine ⟨133616050280044248430178599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178154733706725664573571465 133616050280044248430178599)
  ·
    refine ⟨200424075420066372645267899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133616050280044248430178599 200424075420066372645267899)
    ·
      refine ⟨300636113130099558967901849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200424075420066372645267899 300636113130099558967901849)
      ·
        refine ⟨225477084847574669225926387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300636113130099558967901849 225477084847574669225926387)
        ·
          refine ⟨338215627271362003838889581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225477084847574669225926387 338215627271362003838889581)
          ·
            refine ⟨126830860226760751439583593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338215627271362003838889581 126830860226760751439583593)
            ·
              refine ⟨95123145170070563579687695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126830860226760751439583593 95123145170070563579687695)
              ·
                refine ⟨142684717755105845369531543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95123145170070563579687695 142684717755105845369531543)
                ·
                  refine ⟨214027076632658768054297315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142684717755105845369531543 214027076632658768054297315)
                  ·
                    refine ⟨321040614948988152081445973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 214027076632658768054297315 321040614948988152081445973)
                    ·
                      refine ⟨3762194706433454907204445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 321040614948988152081445973 3762194706433454907204445)
                      ·
                        rfl

theorem cell23_7326848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_7326848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326848 prefixEnd_7326848 := by exact prefixLift 7326848
  have htrace : WordTrace (prefixWord ++ tailWord_7326848) baseStart_7326848 baseEnd_7326848 := by
    simpa [prefixWord, tailWord_7326848, baseEnd_7326848] using wordTrace_append hprefix tailTrace_7326848
  have hstable : (prefixWord ++ tailWord_7326848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326848).length < 2 ^ (prefixWord ++ tailWord_7326848).sum := by decide
  have hdescent : baseEnd_7326848 < baseStart_7326848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326849 : List Nat := [1, 2, 4, 2, 2, 3, 1, 1, 3, 4]
def baseStart_7326849 : Nat := 118140960795 + 7326849 * 2 ^ 59
def prefixEnd_7326849 : Nat := 4983230072969 + 3 ^ 40 * 7326849 * 2
def baseEnd_7326849 : Nat := 1254065073304703134430647

theorem tailTrace_7326849 : CollatzResearch.WordTrace tailWord_7326849 prefixEnd_7326849 1254065073304703134430647 := by
  unfold tailWord_7326849
  simp only [CollatzResearch.WordTrace]
  refine ⟨267232137033084874031143601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178154758022056582687429067 267232137033084874031143601)
  ·
    refine ⟨200424102774813655523357701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267232137033084874031143601 200424102774813655523357701)
    ·
      refine ⟨37579519270277560410629569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200424102774813655523357701 37579519270277560410629569)
      ·
        refine ⟨28184639452708170307972177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37579519270277560410629569 28184639452708170307972177)
        ·
          refine ⟨21138479589531127730979133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28184639452708170307972177 21138479589531127730979133)
          ·
            refine ⟨7926929846074172899117175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21138479589531127730979133 7926929846074172899117175)
            ·
              refine ⟨11890394769111259348675763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7926929846074172899117175 11890394769111259348675763)
              ·
                refine ⟨17835592153666889023013645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11890394769111259348675763 17835592153666889023013645)
                ·
                  refine ⟨6688347057625083383630117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17835592153666889023013645 6688347057625083383630117)
                  ·
                    refine ⟨1254065073304703134430647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6688347057625083383630117 1254065073304703134430647)
                    ·
                      rfl

theorem cell23_7326849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_7326849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326849 prefixEnd_7326849 := by exact prefixLift 7326849
  have htrace : WordTrace (prefixWord ++ tailWord_7326849) baseStart_7326849 baseEnd_7326849 := by
    simpa [prefixWord, tailWord_7326849, baseEnd_7326849] using wordTrace_append hprefix tailTrace_7326849
  have hstable : (prefixWord ++ tailWord_7326849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326849).length < 2 ^ (prefixWord ++ tailWord_7326849).sum := by decide
  have hdescent : baseEnd_7326849 < baseStart_7326849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326862 : List Nat := [4, 1, 1, 3, 2, 2, 1, 3, 6]
def baseStart_7326862 : Nat := 118140960795 + 7326862 * 2 ^ 59
def prefixEnd_7326862 : Nat := 4983230072969 + 3 ^ 40 * 7326862 * 2
def baseEnd_7326862 : Nat := 418022432795846428047709

theorem tailTrace_7326862 : CollatzResearch.WordTrace tailWord_7326862 prefixEnd_7326862 418022432795846428047709 := by
  unfold tailWord_7326862
  simp only [CollatzResearch.WordTrace]
  refine ⟨33404076397754722156420855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178155074121358518167577893 33404076397754722156420855)
  ·
    refine ⟨50106114596632083234631283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33404076397754722156420855 50106114596632083234631283)
    ·
      refine ⟨75159171894948124851946925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50106114596632083234631283 75159171894948124851946925)
      ·
        refine ⟨28184689460605546819480097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75159171894948124851946925 28184689460605546819480097)
        ·
          refine ⟨21138517095454160114610073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28184689460605546819480097 21138517095454160114610073)
          ·
            refine ⟨15853887821590620085957555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21138517095454160114610073 15853887821590620085957555)
            ·
              refine ⟨23780831732385930128936333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15853887821590620085957555 23780831732385930128936333)
              ·
                refine ⟨8917811899644723798351125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23780831732385930128936333 8917811899644723798351125)
                ·
                  refine ⟨418022432795846428047709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8917811899644723798351125 418022432795846428047709)
                  ·
                    rfl

theorem cell23_7326862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_7326862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326862 prefixEnd_7326862 := by exact prefixLift 7326862
  have htrace : WordTrace (prefixWord ++ tailWord_7326862) baseStart_7326862 baseEnd_7326862 := by
    simpa [prefixWord, tailWord_7326862, baseEnd_7326862] using wordTrace_append hprefix tailTrace_7326862
  have hstable : (prefixWord ++ tailWord_7326862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326862).length < 2 ^ (prefixWord ++ tailWord_7326862).sum := by decide
  have hdescent : baseEnd_7326862 < baseStart_7326862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326922 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 1, 6]
def baseStart_7326922 : Nat := 118140960795 + 7326922 * 2 ^ 59
def prefixEnd_7326922 : Nat := 4983230072969 + 3 ^ 40 * 7326922 * 2
def baseEnd_7326922 : Nat := 1254077568000629205893035

theorem tailTrace_7326922 : CollatzResearch.WordTrace tailWord_7326922 prefixEnd_7326922 1254077568000629205893035 := by
  unfold tailWord_7326922
  simp only [CollatzResearch.WordTrace]
  refine ⟨66808699890455101874637755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178156533041213604999034013 66808699890455101874637755)
  ·
    refine ⟨100213049835682652811956633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66808699890455101874637755 100213049835682652811956633)
    ·
      refine ⟨75159787376761989608967475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100213049835682652811956633 75159787376761989608967475)
      ·
        refine ⟨112739681065142984413451213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75159787376761989608967475 112739681065142984413451213)
        ·
          refine ⟨42277380399428619155044205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112739681065142984413451213 42277380399428619155044205)
          ·
            refine ⟨15854017649785732183141577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42277380399428619155044205 15854017649785732183141577)
            ·
              refine ⟨11890513237339299137356183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15854017649785732183141577 11890513237339299137356183)
              ·
                refine ⟨17835769856008948706034275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11890513237339299137356183 17835769856008948706034275)
                ·
                  refine ⟨26753654784013423059051413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17835769856008948706034275 26753654784013423059051413)
                  ·
                    refine ⟨1254077568000629205893035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26753654784013423059051413 1254077568000629205893035)
                    ·
                      rfl

theorem cell23_7326922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_7326922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326922 prefixEnd_7326922 := by exact prefixLift 7326922
  have htrace : WordTrace (prefixWord ++ tailWord_7326922) baseStart_7326922 baseEnd_7326922 := by
    simpa [prefixWord, tailWord_7326922, baseEnd_7326922] using wordTrace_append hprefix tailTrace_7326922
  have hstable : (prefixWord ++ tailWord_7326922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326922).length < 2 ^ (prefixWord ++ tailWord_7326922).sum := by decide
  have hdescent : baseEnd_7326922 < baseStart_7326922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7326979 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 1, 3, 3]
def baseStart_7326979 : Nat := 118140960795 + 7326979 * 2 ^ 59
def prefixEnd_7326979 : Nat := 4983230072969 + 3 ^ 40 * 7326979 * 2
def baseEnd_7326979 : Nat := 3762261972399193894666343

theorem tailTrace_7326979 : CollatzResearch.WordTrace tailWord_7326979 prefixEnd_7326979 3762261972399193894666343 := by
  unfold tailWord_7326979
  simp only [CollatzResearch.WordTrace]
  refine ⟨267236878522613906233375991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178157919015075937488917327 267236878522613906233375991)
  ·
    refine ⟨400855317783920859350063987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267236878522613906233375991 400855317783920859350063987)
    ·
      refine ⟨601282976675881289025095981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400855317783920859350063987 601282976675881289025095981)
      ·
        refine ⟨225481116253455483384410993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 601282976675881289025095981 225481116253455483384410993)
        ·
          refine ⟨169110837190091612538308245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225481116253455483384410993 169110837190091612538308245)
          ·
            refine ⟨7927070493285544337733199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 169110837190091612538308245 7927070493285544337733199)
            ·
              refine ⟨11890605739928316506599799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7927070493285544337733199 11890605739928316506599799)
              ·
                refine ⟨17835908609892474759899699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11890605739928316506599799 17835908609892474759899699)
                ·
                  refine ⟨26753862914838712139849549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17835908609892474759899699 26753862914838712139849549)
                  ·
                    refine ⟨10032698593064517052443581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26753862914838712139849549 10032698593064517052443581)
                    ·
                      refine ⟨3762261972399193894666343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10032698593064517052443581 3762261972399193894666343)
                      ·
                        rfl

theorem cell23_7326979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_7326979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7326979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7326979 prefixEnd_7326979 := by exact prefixLift 7326979
  have htrace : WordTrace (prefixWord ++ tailWord_7326979) baseStart_7326979 baseEnd_7326979 := by
    simpa [prefixWord, tailWord_7326979, baseEnd_7326979] using wordTrace_append hprefix tailTrace_7326979
  have hstable : (prefixWord ++ tailWord_7326979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7326979).length < 2 ^ (prefixWord ++ tailWord_7326979).sum := by decide
  have hdescent : baseEnd_7326979 < baseStart_7326979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7326979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327030 : List Nat := [5, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_7327030 : Nat := 118140960795 + 7327030 * 2 ^ 59
def prefixEnd_7327030 : Nat := 4983230072969 + 3 ^ 40 * 7327030 * 2
def baseEnd_7327030 : Nat := 3762288159912573195128609

theorem tailTrace_7327030 : CollatzResearch.WordTrace tailWord_7327030 prefixEnd_7327030 3762288159912573195128609 := by
  unfold tailWord_7327030
  simp only [CollatzResearch.WordTrace]
  refine ⟨16702421165339321371467659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178159159096952761295655029 16702421165339321371467659)
  ·
    refine ⟨25053631748008982057201489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16702421165339321371467659 25053631748008982057201489)
    ·
      refine ⟨18790223811006736542901117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25053631748008982057201489 18790223811006736542901117)
      ·
        refine ⟨7046333929127526203587919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18790223811006736542901117 7046333929127526203587919)
        ·
          refine ⟨10569500893691289305381879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7046333929127526203587919 10569500893691289305381879)
          ·
            refine ⟨15854251340536933958072819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10569500893691289305381879 15854251340536933958072819)
            ·
              refine ⟨23781377010805400937109229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15854251340536933958072819 23781377010805400937109229)
              ·
                refine ⟨8918016379052025351415961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23781377010805400937109229 8918016379052025351415961)
                ·
                  refine ⟨6688512284289019013561971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8918016379052025351415961 6688512284289019013561971)
                  ·
                    refine ⟨10032768426433528520342957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6688512284289019013561971 10032768426433528520342957)
                    ·
                      refine ⟨3762288159912573195128609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10032768426433528520342957 3762288159912573195128609)
                      ·
                        rfl

theorem cell23_7327030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_7327030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327030 prefixEnd_7327030 := by exact prefixLift 7327030
  have htrace : WordTrace (prefixWord ++ tailWord_7327030) baseStart_7327030 baseEnd_7327030 := by
    simpa [prefixWord, tailWord_7327030, baseEnd_7327030] using wordTrace_append hprefix tailTrace_7327030
  have hstable : (prefixWord ++ tailWord_7327030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327030).length < 2 ^ (prefixWord ++ tailWord_7327030).sum := by decide
  have hdescent : baseEnd_7327030 < baseStart_7327030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327045 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_7327045 : Nat := 118140960795 + 7327045 * 2 ^ 59
def prefixEnd_7327045 : Nat := 4983230072969 + 3 ^ 40 * 7327045 * 2
def baseEnd_7327045 : Nat := 3762295862122390636441039

theorem tailTrace_7327045 : CollatzResearch.WordTrace tailWord_7327045 prefixEnd_7327045 3762295862122390636441039 := by
  unfold tailWord_7327045
  simp only [CollatzResearch.WordTrace]
  refine ⟨267239285740374799505278589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178159523826916533003519059 267239285740374799505278589)
  ·
    refine ⟨100214732152640549814479471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267239285740374799505278589 100214732152640549814479471)
    ·
      refine ⟨150322098228960824721719207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100214732152640549814479471 150322098228960824721719207)
      ·
        refine ⟨225483147343441237082578811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150322098228960824721719207 225483147343441237082578811)
        ·
          refine ⟨338224721015161855623868217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225483147343441237082578811 338224721015161855623868217)
          ·
            refine ⟨253668540761371391717901163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338224721015161855623868217 253668540761371391717901163)
            ·
              refine ⟨380502811142057087576851745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253668540761371391717901163 380502811142057087576851745)
              ·
                refine ⟨285377108356542815682638809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380502811142057087576851745 285377108356542815682638809)
                ·
                  refine ⟨214032831267407111761979107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285377108356542815682638809 214032831267407111761979107)
                  ·
                    refine ⟨321049246901110667642968661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 214032831267407111761979107 321049246901110667642968661)
                    ·
                      refine ⟨3762295862122390636441039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 321049246901110667642968661 3762295862122390636441039)
                      ·
                        rfl

theorem cell23_7327045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_7327045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327045 prefixEnd_7327045 := by exact prefixLift 7327045
  have htrace : WordTrace (prefixWord ++ tailWord_7327045) baseStart_7327045 baseEnd_7327045 := by
    simpa [prefixWord, tailWord_7327045, baseEnd_7327045] using wordTrace_append hprefix tailTrace_7327045
  have hstable : (prefixWord ++ tailWord_7327045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327045).length < 2 ^ (prefixWord ++ tailWord_7327045).sum := by decide
  have hdescent : baseEnd_7327045 < baseStart_7327045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327055 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 5, 7]
def baseStart_7327055 : Nat := 118140960795 + 7327055 * 2 ^ 59
def prefixEnd_7327055 : Nat := 4983230072969 + 3 ^ 40 * 7327055 * 2
def baseEnd_7327055 : Nat := 1254100332309645199105331

theorem tailTrace_7327055 : CollatzResearch.WordTrace tailWord_7327055 prefixEnd_7327055 1254100332309645199105331 := by
  unfold tailWord_7327055
  simp only [CollatzResearch.WordTrace]
  refine ⟨267239650470338571213142619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178159766980225714142095079 267239650470338571213142619)
  ·
    refine ⟨400859475705507856819713929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267239650470338571213142619 400859475705507856819713929)
    ·
      refine ⟨300644606779130892614785447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400859475705507856819713929 300644606779130892614785447)
      ·
        refine ⟨450966910168696338922178171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300644606779130892614785447 450966910168696338922178171)
        ·
          refine ⟨676450365253044508383267257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450966910168696338922178171 676450365253044508383267257)
          ·
            refine ⟨507337773939783381287450443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 676450365253044508383267257 507337773939783381287450443)
            ·
              refine ⟨761006660909675071931175665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507337773939783381287450443 761006660909675071931175665)
              ·
                refine ⟨570754995682256303948381749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761006660909675071931175665 570754995682256303948381749)
                ·
                  refine ⟨53508280845211528495160789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 570754995682256303948381749 53508280845211528495160789)
                  ·
                    refine ⟨1254100332309645199105331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53508280845211528495160789 1254100332309645199105331)
                    ·
                      rfl

theorem cell23_7327055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_7327055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327055 prefixEnd_7327055 := by exact prefixLift 7327055
  have htrace : WordTrace (prefixWord ++ tailWord_7327055) baseStart_7327055 baseEnd_7327055 := by
    simpa [prefixWord, tailWord_7327055, baseEnd_7327055] using wordTrace_append hprefix tailTrace_7327055
  have hstable : (prefixWord ++ tailWord_7327055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327055).length < 2 ^ (prefixWord ++ tailWord_7327055).sum := by decide
  have hdescent : baseEnd_7327055 < baseStart_7327055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327076 : List Nat := [2, 3, 1, 1, 3, 2, 4, 2, 5]
def baseStart_7327076 : Nat := 118140960795 + 7327076 * 2 ^ 59
def prefixEnd_7327076 : Nat := 4983230072969 + 3 ^ 40 * 7327076 * 2
def baseEnd_7327076 : Nat := 418034642224742223905933

theorem tailTrace_7327076 : CollatzResearch.WordTrace tailWord_7327076 prefixEnd_7327076 418034642224742223905933 := by
  unfold tailWord_7327076
  simp only [CollatzResearch.WordTrace]
  refine ⟨133620208201631245899828541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178160277602174994533104721 133620208201631245899828541)
  ·
    refine ⟨50107578075611717212435703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133620208201631245899828541 50107578075611717212435703)
    ·
      refine ⟨75161367113417575818653555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50107578075611717212435703 75161367113417575818653555)
      ·
        refine ⟨112742050670126363727980333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75161367113417575818653555 112742050670126363727980333)
        ·
          refine ⟨42278269001297386397992625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112742050670126363727980333 42278269001297386397992625)
          ·
            refine ⟨31708701750973039798494469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42278269001297386397992625 31708701750973039798494469)
            ·
              refine ⟨5945381578307444962217713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31708701750973039798494469 5945381578307444962217713)
              ·
                refine ⟨4459036183730583721663285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5945381578307444962217713 4459036183730583721663285)
                ·
                  refine ⟨418034642224742223905933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4459036183730583721663285 418034642224742223905933)
                  ·
                    rfl

theorem cell23_7327076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_7327076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327076 prefixEnd_7327076 := by exact prefixLift 7327076
  have htrace : WordTrace (prefixWord ++ tailWord_7327076) baseStart_7327076 baseEnd_7327076 := by
    simpa [prefixWord, tailWord_7327076, baseEnd_7327076] using wordTrace_append hprefix tailTrace_7327076
  have hstable : (prefixWord ++ tailWord_7327076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327076).length < 2 ^ (prefixWord ++ tailWord_7327076).sum := by decide
  have hdescent : baseEnd_7327076 < baseStart_7327076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327106 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_7327106 : Nat := 118140960795 + 7327106 * 2 ^ 59
def prefixEnd_7327106 : Nat := 4983230072969 + 3 ^ 40 * 7327106 * 2
def baseEnd_7327106 : Nat := 1254109061480771632592753

theorem tailTrace_7327106 : CollatzResearch.WordTrace tailWord_7327106 prefixEnd_7327106 1254109061480771632592753 := by
  unfold tailWord_7327106
  simp only [CollatzResearch.WordTrace]
  refine ⟨66810377648288451730812293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178161007062102537948832781 66810377648288451730812293)
  ·
    refine ⟨12526945809054084699527305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66810377648288451730812293 12526945809054084699527305)
    ·
      refine ⟨9395209356790563524645479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12526945809054084699527305 9395209356790563524645479)
      ·
        refine ⟨14092814035185845286968219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9395209356790563524645479 14092814035185845286968219)
        ·
          refine ⟨21139221052778767930452329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14092814035185845286968219 21139221052778767930452329)
          ·
            refine ⟨15854415789584075947839247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21139221052778767930452329 15854415789584075947839247)
            ·
              refine ⟨23781623684376113921758871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15854415789584075947839247 23781623684376113921758871)
              ·
                refine ⟨35672435526564170882638307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23781623684376113921758871 35672435526564170882638307)
                ·
                  refine ⟨53508653289846256323957461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35672435526564170882638307 53508653289846256323957461)
                  ·
                    refine ⟨1254109061480771632592753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53508653289846256323957461 1254109061480771632592753)
                    ·
                      rfl

theorem cell23_7327106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_7327106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327106 prefixEnd_7327106 := by exact prefixLift 7327106
  have htrace : WordTrace (prefixWord ++ tailWord_7327106) baseStart_7327106 baseEnd_7327106 := by
    simpa [prefixWord, tailWord_7327106, baseEnd_7327106] using wordTrace_append hprefix tailTrace_7327106
  have hstable : (prefixWord ++ tailWord_7327106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327106).length < 2 ^ (prefixWord ++ tailWord_7327106).sum := by decide
  have hdescent : baseEnd_7327106 < baseStart_7327106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327109 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 2, 1, 4]
def baseStart_7327109 : Nat := 118140960795 + 7327109 * 2 ^ 59
def prefixEnd_7327109 : Nat := 4983230072969 + 3 ^ 40 * 7327109 * 2
def baseEnd_7327109 : Nat := 3762328724884278386040745

theorem tailTrace_7327109 : CollatzResearch.WordTrace tailWord_7327109 prefixEnd_7327109 3762328724884278386040745 := by
  unfold tailWord_7327109
  simp only [CollatzResearch.WordTrace]
  refine ⟨267241620012142938435608381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178161080008095292290405587 267241620012142938435608381)
  ·
    refine ⟨100215607504553601913353143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267241620012142938435608381 100215607504553601913353143)
    ·
      refine ⟨150323411256830402870029715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100215607504553601913353143 150323411256830402870029715)
      ·
        refine ⟨225485116885245604305044573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150323411256830402870029715 225485116885245604305044573)
        ·
          refine ⟨84556918831967101614391715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225485116885245604305044573 84556918831967101614391715)
          ·
            refine ⟨126835378247950652421587573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84556918831967101614391715 126835378247950652421587573)
            ·
              refine ⟨11890816710745373664523835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126835378247950652421587573 11890816710745373664523835)
              ·
                refine ⟨17836225066118060496785753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11890816710745373664523835 17836225066118060496785753)
                ·
                  refine ⟨13377168799588545372589315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17836225066118060496785753 13377168799588545372589315)
                  ·
                    refine ⟨20065753199382818058883973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13377168799588545372589315 20065753199382818058883973)
                    ·
                      refine ⟨3762328724884278386040745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20065753199382818058883973 3762328724884278386040745)
                      ·
                        rfl

theorem cell23_7327109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_7327109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327109 prefixEnd_7327109 := by exact prefixLift 7327109
  have htrace : WordTrace (prefixWord ++ tailWord_7327109) baseStart_7327109 baseEnd_7327109 := by
    simpa [prefixWord, tailWord_7327109, baseEnd_7327109] using wordTrace_append hprefix tailTrace_7327109
  have hstable : (prefixWord ++ tailWord_7327109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327109).length < 2 ^ (prefixWord ++ tailWord_7327109).sum := by decide
  have hdescent : baseEnd_7327109 < baseStart_7327109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327136 : List Nat := [2, 1, 1, 4, 1, 2, 1, 6, 1, 4]
def baseStart_7327136 : Nat := 118140960795 + 7327136 * 2 ^ 59
def prefixEnd_7327136 : Nat := 4983230072969 + 3 ^ 40 * 7327136 * 2
def baseEnd_7327136 : Nat := 1254114196287316593467707

theorem tailTrace_7327136 : CollatzResearch.WordTrace tailWord_7327136 prefixEnd_7327136 1254114196287316593467707 := by
  unfold tailWord_7327136
  simp only [CollatzResearch.WordTrace]
  refine ⟨133621302391522561023420631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178161736522030081364560841 133621302391522561023420631)
  ·
    refine ⟨200431953587283841535130947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133621302391522561023420631 200431953587283841535130947)
    ·
      refine ⟨300647930380925762302696421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200431953587283841535130947 300647930380925762302696421)
      ·
        refine ⟨56371486946423580431755579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300647930380925762302696421 56371486946423580431755579)
        ·
          refine ⟨84557230419635370647633369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56371486946423580431755579 84557230419635370647633369)
          ·
            refine ⟨63417922814726527985725027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84557230419635370647633369 63417922814726527985725027)
            ·
              refine ⟨95126884222089791978587541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63417922814726527985725027 95126884222089791978587541)
              ·
                refine ⟨4459072697910458998996291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95126884222089791978587541 4459072697910458998996291)
                ·
                  refine ⟨6688609046865688498494437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459072697910458998996291 6688609046865688498494437)
                  ·
                    refine ⟨1254114196287316593467707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6688609046865688498494437 1254114196287316593467707)
                    ·
                      rfl

theorem cell23_7327136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 1, 4].length) (baseStart_7327136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327136 prefixEnd_7327136 := by exact prefixLift 7327136
  have htrace : WordTrace (prefixWord ++ tailWord_7327136) baseStart_7327136 baseEnd_7327136 := by
    simpa [prefixWord, tailWord_7327136, baseEnd_7327136] using wordTrace_append hprefix tailTrace_7327136
  have hstable : (prefixWord ++ tailWord_7327136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327136).length < 2 ^ (prefixWord ++ tailWord_7327136).sum := by decide
  have hdescent : baseEnd_7327136 < baseStart_7327136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327179 : List Nat := [1, 1, 1, 1, 3, 3, 4, 3, 1, 5]
def baseStart_7327179 : Nat := 118140960795 + 7327179 * 2 ^ 59
def prefixEnd_7327179 : Nat := 4983230072969 + 3 ^ 40 * 7327179 * 2
def baseEnd_7327179 : Nat := 1254121556176697704055141

theorem tailTrace_7327179 : CollatzResearch.WordTrace tailWord_7327179 prefixEnd_7327179 1254121556176697704055141 := by
  unfold tailWord_7327179
  simp only [CollatzResearch.WordTrace]
  refine ⟨267244173121889340390656591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178162782081259560260437727 267244173121889340390656591)
  ·
    refine ⟨400866259682834010585984887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267244173121889340390656591 400866259682834010585984887)
    ·
      refine ⟨601299389524251015878977331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400866259682834010585984887 601299389524251015878977331)
      ·
        refine ⟨901949084286376523818465997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601299389524251015878977331 901949084286376523818465997)
        ·
          refine ⟨338230906607391196431924749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 901949084286376523818465997 338230906607391196431924749)
          ·
            refine ⟨126836589977771698661971781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338230906607391196431924749 126836589977771698661971781)
            ·
              refine ⟨23781860620832193499119709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126836589977771698661971781 23781860620832193499119709)
              ·
                refine ⟨8918197732812072562169891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23781860620832193499119709 8918197732812072562169891)
                ·
                  refine ⟨13377296599218108843254837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8918197732812072562169891 13377296599218108843254837)
                  ·
                    refine ⟨1254121556176697704055141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13377296599218108843254837 1254121556176697704055141)
                    ·
                      rfl

theorem cell23_7327179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 5].length) (baseStart_7327179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327179 prefixEnd_7327179 := by exact prefixLift 7327179
  have htrace : WordTrace (prefixWord ++ tailWord_7327179) baseStart_7327179 baseEnd_7327179 := by
    simpa [prefixWord, tailWord_7327179, baseEnd_7327179] using wordTrace_append hprefix tailTrace_7327179
  have hstable : (prefixWord ++ tailWord_7327179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327179).length < 2 ^ (prefixWord ++ tailWord_7327179).sum := by decide
  have hdescent : baseEnd_7327179 < baseStart_7327179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327193 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 3, 1, 3]
def baseStart_7327193 : Nat := 118140960795 + 7327193 * 2 ^ 59
def prefixEnd_7327193 : Nat := 4983230072969 + 3 ^ 40 * 7327193 * 2
def baseEnd_7327193 : Nat := 3762371857259256057390359

theorem tailTrace_7327193 : CollatzResearch.WordTrace tailWord_7327193 prefixEnd_7327193 3762371857259256057390359 := by
  unfold tailWord_7327193
  simp only [CollatzResearch.WordTrace]
  refine ⟨267244683743838620781666233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178163122495892413854444155 267244683743838620781666233)
  ·
    refine ⟨200433512807878965586249675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267244683743838620781666233 200433512807878965586249675)
    ·
      refine ⟨300650269211818448379374513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200433512807878965586249675 300650269211818448379374513)
      ·
        refine ⟨225487701908863836284530885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300650269211818448379374513 225487701908863836284530885)
        ·
          refine ⟨42278944107911969303349541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225487701908863836284530885 42278944107911969303349541)
          ·
            refine ⟨7927302020233494244378039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42278944107911969303349541 7927302020233494244378039)
            ·
              refine ⟨11890953030350241366567059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7927302020233494244378039 11890953030350241366567059)
              ·
                refine ⟨17836429545525362049850589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11890953030350241366567059 17836429545525362049850589)
                ·
                  refine ⟨6688661079572010768693971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17836429545525362049850589 6688661079572010768693971)
                  ·
                    refine ⟨10032991619358016153040957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6688661079572010768693971 10032991619358016153040957)
                    ·
                      refine ⟨3762371857259256057390359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10032991619358016153040957 3762371857259256057390359)
                      ·
                        rfl

theorem cell23_7327193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_7327193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327193 prefixEnd_7327193 := by exact prefixLift 7327193
  have htrace : WordTrace (prefixWord ++ tailWord_7327193) baseStart_7327193 baseEnd_7327193 := by
    simpa [prefixWord, tailWord_7327193, baseEnd_7327193] using wordTrace_append hprefix tailTrace_7327193
  have hstable : (prefixWord ++ tailWord_7327193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327193).length < 2 ^ (prefixWord ++ tailWord_7327193).sum := by decide
  have hdescent : baseEnd_7327193 < baseStart_7327193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327199 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 4]
def baseStart_7327199 : Nat := 118140960795 + 7327199 * 2 ^ 59
def prefixEnd_7327199 : Nat := 4983230072969 + 3 ^ 40 * 7327199 * 2
def baseEnd_7327199 : Nat := 3762374938143183033915331

theorem tailTrace_7327199 : CollatzResearch.WordTrace tailWord_7327199 prefixEnd_7327199 3762374938143183033915331 := by
  unfold tailWord_7327199
  simp only [CollatzResearch.WordTrace]
  refine ⟨267244902581816883806384651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178163268387877922537589767 267244902581816883806384651)
  ·
    refine ⟨400867353872725325709576977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267244902581816883806384651 400867353872725325709576977)
    ·
      refine ⟨300650515404543994282182733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400867353872725325709576977 300650515404543994282182733)
      ·
        refine ⟨112743943276703997855818525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300650515404543994282182733 112743943276703997855818525)
        ·
          refine ⟨42278978728763999195931947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112743943276703997855818525 42278978728763999195931947)
          ·
            refine ⟨63418468093145998793897921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42278978728763999195931947 63418468093145998793897921)
            ·
              refine ⟨47563851069859499095423441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63418468093145998793897921 47563851069859499095423441)
              ·
                refine ⟨35672888302394624321567581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47563851069859499095423441 35672888302394624321567581)
                ·
                  refine ⟨13377333113397984120587843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35672888302394624321567581 13377333113397984120587843)
                  ·
                    refine ⟨20065999670096976180881765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13377333113397984120587843 20065999670096976180881765)
                    ·
                      refine ⟨3762374938143183033915331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20065999670096976180881765 3762374938143183033915331)
                      ·
                        rfl

theorem cell23_7327199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_7327199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327199 prefixEnd_7327199 := by exact prefixLift 7327199
  have htrace : WordTrace (prefixWord ++ tailWord_7327199) baseStart_7327199 baseEnd_7327199 := by
    simpa [prefixWord, tailWord_7327199, baseEnd_7327199] using wordTrace_append hprefix tailTrace_7327199
  have hstable : (prefixWord ++ tailWord_7327199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327199).length < 2 ^ (prefixWord ++ tailWord_7327199).sum := by decide
  have hdescent : baseEnd_7327199 < baseStart_7327199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327216 : List Nat := [2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 4]
def baseStart_7327216 : Nat := 118140960795 + 7327216 * 2 ^ 59
def prefixEnd_7327216 : Nat := 4983230072969 + 3 ^ 40 * 7327216 * 2
def baseEnd_7327216 : Nat := 3762383667314309467402753

theorem tailTrace_7327216 : CollatzResearch.WordTrace tailWord_7327216 prefixEnd_7327216 3762383667314309467402753 := by
  unfold tailWord_7327216
  simp only [CollatzResearch.WordTrace]
  refine ⟨133622761311377647854876751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178163681748503530473169001 133622761311377647854876751)
  ·
    refine ⟨200434141967066471782315127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133622761311377647854876751 200434141967066471782315127)
    ·
      refine ⟨300651212950599707673472691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200434141967066471782315127 300651212950599707673472691)
      ·
        refine ⟨450976819425899561510209037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300651212950599707673472691 450976819425899561510209037)
        ·
          refine ⟨169116307284712335566328389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450976819425899561510209037 169116307284712335566328389)
          ·
            refine ⟨31709307615883562918686573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169116307284712335566328389 31709307615883562918686573)
            ·
              refine ⟨11890990355956336094507465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31709307615883562918686573 11890990355956336094507465)
              ·
                refine ⟨8918242766967252070880599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11890990355956336094507465 8918242766967252070880599)
                ·
                  refine ⟨13377364150450878106320899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8918242766967252070880599 13377364150450878106320899)
                  ·
                    refine ⟨20066046225676317159481349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13377364150450878106320899 20066046225676317159481349)
                    ·
                      refine ⟨3762383667314309467402753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20066046225676317159481349 3762383667314309467402753)
                      ·
                        rfl

theorem cell23_7327216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 4].length) (baseStart_7327216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327216 prefixEnd_7327216 := by exact prefixLift 7327216
  have htrace : WordTrace (prefixWord ++ tailWord_7327216) baseStart_7327216 baseEnd_7327216 := by
    simpa [prefixWord, tailWord_7327216, baseEnd_7327216] using wordTrace_append hprefix tailTrace_7327216
  have hstable : (prefixWord ++ tailWord_7327216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327216).length < 2 ^ (prefixWord ++ tailWord_7327216).sum := by decide
  have hdescent : baseEnd_7327216 < baseStart_7327216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327229 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_7327229 : Nat := 118140960795 + 7327229 * 2 ^ 59
def prefixEnd_7327229 : Nat := 4983230072969 + 3 ^ 40 * 7327229 * 2
def baseEnd_7327229 : Nat := 3762390342562817916540193

theorem tailTrace_7327229 : CollatzResearch.WordTrace tailWord_7327229 prefixEnd_7327229 3762390342562817916540193 := by
  unfold tailWord_7327229
  simp only [CollatzResearch.WordTrace]
  refine ⟨267245996771708198929976741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178163997847805465953317827 267245996771708198929976741)
  ·
    refine ⟨50108624394695287299370639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267245996771708198929976741 50108624394695287299370639)
    ·
      refine ⟨75162936592042930949055959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50108624394695287299370639 75162936592042930949055959)
      ·
        refine ⟨112744404888064396423583939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75162936592042930949055959 112744404888064396423583939)
        ·
          refine ⟨169116607332096594635375909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112744404888064396423583939 169116607332096594635375909)
          ·
            refine ⟨31709363874768111494132983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169116607332096594635375909 31709363874768111494132983)
            ·
              refine ⟨47564045812152167241199475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31709363874768111494132983 47564045812152167241199475)
              ·
                refine ⟨71346068718228250861799213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47564045812152167241199475 71346068718228250861799213)
                ·
                  refine ⟨26754775769335594073174705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71346068718228250861799213 26754775769335594073174705)
                  ·
                    refine ⟨20066081827001695554881029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26754775769335594073174705 20066081827001695554881029)
                    ·
                      refine ⟨3762390342562817916540193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20066081827001695554881029 3762390342562817916540193)
                      ·
                        rfl

theorem cell23_7327229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_7327229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327229 prefixEnd_7327229 := by exact prefixLift 7327229
  have htrace : WordTrace (prefixWord ++ tailWord_7327229) baseStart_7327229 baseEnd_7327229 := by
    simpa [prefixWord, tailWord_7327229, baseEnd_7327229] using wordTrace_append hprefix tailTrace_7327229
  have hstable : (prefixWord ++ tailWord_7327229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327229).length < 2 ^ (prefixWord ++ tailWord_7327229).sum := by decide
  have hdescent : baseEnd_7327229 < baseStart_7327229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327238 : List Nat := [6, 2, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_7327238 : Nat := 118140960795 + 7327238 * 2 ^ 59
def prefixEnd_7327238 : Nat := 4983230072969 + 3 ^ 40 * 7327238 * 2
def baseEnd_7327238 : Nat := 1254131654629569460442551

theorem tailTrace_7327238 : CollatzResearch.WordTrace tailWord_7327238 prefixEnd_7327238 1254131654629569460442551 := by
  unfold tailWord_7327238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8351447657146112295845449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178164216685783728978036245 8351447657146112295845449)
  ·
    refine ⟨6263585742859584221884087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8351447657146112295845449 6263585742859584221884087)
    ·
      refine ⟨9395378614289376332826131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6263585742859584221884087 9395378614289376332826131)
      ·
        refine ⟨14093067921434064499239197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9395378614289376332826131 14093067921434064499239197)
        ·
          refine ⟨5284900470537774187214699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14093067921434064499239197 5284900470537774187214699)
          ·
            refine ⟨7927350705806661280822049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5284900470537774187214699 7927350705806661280822049)
            ·
              refine ⟨5945513029354995960616537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7927350705806661280822049 5945513029354995960616537)
              ·
                refine ⟨4459134772016246970462403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5945513029354995960616537 4459134772016246970462403)
                ·
                  refine ⟨6688702158024370455693605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459134772016246970462403 6688702158024370455693605)
                  ·
                    refine ⟨1254131654629569460442551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6688702158024370455693605 1254131654629569460442551)
                    ·
                      rfl

theorem cell23_7327238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_7327238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327238 prefixEnd_7327238 := by exact prefixLift 7327238
  have htrace : WordTrace (prefixWord ++ tailWord_7327238) baseStart_7327238 baseEnd_7327238 := by
    simpa [prefixWord, tailWord_7327238, baseEnd_7327238] using wordTrace_append hprefix tailTrace_7327238
  have hstable : (prefixWord ++ tailWord_7327238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327238).length < 2 ^ (prefixWord ++ tailWord_7327238).sum := by decide
  have hdescent : baseEnd_7327238 < baseStart_7327238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327243 : List Nat := [1, 1, 1, 1, 8, 1, 2, 2, 2, 4]
def baseStart_7327243 : Nat := 118140960795 + 7327243 * 2 ^ 59
def prefixEnd_7327243 : Nat := 4983230072969 + 3 ^ 40 * 7327243 * 2
def baseEnd_7327243 : Nat := 1254132510430660287255043

theorem tailTrace_7327243 : CollatzResearch.WordTrace tailWord_7327243 prefixEnd_7327243 1254132510430660287255043 := by
  unfold tailWord_7327243
  simp only [CollatzResearch.WordTrace]
  refine ⟨267246507393657479320986383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178164338262438319547324255 267246507393657479320986383)
  ·
    refine ⟨400869761090486218981479575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267246507393657479320986383 400869761090486218981479575)
    ·
      refine ⟨601304641635729328472219363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400869761090486218981479575 601304641635729328472219363)
      ·
        refine ⟨901956962453593992708329045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601304641635729328472219363 901956962453593992708329045)
        ·
          refine ⟨10569808153753054602050731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 901956962453593992708329045 10569808153753054602050731)
          ·
            refine ⟨15854712230629581903076097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10569808153753054602050731 15854712230629581903076097)
            ·
              refine ⟨11891034172972186427307073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15854712230629581903076097 11891034172972186427307073)
              ·
                refine ⟨8918275629729139820480305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11891034172972186427307073 8918275629729139820480305)
                ·
                  refine ⟨6688706722296854865360229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8918275629729139820480305 6688706722296854865360229)
                  ·
                    refine ⟨1254132510430660287255043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6688706722296854865360229 1254132510430660287255043)
                    ·
                      rfl

theorem cell23_7327243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 4].length) (baseStart_7327243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327243 prefixEnd_7327243 := by exact prefixLift 7327243
  have htrace : WordTrace (prefixWord ++ tailWord_7327243) baseStart_7327243 baseEnd_7327243 := by
    simpa [prefixWord, tailWord_7327243, baseEnd_7327243] using wordTrace_append hprefix tailTrace_7327243
  have hstable : (prefixWord ++ tailWord_7327243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327243).length < 2 ^ (prefixWord ++ tailWord_7327243).sum := by decide
  have hdescent : baseEnd_7327243 < baseStart_7327243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327244 : List Nat := [2, 2, 1, 2, 6, 1, 2, 2, 1, 1, 3]
def baseStart_7327244 : Nat := 118140960795 + 7327244 * 2 ^ 59
def prefixEnd_7327244 : Nat := 4983230072969 + 3 ^ 40 * 7327244 * 2
def baseEnd_7327244 : Nat := 3762398044772635357852625

theorem tailTrace_7327244 : CollatzResearch.WordTrace tailWord_7327244 prefixEnd_7327244 3762398044772635357852625 := by
  unfold tailWord_7327244
  simp only [CollatzResearch.WordTrace]
  refine ⟨133623271933326928245886393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178164362577769237661181857 133623271933326928245886393)
  ·
    refine ⟨100217453949995196184414795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133623271933326928245886393 100217453949995196184414795)
    ·
      refine ⟨150326180924992794276622193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100217453949995196184414795 150326180924992794276622193)
      ·
        refine ⟨112744635693744595707466645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150326180924992794276622193 112744635693744595707466645)
        ·
          refine ⟨5284904798144277923787499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112744635693744595707466645 5284904798144277923787499)
          ·
            refine ⟨7927357197216416885681249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5284904798144277923787499 7927357197216416885681249)
            ·
              refine ⟨5945517897912312664260937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7927357197216416885681249 5945517897912312664260937)
              ·
                refine ⟨4459138423434234498195703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5945517897912312664260937 4459138423434234498195703)
                ·
                  refine ⟨6688707635151351747293555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459138423434234498195703 6688707635151351747293555)
                  ·
                    refine ⟨10033061452727027620940333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6688707635151351747293555 10033061452727027620940333)
                    ·
                      refine ⟨3762398044772635357852625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10033061452727027620940333 3762398044772635357852625)
                      ·
                        rfl

theorem cell23_7327244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_7327244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327244 prefixEnd_7327244 := by exact prefixLift 7327244
  have htrace : WordTrace (prefixWord ++ tailWord_7327244) baseStart_7327244 baseEnd_7327244 := by
    simpa [prefixWord, tailWord_7327244, baseEnd_7327244] using wordTrace_append hprefix tailTrace_7327244
  have hstable : (prefixWord ++ tailWord_7327244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327244).length < 2 ^ (prefixWord ++ tailWord_7327244).sum := by decide
  have hdescent : baseEnd_7327244 < baseStart_7327244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327249 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 3]
def baseStart_7327249 : Nat := 118140960795 + 7327249 * 2 ^ 59
def prefixEnd_7327249 : Nat := 4983230072969 + 3 ^ 40 * 7327249 * 2
def baseEnd_7327249 : Nat := 3762400612175907838290101

theorem tailTrace_7327249 : CollatzResearch.WordTrace tailWord_7327249 prefixEnd_7327249 3762400612175907838290101 := by
  unfold tailWord_7327249
  simp only [CollatzResearch.WordTrace]
  refine ⟨267246726231635742345704801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178164484154423828230469867 267246726231635742345704801)
  ·
    refine ⟨200435044673726806759278601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267246726231635742345704801 200435044673726806759278601)
    ·
      refine ⟨150326283505295105069458951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200435044673726806759278601 150326283505295105069458951)
      ·
        refine ⟨225489425257942657604188427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150326283505295105069458951 225489425257942657604188427)
        ·
          refine ⟨338234137886913986406282641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225489425257942657604188427 338234137886913986406282641)
          ·
            refine ⟨253675603415185489804711981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338234137886913986406282641 253675603415185489804711981)
            ·
              refine ⟨95128351280694558676766993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253675603415185489804711981 95128351280694558676766993)
              ·
                refine ⟨71346263460520919007575245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95128351280694558676766993 71346263460520919007575245)
                ·
                  refine ⟨26754848797695344627840717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71346263460520919007575245 26754848797695344627840717)
                  ·
                    refine ⟨10033068299135754235440269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26754848797695344627840717 10033068299135754235440269)
                    ·
                      refine ⟨3762400612175907838290101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10033068299135754235440269 3762400612175907838290101)
                      ·
                        rfl

theorem cell23_7327249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_7327249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327249 prefixEnd_7327249 := by exact prefixLift 7327249
  have htrace : WordTrace (prefixWord ++ tailWord_7327249) baseStart_7327249 baseEnd_7327249 := by
    simpa [prefixWord, tailWord_7327249, baseEnd_7327249] using wordTrace_append hprefix tailTrace_7327249
  have hstable : (prefixWord ++ tailWord_7327249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327249).length < 2 ^ (prefixWord ++ tailWord_7327249).sum := by decide
  have hdescent : baseEnd_7327249 < baseStart_7327249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327256 : List Nat := [2, 1, 2, 3, 4, 2, 1, 8]
def baseStart_7327256 : Nat := 118140960795 + 7327256 * 2 ^ 59
def prefixEnd_7327256 : Nat := 4983230072969 + 3 ^ 40 * 7327256 * 2
def baseEnd_7327256 : Nat := 139348303945944048551947

theorem tailTrace_7327256 : CollatzResearch.WordTrace tailWord_7327256 prefixEnd_7327256 139348303945944048551947 := by
  unfold tailWord_7327256
  simp only [CollatzResearch.WordTrace]
  refine ⟨133623490771305191270604811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178164654361740255027473081 133623490771305191270604811)
  ·
    refine ⟨200435236156957786905907217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133623490771305191270604811 200435236156957786905907217)
    ·
      refine ⟨150326427117718340179430413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200435236156957786905907217 150326427117718340179430413)
      ·
        refine ⟨56372410169144377567286405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150326427117718340179430413 56372410169144377567286405)
        ·
          refine ⟨10569826906714570793866201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56372410169144377567286405 10569826906714570793866201)
          ·
            refine ⟨7927370180035928095399651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10569826906714570793866201 7927370180035928095399651)
            ·
              refine ⟨11891055270053892143099477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7927370180035928095399651 11891055270053892143099477)
              ·
                refine ⟨139348303945944048551947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11891055270053892143099477 139348303945944048551947)
                ·
                  rfl

theorem cell23_7327256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 8].length) (baseStart_7327256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327256 prefixEnd_7327256 := by exact prefixLift 7327256
  have htrace : WordTrace (prefixWord ++ tailWord_7327256) baseStart_7327256 baseEnd_7327256 := by
    simpa [prefixWord, tailWord_7327256, baseEnd_7327256] using wordTrace_append hprefix tailTrace_7327256
  have hstable : (prefixWord ++ tailWord_7327256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327256).length < 2 ^ (prefixWord ++ tailWord_7327256).sum := by decide
  have hdescent : baseEnd_7327256 < baseStart_7327256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327266 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_7327266 : Nat := 118140960795 + 7327266 * 2 ^ 59
def prefixEnd_7327266 : Nat := 4983230072969 + 3 ^ 40 * 7327266 * 2
def baseEnd_7327266 : Nat := 3762409341347034271777523

theorem tailTrace_7327266 : CollatzResearch.WordTrace tailWord_7327266 prefixEnd_7327266 3762409341347034271777523 := by
  unfold tailWord_7327266
  simp only [CollatzResearch.WordTrace]
  refine ⟨66811836568143538562268413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178164897515049436166049101 66811836568143538562268413)
  ·
    refine ⟨25054438713053826960850655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66811836568143538562268413 25054438713053826960850655)
    ·
      refine ⟨37581658069580740441275983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25054438713053826960850655 37581658069580740441275983)
      ·
        refine ⟨56372487104371110661913975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37581658069580740441275983 56372487104371110661913975)
        ·
          refine ⟨84558730656556665992870963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56372487104371110661913975 84558730656556665992870963)
          ·
            refine ⟨126838095984834998989306445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84558730656556665992870963 126838095984834998989306445)
            ·
              refine ⟨47564285994313124620989917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126838095984834998989306445 47564285994313124620989917)
              ·
                refine ⟨17836607247867421732871219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47564285994313124620989917 17836607247867421732871219)
                ·
                  refine ⟨26754910871801132599306829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17836607247867421732871219 26754910871801132599306829)
                  ·
                    refine ⟨10033091576925424724740061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26754910871801132599306829 10033091576925424724740061)
                    ·
                      refine ⟨3762409341347034271777523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10033091576925424724740061 3762409341347034271777523)
                      ·
                        rfl

theorem cell23_7327266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_7327266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327266 prefixEnd_7327266 := by exact prefixLift 7327266
  have htrace : WordTrace (prefixWord ++ tailWord_7327266) baseStart_7327266 baseEnd_7327266 := by
    simpa [prefixWord, tailWord_7327266, baseEnd_7327266] using wordTrace_append hprefix tailTrace_7327266
  have hstable : (prefixWord ++ tailWord_7327266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327266).length < 2 ^ (prefixWord ++ tailWord_7327266).sum := by decide
  have hdescent : baseEnd_7327266 < baseStart_7327266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327329 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 7]
def baseStart_7327329 : Nat := 118140960795 + 7327329 * 2 ^ 59
def prefixEnd_7327329 : Nat := 4983230072969 + 3 ^ 40 * 7327329 * 2
def baseEnd_7327329 : Nat := 418049076736474169476637

theorem tailTrace_7327329 : CollatzResearch.WordTrace tailWord_7327329 prefixEnd_7327329 418049076736474169476637 := by
  unfold tailWord_7327329
  simp only [CollatzResearch.WordTrace]
  refine ⟨267249644071345916008617041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178166429380897277339078027 267249644071345916008617041)
  ·
    refine ⟨200437233053509437006462781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267249644071345916008617041 200437233053509437006462781)
    ·
      refine ⟨75163962395066038877423543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200437233053509437006462781 75163962395066038877423543)
      ·
        refine ⟨112745943592599058316135315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75163962395066038877423543 112745943592599058316135315)
        ·
          refine ⟨169118915388898587474202973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112745943592599058316135315 169118915388898587474202973)
          ·
            refine ⟨63419593270836970302826115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169118915388898587474202973 63419593270836970302826115)
            ·
              refine ⟨95129389906255455454239173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63419593270836970302826115 95129389906255455454239173)
              ·
                refine ⟨17836760607422897897669845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95129389906255455454239173 17836760607422897897669845)
                ·
                  refine ⟨418049076736474169476637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17836760607422897897669845 418049076736474169476637)
                  ·
                    rfl

theorem cell23_7327329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 7].length) (baseStart_7327329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327329 prefixEnd_7327329 := by exact prefixLift 7327329
  have htrace : WordTrace (prefixWord ++ tailWord_7327329) baseStart_7327329 baseEnd_7327329 := by
    simpa [prefixWord, tailWord_7327329, baseEnd_7327329] using wordTrace_append hprefix tailTrace_7327329
  have hstable : (prefixWord ++ tailWord_7327329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327329).length < 2 ^ (prefixWord ++ tailWord_7327329).sum := by decide
  have hdescent : baseEnd_7327329 < baseStart_7327329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327369 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 7]
def baseStart_7327369 : Nat := 118140960795 + 7327369 * 2 ^ 59
def prefixEnd_7327369 : Nat := 4983230072969 + 3 ^ 40 * 7327369 * 2
def baseEnd_7327369 : Nat := 3762462229854447368789549

theorem tailTrace_7327369 : CollatzResearch.WordTrace tailWord_7327369 prefixEnd_7327369 3762462229854447368789549 := by
  unfold tailWord_7327369
  simp only [CollatzResearch.WordTrace]
  refine ⟨267251102991201002840073161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178167401994134001893382107 267251102991201002840073161)
  ·
    refine ⟨200438327243400752130054871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267251102991201002840073161 200438327243400752130054871)
    ·
      refine ⟨300657490865101128195082307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200438327243400752130054871 300657490865101128195082307)
      ·
        refine ⟨450986236297651692292623461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300657490865101128195082307 450986236297651692292623461)
        ·
          refine ⟨84559919305809692304866899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 450986236297651692292623461 84559919305809692304866899)
          ·
            refine ⟨126839878958714538457300349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84559919305809692304866899 126839878958714538457300349)
            ·
              refine ⟨47564954609517951921487631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126839878958714538457300349 47564954609517951921487631)
              ·
                refine ⟨71347431914276927882231447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47564954609517951921487631 71347431914276927882231447)
                ·
                  refine ⟨107021147871415391823347171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71347431914276927882231447 107021147871415391823347171)
                  ·
                    refine ⟨160531721807123087735020757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107021147871415391823347171 160531721807123087735020757)
                    ·
                      refine ⟨3762462229854447368789549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160531721807123087735020757 3762462229854447368789549)
                      ·
                        rfl

theorem cell23_7327369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_7327369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327369 prefixEnd_7327369 := by exact prefixLift 7327369
  have htrace : WordTrace (prefixWord ++ tailWord_7327369) baseStart_7327369 baseEnd_7327369 := by
    simpa [prefixWord, tailWord_7327369, baseEnd_7327369] using wordTrace_append hprefix tailTrace_7327369
  have hstable : (prefixWord ++ tailWord_7327369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327369).length < 2 ^ (prefixWord ++ tailWord_7327369).sum := by decide
  have hdescent : baseEnd_7327369 < baseStart_7327369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327374 : List Nat := [4, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2]
def baseStart_7327374 : Nat := 118140960795 + 7327374 * 2 ^ 59
def prefixEnd_7327374 : Nat := 4983230072969 + 3 ^ 40 * 7327374 * 2
def baseEnd_7327374 : Nat := 3762464797257719849227027

theorem tailTrace_7327374 : CollatzResearch.WordTrace tailWord_7327374 prefixEnd_7327374 3762464797257719849227027 := by
  unfold tailWord_7327374
  simp only [CollatzResearch.WordTrace]
  refine ⟨33406410669522861086750647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178167523570788592462670117 33406410669522861086750647)
  ·
    refine ⟨50109616004284291630125971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33406410669522861086750647 50109616004284291630125971)
    ·
      refine ⟨75164424006426437445188957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50109616004284291630125971 75164424006426437445188957)
      ·
        refine ⟨28186659002409914041945859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75164424006426437445188957 28186659002409914041945859)
        ·
          refine ⟨42279988503614871062918789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28186659002409914041945859 42279988503614871062918789)
          ·
            refine ⟨7927497844427788324297273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42279988503614871062918789 7927497844427788324297273)
            ·
              refine ⟨5945623383320841243222955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7927497844427788324297273 5945623383320841243222955)
              ·
                refine ⟨8918435074981261864834433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5945623383320841243222955 8918435074981261864834433)
                ·
                  refine ⟨6688826306235946398625825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8918435074981261864834433 6688826306235946398625825)
                  ·
                    refine ⟨5016619729676959798969369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6688826306235946398625825 5016619729676959798969369)
                    ·
                      refine ⟨3762464797257719849227027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5016619729676959798969369 3762464797257719849227027)
                      ·
                        rfl

theorem cell23_7327374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_7327374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327374 prefixEnd_7327374 := by exact prefixLift 7327374
  have htrace : WordTrace (prefixWord ++ tailWord_7327374) baseStart_7327374 baseEnd_7327374 := by
    simpa [prefixWord, tailWord_7327374, baseEnd_7327374] using wordTrace_append hprefix tailTrace_7327374
  have hstable : (prefixWord ++ tailWord_7327374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327374).length < 2 ^ (prefixWord ++ tailWord_7327374).sum := by decide
  have hdescent : baseEnd_7327374 < baseStart_7327374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327393 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 2, 5]
def baseStart_7327393 : Nat := 118140960795 + 7327393 * 2 ^ 59
def prefixEnd_7327393 : Nat := 4983230072969 + 3 ^ 40 * 7327393 * 2
def baseEnd_7327393 : Nat := 1254158184463385091629813

theorem tailTrace_7327393 : CollatzResearch.WordTrace tailWord_7327393 prefixEnd_7327393 1254158184463385091629813 := by
  unfold tailWord_7327393
  simp only [CollatzResearch.WordTrace]
  refine ⟨267251978343114054938946833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178167985562076036625964555 267251978343114054938946833)
  ·
    refine ⟨200438983757335541204210125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267251978343114054938946833 200438983757335541204210125)
    ·
      refine ⟨75164618909000827951578797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200438983757335541204210125 75164618909000827951578797)
      ·
        refine ⟨28186732090875310481842049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75164618909000827951578797 28186732090875310481842049)
        ·
          refine ⟨21140049068156482861381537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28186732090875310481842049 21140049068156482861381537)
          ·
            refine ⟨15855036801117362146036153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21140049068156482861381537 15855036801117362146036153)
            ·
              refine ⟨11891277600838021609527115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15855036801117362146036153 11891277600838021609527115)
              ·
                refine ⟨17836916401257032414290673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11891277600838021609527115 17836916401257032414290673)
                ·
                  refine ⟨13377687300942774310718005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17836916401257032414290673 13377687300942774310718005)
                  ·
                    refine ⟨1254158184463385091629813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13377687300942774310718005 1254158184463385091629813)
                    ·
                      rfl

theorem cell23_7327393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_7327393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327393 prefixEnd_7327393 := by exact prefixLift 7327393
  have htrace : WordTrace (prefixWord ++ tailWord_7327393) baseStart_7327393 baseEnd_7327393 := by
    simpa [prefixWord, tailWord_7327393, baseEnd_7327393] using wordTrace_append hprefix tailTrace_7327393
  have hstable : (prefixWord ++ tailWord_7327393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327393).length < 2 ^ (prefixWord ++ tailWord_7327393).sum := by decide
  have hdescent : baseEnd_7327393 < baseStart_7327393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327414 : List Nat := [5, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_7327414 : Nat := 118140960795 + 7327414 * 2 ^ 59
def prefixEnd_7327414 : Nat := 4983230072969 + 3 ^ 40 * 7327414 * 2
def baseEnd_7327414 : Nat := 418053926275988854747427

theorem tailTrace_7327414 : CollatzResearch.WordTrace tailWord_7327414 prefixEnd_7327414 418053926275988854747427 := by
  unfold tailWord_7327414
  simp only [CollatzResearch.WordTrace]
  refine ⟨16703296517252373470341331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178168496184025317016974197 16703296517252373470341331)
  ·
    refine ⟨25054944775878560205511997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16703296517252373470341331 25054944775878560205511997)
    ·
      refine ⟨9395604290954460077066999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25054944775878560205511997 9395604290954460077066999)
      ·
        refine ⟨14093406436431690115600499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9395604290954460077066999 14093406436431690115600499)
        ·
          refine ⟨21140109654647535173400749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14093406436431690115600499 21140109654647535173400749)
          ·
            refine ⟨7927541120492825690025281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21140109654647535173400749 7927541120492825690025281)
            ·
              refine ⟨5945655840369619267518961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7927541120492825690025281 5945655840369619267518961)
              ·
                refine ⟨4459241880277214450639221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5945655840369619267518961 4459241880277214450639221)
                ·
                  refine ⟨418053926275988854747427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4459241880277214450639221 418053926275988854747427)
                  ·
                    rfl

theorem cell23_7327414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_7327414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327414 prefixEnd_7327414 := by exact prefixLift 7327414
  have htrace : WordTrace (prefixWord ++ tailWord_7327414) baseStart_7327414 baseEnd_7327414 := by
    simpa [prefixWord, tailWord_7327414, baseEnd_7327414] using wordTrace_append hprefix tailTrace_7327414
  have hstable : (prefixWord ++ tailWord_7327414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327414).length < 2 ^ (prefixWord ++ tailWord_7327414).sum := by decide
  have hdescent : baseEnd_7327414 < baseStart_7327414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327419 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 8]
def baseStart_7327419 : Nat := 118140960795 + 7327419 * 2 ^ 59
def prefixEnd_7327419 : Nat := 4983230072969 + 3 ^ 40 * 7327419 * 2
def baseEnd_7327419 : Nat := 418054211543019130351591

theorem tailTrace_7327419 : CollatzResearch.WordTrace tailWord_7327419 prefixEnd_7327419 418054211543019130351591 := by
  unfold tailWord_7327419
  simp only [CollatzResearch.WordTrace]
  refine ⟨267252926641019861379393311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178168617760679907586262207 267252926641019861379393311)
  ·
    refine ⟨400879389961529792069089967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267252926641019861379393311 400879389961529792069089967)
    ·
      refine ⟨601319084942294688103634951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400879389961529792069089967 601319084942294688103634951)
      ·
        refine ⟨901978627413442032155452427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601319084942294688103634951 901978627413442032155452427)
        ·
          refine ⟨1352967941120163048233178641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901978627413442032155452427 1352967941120163048233178641)
          ·
            refine ⟨1014725955840122286174883981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1352967941120163048233178641 1014725955840122286174883981)
            ·
              refine ⟨380522233440045857315581493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1014725955840122286174883981 380522233440045857315581493)
              ·
                refine ⟨35673959385004299123335765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 380522233440045857315581493 35673959385004299123335765)
                ·
                  refine ⟨418054211543019130351591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35673959385004299123335765 418054211543019130351591)
                  ·
                    rfl

theorem cell23_7327419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 8].length) (baseStart_7327419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327419 prefixEnd_7327419 := by exact prefixLift 7327419
  have htrace : WordTrace (prefixWord ++ tailWord_7327419) baseStart_7327419 baseEnd_7327419 := by
    simpa [prefixWord, tailWord_7327419, baseEnd_7327419] using wordTrace_append hprefix tailTrace_7327419
  have hstable : (prefixWord ++ tailWord_7327419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327419).length < 2 ^ (prefixWord ++ tailWord_7327419).sum := by decide
  have hdescent : baseEnd_7327419 < baseStart_7327419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327450 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3]
def baseStart_7327450 : Nat := 118140960795 + 7327450 * 2 ^ 59
def prefixEnd_7327450 : Nat := 4983230072969 + 3 ^ 40 * 7327450 * 2
def baseEnd_7327450 : Nat := 3762503821787461551876677

theorem tailTrace_7327450 : CollatzResearch.WordTrace tailWord_7327450 prefixEnd_7327450 3762503821787461551876677 := by
  unfold tailWord_7327450
  simp only [CollatzResearch.WordTrace]
  refine ⟨66813514325976888418442951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178169371535938369115847869 66813514325976888418442951)
  ·
    refine ⟨100220271488965332627664427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66813514325976888418442951 100220271488965332627664427)
    ·
      refine ⟨150330407233447998941496641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100220271488965332627664427 150330407233447998941496641)
      ·
        refine ⟨112747805425085999206122481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150330407233447998941496641 112747805425085999206122481)
        ·
          refine ⟨84560854068814499404591861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112747805425085999206122481 84560854068814499404591861)
          ·
            refine ⟨7927580068951359319180487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84560854068814499404591861 7927580068951359319180487)
            ·
              refine ⟨11891370103427038978770731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7927580068951359319180487 11891370103427038978770731)
              ·
                refine ⟨17837055155140558468156097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11891370103427038978770731 17837055155140558468156097)
                ·
                  refine ⟨13377791366355418851117073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17837055155140558468156097 13377791366355418851117073)
                  ·
                    refine ⟨10033343524766564138337805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13377791366355418851117073 10033343524766564138337805)
                    ·
                      refine ⟨3762503821787461551876677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10033343524766564138337805 3762503821787461551876677)
                      ·
                        rfl

theorem cell23_7327450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_7327450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327450 prefixEnd_7327450 := by exact prefixLift 7327450
  have htrace : WordTrace (prefixWord ++ tailWord_7327450) baseStart_7327450 baseEnd_7327450 := by
    simpa [prefixWord, tailWord_7327450, baseEnd_7327450] using wordTrace_append hprefix tailTrace_7327450
  have hstable : (prefixWord ++ tailWord_7327450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327450).length < 2 ^ (prefixWord ++ tailWord_7327450).sum := by decide
  have hdescent : baseEnd_7327450 < baseStart_7327450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327457 : List Nat := [1, 2, 3, 1, 5, 1, 2, 3, 1, 4]
def baseStart_7327457 : Nat := 118140960795 + 7327457 * 2 ^ 59
def prefixEnd_7327457 : Nat := 4983230072969 + 3 ^ 40 * 7327457 * 2
def baseEnd_7327457 : Nat := 1254169138717347674829715

theorem tailTrace_7327457 : CollatzResearch.WordTrace tailWord_7327457 prefixEnd_7327457 1254169138717347674829715 := by
  unfold tailWord_7327457
  simp only [CollatzResearch.WordTrace]
  refine ⟨267254312614882193869276625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178169541743254795912851083 267254312614882193869276625)
  ·
    refine ⟨200440734461161645401957469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267254312614882193869276625 200440734461161645401957469)
    ·
      refine ⟨75165275422935617025734051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200440734461161645401957469 75165275422935617025734051)
      ·
        refine ⟨112747913134403425538601077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75165275422935617025734051 112747913134403425538601077)
        ·
          refine ⟨10570116856350321144243851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112747913134403425538601077 10570116856350321144243851)
          ·
            refine ⟨15855175284525481716365777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10570116856350321144243851 15855175284525481716365777)
            ·
              refine ⟨11891381463394111287274333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15855175284525481716365777 11891381463394111287274333)
              ·
                refine ⟨4459268048772791732727875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11891381463394111287274333 4459268048772791732727875)
                ·
                  refine ⟨6688902073159187599091813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459268048772791732727875 6688902073159187599091813)
                  ·
                    refine ⟨1254169138717347674829715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6688902073159187599091813 1254169138717347674829715)
                    ·
                      rfl

theorem cell23_7327457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_7327457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327457 prefixEnd_7327457 := by exact prefixLift 7327457
  have htrace : WordTrace (prefixWord ++ tailWord_7327457) baseStart_7327457 baseEnd_7327457 := by
    simpa [prefixWord, tailWord_7327457, baseEnd_7327457] using wordTrace_append hprefix tailTrace_7327457
  have hstable : (prefixWord ++ tailWord_7327457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327457).length < 2 ^ (prefixWord ++ tailWord_7327457).sum := by decide
  have hdescent : baseEnd_7327457 < baseStart_7327457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327490 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_7327490 : Nat := 118140960795 + 7327490 * 2 ^ 59
def prefixEnd_7327490 : Nat := 4983230072969 + 3 ^ 40 * 7327490 * 2
def baseEnd_7327490 : Nat := 3762524361013641395376493

theorem tailTrace_7327490 : CollatzResearch.WordTrace tailWord_7327490 prefixEnd_7327490 3762524361013641395376493 := by
  unfold tailWord_7327490
  simp only [CollatzResearch.WordTrace]
  refine ⟨66813879055940660126306981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178170344149175093670151949 66813879055940660126306981)
  ·
    refine ⟨12527602322988873773682559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66813879055940660126306981 12527602322988873773682559)
    ·
      refine ⟨18791403484483310660523839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12527602322988873773682559 18791403484483310660523839)
      ·
        refine ⟨28187105226724965990785759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18791403484483310660523839 28187105226724965990785759)
        ·
          refine ⟨42280657840087448986178639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28187105226724965990785759 42280657840087448986178639)
          ·
            refine ⟨63420986760131173479267959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42280657840087448986178639 63420986760131173479267959)
            ·
              refine ⟨95131480140196760218901939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63420986760131173479267959 95131480140196760218901939)
              ·
                refine ⟨142697220210295140328352909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95131480140196760218901939 142697220210295140328352909)
                ·
                  refine ⟨53511457578860677623132341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142697220210295140328352909 53511457578860677623132341)
                  ·
                    refine ⟨5016699148018188527168657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53511457578860677623132341 5016699148018188527168657)
                    ·
                      refine ⟨3762524361013641395376493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5016699148018188527168657 3762524361013641395376493)
                      ·
                        rfl

theorem cell23_7327490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_7327490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327490 prefixEnd_7327490 := by exact prefixLift 7327490
  have htrace : WordTrace (prefixWord ++ tailWord_7327490) baseStart_7327490 baseEnd_7327490 := by
    simpa [prefixWord, tailWord_7327490, baseEnd_7327490] using wordTrace_append hprefix tailTrace_7327490
  have hstable : (prefixWord ++ tailWord_7327490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327490).length < 2 ^ (prefixWord ++ tailWord_7327490).sum := by decide
  have hdescent : baseEnd_7327490 < baseStart_7327490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327508 : List Nat := [2, 4, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_7327508 : Nat := 118140960795 + 7327508 * 2 ^ 59
def prefixEnd_7327508 : Nat := 4983230072969 + 3 ^ 40 * 7327508 * 2
def baseEnd_7327508 : Nat := 1254177867888474108317137

theorem tailTrace_7327508 : CollatzResearch.WordTrace tailWord_7327508 prefixEnd_7327508 1254177867888474108317137 := by
  unfold tailWord_7327508
  simp only [CollatzResearch.WordTrace]
  refine ⟨133628086368848714789691589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178170781825131619719588785 133628086368848714789691589)
  ·
    refine ⟨25055266194159134023067173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133628086368848714789691589 25055266194159134023067173)
    ·
      refine ⟨4697862411404837629325095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25055266194159134023067173 4697862411404837629325095)
      ·
        refine ⟨7046793617107256443987643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4697862411404837629325095 7046793617107256443987643)
        ·
          refine ⟨10570190425660884665981465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7046793617107256443987643 10570190425660884665981465)
          ·
            refine ⟨7927642819245663499486099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10570190425660884665981465 7927642819245663499486099)
            ·
              refine ⟨11891464228868495249229149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7927642819245663499486099 11891464228868495249229149)
              ·
                refine ⟨4459299085825685718460931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11891464228868495249229149 4459299085825685718460931)
                ·
                  refine ⟨6688948628738528577691397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459299085825685718460931 6688948628738528577691397)
                  ·
                    refine ⟨1254177867888474108317137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6688948628738528577691397 1254177867888474108317137)
                    ·
                      rfl

theorem cell23_7327508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_7327508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327508 prefixEnd_7327508 := by exact prefixLift 7327508
  have htrace : WordTrace (prefixWord ++ tailWord_7327508) baseStart_7327508 baseEnd_7327508 := by
    simpa [prefixWord, tailWord_7327508, baseEnd_7327508] using wordTrace_append hprefix tailTrace_7327508
  have hstable : (prefixWord ++ tailWord_7327508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327508).length < 2 ^ (prefixWord ++ tailWord_7327508).sum := by decide
  have hdescent : baseEnd_7327508 < baseStart_7327508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327514 : List Nat := [3, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3]
def baseStart_7327514 : Nat := 118140960795 + 7327514 * 2 ^ 59
def prefixEnd_7327514 : Nat := 4983230072969 + 3 ^ 40 * 7327514 * 2
def baseEnd_7327514 : Nat := 3762536684549349301476383

theorem tailTrace_7327514 : CollatzResearch.WordTrace tailWord_7327514 prefixEnd_7327514 3762536684549349301476383 := by
  unfold tailWord_7327514
  simp only [CollatzResearch.WordTrace]
  refine ⟨66814097893918923151025399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178170927717117128402734397 66814097893918923151025399)
  ·
    refine ⟨100221146840878384726538099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66814097893918923151025399 100221146840878384726538099)
    ·
      refine ⟨150331720261317577089807149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100221146840878384726538099 150331720261317577089807149)
      ·
        refine ⟨56374395097994091408677681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150331720261317577089807149 56374395097994091408677681)
        ·
          refine ⟨42280796323495568556508261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56374395097994091408677681 42280796323495568556508261)
          ·
            refine ⟨7927649310655419104345299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42280796323495568556508261 7927649310655419104345299)
            ·
              refine ⟨11891473965983128656517949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7927649310655419104345299 11891473965983128656517949)
              ·
                refine ⟨4459302737243673246194231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11891473965983128656517949 4459302737243673246194231)
                ·
                  refine ⟨6688954105865509869291347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459302737243673246194231 6688954105865509869291347)
                  ·
                    refine ⟨10033431158798264803937021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6688954105865509869291347 10033431158798264803937021)
                    ·
                      refine ⟨3762536684549349301476383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10033431158798264803937021 3762536684549349301476383)
                      ·
                        rfl

theorem cell23_7327514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_7327514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327514 prefixEnd_7327514 := by exact prefixLift 7327514
  have htrace : WordTrace (prefixWord ++ tailWord_7327514) baseStart_7327514 baseEnd_7327514 := by
    simpa [prefixWord, tailWord_7327514, baseEnd_7327514] using wordTrace_append hprefix tailTrace_7327514
  have hstable : (prefixWord ++ tailWord_7327514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327514).length < 2 ^ (prefixWord ++ tailWord_7327514).sum := by decide
  have hdescent : baseEnd_7327514 < baseStart_7327514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327537 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 3, 2, 2]
def baseStart_7327537 : Nat := 118140960795 + 7327537 * 2 ^ 59
def prefixEnd_7327537 : Nat := 4983230072969 + 3 ^ 40 * 7327537 * 2
def baseEnd_7327537 : Nat := 3762548494604402711488777

theorem tailTrace_7327537 : CollatzResearch.WordTrace tailWord_7327537 prefixEnd_7327537 3762548494604402711488777 := by
  unfold tailWord_7327537
  simp only [CollatzResearch.WordTrace]
  refine ⟨267257230454592367532188865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178171486969728245021459243 267257230454592367532188865)
  ·
    refine ⟨200442922840944275649141649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267257230454592367532188865 200442922840944275649141649)
    ·
      refine ⟨150332192130708206736856237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200442922840944275649141649 150332192130708206736856237)
      ·
        refine ⟨56374572049015577526321089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150332192130708206736856237 56374572049015577526321089)
        ·
          refine ⟨42280929036761683144740817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56374572049015577526321089 42280929036761683144740817)
          ·
            refine ⟨31710696777571262358555613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42280929036761683144740817 31710696777571262358555613)
            ·
              refine ⟨11891511291589223384458355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31710696777571262358555613 11891511291589223384458355)
              ·
                refine ⟨17837266937383835076687533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11891511291589223384458355 17837266937383835076687533)
                ·
                  refine ⟨6688975101518938153757825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17837266937383835076687533 6688975101518938153757825)
                  ·
                    refine ⟨5016731326139203615318369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6688975101518938153757825 5016731326139203615318369)
                    ·
                      refine ⟨3762548494604402711488777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5016731326139203615318369 3762548494604402711488777)
                      ·
                        rfl

theorem cell23_7327537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_7327537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327537 prefixEnd_7327537 := by exact prefixLift 7327537
  have htrace : WordTrace (prefixWord ++ tailWord_7327537) baseStart_7327537 baseEnd_7327537 := by
    simpa [prefixWord, tailWord_7327537, baseEnd_7327537] using wordTrace_append hprefix tailTrace_7327537
  have hstable : (prefixWord ++ tailWord_7327537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327537).length < 2 ^ (prefixWord ++ tailWord_7327537).sum := by decide
  have hdescent : baseEnd_7327537 < baseStart_7327537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327540 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_7327540 : Nat := 118140960795 + 7327540 * 2 ^ 59
def prefixEnd_7327540 : Nat := 4983230072969 + 3 ^ 40 * 7327540 * 2
def baseEnd_7327540 : Nat := 3762550035046366199751263

theorem tailTrace_7327540 : CollatzResearch.WordTrace tailWord_7327540 prefixEnd_7327540 3762550035046366199751263 := by
  unfold tailWord_7327540
  simp only [CollatzResearch.WordTrace]
  refine ⟨133628669936790749522274037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178171559915720999363032049 133628669936790749522274037)
  ·
    refine ⟨12527687806574132767713191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133628669936790749522274037 12527687806574132767713191)
    ·
      refine ⟨18791531709861199151569787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12527687806574132767713191 18791531709861199151569787)
      ·
        refine ⟨28187297564791798727354681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18791531709861199151569787 28187297564791798727354681)
        ·
          refine ⟨21140473173593849045516011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28187297564791798727354681 21140473173593849045516011)
          ·
            refine ⟨31710709760390773568274017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21140473173593849045516011 31710709760390773568274017)
            ·
              refine ⟨23783032320293080176205513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31710709760390773568274017 23783032320293080176205513)
              ·
                refine ⟨17837274240219810132154135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23783032320293080176205513 17837274240219810132154135)
                ·
                  refine ⟨26755911360329715198231203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17837274240219810132154135 26755911360329715198231203)
                  ·
                    refine ⟨40133867040494572797346805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26755911360329715198231203 40133867040494572797346805)
                    ·
                      refine ⟨3762550035046366199751263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40133867040494572797346805 3762550035046366199751263)
                      ·
                        rfl

theorem cell23_7327540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_7327540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327540 prefixEnd_7327540 := by exact prefixLift 7327540
  have htrace : WordTrace (prefixWord ++ tailWord_7327540) baseStart_7327540 baseEnd_7327540 := by
    simpa [prefixWord, tailWord_7327540, baseEnd_7327540] using wordTrace_append hprefix tailTrace_7327540
  have hstable : (prefixWord ++ tailWord_7327540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327540).length < 2 ^ (prefixWord ++ tailWord_7327540).sum := by decide
  have hdescent : baseEnd_7327540 < baseStart_7327540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327570 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_7327570 : Nat := 118140960795 + 7327570 * 2 ^ 59
def prefixEnd_7327570 : Nat := 4983230072969 + 3 ^ 40 * 7327570 * 2
def baseEnd_7327570 : Nat := 3762565439466001082376125

theorem tailTrace_7327570 : CollatzResearch.WordTrace tailWord_7327570 prefixEnd_7327570 3762565439466001082376125 := by
  unfold tailWord_7327570
  simp only [CollatzResearch.WordTrace]
  refine ⟨66814608515868203542035041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178172289375648542778760109 66814608515868203542035041)
  ·
    refine ⟨50110956386901152656526281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66814608515868203542035041 50110956386901152656526281)
    ·
      refine ⟨37583217290175864492394711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50110956386901152656526281 37583217290175864492394711)
      ·
        refine ⟨56374825935263796738592067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37583217290175864492394711 56374825935263796738592067)
        ·
          refine ⟨84562238902895695107888101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56374825935263796738592067 84562238902895695107888101)
          ·
            refine ⟨15855419794292942832729019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84562238902895695107888101 15855419794292942832729019)
            ·
              refine ⟨23783129691439414249093529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15855419794292942832729019 23783129691439414249093529)
              ·
                refine ⟨17837347268579560686820147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23783129691439414249093529 17837347268579560686820147)
                ·
                  refine ⟨26756020902869341030230221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17837347268579560686820147 26756020902869341030230221)
                  ·
                    refine ⟨10033507838576002886336333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26756020902869341030230221 10033507838576002886336333)
                    ·
                      refine ⟨3762565439466001082376125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10033507838576002886336333 3762565439466001082376125)
                      ·
                        rfl

theorem cell23_7327570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_7327570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327570 prefixEnd_7327570 := by exact prefixLift 7327570
  have htrace : WordTrace (prefixWord ++ tailWord_7327570) baseStart_7327570 baseEnd_7327570 := by
    simpa [prefixWord, tailWord_7327570, baseEnd_7327570] using wordTrace_append hprefix tailTrace_7327570
  have hstable : (prefixWord ++ tailWord_7327570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327570).length < 2 ^ (prefixWord ++ tailWord_7327570).sum := by decide
  have hdescent : baseEnd_7327570 < baseStart_7327570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327588 : List Nat := [2, 3, 1, 1, 5, 2, 2, 2, 1, 2, 2]
def baseStart_7327588 : Nat := 118140960795 + 7327588 * 2 ^ 59
def prefixEnd_7327588 : Nat := 4983230072969 + 3 ^ 40 * 7327588 * 2
def baseEnd_7327588 : Nat := 3762574682117782011951043

theorem tailTrace_7327588 : CollatzResearch.WordTrace tailWord_7327588 prefixEnd_7327588 3762574682117782011951043 := by
  unfold tailWord_7327588
  simp only [CollatzResearch.WordTrace]
  refine ⟨133629545288703801621147709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178172727051605068828196945 133629545288703801621147709)
  ·
    refine ⟨50111079483263925607930391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133629545288703801621147709 50111079483263925607930391)
    ·
      refine ⟨75166619224895888411895587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50111079483263925607930391 75166619224895888411895587)
      ·
        refine ⟨112749928837343832617843381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75166619224895888411895587 112749928837343832617843381)
        ·
          refine ⟨10570305828500984307922817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112749928837343832617843381 10570305828500984307922817)
          ·
            refine ⟨7927729371375738230942113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10570305828500984307922817 7927729371375738230942113)
            ·
              refine ⟨5945797028531803673206585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7927729371375738230942113 5945797028531803673206585)
              ·
                refine ⟨4459347771398852754904939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5945797028531803673206585 4459347771398852754904939)
                ·
                  refine ⟨6689021657098279132357409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459347771398852754904939 6689021657098279132357409)
                  ·
                    refine ⟨5016766242823709349268057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6689021657098279132357409 5016766242823709349268057)
                    ·
                      refine ⟨3762574682117782011951043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5016766242823709349268057 3762574682117782011951043)
                      ·
                        rfl

theorem cell23_7327588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_7327588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327588 prefixEnd_7327588 := by exact prefixLift 7327588
  have htrace : WordTrace (prefixWord ++ tailWord_7327588) baseStart_7327588 baseEnd_7327588 := by
    simpa [prefixWord, tailWord_7327588, baseEnd_7327588] using wordTrace_append hprefix tailTrace_7327588
  have hstable : (prefixWord ++ tailWord_7327588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327588).length < 2 ^ (prefixWord ++ tailWord_7327588).sum := by decide
  have hdescent : baseEnd_7327588 < baseStart_7327588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327610 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2]
def baseStart_7327610 : Nat := 118140960795 + 7327610 * 2 ^ 59
def prefixEnd_7327610 : Nat := 4983230072969 + 3 ^ 40 * 7327610 * 2
def baseEnd_7327610 : Nat := 3762585978692180925875941

theorem tailTrace_7327610 : CollatzResearch.WordTrace tailWord_7327610 prefixEnd_7327610 3762585978692180925875941 := by
  unfold tailWord_7327610
  simp only [CollatzResearch.WordTrace]
  refine ⟨66814973245831975249899071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178173261988885267333064189 66814973245831975249899071)
  ·
    refine ⟨100222459868747962874848607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66814973245831975249899071 100222459868747962874848607)
    ·
      refine ⟨150333689803121944312272911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100222459868747962874848607 150333689803121944312272911)
      ·
        refine ⟨225500534704682916468409367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150333689803121944312272911 225500534704682916468409367)
        ·
          refine ⟨338250802057024374702614051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225500534704682916468409367 338250802057024374702614051)
          ·
            refine ⟨507376203085536562053921077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338250802057024374702614051 507376203085536562053921077)
            ·
              refine ⟨47566519039269052692555101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 507376203085536562053921077 47566519039269052692555101)
              ·
                refine ⟨17837444639725894759708163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47566519039269052692555101 17837444639725894759708163)
                ·
                  refine ⟨26756166959588842139562245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17837444639725894759708163 26756166959588842139562245)
                  ·
                    refine ⟨5016781304922907901167921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26756166959588842139562245 5016781304922907901167921)
                    ·
                      refine ⟨3762585978692180925875941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5016781304922907901167921 3762585978692180925875941)
                      ·
                        rfl

theorem cell23_7327610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2].length) (baseStart_7327610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327610 prefixEnd_7327610 := by exact prefixLift 7327610
  have htrace : WordTrace (prefixWord ++ tailWord_7327610) baseStart_7327610 baseEnd_7327610 := by
    simpa [prefixWord, tailWord_7327610, baseEnd_7327610] using wordTrace_append hprefix tailTrace_7327610
  have hstable : (prefixWord ++ tailWord_7327610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327610).length < 2 ^ (prefixWord ++ tailWord_7327610).sum := by decide
  have hdescent : baseEnd_7327610 < baseStart_7327610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327613 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_7327613 : Nat := 118140960795 + 7327613 * 2 ^ 59
def prefixEnd_7327613 : Nat := 4983230072969 + 3 ^ 40 * 7327613 * 2
def baseEnd_7327613 : Nat := 3762587519134144414138427

theorem tailTrace_7327613 : CollatzResearch.WordTrace tailWord_7327613 prefixEnd_7327613 3762587519134144414138427 := by
  unfold tailWord_7327613
  simp only [CollatzResearch.WordTrace]
  refine ⟨267260002402317032511955493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178173334934878021674636995 267260002402317032511955493)
  ·
    refine ⟨50111250450434443595991655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267260002402317032511955493 50111250450434443595991655)
    ·
      refine ⟨75166875675651665393987483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50111250450434443595991655 75166875675651665393987483)
      ·
        refine ⟨112750313513477498090981225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75166875675651665393987483 112750313513477498090981225)
        ·
          refine ⟨84562735135108123568235919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112750313513477498090981225 84562735135108123568235919)
          ·
            refine ⟨126844102702662185352353879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84562735135108123568235919 126844102702662185352353879)
            ·
              refine ⟨190266154053993278028530819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126844102702662185352353879 190266154053993278028530819)
              ·
                refine ⟨285399231080989917042796229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190266154053993278028530819 285399231080989917042796229)
                ·
                  refine ⟨53512355827685609445524293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285399231080989917042796229 53512355827685609445524293)
                  ·
                    refine ⟨10033566717691051771035805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53512355827685609445524293 10033566717691051771035805)
                    ·
                      refine ⟨3762587519134144414138427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10033566717691051771035805 3762587519134144414138427)
                      ·
                        rfl

theorem cell23_7327613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_7327613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327613 prefixEnd_7327613 := by exact prefixLift 7327613
  have htrace : WordTrace (prefixWord ++ tailWord_7327613) baseStart_7327613 baseEnd_7327613 := by
    simpa [prefixWord, tailWord_7327613, baseEnd_7327613] using wordTrace_append hprefix tailTrace_7327613
  have hstable : (prefixWord ++ tailWord_7327613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327613).length < 2 ^ (prefixWord ++ tailWord_7327613).sum := by decide
  have hdescent : baseEnd_7327613 < baseStart_7327613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327614 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_7327614 : Nat := 118140960795 + 7327614 * 2 ^ 59
def prefixEnd_7327614 : Nat := 4983230072969 + 3 ^ 40 * 7327614 * 2
def baseEnd_7327614 : Nat := 3762588032614798910225923

theorem tailTrace_7327614 : CollatzResearch.WordTrace tailWord_7327614 prefixEnd_7327614 3762588032614798910225923 := by
  unfold tailWord_7327614
  simp only [CollatzResearch.WordTrace]
  refine ⟨33407504859414176210342737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178173359250208939788494597 33407504859414176210342737)
  ·
    refine ⟨25055628644560632157757053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33407504859414176210342737 25055628644560632157757053)
    ·
      refine ⟨9395860741710237059158895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25055628644560632157757053 9395860741710237059158895)
      ·
        refine ⟨14093791112565355588738343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9395860741710237059158895 14093791112565355588738343)
        ·
          refine ⟨21140686668848033383107515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14093791112565355588738343 21140686668848033383107515)
          ·
            refine ⟨31711030003272050074661273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21140686668848033383107515 31711030003272050074661273)
            ·
              refine ⟨23783272502454037555995955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31711030003272050074661273 23783272502454037555995955)
              ·
                refine ⟨35674908753681056333993933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23783272502454037555995955 35674908753681056333993933)
                ·
                  refine ⟨13378090782630396125247725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35674908753681056333993933 13378090782630396125247725)
                  ·
                    refine ⟨5016784043486398546967897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13378090782630396125247725 5016784043486398546967897)
                    ·
                      refine ⟨3762588032614798910225923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5016784043486398546967897 3762588032614798910225923)
                      ·
                        rfl

theorem cell23_7327614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_7327614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327614 prefixEnd_7327614 := by exact prefixLift 7327614
  have htrace : WordTrace (prefixWord ++ tailWord_7327614) baseStart_7327614 baseEnd_7327614 := by
    simpa [prefixWord, tailWord_7327614, baseEnd_7327614] using wordTrace_append hprefix tailTrace_7327614
  have hstable : (prefixWord ++ tailWord_7327614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327614).length < 2 ^ (prefixWord ++ tailWord_7327614).sum := by decide
  have hdescent : baseEnd_7327614 < baseStart_7327614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327644 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_7327644 : Nat := 118140960795 + 7327644 * 2 ^ 59
def prefixEnd_7327644 : Nat := 4983230072969 + 3 ^ 40 * 7327644 * 2
def baseEnd_7327644 : Nat := 3762603437034433792850785

theorem tailTrace_7327644 : CollatzResearch.WordTrace tailWord_7327644 prefixEnd_7327644 3762603437034433792850785 := by
  unfold tailWord_7327644
  simp only [CollatzResearch.WordTrace]
  refine ⟨133630566532602362403166993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178174088710136483204222657 133630566532602362403166993)
  ·
    refine ⟨100222924899451771802375245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133630566532602362403166993 100222924899451771802375245)
    ·
      refine ⟨37583596837294414425890717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100222924899451771802375245 37583596837294414425890717)
      ·
        refine ⟨14093848813985405409709019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37583596837294414425890717 14093848813985405409709019)
        ·
          refine ⟨21140773220978108114563529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14093848813985405409709019 21140773220978108114563529)
          ·
            refine ⟨15855579915733581085922647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21140773220978108114563529 15855579915733581085922647)
            ·
              refine ⟨23783369873600371628883971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15855579915733581085922647 23783369873600371628883971)
              ·
                refine ⟨35675054810400557443325957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23783369873600371628883971 35675054810400557443325957)
                ·
                  refine ⟨6689072776950104520623617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35675054810400557443325957 6689072776950104520623617)
                  ·
                    refine ⟨5016804582712578390467713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6689072776950104520623617 5016804582712578390467713)
                    ·
                      refine ⟨3762603437034433792850785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5016804582712578390467713 3762603437034433792850785)
                      ·
                        rfl

theorem cell23_7327644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_7327644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327644 prefixEnd_7327644 := by exact prefixLift 7327644
  have htrace : WordTrace (prefixWord ++ tailWord_7327644) baseStart_7327644 baseEnd_7327644 := by
    simpa [prefixWord, tailWord_7327644, baseEnd_7327644] using wordTrace_append hprefix tailTrace_7327644
  have hstable : (prefixWord ++ tailWord_7327644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327644).length < 2 ^ (prefixWord ++ tailWord_7327644).sum := by decide
  have hdescent : baseEnd_7327644 < baseStart_7327644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327713 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_7327713 : Nat := 118140960795 + 7327713 * 2 ^ 59
def prefixEnd_7327713 : Nat := 4983230072969 + 3 ^ 40 * 7327713 * 2
def baseEnd_7327713 : Nat := 3762638867199594022887967

theorem tailTrace_7327713 : CollatzResearch.WordTrace tailWord_7327713 prefixEnd_7327713 3762638867199594022887967 := by
  unfold tailWord_7327713
  simp only [CollatzResearch.WordTrace]
  refine ⟨267263649701954749590595793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178175766467969833060397195 267263649701954749590595793)
  ·
    refine ⟨200447737276466062192946845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267263649701954749590595793 200447737276466062192946845)
    ·
      refine ⟨75167901478674773322355067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200447737276466062192946845 75167901478674773322355067)
      ·
        refine ⟨112751852218012159983532601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75167901478674773322355067 112751852218012159983532601)
        ·
          refine ⟨84563889163509119987649451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112751852218012159983532601 84563889163509119987649451)
          ·
            refine ⟨126845833745263679981474177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84563889163509119987649451 126845833745263679981474177)
            ·
              refine ⟨95134375308947759986105633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126845833745263679981474177 95134375308947759986105633)
              ·
                refine ⟨71350781481710819989579225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95134375308947759986105633 71350781481710819989579225)
                ·
                  refine ⟨53513086111283114992184419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71350781481710819989579225 53513086111283114992184419)
                  ·
                    refine ⟨80269629166924672488276629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53513086111283114992184419 80269629166924672488276629)
                    ·
                      refine ⟨3762638867199594022887967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80269629166924672488276629 3762638867199594022887967)
                      ·
                        rfl

theorem cell23_7327713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_7327713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327713 prefixEnd_7327713 := by exact prefixLift 7327713
  have htrace : WordTrace (prefixWord ++ tailWord_7327713) baseStart_7327713 baseEnd_7327713 := by
    simpa [prefixWord, tailWord_7327713, baseEnd_7327713] using wordTrace_append hprefix tailTrace_7327713
  have hstable : (prefixWord ++ tailWord_7327713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327713).length < 2 ^ (prefixWord ++ tailWord_7327713).sum := by decide
  have hdescent : baseEnd_7327713 < baseStart_7327713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327720 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_7327720 : Nat := 118140960795 + 7327720 * 2 ^ 59
def prefixEnd_7327720 : Nat := 4983230072969 + 3 ^ 40 * 7327720 * 2
def baseEnd_7327720 : Nat := 3762642461564175495500435

theorem tailTrace_7327720 : CollatzResearch.WordTrace tailWord_7327720 prefixEnd_7327720 3762642461564175495500435 := by
  unfold tailWord_7327720
  simp only [CollatzResearch.WordTrace]
  refine ⟨133631952506464694893050307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178175936675286259857400409 133631952506464694893050307)
  ·
    refine ⟨200447928759697042339575461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133631952506464694893050307 200447928759697042339575461)
    ·
      refine ⟨37583986642443195438670399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200447928759697042339575461 37583986642443195438670399)
      ·
        refine ⟨56375979963664793158005599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37583986642443195438670399 56375979963664793158005599)
        ·
          refine ⟨84563969945497189737008399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56375979963664793158005599 84563969945497189737008399)
          ·
            refine ⟨126845954918245784605512599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84563969945497189737008399 126845954918245784605512599)
            ·
              refine ⟨190268932377368676908268899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126845954918245784605512599 190268932377368676908268899)
              ·
                refine ⟨285403398566053015362403349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190268932377368676908268899 285403398566053015362403349)
                ·
                  refine ⟨13378284307783735095112657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 285403398566053015362403349 13378284307783735095112657)
                  ·
                    refine ⟨10033713230837801321334493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13378284307783735095112657 10033713230837801321334493)
                    ·
                      refine ⟨3762642461564175495500435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10033713230837801321334493 3762642461564175495500435)
                      ·
                        rfl

theorem cell23_7327720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_7327720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327720 prefixEnd_7327720 := by exact prefixLift 7327720
  have htrace : WordTrace (prefixWord ++ tailWord_7327720) baseStart_7327720 baseEnd_7327720 := by
    simpa [prefixWord, tailWord_7327720, baseEnd_7327720] using wordTrace_append hprefix tailTrace_7327720
  have hstable : (prefixWord ++ tailWord_7327720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327720).length < 2 ^ (prefixWord ++ tailWord_7327720).sum := by decide
  have hdescent : baseEnd_7327720 < baseStart_7327720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327734 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_7327734 : Nat := 118140960795 + 7327734 * 2 ^ 59
def prefixEnd_7327734 : Nat := 4983230072969 + 3 ^ 40 * 7327734 * 2
def baseEnd_7327734 : Nat := 3762649650293338440725371

theorem tailTrace_7327734 : CollatzResearch.WordTrace tailWord_7327734 prefixEnd_7327734 3762649650293338440725371 := by
  unfold tailWord_7327734
  simp only [CollatzResearch.WordTrace]
  refine ⟨16704025977179916886069391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178176277089919113451406837 16704025977179916886069391)
  ·
    refine ⟨25056038965769875329104087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16704025977179916886069391 25056038965769875329104087)
    ·
      refine ⟨37584058448654812993656131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25056038965769875329104087 37584058448654812993656131)
      ·
        refine ⟨56376087672982219490484197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37584058448654812993656131 56376087672982219490484197)
        ·
          refine ⟨10570516438684166154465787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56376087672982219490484197 10570516438684166154465787)
          ·
            refine ⟨15855774658026249231698681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10570516438684166154465787 15855774658026249231698681)
            ·
              refine ⟨11891830993519686923774011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15855774658026249231698681 11891830993519686923774011)
              ·
                refine ⟨17837746490279530385661017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11891830993519686923774011 17837746490279530385661017)
                ·
                  refine ⟨13378309867709647789245763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17837746490279530385661017 13378309867709647789245763)
                  ·
                    refine ⟨20067464801564471683868645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13378309867709647789245763 20067464801564471683868645)
                    ·
                      refine ⟨3762649650293338440725371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20067464801564471683868645 3762649650293338440725371)
                      ·
                        rfl

theorem cell23_7327734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_7327734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327734 prefixEnd_7327734 := by exact prefixLift 7327734
  have htrace : WordTrace (prefixWord ++ tailWord_7327734) baseStart_7327734 baseEnd_7327734 := by
    simpa [prefixWord, tailWord_7327734, baseEnd_7327734] using wordTrace_append hprefix tailTrace_7327734
  have hstable : (prefixWord ++ tailWord_7327734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327734).length < 2 ^ (prefixWord ++ tailWord_7327734).sum := by decide
  have hdescent : baseEnd_7327734 < baseStart_7327734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327737 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 2, 2, 3]
def baseStart_7327737 : Nat := 118140960795 + 7327737 * 2 ^ 59
def prefixEnd_7327737 : Nat := 4983230072969 + 3 ^ 40 * 7327737 * 2
def baseEnd_7327737 : Nat := 3762651190735301928987857

theorem tailTrace_7327737 : CollatzResearch.WordTrace tailWord_7327737 prefixEnd_7327737 3762651190735301928987857 := by
  unfold tailWord_7327737
  simp only [CollatzResearch.WordTrace]
  refine ⟨267264525053867801689469465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178176350035911867792979643 267264525053867801689469465)
  ·
    refine ⟨200448393790400851267102099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267264525053867801689469465 200448393790400851267102099)
    ·
      refine ⟨300672590685601276900653149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200448393790400851267102099 300672590685601276900653149)
      ·
        refine ⟨112752221507100478837744931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300672590685601276900653149 112752221507100478837744931)
        ·
          refine ⟨169128332260650718256617397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112752221507100478837744931 169128332260650718256617397)
          ·
            refine ⟨15855781149436004836557881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169128332260650718256617397 15855781149436004836557881)
            ·
              refine ⟨11891835862077003627418411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15855781149436004836557881 11891835862077003627418411)
              ·
                refine ⟨17837753793115505441127617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11891835862077003627418411 17837753793115505441127617)
                ·
                  refine ⟨13378315344836629080845713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17837753793115505441127617 13378315344836629080845713)
                  ·
                    refine ⟨10033736508627471810634285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13378315344836629080845713 10033736508627471810634285)
                    ·
                      refine ⟨3762651190735301928987857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10033736508627471810634285 3762651190735301928987857)
                      ·
                        rfl

theorem cell23_7327737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_7327737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327737 prefixEnd_7327737 := by exact prefixLift 7327737
  have htrace : WordTrace (prefixWord ++ tailWord_7327737) baseStart_7327737 baseEnd_7327737 := by
    simpa [prefixWord, tailWord_7327737, baseEnd_7327737] using wordTrace_append hprefix tailTrace_7327737
  have hstable : (prefixWord ++ tailWord_7327737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327737).length < 2 ^ (prefixWord ++ tailWord_7327737).sum := by decide
  have hdescent : baseEnd_7327737 < baseStart_7327737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327770 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 3, 5]
def baseStart_7327770 : Nat := 118140960795 + 7327770 * 2 ^ 59
def prefixEnd_7327770 : Nat := 4983230072969 + 3 ^ 40 * 7327770 * 2
def baseEnd_7327770 : Nat := 1254222711865633433291735

theorem tailTrace_7327770 : CollatzResearch.WordTrace tailWord_7327770 prefixEnd_7327770 1254222711865633433291735 := by
  unfold tailWord_7327770
  simp only [CollatzResearch.WordTrace]
  refine ⟨66816432165687062081355191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178177152441832165550280509 66816432165687062081355191)
  ·
    refine ⟨100224648248530593122032787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66816432165687062081355191 100224648248530593122032787)
    ·
      refine ⟨150336972372795889683049181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100224648248530593122032787 150336972372795889683049181)
      ·
        refine ⟨56376364639798458631143443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150336972372795889683049181 56376364639798458631143443)
        ·
          refine ⟨84564546959697687946715165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56376364639798458631143443 84564546959697687946715165)
          ·
            refine ⟨31711705109886632980018187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84564546959697687946715165 31711705109886632980018187)
            ·
              refine ⟨47567557664829949470027281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31711705109886632980018187 47567557664829949470027281)
              ·
                refine ⟨35675668248622462102520461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47567557664829949470027281 35675668248622462102520461)
                ·
                  refine ⟨13378375593233423288445173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35675668248622462102520461 13378375593233423288445173)
                  ·
                    refine ⟨1254222711865633433291735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13378375593233423288445173 1254222711865633433291735)
                    ·
                      rfl

theorem cell23_7327770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_7327770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327770 prefixEnd_7327770 := by exact prefixLift 7327770
  have htrace : WordTrace (prefixWord ++ tailWord_7327770) baseStart_7327770 baseEnd_7327770 := by
    simpa [prefixWord, tailWord_7327770, baseEnd_7327770] using wordTrace_append hprefix tailTrace_7327770
  have hstable : (prefixWord ++ tailWord_7327770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327770).length < 2 ^ (prefixWord ++ tailWord_7327770).sum := by decide
  have hdescent : baseEnd_7327770 < baseStart_7327770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327794 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2]
def baseStart_7327794 : Nat := 118140960795 + 7327794 * 2 ^ 59
def prefixEnd_7327794 : Nat := 4983230072969 + 3 ^ 40 * 7327794 * 2
def baseEnd_7327794 : Nat := 3762680459132608205975095

theorem tailTrace_7327794 : CollatzResearch.WordTrace tailWord_7327794 prefixEnd_7327794 3762680459132608205975095 := by
  unfold tailWord_7327794
  simp only [CollatzResearch.WordTrace]
  refine ⟨66816651003665325106073609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178177736009774200282862957 66816651003665325106073609)
  ·
    refine ⟨50112488252748993829555207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66816651003665325106073609 50112488252748993829555207)
    ·
      refine ⟨75168732379123490744332811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50112488252748993829555207 75168732379123490744332811)
      ·
        refine ⟨112753098568685236116499217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75168732379123490744332811 112753098568685236116499217)
        ·
          refine ⟨84564823926513927087374413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112753098568685236116499217 84564823926513927087374413)
          ·
            refine ⟨31711808972442722657765405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84564823926513927087374413 31711808972442722657765405)
            ·
              refine ⟨11891928364666020996662027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31711808972442722657765405 11891928364666020996662027)
              ·
                refine ⟨17837892546999031494993041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11891928364666020996662027 17837892546999031494993041)
                ·
                  refine ⟨13378419410249273621244781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17837892546999031494993041 13378419410249273621244781)
                  ·
                    refine ⟨5016907278843477607966793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13378419410249273621244781 5016907278843477607966793)
                    ·
                      refine ⟨3762680459132608205975095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5016907278843477607966793 3762680459132608205975095)
                      ·
                        rfl

theorem cell23_7327794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_7327794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327794 prefixEnd_7327794 := by exact prefixLift 7327794
  have htrace : WordTrace (prefixWord ++ tailWord_7327794) baseStart_7327794 baseEnd_7327794 := by
    simpa [prefixWord, tailWord_7327794, baseEnd_7327794] using wordTrace_append hprefix tailTrace_7327794
  have hstable : (prefixWord ++ tailWord_7327794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327794).length < 2 ^ (prefixWord ++ tailWord_7327794).sum := by decide
  have hdescent : baseEnd_7327794 < baseStart_7327794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327820 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_7327820 : Nat := 118140960795 + 7327820 * 2 ^ 59
def prefixEnd_7327820 : Nat := 4983230072969 + 3 ^ 40 * 7327820 * 2
def baseEnd_7327820 : Nat := 3762693809629625104249975

theorem tailTrace_7327820 : CollatzResearch.WordTrace tailWord_7327820 prefixEnd_7327820 3762693809629625104249975 := by
  unfold tailWord_7327820
  simp only [CollatzResearch.WordTrace]
  refine ⟨133633776156283553432370457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178178368208378071243160609 133633776156283553432370457)
  ·
    refine ⟨100225332117212665074277843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133633776156283553432370457 100225332117212665074277843)
    ·
      refine ⟨150337998175818997611416765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100225332117212665074277843 150337998175818997611416765)
      ·
        refine ⟨56376749315932124104281287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150337998175818997611416765 56376749315932124104281287)
        ·
          refine ⟨84565123973898186156421931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56376749315932124104281287 84565123973898186156421931)
          ·
            refine ⟨126847685960847279234632897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84565123973898186156421931 126847685960847279234632897)
            ·
              refine ⟨95135764470635459425974673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126847685960847279234632897 95135764470635459425974673)
              ·
                refine ⟨71351823352976594569481005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95135764470635459425974673 71351823352976594569481005)
                ·
                  refine ⟨26756933757366222963555377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71351823352976594569481005 26756933757366222963555377)
                  ·
                    refine ⟨20067700318024667222666533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26756933757366222963555377 20067700318024667222666533)
                    ·
                      refine ⟨3762693809629625104249975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20067700318024667222666533 3762693809629625104249975)
                      ·
                        rfl

theorem cell23_7327820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_7327820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327820 prefixEnd_7327820 := by exact prefixLift 7327820
  have htrace : WordTrace (prefixWord ++ tailWord_7327820) baseStart_7327820 baseEnd_7327820 := by
    simpa [prefixWord, tailWord_7327820, baseEnd_7327820] using wordTrace_append hprefix tailTrace_7327820
  have hstable : (prefixWord ++ tailWord_7327820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327820).length < 2 ^ (prefixWord ++ tailWord_7327820).sum := by decide
  have hdescent : baseEnd_7327820 < baseStart_7327820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327834 : List Nat := [3, 1, 1, 2, 1, 1, 7, 1, 2, 4]
def baseStart_7327834 : Nat := 118140960795 + 7327834 * 2 ^ 59
def prefixEnd_7327834 : Nat := 4983230072969 + 3 ^ 40 * 7327834 * 2
def baseEnd_7327834 : Nat := 1254233666119596016491637

theorem tailTrace_7327834 : CollatzResearch.WordTrace tailWord_7327834 prefixEnd_7327834 1254233666119596016491637 := by
  unfold tailWord_7327834
  simp only [CollatzResearch.WordTrace]
  refine ⟨66817015733629096813937639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178178708623010924837167037 66817015733629096813937639)
  ·
    refine ⟨100225523600443645220906459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66817015733629096813937639 100225523600443645220906459)
    ·
      refine ⟨150338285400665467831359689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100225523600443645220906459 150338285400665467831359689)
      ·
        refine ⟨112753714050499100873519767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150338285400665467831359689 112753714050499100873519767)
        ·
          refine ⟨169130571075748651310279651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112753714050499100873519767 169130571075748651310279651)
          ·
            refine ⟨253695856613622976965419477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169130571075748651310279651 253695856613622976965419477)
            ·
              refine ⟨5945996639381788522627019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 253695856613622976965419477 5945996639381788522627019)
              ·
                refine ⟨8918994959072682783940529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5945996639381788522627019 8918994959072682783940529)
                ·
                  refine ⟨6689246219304512087955397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8918994959072682783940529 6689246219304512087955397)
                  ·
                    refine ⟨1254233666119596016491637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6689246219304512087955397 1254233666119596016491637)
                    ·
                      rfl

theorem cell23_7327834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_7327834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327834 prefixEnd_7327834 := by exact prefixLift 7327834
  have htrace : WordTrace (prefixWord ++ tailWord_7327834) baseStart_7327834 baseEnd_7327834 := by
    simpa [prefixWord, tailWord_7327834, baseEnd_7327834] using wordTrace_append hprefix tailTrace_7327834
  have hstable : (prefixWord ++ tailWord_7327834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327834).length < 2 ^ (prefixWord ++ tailWord_7327834).sum := by decide
  have hdescent : baseEnd_7327834 < baseStart_7327834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327838 : List Nat := [4, 4, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_7327838 : Nat := 118140960795 + 7327838 * 2 ^ 59
def prefixEnd_7327838 : Nat := 4983230072969 + 3 ^ 40 * 7327838 * 2
def baseEnd_7327838 : Nat := 1254234350760468677941631

theorem tailTrace_7327838 : CollatzResearch.WordTrace tailWord_7327838 prefixEnd_7327838 1254234350760468677941631 := by
  unfold tailWord_7327838
  simp only [CollatzResearch.WordTrace]
  refine ⟨33408526103312736992362021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178178805884334597292597445 33408526103312736992362021)
  ·
    refine ⟨6264098644371138186067879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33408526103312736992362021 6264098644371138186067879)
    ·
      refine ⟨9396147966556707279101819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6264098644371138186067879 9396147966556707279101819)
      ·
        refine ⟨14094221949835060918652729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9396147966556707279101819 14094221949835060918652729)
        ·
          refine ⟨10570666462376295688989547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14094221949835060918652729 10570666462376295688989547)
          ·
            refine ⟨15855999693564443533484321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10570666462376295688989547 15855999693564443533484321)
            ·
              refine ⟨11891999770173332650113241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15855999693564443533484321 11891999770173332650113241)
              ·
                refine ⟨8918999827629999487584931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11891999770173332650113241 8918999827629999487584931)
                ·
                  refine ⟨13378499741444999231377397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8918999827629999487584931 13378499741444999231377397)
                  ·
                    refine ⟨1254234350760468677941631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13378499741444999231377397 1254234350760468677941631)
                    ·
                      rfl

theorem cell23_7327838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_7327838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327838 prefixEnd_7327838 := by exact prefixLift 7327838
  have htrace : WordTrace (prefixWord ++ tailWord_7327838) baseStart_7327838 baseEnd_7327838 := by
    simpa [prefixWord, tailWord_7327838, baseEnd_7327838] using wordTrace_append hprefix tailTrace_7327838
  have hstable : (prefixWord ++ tailWord_7327838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327838).length < 2 ^ (prefixWord ++ tailWord_7327838).sum := by decide
  have hdescent : baseEnd_7327838 < baseStart_7327838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327857 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 6, 1, 3]
def baseStart_7327857 : Nat := 118140960795 + 7327857 * 2 ^ 59
def prefixEnd_7327857 : Nat := 4983230072969 + 3 ^ 40 * 7327857 * 2
def baseEnd_7327857 : Nat := 3762712808413841459487305

theorem tailTrace_7327857 : CollatzResearch.WordTrace tailWord_7327857 prefixEnd_7327857 3762712808413841459487305 := by
  unfold tailWord_7327857
  simp only [CollatzResearch.WordTrace]
  refine ⟨267268901813433062183837825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178179267875622041455891883 267268901813433062183837825)
  ·
    refine ⟨200451676360074796637878369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267268901813433062183837825 200451676360074796637878369)
    ·
      refine ⟨150338757270056097478408777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200451676360074796637878369 150338757270056097478408777)
      ·
        refine ⟨112754067952542073108806583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150338757270056097478408777 112754067952542073108806583)
        ·
          refine ⟨169131101928813109663209875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112754067952542073108806583 169131101928813109663209875)
          ·
            refine ⟨253696652893219664494814813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169131101928813109663209875 253696652893219664494814813)
            ·
              refine ⟨95136244834957374185555555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253696652893219664494814813 95136244834957374185555555)
              ·
                refine ⟨142704367252436061278333333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95136244834957374185555555 142704367252436061278333333)
                ·
                  refine ⟨6689267214957940372421875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142704367252436061278333333 6689267214957940372421875)
                  ·
                    refine ⟨10033900822436910558632813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6689267214957940372421875 10033900822436910558632813)
                    ·
                      refine ⟨3762712808413841459487305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10033900822436910558632813 3762712808413841459487305)
                      ·
                        rfl

theorem cell23_7327857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_7327857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327857 prefixEnd_7327857 := by exact prefixLift 7327857
  have htrace : WordTrace (prefixWord ++ tailWord_7327857) baseStart_7327857 baseEnd_7327857 := by
    simpa [prefixWord, tailWord_7327857, baseEnd_7327857] using wordTrace_append hprefix tailTrace_7327857
  have hstable : (prefixWord ++ tailWord_7327857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327857).length < 2 ^ (prefixWord ++ tailWord_7327857).sum := by decide
  have hdescent : baseEnd_7327857 < baseStart_7327857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327858 : List Nat := [3, 2, 1, 2, 2, 2, 3, 3, 1, 2, 2]
def baseStart_7327858 : Nat := 118140960795 + 7327858 * 2 ^ 59
def prefixEnd_7327858 : Nat := 4983230072969 + 3 ^ 40 * 7327858 * 2
def baseEnd_7327858 : Nat := 3762713321894495955574801

theorem tailTrace_7327858 : CollatzResearch.WordTrace tailWord_7327858 prefixEnd_7327858 3762713321894495955574801 := by
  unfold tailWord_7327858
  simp only [CollatzResearch.WordTrace]
  refine ⟨66817234571607359838656057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178179292190952959569749485 66817234571607359838656057)
  ·
    refine ⟨50112925928705519878992043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66817234571607359838656057 50112925928705519878992043)
    ·
      refine ⟨75169388893058279818488065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50112925928705519878992043 75169388893058279818488065)
      ·
        refine ⟨56377041669793709863866049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75169388893058279818488065 56377041669793709863866049)
        ·
          refine ⟨42282781252345282397899537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56377041669793709863866049 42282781252345282397899537)
          ·
            refine ⟨31712085939258961798424653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42282781252345282397899537 31712085939258961798424653)
            ·
              refine ⟨11892032227222110674409245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31712085939258961798424653 11892032227222110674409245)
              ·
                refine ⟨4459512085208291502903467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11892032227222110674409245 4459512085208291502903467)
                ·
                  refine ⟨6689268127812437254355201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459512085208291502903467 6689268127812437254355201)
                  ·
                    refine ⟨5016951095859327940766401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6689268127812437254355201 5016951095859327940766401)
                    ·
                      refine ⟨3762713321894495955574801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5016951095859327940766401 3762713321894495955574801)
                      ·
                        rfl

theorem cell23_7327858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_7327858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327858 prefixEnd_7327858 := by exact prefixLift 7327858
  have htrace : WordTrace (prefixWord ++ tailWord_7327858) baseStart_7327858 baseEnd_7327858 := by
    simpa [prefixWord, tailWord_7327858, baseEnd_7327858] using wordTrace_append hprefix tailTrace_7327858
  have hstable : (prefixWord ++ tailWord_7327858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327858).length < 2 ^ (prefixWord ++ tailWord_7327858).sum := by decide
  have hdescent : baseEnd_7327858 < baseStart_7327858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327867 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 7, 3, 2]
def baseStart_7327867 : Nat := 118140960795 + 7327867 * 2 ^ 59
def prefixEnd_7327867 : Nat := 4983230072969 + 3 ^ 40 * 7327867 * 2
def baseEnd_7327867 : Nat := 3762717943220386420362259

theorem tailTrace_7327867 : CollatzResearch.WordTrace tailWord_7327867 prefixEnd_7327867 3762717943220386420362259 := by
  unfold tailWord_7327867
  simp only [CollatzResearch.WordTrace]
  refine ⟨267269266543396833891701855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178179511028931222594467903 267269266543396833891701855)
  ·
    refine ⟨400903899815095250837552783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267269266543396833891701855 400903899815095250837552783)
    ·
      refine ⟨601355849722642876256329175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400903899815095250837552783 601355849722642876256329175)
      ·
        refine ⟨902033774583964314384493763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601355849722642876256329175 902033774583964314384493763)
        ·
          refine ⟨1353050661875946471576740645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902033774583964314384493763 1353050661875946471576740645)
          ·
            refine ⟨253696999101739963420638871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1353050661875946471576740645 253696999101739963420638871)
            ·
              refine ⟨380545498652609945130958307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253696999101739963420638871 380545498652609945130958307)
              ·
                refine ⟨570818247978914917696437461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380545498652609945130958307 570818247978914917696437461)
                ·
                  refine ⟨13378552687005818383510253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 570818247978914917696437461 13378552687005818383510253)
                  ·
                    refine ⟨5016957257627181893816345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13378552687005818383510253 5016957257627181893816345)
                    ·
                      refine ⟨3762717943220386420362259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5016957257627181893816345 3762717943220386420362259)
                      ·
                        rfl

theorem cell23_7327867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 3, 2].length) (baseStart_7327867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327867 prefixEnd_7327867 := by exact prefixLift 7327867
  have htrace : WordTrace (prefixWord ++ tailWord_7327867) baseStart_7327867 baseEnd_7327867 := by
    simpa [prefixWord, tailWord_7327867, baseEnd_7327867] using wordTrace_append hprefix tailTrace_7327867
  have hstable : (prefixWord ++ tailWord_7327867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327867).length < 2 ^ (prefixWord ++ tailWord_7327867).sum := by decide
  have hdescent : baseEnd_7327867 < baseStart_7327867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327897 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 5, 4, 2]
def baseStart_7327897 : Nat := 118140960795 + 7327897 * 2 ^ 59
def prefixEnd_7327897 : Nat := 4983230072969 + 3 ^ 40 * 7327897 * 2
def baseEnd_7327897 : Nat := 3762733347640021302987121

theorem tailTrace_7327897 : CollatzResearch.WordTrace tailWord_7327897 prefixEnd_7327897 3762733347640021302987121 := by
  unfold tailWord_7327897
  simp only [CollatzResearch.WordTrace]
  refine ⟨267270360733288149015293945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178180240488858766010195963 267270360733288149015293945)
  ·
    refine ⟨200452770549966111761470459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267270360733288149015293945 200452770549966111761470459)
    ·
      refine ⟨300679155824949167642205689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200452770549966111761470459 300679155824949167642205689)
      ·
        refine ⟨225509366868711875731654267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300679155824949167642205689 225509366868711875731654267)
        ·
          refine ⟨338264050303067813597481401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225509366868711875731654267 338264050303067813597481401)
          ·
            refine ⟨253698037727300860198111051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338264050303067813597481401 253698037727300860198111051)
            ·
              refine ⟨380547056590951290297166577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253698037727300860198111051 380547056590951290297166577)
              ·
                refine ⟨285410292443213467722874933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380547056590951290297166577 285410292443213467722874933)
                ·
                  refine ⟨26757214916551262599019525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 285410292443213467722874933 26757214916551262599019525)
                  ·
                    refine ⟨5016977796853361737316161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26757214916551262599019525 5016977796853361737316161)
                    ·
                      refine ⟨3762733347640021302987121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5016977796853361737316161 3762733347640021302987121)
                      ·
                        rfl

theorem cell23_7327897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 4, 2].length) (baseStart_7327897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327897 prefixEnd_7327897 := by exact prefixLift 7327897
  have htrace : WordTrace (prefixWord ++ tailWord_7327897) baseStart_7327897 baseEnd_7327897 := by
    simpa [prefixWord, tailWord_7327897, baseEnd_7327897] using wordTrace_append hprefix tailTrace_7327897
  have hstable : (prefixWord ++ tailWord_7327897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327897).length < 2 ^ (prefixWord ++ tailWord_7327897).sum := by decide
  have hdescent : baseEnd_7327897 < baseStart_7327897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327901 : List Nat := [1, 4, 2, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_7327901 : Nat := 118140960795 + 7327901 * 2 ^ 59
def prefixEnd_7327901 : Nat := 4983230072969 + 3 ^ 40 * 7327901 * 2
def baseEnd_7327901 : Nat := 3762735401562639287337103

theorem tailTrace_7327901 : CollatzResearch.WordTrace tailWord_7327901 prefixEnd_7327901 3762735401562639287337103 := by
  unfold tailWord_7327901
  simp only [CollatzResearch.WordTrace]
  refine ⟨267270506625273657698439557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178180337750182438465626371 267270506625273657698439557)
  ·
    refine ⟨50113219992238810818457417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267270506625273657698439557 50113219992238810818457417)
    ·
      refine ⟨37584914994179108113843063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50113219992238810818457417 37584914994179108113843063)
      ·
        refine ⟨56377372491268662170764595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37584914994179108113843063 56377372491268662170764595)
        ·
          refine ⟨84566058736902993256146893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56377372491268662170764595 84566058736902993256146893)
          ·
            refine ⟨31712272026338622471055085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84566058736902993256146893 31712272026338622471055085)
            ·
              refine ⟨11892102009876983426645657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31712272026338622471055085 11892102009876983426645657)
              ·
                refine ⟨8919076507407737569984243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11892102009876983426645657 8919076507407737569984243)
                ·
                  refine ⟨13378614761111606354976365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8919076507407737569984243 13378614761111606354976365)
                  ·
                    refine ⟨5016980535416852383116137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13378614761111606354976365 5016980535416852383116137)
                    ·
                      refine ⟨3762735401562639287337103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5016980535416852383116137 3762735401562639287337103)
                      ·
                        rfl

theorem cell23_7327901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_7327901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327901 prefixEnd_7327901 := by exact prefixLift 7327901
  have htrace : WordTrace (prefixWord ++ tailWord_7327901) baseStart_7327901 baseEnd_7327901 := by
    simpa [prefixWord, tailWord_7327901, baseEnd_7327901] using wordTrace_append hprefix tailTrace_7327901
  have hstable : (prefixWord ++ tailWord_7327901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327901).length < 2 ^ (prefixWord ++ tailWord_7327901).sum := by decide
  have hdescent : baseEnd_7327901 < baseStart_7327901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327930 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_7327930 : Nat := 118140960795 + 7327930 * 2 ^ 59
def prefixEnd_7327930 : Nat := 4983230072969 + 3 ^ 40 * 7327930 * 2
def baseEnd_7327930 : Nat := 3762750292501619673874469

theorem tailTrace_7327930 : CollatzResearch.WordTrace tailWord_7327930 prefixEnd_7327930 3762750292501619673874469 := by
  unfold tailWord_7327930
  simp only [CollatzResearch.WordTrace]
  refine ⟨66817891085542148912811311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178181042894779063767496829 66817891085542148912811311)
  ·
    refine ⟨100226836628313223369216967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66817891085542148912811311 100226836628313223369216967)
    ·
      refine ⟨150340254942469835053825451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100226836628313223369216967 150340254942469835053825451)
      ·
        refine ⟨225510382413704752580738177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150340254942469835053825451 225510382413704752580738177)
        ·
          refine ⟨169132786810278564435553633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225510382413704752580738177 169132786810278564435553633)
          ·
            refine ⟨126849590107708923326665225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169132786810278564435553633 126849590107708923326665225)
            ·
              refine ⟨95137192580781692494998919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126849590107708923326665225 95137192580781692494998919)
              ·
                refine ⟨142705788871172538742498379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95137192580781692494998919 142705788871172538742498379)
                ·
                  refine ⟨214058683306758808113747569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142705788871172538742498379 214058683306758808113747569)
                  ·
                    refine ⟨160544012480069106085310677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 214058683306758808113747569 160544012480069106085310677)
                    ·
                      refine ⟨3762750292501619673874469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160544012480069106085310677 3762750292501619673874469)
                      ·
                        rfl

theorem cell23_7327930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_7327930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327930 prefixEnd_7327930 := by exact prefixLift 7327930
  have htrace : WordTrace (prefixWord ++ tailWord_7327930) baseStart_7327930 baseEnd_7327930 := by
    simpa [prefixWord, tailWord_7327930, baseEnd_7327930] using wordTrace_append hprefix tailTrace_7327930
  have hstable : (prefixWord ++ tailWord_7327930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327930).length < 2 ^ (prefixWord ++ tailWord_7327930).sum := by decide
  have hdescent : baseEnd_7327930 < baseStart_7327930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327931 : List Nat := [1, 1, 1, 1, 1, 2, 8, 2, 2, 2, 2]
def baseStart_7327931 : Nat := 118140960795 + 7327931 * 2 ^ 59
def prefixEnd_7327931 : Nat := 4983230072969 + 3 ^ 40 * 7327931 * 2
def baseEnd_7327931 : Nat := 3762750805982274169961965

theorem tailTrace_7327931 : CollatzResearch.WordTrace tailWord_7327931 prefixEnd_7327931 3762750805982274169961965 := by
  unfold tailWord_7327931
  simp only [CollatzResearch.WordTrace]
  refine ⟨267271600815164972822031647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178181067210109981881354431 267271600815164972822031647)
  ·
    refine ⟨400907401222747459233047471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267271600815164972822031647 400907401222747459233047471)
    ·
      refine ⟨601361101834121188849571207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400907401222747459233047471 601361101834121188849571207)
      ·
        refine ⟨902041652751181783274356811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601361101834121188849571207 902041652751181783274356811)
        ·
          refine ⟨1353062479126772674911535217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902041652751181783274356811 1353062479126772674911535217)
          ·
            refine ⟨1014796859345079506183651413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1353062479126772674911535217 1014796859345079506183651413)
            ·
              refine ⟨11892150695450150463089665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1014796859345079506183651413 11892150695450150463089665)
              ·
                refine ⟨8919113021587612847317249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11892150695450150463089665 8919113021587612847317249)
                ·
                  refine ⟨6689334766190709635487937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8919113021587612847317249 6689334766190709635487937)
                  ·
                    refine ⟨5017001074643032226615953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6689334766190709635487937 5017001074643032226615953)
                    ·
                      refine ⟨3762750805982274169961965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017001074643032226615953 3762750805982274169961965)
                      ·
                        rfl

theorem cell23_7327931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 2, 2].length) (baseStart_7327931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327931 prefixEnd_7327931 := by exact prefixLift 7327931
  have htrace : WordTrace (prefixWord ++ tailWord_7327931) baseStart_7327931 baseEnd_7327931 := by
    simpa [prefixWord, tailWord_7327931, baseEnd_7327931] using wordTrace_append hprefix tailTrace_7327931
  have hstable : (prefixWord ++ tailWord_7327931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327931).length < 2 ^ (prefixWord ++ tailWord_7327931).sum := by decide
  have hdescent : baseEnd_7327931 < baseStart_7327931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327947 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 3]
def baseStart_7327947 : Nat := 118140960795 + 7327947 * 2 ^ 59
def prefixEnd_7327947 : Nat := 4983230072969 + 3 ^ 40 * 7327947 * 2
def baseEnd_7327947 : Nat := 3762759021672746107361891

theorem tailTrace_7327947 : CollatzResearch.WordTrace tailWord_7327947 prefixEnd_7327947 3762759021672746107361891 := by
  unfold tailWord_7327947
  simp only [CollatzResearch.WordTrace]
  refine ⟨267272184383107007554614095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178181456255404671703076063 267272184383107007554614095)
  ·
    refine ⟨400908276574660511331921143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267272184383107007554614095 400908276574660511331921143)
    ·
      refine ⟨601362414861990766997881715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400908276574660511331921143 601362414861990766997881715)
      ·
        refine ⟨902043622292986150496822573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601362414861990766997881715 902043622292986150496822573)
        ·
          refine ⟨338266358359869806436308465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 902043622292986150496822573 338266358359869806436308465)
          ·
            refine ⟨253699768769902354827231349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338266358359869806436308465 253699768769902354827231349)
            ·
              refine ⟨23784353322178345765052939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253699768769902354827231349 23784353322178345765052939)
              ·
                refine ⟨35676529983267518647579409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23784353322178345765052939 35676529983267518647579409)
                ·
                  refine ⟨26757397487450638985684557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35676529983267518647579409 26757397487450638985684557)
                  ·
                    refine ⟨10034024057793989619631709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26757397487450638985684557 10034024057793989619631709)
                    ·
                      refine ⟨3762759021672746107361891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10034024057793989619631709 3762759021672746107361891)
                      ·
                        rfl

theorem cell23_7327947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 3].length) (baseStart_7327947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327947 prefixEnd_7327947 := by exact prefixLift 7327947
  have htrace : WordTrace (prefixWord ++ tailWord_7327947) baseStart_7327947 baseEnd_7327947 := by
    simpa [prefixWord, tailWord_7327947, baseEnd_7327947] using wordTrace_append hprefix tailTrace_7327947
  have hstable : (prefixWord ++ tailWord_7327947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327947).length < 2 ^ (prefixWord ++ tailWord_7327947).sum := by decide
  have hdescent : baseEnd_7327947 < baseStart_7327947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327948 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 1, 4, 2]
def baseStart_7327948 : Nat := 118140960795 + 7327948 * 2 ^ 59
def prefixEnd_7327948 : Nat := 4983230072969 + 3 ^ 40 * 7327948 * 2
def baseEnd_7327948 : Nat := 3762759535153400603449387

theorem tailTrace_7327948 : CollatzResearch.WordTrace tailWord_7327948 prefixEnd_7327948 3762759535153400603449387 := by
  unfold tailWord_7327948
  simp only [CollatzResearch.WordTrace]
  refine ⟨133636110428051692362700249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178181480570735589816933665 133636110428051692362700249)
  ·
    refine ⟨100227082821038769272025187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133636110428051692362700249 100227082821038769272025187)
    ·
      refine ⟨150340624231558153908037781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100227082821038769272025187 150340624231558153908037781)
      ·
        refine ⟨7047216760854288464439271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150340624231558153908037781 7047216760854288464439271)
        ·
          refine ⟨10570825141281432696658907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7047216760854288464439271 10570825141281432696658907)
          ·
            refine ⟨15856237711922149044988361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10570825141281432696658907 15856237711922149044988361)
            ·
              refine ⟨11892178283941611783741271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15856237711922149044988361 11892178283941611783741271)
              ·
                refine ⟨17838267425912417675611907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11892178283941611783741271 17838267425912417675611907)
                ·
                  refine ⟨26757401138868626513417861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17838267425912417675611907 26757401138868626513417861)
                  ·
                    refine ⟨5017012713537867471265849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26757401138868626513417861 5017012713537867471265849)
                    ·
                      refine ⟨3762759535153400603449387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017012713537867471265849 3762759535153400603449387)
                      ·
                        rfl

theorem cell23_7327948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_7327948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327948 prefixEnd_7327948 := by exact prefixLift 7327948
  have htrace : WordTrace (prefixWord ++ tailWord_7327948) baseStart_7327948 baseEnd_7327948 := by
    simpa [prefixWord, tailWord_7327948, baseEnd_7327948] using wordTrace_append hprefix tailTrace_7327948
  have hstable : (prefixWord ++ tailWord_7327948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327948).length < 2 ^ (prefixWord ++ tailWord_7327948).sum := by decide
  have hdescent : baseEnd_7327948 < baseStart_7327948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7327987 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 4]
def baseStart_7327987 : Nat := 118140960795 + 7327987 * 2 ^ 59
def prefixEnd_7327987 : Nat := 4983230072969 + 3 ^ 40 * 7327987 * 2
def baseEnd_7327987 : Nat := 3762779560898925950861707

theorem tailTrace_7327987 : CollatzResearch.WordTrace tailWord_7327987 prefixEnd_7327987 3762779560898925950861707 := by
  unfold tailWord_7327987
  simp only [CollatzResearch.WordTrace]
  refine ⟨267273643302962094386070215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178182428868641396257380143 267273643302962094386070215)
  ·
    refine ⟨400910464954443141579105323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267273643302962094386070215 400910464954443141579105323)
    ·
      refine ⟨601365697431664712368657985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400910464954443141579105323 601365697431664712368657985)
      ·
        refine ⟨451024273073748534276493489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601365697431664712368657985 451024273073748534276493489)
        ·
          refine ⟨338268204805311400707370117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451024273073748534276493489 338268204805311400707370117)
          ·
            refine ⟨63425288400995887632631897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338268204805311400707370117 63425288400995887632631897)
            ·
              refine ⟨47568966300746915724473923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63425288400995887632631897 47568966300746915724473923)
              ·
                refine ⟨71353449451120373586710885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47568966300746915724473923 71353449451120373586710885)
                ·
                  refine ⟨13378771772085070047508291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71353449451120373586710885 13378771772085070047508291)
                  ·
                    refine ⟨20068157658127605071262437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13378771772085070047508291 20068157658127605071262437)
                    ·
                      refine ⟨3762779560898925950861707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20068157658127605071262437 3762779560898925950861707)
                      ·
                        rfl

theorem cell23_7327987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_7327987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7327987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7327987 prefixEnd_7327987 := by exact prefixLift 7327987
  have htrace : WordTrace (prefixWord ++ tailWord_7327987) baseStart_7327987 baseEnd_7327987 := by
    simpa [prefixWord, tailWord_7327987, baseEnd_7327987] using wordTrace_append hprefix tailTrace_7327987
  have hstable : (prefixWord ++ tailWord_7327987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7327987).length < 2 ^ (prefixWord ++ tailWord_7327987).sum := by decide
  have hdescent : baseEnd_7327987 < baseStart_7327987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7327987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328014 : List Nat := [4, 1, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_7328014 : Nat := 118140960795 + 7328014 * 2 ^ 59
def prefixEnd_7328014 : Nat := 4983230072969 + 3 ^ 40 * 7328014 * 2
def baseEnd_7328014 : Nat := 1254264474958865781741361

theorem tailTrace_7328014 : CollatzResearch.WordTrace tailWord_7328014 prefixEnd_7328014 1254264474958865781741361 := by
  unfold tailWord_7328014
  simp only [CollatzResearch.WordTrace]
  refine ⟨33409328509233034749662887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178183085382576185331535397 33409328509233034749662887)
  ·
    refine ⟨50113992763849552124494331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33409328509233034749662887 50113992763849552124494331)
    ·
      refine ⟨75170989145774328186741497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50113992763849552124494331 75170989145774328186741497)
      ·
        refine ⟨56378241859330746140056123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75170989145774328186741497 56378241859330746140056123)
        ·
          refine ⟨84567362788996119210084185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56378241859330746140056123 84567362788996119210084185)
          ·
            refine ⟨63425522091747089407563139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84567362788996119210084185 63425522091747089407563139)
            ·
              refine ⟨95138283137620634111344709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63425522091747089407563139 95138283137620634111344709)
              ·
                refine ⟨17838428088303868895877133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95138283137620634111344709 17838428088303868895877133)
                ·
                  refine ⟨6689410533113950835953925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17838428088303868895877133 6689410533113950835953925)
                  ·
                    refine ⟨1254264474958865781741361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6689410533113950835953925 1254264474958865781741361)
                    ·
                      rfl

theorem cell23_7328014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_7328014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328014 prefixEnd_7328014 := by exact prefixLift 7328014
  have htrace : WordTrace (prefixWord ++ tailWord_7328014) baseStart_7328014 baseEnd_7328014 := by
    simpa [prefixWord, tailWord_7328014, baseEnd_7328014] using wordTrace_append hprefix tailTrace_7328014
  have hstable : (prefixWord ++ tailWord_7328014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328014).length < 2 ^ (prefixWord ++ tailWord_7328014).sum := by decide
  have hdescent : baseEnd_7328014 < baseStart_7328014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328024 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 2, 2, 3]
def baseStart_7328024 : Nat := 118140960795 + 7328024 * 2 ^ 59
def prefixEnd_7328024 : Nat := 4983230072969 + 3 ^ 40 * 7328024 * 2
def baseEnd_7328024 : Nat := 3762798559683142306099037

theorem tailTrace_7328024 : CollatzResearch.WordTrace tailWord_7328024 prefixEnd_7328024 3762798559683142306099037 := by
  unfold tailWord_7328024
  simp only [CollatzResearch.WordTrace]
  refine ⟨133637496401914024852583563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178183328535885366470111417 133637496401914024852583563)
  ·
    refine ⟨200456244602871037278875345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133637496401914024852583563 200456244602871037278875345)
    ·
      refine ⟨150342183452153277959156509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200456244602871037278875345 150342183452153277959156509)
      ·
        refine ⟨56378318794557479234683691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150342183452153277959156509 56378318794557479234683691)
        ·
          refine ⟨84567478191836218852025537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56378318794557479234683691 84567478191836218852025537)
          ·
            refine ⟨63425608643877164139019153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84567478191836218852025537 63425608643877164139019153)
            ·
              refine ⟨47569206482907873104264365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63425608643877164139019153 47569206482907873104264365)
              ·
                refine ⟨17838452431090452414099137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47569206482907873104264365 17838452431090452414099137)
                ·
                  refine ⟨13378839323317839310574353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17838452431090452414099137 13378839323317839310574353)
                  ·
                    refine ⟨10034129492488379482930765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13378839323317839310574353 10034129492488379482930765)
                    ·
                      refine ⟨3762798559683142306099037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10034129492488379482930765 3762798559683142306099037)
                      ·
                        rfl

theorem cell23_7328024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_7328024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328024 prefixEnd_7328024 := by exact prefixLift 7328024
  have htrace : WordTrace (prefixWord ++ tailWord_7328024) baseStart_7328024 baseEnd_7328024 := by
    simpa [prefixWord, tailWord_7328024, baseEnd_7328024] using wordTrace_append hprefix tailTrace_7328024
  have hstable : (prefixWord ++ tailWord_7328024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328024).length < 2 ^ (prefixWord ++ tailWord_7328024).sum := by decide
  have hdescent : baseEnd_7328024 < baseStart_7328024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328064 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 1, 5, 2]
def baseStart_7328064 : Nat := 118140960795 + 7328064 * 2 ^ 59
def prefixEnd_7328064 : Nat := 4983230072969 + 3 ^ 40 * 7328064 * 2
def baseEnd_7328064 : Nat := 3762819098909322149598853

theorem tailTrace_7328064 : CollatzResearch.WordTrace tailWord_7328064 prefixEnd_7328064 3762819098909322149598853 := by
  unfold tailWord_7328064
  simp only [CollatzResearch.WordTrace]
  refine ⟨133638225861841568268311623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178184301149122091024415497 133638225861841568268311623)
  ·
    refine ⟨200457338792762352402467435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133638225861841568268311623 200457338792762352402467435)
    ·
      refine ⟨300686008189143528603701153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200457338792762352402467435 300686008189143528603701153)
      ·
        refine ⟨225514506141857646452775865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300686008189143528603701153 225514506141857646452775865)
        ·
          refine ⟨169135879606393234839581899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225514506141857646452775865 169135879606393234839581899)
          ·
            refine ⟨253703819409589852259372849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169135879606393234839581899 253703819409589852259372849)
            ·
              refine ⟨190277864557192389194529637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253703819409589852259372849 190277864557192389194529637)
              ·
                refine ⟨35677099604473572973974307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190277864557192389194529637 35677099604473572973974307)
                ·
                  refine ⟨53515649406710359460961461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35677099604473572973974307 53515649406710359460961461)
                  ·
                    refine ⟨5017092131879096199465137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53515649406710359460961461 5017092131879096199465137)
                    ·
                      refine ⟨3762819098909322149598853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017092131879096199465137 3762819098909322149598853)
                      ·
                        rfl

theorem cell23_7328064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 5, 2].length) (baseStart_7328064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328064 prefixEnd_7328064 := by exact prefixLift 7328064
  have htrace : WordTrace (prefixWord ++ tailWord_7328064) baseStart_7328064 baseEnd_7328064 := by
    simpa [prefixWord, tailWord_7328064, baseEnd_7328064] using wordTrace_append hprefix tailTrace_7328064
  have hstable : (prefixWord ++ tailWord_7328064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328064).length < 2 ^ (prefixWord ++ tailWord_7328064).sum := by decide
  have hdescent : baseEnd_7328064 < baseStart_7328064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328081 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 2, 3, 2]
def baseStart_7328081 : Nat := 118140960795 + 7328081 * 2 ^ 59
def prefixEnd_7328081 : Nat := 4983230072969 + 3 ^ 40 * 7328081 * 2
def baseEnd_7328081 : Nat := 3762827828080448583086275

theorem tailTrace_7328081 : CollatzResearch.WordTrace tailWord_7328081 prefixEnd_7328081 3762827828080448583086275 := by
  unfold tailWord_7328081
  simp only [CollatzResearch.WordTrace]
  refine ⟨267277071764621548439992097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178184714509747698959994731 267277071764621548439992097)
  ·
    refine ⟨200457803823466161329994073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267277071764621548439992097 200457803823466161329994073)
    ·
      refine ⟨150343352867599620997495555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200457803823466161329994073 150343352867599620997495555)
      ·
        refine ⟨225515029301399431496243333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150343352867599620997495555 225515029301399431496243333)
        ·
          refine ⟨42284067994012393405545625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225515029301399431496243333 42284067994012393405545625)
          ·
            refine ⟨31713050995509295054159219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42284067994012393405545625 31713050995509295054159219)
            ·
              refine ⟨47569576493263942581238829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31713050995509295054159219 47569576493263942581238829)
              ·
                refine ⟨17838591184973978467964561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47569576493263942581238829 17838591184973978467964561)
                ·
                  refine ⟨13378943388730483850973421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17838591184973978467964561 13378943388730483850973421)
                  ·
                    refine ⟨5017103770773931444115033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13378943388730483850973421 5017103770773931444115033)
                    ·
                      refine ⟨3762827828080448583086275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017103770773931444115033 3762827828080448583086275)
                      ·
                        rfl

theorem cell23_7328081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 3, 2].length) (baseStart_7328081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328081 prefixEnd_7328081 := by exact prefixLift 7328081
  have htrace : WordTrace (prefixWord ++ tailWord_7328081) baseStart_7328081 baseEnd_7328081 := by
    simpa [prefixWord, tailWord_7328081, baseEnd_7328081] using wordTrace_append hprefix tailTrace_7328081
  have hstable : (prefixWord ++ tailWord_7328081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328081).length < 2 ^ (prefixWord ++ tailWord_7328081).sum := by decide
  have hdescent : baseEnd_7328081 < baseStart_7328081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328098 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_7328098 : Nat := 118140960795 + 7328098 * 2 ^ 59
def prefixEnd_7328098 : Nat := 4983230072969 + 3 ^ 40 * 7328098 * 2
def baseEnd_7328098 : Nat := 3762836557251575016573697

theorem tailTrace_7328098 : CollatzResearch.WordTrace tailWord_7328098 prefixEnd_7328098 3762836557251575016573697 := by
  unfold tailWord_7328098
  simp only [CollatzResearch.WordTrace]
  refine ⟨66819422951389990085840237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178185127870373306895573965 66819422951389990085840237)
  ·
    refine ⟨25057283606771246282190089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66819422951389990085840237 25057283606771246282190089)
    ·
      refine ⟨18792962705078434711642567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25057283606771246282190089 18792962705078434711642567)
      ·
        refine ⟨28189444057617652067463851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18792962705078434711642567 28189444057617652067463851)
        ·
          refine ⟨42284166086426478101195777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28189444057617652067463851 42284166086426478101195777)
          ·
            refine ⟨31713124564819858575896833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42284166086426478101195777 31713124564819858575896833)
            ·
              refine ⟨23784843423614893931922625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31713124564819858575896833 23784843423614893931922625)
              ·
                refine ⟨17838632567711170448941969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23784843423614893931922625 17838632567711170448941969)
                ·
                  refine ⟨13378974425783377836706477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17838632567711170448941969 13378974425783377836706477)
                  ·
                    refine ⟨5017115409668766688764929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13378974425783377836706477 5017115409668766688764929)
                    ·
                      refine ⟨3762836557251575016573697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017115409668766688764929 3762836557251575016573697)
                      ·
                        rfl

theorem cell23_7328098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_7328098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328098 prefixEnd_7328098 := by exact prefixLift 7328098
  have htrace : WordTrace (prefixWord ++ tailWord_7328098) baseStart_7328098 baseEnd_7328098 := by
    simpa [prefixWord, tailWord_7328098, baseEnd_7328098] using wordTrace_append hprefix tailTrace_7328098
  have hstable : (prefixWord ++ tailWord_7328098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328098).length < 2 ^ (prefixWord ++ tailWord_7328098).sum := by decide
  have hdescent : baseEnd_7328098 < baseStart_7328098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328187 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 9]
def baseStart_7328187 : Nat := 118140960795 + 7328187 * 2 ^ 59
def prefixEnd_7328187 : Nat := 4983230072969 + 3 ^ 40 * 7328187 * 2
def baseEnd_7328187 : Nat := 3762882257029825168360787

theorem tailTrace_7328187 : CollatzResearch.WordTrace tailWord_7328187 prefixEnd_7328187 3762882257029825168360787 := by
  unfold tailWord_7328187
  simp only [CollatzResearch.WordTrace]
  refine ⟨267280937902237528543350815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178187291934825019028900543 267280937902237528543350815)
  ·
    refine ⟨400921406853356292815026223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267280937902237528543350815 400921406853356292815026223)
    ·
      refine ⟨601382110280034439222539335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400921406853356292815026223 601382110280034439222539335)
      ·
        refine ⟨902073165420051658833809003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601382110280034439222539335 902073165420051658833809003)
        ·
          refine ⟨1353109748130077488250713505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902073165420051658833809003 1353109748130077488250713505)
          ·
            refine ⟨1014832311097558116188035129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1353109748130077488250713505 1014832311097558116188035129)
            ·
              refine ⟨761124233323168587141026347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1014832311097558116188035129 761124233323168587141026347)
              ·
                refine ⟨1141686349984752880711539521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761124233323168587141026347 1141686349984752880711539521)
                ·
                  refine ⟨856264762488564660533654641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1141686349984752880711539521 856264762488564660533654641)
                  ·
                    refine ⟨642198571866423495400240981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 856264762488564660533654641 642198571866423495400240981)
                    ·
                      refine ⟨3762882257029825168360787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 642198571866423495400240981 3762882257029825168360787)
                      ·
                        rfl

theorem cell23_7328187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_7328187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328187 prefixEnd_7328187 := by exact prefixLift 7328187
  have htrace : WordTrace (prefixWord ++ tailWord_7328187) baseStart_7328187 baseEnd_7328187 := by
    simpa [prefixWord, tailWord_7328187, baseEnd_7328187] using wordTrace_append hprefix tailTrace_7328187
  have hstable : (prefixWord ++ tailWord_7328187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328187).length < 2 ^ (prefixWord ++ tailWord_7328187).sum := by decide
  have hdescent : baseEnd_7328187 < baseStart_7328187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328196 : List Nat := [2, 3, 3, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_7328196 : Nat := 118140960795 + 7328196 * 2 ^ 59
def prefixEnd_7328196 : Nat := 4983230072969 + 3 ^ 40 * 7328196 * 2
def baseEnd_7328196 : Nat := 3762886878355715633148247

theorem tailTrace_7328196 : CollatzResearch.WordTrace tailWord_7328196 prefixEnd_7328196 3762886878355715633148247 := by
  unfold tailWord_7328196
  simp only [CollatzResearch.WordTrace]
  refine ⟨133640633079602461540214221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178187510772803282053618961 133640633079602461540214221)
  ·
    refine ⟨50115237404850923077580333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133640633079602461540214221 50115237404850923077580333)
    ·
      refine ⟨18793214026819096154092625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50115237404850923077580333 18793214026819096154092625)
      ·
        refine ⟨14094910520114322115569469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18793214026819096154092625 14094910520114322115569469)
        ·
          refine ⟨5285591445042870793338551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14094910520114322115569469 5285591445042870793338551)
          ·
            refine ⟨7928387167564306190007827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5285591445042870793338551 7928387167564306190007827)
            ·
              refine ⟨11892580751346459285011741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7928387167564306190007827 11892580751346459285011741)
              ·
                refine ⟨4459717781754922231879403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11892580751346459285011741 4459717781754922231879403)
                ·
                  refine ⟨6689576672632383347819105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459717781754922231879403 6689576672632383347819105)
                  ·
                    refine ⟨5017182504474287510864329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6689576672632383347819105 5017182504474287510864329)
                    ·
                      refine ⟨3762886878355715633148247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017182504474287510864329 3762886878355715633148247)
                      ·
                        rfl

theorem cell23_7328196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_7328196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328196 prefixEnd_7328196 := by exact prefixLift 7328196
  have htrace : WordTrace (prefixWord ++ tailWord_7328196) baseStart_7328196 baseEnd_7328196 := by
    simpa [prefixWord, tailWord_7328196, baseEnd_7328196] using wordTrace_append hprefix tailTrace_7328196
  have hstable : (prefixWord ++ tailWord_7328196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328196).length < 2 ^ (prefixWord ++ tailWord_7328196).sum := by decide
  have hdescent : baseEnd_7328196 < baseStart_7328196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328201 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 1, 4, 2]
def baseStart_7328201 : Nat := 118140960795 + 7328201 * 2 ^ 59
def prefixEnd_7328201 : Nat := 4983230072969 + 3 ^ 40 * 7328201 * 2
def baseEnd_7328201 : Nat := 3762889445758988113585723

theorem tailTrace_7328201 : CollatzResearch.WordTrace tailWord_7328201 prefixEnd_7328201 3762889445758988113585723 := by
  unfold tailWord_7328201
  simp only [CollatzResearch.WordTrace]
  refine ⟨267281448524186808934360457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178187632349457872622906971 267281448524186808934360457)
  ·
    refine ⟨200461086393140106700770343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267281448524186808934360457 200461086393140106700770343)
    ·
      refine ⟨300691629589710160051155515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200461086393140106700770343 300691629589710160051155515)
      ·
        refine ⟨451037444384565240076733273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300691629589710160051155515 451037444384565240076733273)
        ·
          refine ⟨338278083288423930057549955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451037444384565240076733273 338278083288423930057549955)
          ·
            refine ⟨507417124932635895086324933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338278083288423930057549955 507417124932635895086324933)
            ·
              refine ⟨95140710924869230328685925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 507417124932635895086324933 95140710924869230328685925)
              ·
                refine ⟨17838883298412980686628611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95140710924869230328685925 17838883298412980686628611)
                ·
                  refine ⟨26758324947619471029942917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17838883298412980686628611 26758324947619471029942917)
                  ·
                    refine ⟨5017185927678650818114297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26758324947619471029942917 5017185927678650818114297)
                    ·
                      refine ⟨3762889445758988113585723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017185927678650818114297 3762889445758988113585723)
                      ·
                        rfl

theorem cell23_7328201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 4, 2].length) (baseStart_7328201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328201 prefixEnd_7328201 := by exact prefixLift 7328201
  have htrace : WordTrace (prefixWord ++ tailWord_7328201) baseStart_7328201 baseEnd_7328201 := by
    simpa [prefixWord, tailWord_7328201, baseEnd_7328201] using wordTrace_append hprefix tailTrace_7328201
  have hstable : (prefixWord ++ tailWord_7328201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328201).length < 2 ^ (prefixWord ++ tailWord_7328201).sum := by decide
  have hdescent : baseEnd_7328201 < baseStart_7328201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328218 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2]
def baseStart_7328218 : Nat := 118140960795 + 7328218 * 2 ^ 59
def prefixEnd_7328218 : Nat := 4983230072969 + 3 ^ 40 * 7328218 * 2
def baseEnd_7328218 : Nat := 3762898174930114547073145

theorem tailTrace_7328218 : CollatzResearch.WordTrace tailWord_7328218 prefixEnd_7328218 3762898174930114547073145 := by
  unfold tailWord_7328218
  simp only [CollatzResearch.WordTrace]
  refine ⟨66820517141281305209432327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178188045710083480558486205 66820517141281305209432327)
  ·
    refine ⟨100230775711921957814148491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66820517141281305209432327 100230775711921957814148491)
    ·
      refine ⟨150346163567882936721222737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100230775711921957814148491 150346163567882936721222737)
      ·
        refine ⟨112759622675912202540917053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150346163567882936721222737 112759622675912202540917053)
        ·
          refine ⟨42284858503467075952843895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112759622675912202540917053 42284858503467075952843895)
          ·
            refine ⟨63427287755200613929265843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42284858503467075952843895 63427287755200613929265843)
            ·
              refine ⟨95140931632800920893898765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63427287755200613929265843 95140931632800920893898765)
              ·
                refine ⟨35677849362300345335212037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95140931632800920893898765 35677849362300345335212037)
                ·
                  refine ⟨6689596755431314750352257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35677849362300345335212037 6689596755431314750352257)
                  ·
                    refine ⟨5017197566573486062764193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6689596755431314750352257 5017197566573486062764193)
                    ·
                      refine ⟨3762898174930114547073145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017197566573486062764193 3762898174930114547073145)
                      ·
                        rfl

theorem cell23_7328218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_7328218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328218 prefixEnd_7328218 := by exact prefixLift 7328218
  have htrace : WordTrace (prefixWord ++ tailWord_7328218) baseStart_7328218 baseEnd_7328218 := by
    simpa [prefixWord, tailWord_7328218, baseEnd_7328218] using wordTrace_append hprefix tailTrace_7328218
  have hstable : (prefixWord ++ tailWord_7328218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328218).length < 2 ^ (prefixWord ++ tailWord_7328218).sum := by decide
  have hdescent : baseEnd_7328218 < baseStart_7328218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328221 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_7328221 : Nat := 118140960795 + 7328221 * 2 ^ 59
def prefixEnd_7328221 : Nat := 4983230072969 + 3 ^ 40 * 7328221 * 2
def baseEnd_7328221 : Nat := 3762899715372078035335631

theorem tailTrace_7328221 : CollatzResearch.WordTrace tailWord_7328221 prefixEnd_7328221 3762899715372078035335631 := by
  unfold tailWord_7328221
  simp only [CollatzResearch.WordTrace]
  refine ⟨267282177984114352350088517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178188118656076234900059011 267282177984114352350088517)
  ·
    refine ⟨50115408372021441065641597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267282177984114352350088517 50115408372021441065641597)
    ·
      refine ⟨18793278139508040399615599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50115408372021441065641597 18793278139508040399615599)
      ·
        refine ⟨28189917209262060599423399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18793278139508040399615599 28189917209262060599423399)
        ·
          refine ⟨42284875813893090899135099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28189917209262060599423399 42284875813893090899135099)
          ·
            refine ⟨63427313720839636348702649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42284875813893090899135099 63427313720839636348702649)
            ·
              refine ⟨47570485290629727261526987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63427313720839636348702649 47570485290629727261526987)
              ·
                refine ⟨71355727935944590892290481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47570485290629727261526987 71355727935944590892290481)
                ·
                  refine ⟨53516795951958443169217861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71355727935944590892290481 53516795951958443169217861)
                  ·
                    refine ⟨10034399240992208094228349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53516795951958443169217861 10034399240992208094228349)
                    ·
                      refine ⟨3762899715372078035335631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10034399240992208094228349 3762899715372078035335631)
                      ·
                        rfl

theorem cell23_7328221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_7328221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328221 prefixEnd_7328221 := by exact prefixLift 7328221
  have htrace : WordTrace (prefixWord ++ tailWord_7328221) baseStart_7328221 baseEnd_7328221 := by
    simpa [prefixWord, tailWord_7328221, baseEnd_7328221] using wordTrace_append hprefix tailTrace_7328221
  have hstable : (prefixWord ++ tailWord_7328221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328221).length < 2 ^ (prefixWord ++ tailWord_7328221).sum := by decide
  have hdescent : baseEnd_7328221 < baseStart_7328221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328229 : List Nat := [1, 3, 1, 5, 3, 1, 2, 1, 2, 1, 3]
def baseStart_7328229 : Nat := 118140960795 + 7328229 * 2 ^ 59
def prefixEnd_7328229 : Nat := 4983230072969 + 3 ^ 40 * 7328229 * 2
def baseEnd_7328229 : Nat := 3762903823217314004035595

theorem tailTrace_7328229 : CollatzResearch.WordTrace tailWord_7328229 prefixEnd_7328229 3762903823217314004035595 := by
  unfold tailWord_7328229
  simp only [CollatzResearch.WordTrace]
  refine ⟨267282469768085369716379741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178188313178723579810919827 267282469768085369716379741)
  ·
    refine ⟨100230926163032013643642403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267282469768085369716379741 100230926163032013643642403)
    ·
      refine ⟨150346389244548020465463605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100230926163032013643642403 150346389244548020465463605)
      ·
        refine ⟨14094973991676376918637213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150346389244548020465463605 14094973991676376918637213)
        ·
          refine ⟨5285615246878641344488955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14094973991676376918637213 5285615246878641344488955)
          ·
            refine ⟨7928422870317962016733433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5285615246878641344488955 7928422870317962016733433)
            ·
              refine ⟨5946317152738471512550075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7928422870317962016733433 5946317152738471512550075)
              ·
                refine ⟨8919475729107707268825113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5946317152738471512550075 8919475729107707268825113)
                ·
                  refine ⟨6689606796830780451618835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8919475729107707268825113 6689606796830780451618835)
                  ·
                    refine ⟨10034410195246170677428253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6689606796830780451618835 10034410195246170677428253)
                    ·
                      refine ⟨3762903823217314004035595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10034410195246170677428253 3762903823217314004035595)
                      ·
                        rfl

theorem cell23_7328229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_7328229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328229 prefixEnd_7328229 := by exact prefixLift 7328229
  have htrace : WordTrace (prefixWord ++ tailWord_7328229) baseStart_7328229 baseEnd_7328229 := by
    simpa [prefixWord, tailWord_7328229, baseEnd_7328229] using wordTrace_append hprefix tailTrace_7328229
  have hstable : (prefixWord ++ tailWord_7328229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328229).length < 2 ^ (prefixWord ++ tailWord_7328229).sum := by decide
  have hdescent : baseEnd_7328229 < baseStart_7328229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328269 : List Nat := [1, 7, 1, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_7328269 : Nat := 118140960795 + 7328269 * 2 ^ 59
def prefixEnd_7328269 : Nat := 4983230072969 + 3 ^ 40 * 7328269 * 2
def baseEnd_7328269 : Nat := 3762924362443493847535411

theorem tailTrace_7328269 : CollatzResearch.WordTrace tailWord_7328269 prefixEnd_7328269 3762924362443493847535411 := by
  unfold tailWord_7328269
  simp only [CollatzResearch.WordTrace]
  refine ⟨267283928687940456547835861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178189285791960304365223907 267283928687940456547835861)
  ·
    refine ⟨6264467078623604450339903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 267283928687940456547835861 6264467078623604450339903)
    ·
      refine ⟨9396700617935406675509855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6264467078623604450339903 9396700617935406675509855)
      ·
        refine ⟨14095050926903110013264783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9396700617935406675509855 14095050926903110013264783)
        ·
          refine ⟨21142576390354665019897175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14095050926903110013264783 21142576390354665019897175)
          ·
            refine ⟨31713864585531997529845763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21142576390354665019897175 31713864585531997529845763)
            ·
              refine ⟨47570796878297996294768645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31713864585531997529845763 47570796878297996294768645)
              ·
                refine ⟨8919524414680874305269121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47570796878297996294768645 8919524414680874305269121)
                ·
                  refine ⟨6689643311010655728951841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8919524414680874305269121 6689643311010655728951841)
                  ·
                    refine ⟨5017232483257991796713881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6689643311010655728951841 5017232483257991796713881)
                    ·
                      refine ⟨3762924362443493847535411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017232483257991796713881 3762924362443493847535411)
                      ·
                        rfl

theorem cell23_7328269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_7328269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328269 prefixEnd_7328269 := by exact prefixLift 7328269
  have htrace : WordTrace (prefixWord ++ tailWord_7328269) baseStart_7328269 baseEnd_7328269 := by
    simpa [prefixWord, tailWord_7328269, baseEnd_7328269] using wordTrace_append hprefix tailTrace_7328269
  have hstable : (prefixWord ++ tailWord_7328269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328269).length < 2 ^ (prefixWord ++ tailWord_7328269).sum := by decide
  have hdescent : baseEnd_7328269 < baseStart_7328269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328311 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 3]
def baseStart_7328311 : Nat := 118140960795 + 7328311 * 2 ^ 59
def prefixEnd_7328311 : Nat := 4983230072969 + 3 ^ 40 * 7328311 * 2
def baseEnd_7328311 : Nat := 3762945928630982683210217

theorem tailTrace_7328311 : CollatzResearch.WordTrace tailWord_7328311 prefixEnd_7328311 3762945928630982683210217 := by
  unfold tailWord_7328311
  simp only [CollatzResearch.WordTrace]
  refine ⟨267285460553788297720864787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178190307035858865147243191 267285460553788297720864787)
  ·
    refine ⟨400928190830682446581297181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267285460553788297720864787 400928190830682446581297181)
    ·
      refine ⟨150348071561505917467986443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400928190830682446581297181 150348071561505917467986443)
      ·
        refine ⟨225522107342258876201979665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150348071561505917467986443 225522107342258876201979665)
        ·
          refine ⟨169141580506694157151484749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225522107342258876201979665 169141580506694157151484749)
          ·
            refine ⟨63428092690010308931806781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169141580506694157151484749 63428092690010308931806781)
            ·
              refine ⟨23785534758753865849427543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63428092690010308931806781 23785534758753865849427543)
              ·
                refine ⟨35678302138130798774141315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23785534758753865849427543 35678302138130798774141315)
                ·
                  refine ⟨53517453207196198161211973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35678302138130798774141315 53517453207196198161211973)
                  ·
                    refine ⟨10034522476349287155227245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53517453207196198161211973 10034522476349287155227245)
                    ·
                      refine ⟨3762945928630982683210217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10034522476349287155227245 3762945928630982683210217)
                      ·
                        rfl

theorem cell23_7328311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_7328311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328311 prefixEnd_7328311 := by exact prefixLift 7328311
  have htrace : WordTrace (prefixWord ++ tailWord_7328311) baseStart_7328311 baseEnd_7328311 := by
    simpa [prefixWord, tailWord_7328311, baseEnd_7328311] using wordTrace_append hprefix tailTrace_7328311
  have hstable : (prefixWord ++ tailWord_7328311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328311).length < 2 ^ (prefixWord ++ tailWord_7328311).sum := by decide
  have hdescent : baseEnd_7328311 < baseStart_7328311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328321 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_7328321 : Nat := 118140960795 + 7328321 * 2 ^ 59
def prefixEnd_7328321 : Nat := 4983230072969 + 3 ^ 40 * 7328321 * 2
def baseEnd_7328321 : Nat := 3762951063437527644085171

theorem tailTrace_7328321 : CollatzResearch.WordTrace tailWord_7328321 prefixEnd_7328321 3762951063437527644085171 := by
  unfold tailWord_7328321
  simp only [CollatzResearch.WordTrace]
  refine ⟨267285825283752069428728817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178190550189168046285819211 267285825283752069428728817)
  ·
    refine ⟨200464368962814052071546613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267285825283752069428728817 200464368962814052071546613)
    ·
      refine ⟨18793534590263817381707495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200464368962814052071546613 18793534590263817381707495)
      ·
        refine ⟨28190301885395726072561243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18793534590263817381707495 28190301885395726072561243)
        ·
          refine ⟨42285452828093589108841865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28190301885395726072561243 42285452828093589108841865)
          ·
            refine ⟨31714089621070191831631399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42285452828093589108841865 31714089621070191831631399)
            ·
              refine ⟨47571134431605287747447099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31714089621070191831631399 47571134431605287747447099)
              ·
                refine ⟨71356701647407931621170649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47571134431605287747447099 71356701647407931621170649)
                ·
                  refine ⟨53517526235555948715877987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71356701647407931621170649 53517526235555948715877987)
                  ·
                    refine ⟨80276289353333923073816981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53517526235555948715877987 80276289353333923073816981)
                    ·
                      refine ⟨3762951063437527644085171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80276289353333923073816981 3762951063437527644085171)
                      ·
                        rfl

theorem cell23_7328321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_7328321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328321 prefixEnd_7328321 := by exact prefixLift 7328321
  have htrace : WordTrace (prefixWord ++ tailWord_7328321) baseStart_7328321 baseEnd_7328321 := by
    simpa [prefixWord, tailWord_7328321, baseEnd_7328321] using wordTrace_append hprefix tailTrace_7328321
  have hstable : (prefixWord ++ tailWord_7328321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328321).length < 2 ^ (prefixWord ++ tailWord_7328321).sum := by decide
  have hdescent : baseEnd_7328321 < baseStart_7328321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328331 : List Nat := [1, 1, 1, 1, 3, 1, 7, 2, 6]
def baseStart_7328331 : Nat := 118140960795 + 7328331 * 2 ^ 59
def prefixEnd_7328331 : Nat := 4983230072969 + 3 ^ 40 * 7328331 * 2
def baseEnd_7328331 : Nat := 418106244249341400551125

theorem tailTrace_7328331 : CollatzResearch.WordTrace tailWord_7328331 prefixEnd_7328331 418106244249341400551125 := by
  unfold tailWord_7328331
  simp only [CollatzResearch.WordTrace]
  refine ⟨267286190013715841136592847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178190793342477227424395231 267286190013715841136592847)
  ·
    refine ⟨400929285020573761704889271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267286190013715841136592847 400929285020573761704889271)
    ·
      refine ⟨601393927530860642557333907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400929285020573761704889271 601393927530860642557333907)
      ·
        refine ⟨902090891296290963836000861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601393927530860642557333907 902090891296290963836000861)
        ·
          refine ⟨338284084236109111438500323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 902090891296290963836000861 338284084236109111438500323)
          ·
            refine ⟨507426126354163667157750485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338284084236109111438500323 507426126354163667157750485)
            ·
              refine ⟨11892799836425710949009777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 507426126354163667157750485 11892799836425710949009777)
              ·
                refine ⟨8919599877319283211757333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11892799836425710949009777 8919599877319283211757333)
                ·
                  refine ⟨418106244249341400551125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8919599877319283211757333 418106244249341400551125)
                  ·
                    rfl

theorem cell23_7328331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 6].length) (baseStart_7328331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328331 prefixEnd_7328331 := by exact prefixLift 7328331
  have htrace : WordTrace (prefixWord ++ tailWord_7328331) baseStart_7328331 baseEnd_7328331 := by
    simpa [prefixWord, tailWord_7328331, baseEnd_7328331] using wordTrace_append hprefix tailTrace_7328331
  have hstable : (prefixWord ++ tailWord_7328331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328331).length < 2 ^ (prefixWord ++ tailWord_7328331).sum := by decide
  have hdescent : baseEnd_7328331 < baseStart_7328331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328385 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_7328385 : Nat := 118140960795 + 7328385 * 2 ^ 59
def prefixEnd_7328385 : Nat := 4983230072969 + 3 ^ 40 * 7328385 * 2
def baseEnd_7328385 : Nat := 3762983926199415393684877

theorem tailTrace_7328385 : CollatzResearch.WordTrace tailWord_7328385 prefixEnd_7328385 3762983926199415393684877 := by
  unfold tailWord_7328385
  simp only [CollatzResearch.WordTrace]
  refine ⟨267288159555520208359058609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178192106370346805572705739 267288159555520208359058609)
  ·
    refine ⟨200466119666640156269293957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267288159555520208359058609 200466119666640156269293957)
    ·
      refine ⟨37587397437495029300492617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200466119666640156269293957 37587397437495029300492617)
      ·
        refine ⟨28190548078121271975369463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37587397437495029300492617 28190548078121271975369463)
        ·
          refine ⟨42285822117181907963054195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28190548078121271975369463 42285822117181907963054195)
          ·
            refine ⟨63428733175772861944581293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42285822117181907963054195 63428733175772861944581293)
            ·
              refine ⟨23785774940914823229217985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63428733175772861944581293 23785774940914823229217985)
              ·
                refine ⟨17839331205686117421913489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23785774940914823229217985 17839331205686117421913489)
                ·
                  refine ⟨13379498404264588066435117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17839331205686117421913489 13379498404264588066435117)
                  ·
                    refine ⟨5017311901599220524913169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13379498404264588066435117 5017311901599220524913169)
                    ·
                      refine ⟨3762983926199415393684877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017311901599220524913169 3762983926199415393684877)
                      ·
                        rfl

theorem cell23_7328385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_7328385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328385 prefixEnd_7328385 := by exact prefixLift 7328385
  have htrace : WordTrace (prefixWord ++ tailWord_7328385) baseStart_7328385 baseEnd_7328385 := by
    simpa [prefixWord, tailWord_7328385, baseEnd_7328385] using wordTrace_append hprefix tailTrace_7328385
  have hstable : (prefixWord ++ tailWord_7328385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328385).length < 2 ^ (prefixWord ++ tailWord_7328385).sum := by decide
  have hdescent : baseEnd_7328385 < baseStart_7328385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328386 : List Nat := [3, 4, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7328386 : Nat := 118140960795 + 7328386 * 2 ^ 59
def prefixEnd_7328386 : Nat := 4983230072969 + 3 ^ 40 * 7328386 * 2
def baseEnd_7328386 : Nat := 1254328146560023296590791

theorem tailTrace_7328386 : CollatzResearch.WordTrace tailWord_7328386 prefixEnd_7328386 1254328146560023296590791 := by
  unfold tailWord_7328386
  simp only [CollatzResearch.WordTrace]
  refine ⟨66822049007129146382461253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178192130685677723686563341 66822049007129146382461253)
  ·
    refine ⟨12529134188836714946711485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66822049007129146382461253 12529134188836714946711485)
    ·
      refine ⟨4698425320813768105016807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12529134188836714946711485 4698425320813768105016807)
      ·
        refine ⟨7047637981220652157525211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4698425320813768105016807 7047637981220652157525211)
        ·
          refine ⟨10571456971830978236287817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7047637981220652157525211 10571456971830978236287817)
          ·
            refine ⟨7928592728873233677215863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10571456971830978236287817 7928592728873233677215863)
            ·
              refine ⟨11892889093309850515823795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7928592728873233677215863 11892889093309850515823795)
              ·
                refine ⟨17839333639964775773735693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11892889093309850515823795 17839333639964775773735693)
                ·
                  refine ⟨6689750114986790915150885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17839333639964775773735693 6689750114986790915150885)
                  ·
                    refine ⟨1254328146560023296590791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6689750114986790915150885 1254328146560023296590791)
                    ·
                      rfl

theorem cell23_7328386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7328386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328386 prefixEnd_7328386 := by exact prefixLift 7328386
  have htrace : WordTrace (prefixWord ++ tailWord_7328386) baseStart_7328386 baseEnd_7328386 := by
    simpa [prefixWord, tailWord_7328386, baseEnd_7328386] using wordTrace_append hprefix tailTrace_7328386
  have hstable : (prefixWord ++ tailWord_7328386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328386).length < 2 ^ (prefixWord ++ tailWord_7328386).sum := by decide
  have hdescent : baseEnd_7328386 < baseStart_7328386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328398 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_7328398 : Nat := 118140960795 + 7328398 * 2 ^ 59
def prefixEnd_7328398 : Nat := 4983230072969 + 3 ^ 40 * 7328398 * 2
def baseEnd_7328398 : Nat := 3762990601447923842822317

theorem tailTrace_7328398 : CollatzResearch.WordTrace tailWord_7328398 prefixEnd_7328398 3762990601447923842822317 := by
  unfold tailWord_7328398
  simp only [CollatzResearch.WordTrace]
  refine ⟨33411079213059138947410231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178192422469648741052854565 33411079213059138947410231)
  ·
    refine ⟨50116618819588708421115347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33411079213059138947410231 50116618819588708421115347)
    ·
      refine ⟨75174928229383062631673021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50116618819588708421115347 75174928229383062631673021)
      ·
        refine ⟨28190598086018648486877383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75174928229383062631673021 28190598086018648486877383)
        ·
          refine ⟨42285897129027972730316075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28190598086018648486877383 42285897129027972730316075)
          ·
            refine ⟨63428845693541959095474113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42285897129027972730316075 63428845693541959095474113)
            ·
              refine ⟨47571634270156469321605585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63428845693541959095474113 47571634270156469321605585)
              ·
                refine ⟨35678725702617351991204189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47571634270156469321605585 35678725702617351991204189)
                ·
                  refine ⟨13379522138481506996701571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35678725702617351991204189 13379522138481506996701571)
                  ·
                    refine ⟨20069283207722260495052357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13379522138481506996701571 20069283207722260495052357)
                    ·
                      refine ⟨3762990601447923842822317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20069283207722260495052357 3762990601447923842822317)
                      ·
                        rfl

theorem cell23_7328398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_7328398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328398 prefixEnd_7328398 := by exact prefixLift 7328398
  have htrace : WordTrace (prefixWord ++ tailWord_7328398) baseStart_7328398 baseEnd_7328398 := by
    simpa [prefixWord, tailWord_7328398, baseEnd_7328398] using wordTrace_append hprefix tailTrace_7328398
  have hstable : (prefixWord ++ tailWord_7328398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328398).length < 2 ^ (prefixWord ++ tailWord_7328398).sum := by decide
  have hdescent : baseEnd_7328398 < baseStart_7328398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328432 : List Nat := [2, 1, 1, 1, 2, 1, 3, 7, 1, 2, 2]
def baseStart_7328432 : Nat := 118140960795 + 7328432 * 2 ^ 59
def prefixEnd_7328432 : Nat := 4983230072969 + 3 ^ 40 * 7328432 * 2
def baseEnd_7328432 : Nat := 3763008059790176709797161

theorem tailTrace_7328432 : CollatzResearch.WordTrace tailWord_7328432 prefixEnd_7328432 3763008059790176709797161 := by
  unfold tailWord_7328432
  simp only [CollatzResearch.WordTrace]
  refine ⟨133644936893174967693009775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178193249190899956924013033 133644936893174967693009775)
  ·
    refine ⟨200467405339762451539514663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133644936893174967693009775 200467405339762451539514663)
    ·
      refine ⟨300701108009643677309271995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200467405339762451539514663 300701108009643677309271995)
      ·
        refine ⟨451051662014465515963907993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300701108009643677309271995 451051662014465515963907993)
        ·
          refine ⟨338288746510849136972930995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451051662014465515963907993 338288746510849136972930995)
          ·
            refine ⟨507433119766273705459396493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338288746510849136972930995 507433119766273705459396493)
            ·
              refine ⟨190287419912352639547273685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507433119766273705459396493 190287419912352639547273685)
              ·
                refine ⟨4459861404195764989389227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 190287419912352639547273685 4459861404195764989389227)
                ·
                  refine ⟨6689792106293647484083841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459861404195764989389227 6689792106293647484083841)
                  ·
                    refine ⟨5017344079720235613062881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6689792106293647484083841 5017344079720235613062881)
                    ·
                      refine ⟨3763008059790176709797161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017344079720235613062881 3763008059790176709797161)
                      ·
                        rfl

theorem cell23_7328432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 1, 2, 2].length) (baseStart_7328432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328432 prefixEnd_7328432 := by exact prefixLift 7328432
  have htrace : WordTrace (prefixWord ++ tailWord_7328432) baseStart_7328432 baseEnd_7328432 := by
    simpa [prefixWord, tailWord_7328432, baseEnd_7328432] using wordTrace_append hprefix tailTrace_7328432
  have hstable : (prefixWord ++ tailWord_7328432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328432).length < 2 ^ (prefixWord ++ tailWord_7328432).sum := by decide
  have hdescent : baseEnd_7328432 < baseStart_7328432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328438 : List Nat := [5, 1, 3, 1, 13]
def baseStart_7328438 : Nat := 118140960795 + 7328438 * 2 ^ 59
def prefixEnd_7328438 : Nat := 4983230072969 + 3 ^ 40 * 7328438 * 2
def baseEnd_7328438 : Nat := 5161880851404806154077

theorem tailTrace_7328438 : CollatzResearch.WordTrace tailWord_7328438 prefixEnd_7328438 5161880851404806154077 := by
  unfold tailWord_7328438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16705630789020512400671123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178193395082885465607158645 16705630789020512400671123)
  ·
    refine ⟨25058446183530768601006685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16705630789020512400671123 25058446183530768601006685)
    ·
      refine ⟨9396917318824038225377507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25058446183530768601006685 9396917318824038225377507)
      ·
        refine ⟨14095375978236057338066261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9396917318824038225377507 14095375978236057338066261)
        ·
          refine ⟨5161880851404806154077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 14095375978236057338066261 5161880851404806154077)
          ·
            rfl

theorem cell23_7328438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 13].length) (baseStart_7328438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328438 prefixEnd_7328438 := by exact prefixLift 7328438
  have htrace : WordTrace (prefixWord ++ tailWord_7328438) baseStart_7328438 baseEnd_7328438 := by
    simpa [prefixWord, tailWord_7328438, baseEnd_7328438] using wordTrace_append hprefix tailTrace_7328438
  have hstable : (prefixWord ++ tailWord_7328438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328438).length < 2 ^ (prefixWord ++ tailWord_7328438).sum := by decide
  have hdescent : baseEnd_7328438 < baseStart_7328438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328465 : List Nat := [1, 2, 2, 1, 2, 3, 1, 5, 2, 1, 3]
def baseStart_7328465 : Nat := 118140960795 + 7328465 * 2 ^ 59
def prefixEnd_7328465 : Nat := 4983230072969 + 3 ^ 40 * 7328465 * 2
def baseEnd_7328465 : Nat := 3763025004651775080684509

theorem tailTrace_7328465 : CollatzResearch.WordTrace tailWord_7328465 prefixEnd_7328465 3763025004651775080684509 := by
  unfold tailWord_7328465
  simp only [CollatzResearch.WordTrace]
  refine ⟨267291077395230382021970849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178194051596820254681313899 267291077395230382021970849)
  ·
    refine ⟨200468308046422786516478137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267291077395230382021970849 200468308046422786516478137)
    ·
      refine ⟨150351231034817089887358603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200468308046422786516478137 150351231034817089887358603)
      ·
        refine ⟨225526846552225634831037905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150351231034817089887358603 225526846552225634831037905)
        ·
          refine ⟨169145134914169226123278429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225526846552225634831037905 169145134914169226123278429)
          ·
            refine ⟨63429425592813459796229411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169145134914169226123278429 63429425592813459796229411)
            ·
              refine ⟨95144138389220189694344117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63429425592813459796229411 95144138389220189694344117)
              ·
                refine ⟨8919762973989392783844761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95144138389220189694344117 8919762973989392783844761)
                ·
                  refine ⟨6689822230492044587883571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8919762973989392783844761 6689822230492044587883571)
                  ·
                    refine ⟨10034733345738066881825357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6689822230492044587883571 10034733345738066881825357)
                    ·
                      refine ⟨3763025004651775080684509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10034733345738066881825357 3763025004651775080684509)
                      ·
                        rfl

theorem cell23_7328465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_7328465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328465 prefixEnd_7328465 := by exact prefixLift 7328465
  have htrace : WordTrace (prefixWord ++ tailWord_7328465) baseStart_7328465 baseEnd_7328465 := by
    simpa [prefixWord, tailWord_7328465, baseEnd_7328465] using wordTrace_append hprefix tailTrace_7328465
  have hstable : (prefixWord ++ tailWord_7328465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328465).length < 2 ^ (prefixWord ++ tailWord_7328465).sum := by decide
  have hdescent : baseEnd_7328465 < baseStart_7328465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328491 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 5]
def baseStart_7328491 : Nat := 118140960795 + 7328491 * 2 ^ 59
def prefixEnd_7328491 : Nat := 4983230072969 + 3 ^ 40 * 7328491 * 2
def baseEnd_7328491 : Nat := 3763038355148791978959389

theorem tailTrace_7328491 : CollatzResearch.WordTrace tailWord_7328491 prefixEnd_7328491 3763038355148791978959389 := by
  unfold tailWord_7328491
  simp only [CollatzResearch.WordTrace]
  refine ⟨267292025693136188462417327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178194683795424125641611551 267292025693136188462417327)
  ·
    refine ⟨400938038539704282693625991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267292025693136188462417327 400938038539704282693625991)
    ·
      refine ⟨601407057809556424040438987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400938038539704282693625991 601407057809556424040438987)
      ·
        refine ⟨902110586714334636060658481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601407057809556424040438987 902110586714334636060658481)
        ·
          refine ⟨676582940035750977045493861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 902110586714334636060658481 676582940035750977045493861)
          ·
            refine ⟨126859301256703308196030099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 676582940035750977045493861 126859301256703308196030099)
            ·
              refine ⟨190288951885054962294045149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126859301256703308196030099 190288951885054962294045149)
              ·
                refine ⟨71358356956895610860266931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190288951885054962294045149 71358356956895610860266931)
                ·
                  refine ⟨107037535435343416290400397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71358356956895610860266931 107037535435343416290400397)
                  ·
                    refine ⟨40139075788253781108900149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107037535435343416290400397 40139075788253781108900149)
                    ·
                      refine ⟨3763038355148791978959389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40139075788253781108900149 3763038355148791978959389)
                      ·
                        rfl

theorem cell23_7328491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 5].length) (baseStart_7328491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328491 prefixEnd_7328491 := by exact prefixLift 7328491
  have htrace : WordTrace (prefixWord ++ tailWord_7328491) baseStart_7328491 baseEnd_7328491 := by
    simpa [prefixWord, tailWord_7328491, baseEnd_7328491] using wordTrace_append hprefix tailTrace_7328491
  have hstable : (prefixWord ++ tailWord_7328491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328491).length < 2 ^ (prefixWord ++ tailWord_7328491).sum := by decide
  have hdescent : baseEnd_7328491 < baseStart_7328491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328498 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_7328498 : Nat := 118140960795 + 7328498 * 2 ^ 59
def prefixEnd_7328498 : Nat := 4983230072969 + 3 ^ 40 * 7328498 * 2
def baseEnd_7328498 : Nat := 1254347316504457817190619

theorem tailTrace_7328498 : CollatzResearch.WordTrace tailWord_7328498 prefixEnd_7328498 1254347316504457817190619 := by
  unfold tailWord_7328498
  simp only [CollatzResearch.WordTrace]
  refine ⟨66823070251027707164480537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178194854002740552438614765 66823070251027707164480537)
  ·
    refine ⟨50117302688270780373360403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66823070251027707164480537 50117302688270780373360403)
    ·
      refine ⟨75175954032406170560040605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50117302688270780373360403 75175954032406170560040605)
      ·
        refine ⟨28190982762152313960015227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75175954032406170560040605 28190982762152313960015227)
        ·
          refine ⟨42286474143228470940022841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28190982762152313960015227 42286474143228470940022841)
          ·
            refine ⟨31714855607421353205017131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42286474143228470940022841 31714855607421353205017131)
            ·
              refine ⟨47572283411132029807525697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31714855607421353205017131 47572283411132029807525697)
              ·
                refine ⟨35679212558349022355644273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47572283411132029807525697 35679212558349022355644273)
                ·
                  refine ⟨26759409418761766766733205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35679212558349022355644273 26759409418761766766733205)
                  ·
                    refine ⟨1254347316504457817190619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26759409418761766766733205 1254347316504457817190619)
                    ·
                      rfl

theorem cell23_7328498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_7328498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328498 prefixEnd_7328498 := by exact prefixLift 7328498
  have htrace : WordTrace (prefixWord ++ tailWord_7328498) baseStart_7328498 baseEnd_7328498 := by
    simpa [prefixWord, tailWord_7328498, baseEnd_7328498] using wordTrace_append hprefix tailTrace_7328498
  have hstable : (prefixWord ++ tailWord_7328498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328498).length < 2 ^ (prefixWord ++ tailWord_7328498).sum := by decide
  have hdescent : baseEnd_7328498 < baseStart_7328498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328562 : List Nat := [3, 2, 1, 1, 3, 1, 5, 2, 5]
def baseStart_7328562 : Nat := 118140960795 + 7328562 * 2 ^ 59
def prefixEnd_7328562 : Nat := 4983230072969 + 3 ^ 40 * 7328562 * 2
def baseEnd_7328562 : Nat := 418119423586140133463507

theorem tailTrace_7328562 : CollatzResearch.WordTrace tailWord_7328562 prefixEnd_7328562 418119423586140133463507 := by
  unfold tailWord_7328562
  simp only [CollatzResearch.WordTrace]
  refine ⟨66823653818969741897062985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178196410183919311725501293 66823653818969741897062985)
  ·
    refine ⟨50117740364227306422797239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66823653818969741897062985 50117740364227306422797239)
    ·
      refine ⟨75176610546340959634195859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50117740364227306422797239 75176610546340959634195859)
      ·
        refine ⟨112764915819511439451293789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75176610546340959634195859 112764915819511439451293789)
        ·
          refine ⟨42286843432316789794235171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112764915819511439451293789 42286843432316789794235171)
          ·
            refine ⟨63430265148475184691352757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42286843432316789794235171 63430265148475184691352757)
            ·
              refine ⟨5946587357669548564814321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63430265148475184691352757 5946587357669548564814321)
              ·
                refine ⟨4459940518252161423610741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5946587357669548564814321 4459940518252161423610741)
                ·
                  refine ⟨418119423586140133463507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4459940518252161423610741 418119423586140133463507)
                  ·
                    rfl

theorem cell23_7328562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_7328562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328562 prefixEnd_7328562 := by exact prefixLift 7328562
  have htrace : WordTrace (prefixWord ++ tailWord_7328562) baseStart_7328562 baseEnd_7328562 := by
    simpa [prefixWord, tailWord_7328562, baseEnd_7328562] using wordTrace_append hprefix tailTrace_7328562
  have hstable : (prefixWord ++ tailWord_7328562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328562).length < 2 ^ (prefixWord ++ tailWord_7328562).sum := by decide
  have hdescent : baseEnd_7328562 < baseStart_7328562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328568 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_7328568 : Nat := 118140960795 + 7328568 * 2 ^ 59
def prefixEnd_7328568 : Nat := 4983230072969 + 3 ^ 40 * 7328568 * 2
def baseEnd_7328568 : Nat := 3763077893159188177696535

theorem tailTrace_7328568 : CollatzResearch.WordTrace tailWord_7328568 prefixEnd_7328568 3763077893159188177696535 := by
  unfold tailWord_7328568
  simp only [CollatzResearch.WordTrace]
  refine ⟨133647417056928615306485179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178196556075904820408646905 133647417056928615306485179)
  ·
    refine ⟨200471125585392922959727769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133647417056928615306485179 200471125585392922959727769)
    ·
      refine ⟨150353344189044692219795827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200471125585392922959727769 150353344189044692219795827)
      ·
        refine ⟨225530016283567038329693741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150353344189044692219795827 225530016283567038329693741)
        ·
          refine ⟨84573756106337639373635153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225530016283567038329693741 84573756106337639373635153)
          ·
            refine ⟨63430317079753229530226365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84573756106337639373635153 63430317079753229530226365)
            ·
              refine ⟨23786368904907461073834887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63430317079753229530226365 23786368904907461073834887)
              ·
                refine ⟨35679553357361191610752331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23786368904907461073834887 35679553357361191610752331)
                ·
                  refine ⟨53519330036041787416128497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35679553357361191610752331 53519330036041787416128497)
                  ·
                    refine ⟨40139497527031340562096373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53519330036041787416128497 40139497527031340562096373)
                    ·
                      refine ⟨3763077893159188177696535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40139497527031340562096373 3763077893159188177696535)
                      ·
                        rfl

theorem cell23_7328568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_7328568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328568 prefixEnd_7328568 := by exact prefixLift 7328568
  have htrace : WordTrace (prefixWord ++ tailWord_7328568) baseStart_7328568 baseEnd_7328568 := by
    simpa [prefixWord, tailWord_7328568, baseEnd_7328568] using wordTrace_append hprefix tailTrace_7328568
  have hstable : (prefixWord ++ tailWord_7328568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328568).length < 2 ^ (prefixWord ++ tailWord_7328568).sum := by decide
  have hdescent : baseEnd_7328568 < baseStart_7328568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328573 : List Nat := [1, 4, 1, 4, 2, 2, 2, 1, 2, 2, 2]
def baseStart_7328573 : Nat := 118140960795 + 7328573 * 2 ^ 59
def prefixEnd_7328573 : Nat := 4983230072969 + 3 ^ 40 * 7328573 * 2
def baseEnd_7328573 : Nat := 3763080460562460658134013

theorem tailTrace_7328573 : CollatzResearch.WordTrace tailWord_7328573 prefixEnd_7328573 3763080460562460658134013 := by
  unfold tailWord_7328573
  simp only [CollatzResearch.WordTrace]
  refine ⟨267295016478839116466902373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178196677652559410977934915 267295016478839116466902373)
  ·
    refine ⟨50117815589782334337544195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267295016478839116466902373 50117815589782334337544195)
    ·
      refine ⟨75176723384673501506316293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50117815589782334337544195 75176723384673501506316293)
      ·
        refine ⟨14095635634626281532434305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75176723384673501506316293 14095635634626281532434305)
        ·
          refine ⟨10571726725969711149325729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14095635634626281532434305 10571726725969711149325729)
          ·
            refine ⟨7928795044477283361994297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10571726725969711149325729 7928795044477283361994297)
            ·
              refine ⟨5946596283357962521495723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7928795044477283361994297 5946596283357962521495723)
              ·
                refine ⟨8919894425036943782243585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5946596283357962521495723 8919894425036943782243585)
                ·
                  refine ⟨6689920818777707836682689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8919894425036943782243585 6689920818777707836682689)
                  ·
                    refine ⟨5017440614083280877512017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6689920818777707836682689 5017440614083280877512017)
                    ·
                      refine ⟨3763080460562460658134013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017440614083280877512017 3763080460562460658134013)
                      ·
                        rfl

theorem cell23_7328573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_7328573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328573 prefixEnd_7328573 := by exact prefixLift 7328573
  have htrace : WordTrace (prefixWord ++ tailWord_7328573) baseStart_7328573 baseEnd_7328573 := by
    simpa [prefixWord, tailWord_7328573, baseEnd_7328573] using wordTrace_append hprefix tailTrace_7328573
  have hstable : (prefixWord ++ tailWord_7328573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328573).length < 2 ^ (prefixWord ++ tailWord_7328573).sum := by decide
  have hdescent : baseEnd_7328573 < baseStart_7328573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328608 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 6]
def baseStart_7328608 : Nat := 118140960795 + 7328608 * 2 ^ 59
def prefixEnd_7328608 : Nat := 4983230072969 + 3 ^ 40 * 7328608 * 2
def baseEnd_7328608 : Nat := 3763098432385368021196351

theorem tailTrace_7328608 : CollatzResearch.WordTrace tailWord_7328608 prefixEnd_7328608 3763098432385368021196351 := by
  unfold tailWord_7328608
  simp only [CollatzResearch.WordTrace]
  refine ⟨133648146516856158722213239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178197528689141544962950985 133648146516856158722213239)
  ·
    refine ⟨200472219775284238083319859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133648146516856158722213239 200472219775284238083319859)
    ·
      refine ⟨300708329662926357124979789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200472219775284238083319859 300708329662926357124979789)
      ·
        refine ⟨112765623623597383921867421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300708329662926357124979789 112765623623597383921867421)
        ·
          refine ⟨42287108858849018970700283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112765623623597383921867421 42287108858849018970700283)
          ·
            refine ⟨63430663288273528456050425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42287108858849018970700283 63430663288273528456050425)
            ·
              refine ⟨47572997466205146342037819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63430663288273528456050425 47572997466205146342037819)
              ·
                refine ⟨71359496199307719513056729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47572997466205146342037819 71359496199307719513056729)
                ·
                  refine ⟨53519622149480789634792547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71359496199307719513056729 53519622149480789634792547)
                  ·
                    refine ⟨80279433224221184452188821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53519622149480789634792547 80279433224221184452188821)
                    ·
                      refine ⟨3763098432385368021196351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80279433224221184452188821 3763098432385368021196351)
                      ·
                        rfl

theorem cell23_7328608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_7328608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328608 prefixEnd_7328608 := by exact prefixLift 7328608
  have htrace : WordTrace (prefixWord ++ tailWord_7328608) baseStart_7328608 baseEnd_7328608 := by
    simpa [prefixWord, tailWord_7328608, baseEnd_7328608] using wordTrace_append hprefix tailTrace_7328608
  have hstable : (prefixWord ++ tailWord_7328608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328608).length < 2 ^ (prefixWord ++ tailWord_7328608).sum := by decide
  have hdescent : baseEnd_7328608 < baseStart_7328608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328672 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 2, 3, 2]
def baseStart_7328672 : Nat := 118140960795 + 7328672 * 2 ^ 59
def prefixEnd_7328672 : Nat := 4983230072969 + 3 ^ 40 * 7328672 * 2
def baseEnd_7328672 : Nat := 3763131295147255770796057

theorem tailTrace_7328672 : CollatzResearch.WordTrace tailWord_7328672 prefixEnd_7328672 3763131295147255770796057 := by
  unfold tailWord_7328672
  simp only [CollatzResearch.WordTrace]
  refine ⟨133649313652740228187378135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178199084870320304249837513 133649313652740228187378135)
  ·
    refine ⟨200473970479110342281067203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133649313652740228187378135 200473970479110342281067203)
    ·
      refine ⟨300710955718665513421600805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200473970479110342281067203 300710955718665513421600805)
      ·
        refine ⟨56383304197249783766550151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300710955718665513421600805 56383304197249783766550151)
        ·
          refine ⟨84574956295874675649825227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56383304197249783766550151 84574956295874675649825227)
          ·
            refine ⟨126862434443812013474737841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84574956295874675649825227 126862434443812013474737841)
            ·
              refine ⟨95146825832859010106053381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126862434443812013474737841 95146825832859010106053381)
              ·
                refine ⟨17840029843661064394885009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95146825832859010106053381 17840029843661064394885009)
                ·
                  refine ⟨13380022382745798296163757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17840029843661064394885009 13380022382745798296163757)
                  ·
                    refine ⟨5017508393529674361061409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13380022382745798296163757 5017508393529674361061409)
                    ·
                      refine ⟨3763131295147255770796057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017508393529674361061409 3763131295147255770796057)
                      ·
                        rfl

theorem cell23_7328672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_7328672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328672 prefixEnd_7328672 := by exact prefixLift 7328672
  have htrace : WordTrace (prefixWord ++ tailWord_7328672) baseStart_7328672 baseEnd_7328672 := by
    simpa [prefixWord, tailWord_7328672, baseEnd_7328672] using wordTrace_append hprefix tailTrace_7328672
  have hstable : (prefixWord ++ tailWord_7328672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328672).length < 2 ^ (prefixWord ++ tailWord_7328672).sum := by decide
  have hdescent : baseEnd_7328672 < baseStart_7328672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328695 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 1, 6]
def baseStart_7328695 : Nat := 118140960795 + 7328695 * 2 ^ 59
def prefixEnd_7328695 : Nat := 4983230072969 + 3 ^ 40 * 7328695 * 2
def baseEnd_7328695 : Nat := 1254381035067436393602817

theorem tailTrace_7328695 : CollatzResearch.WordTrace tailWord_7328695 prefixEnd_7328695 1254381035067436393602817 := by
  unfold tailWord_7328695
  simp only [CollatzResearch.WordTrace]
  refine ⟨267299466184397131302843539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178199644122931420868562359 267299466184397131302843539)
  ·
    refine ⟨400949199276595696954265309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267299466184397131302843539 400949199276595696954265309)
    ·
      refine ⟨150355949728723386357849491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400949199276595696954265309 150355949728723386357849491)
      ·
        refine ⟨225533924593085079536774237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150355949728723386357849491 225533924593085079536774237)
        ·
          refine ⟨84575221722406904826290339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225533924593085079536774237 84575221722406904826290339)
          ·
            refine ⟨126862832583610357239435509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84575221722406904826290339 126862832583610357239435509)
            ·
              refine ⟨11893390554713470991197079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126862832583610357239435509 11893390554713470991197079)
              ·
                refine ⟨17840085832070206486795619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11893390554713470991197079 17840085832070206486795619)
                ·
                  refine ⟨26760128748105309730193429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17840085832070206486795619 26760128748105309730193429)
                  ·
                    refine ⟨1254381035067436393602817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26760128748105309730193429 1254381035067436393602817)
                    ·
                      rfl

theorem cell23_7328695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_7328695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328695 prefixEnd_7328695 := by exact prefixLift 7328695
  have htrace : WordTrace (prefixWord ++ tailWord_7328695) baseStart_7328695 baseEnd_7328695 := by
    simpa [prefixWord, tailWord_7328695, baseEnd_7328695] using wordTrace_append hprefix tailTrace_7328695
  have hstable : (prefixWord ++ tailWord_7328695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328695).length < 2 ^ (prefixWord ++ tailWord_7328695).sum := by decide
  have hdescent : baseEnd_7328695 < baseStart_7328695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328702 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_7328702 : Nat := 118140960795 + 7328702 * 2 ^ 59
def prefixEnd_7328702 : Nat := 4983230072969 + 3 ^ 40 * 7328702 * 2
def baseEnd_7328702 : Nat := 3763146699566890653420919

theorem tailTrace_7328702 : CollatzResearch.WordTrace tailWord_7328702 prefixEnd_7328702 3763146699566890653420919 := by
  unfold tailWord_7328702
  simp only [CollatzResearch.WordTrace]
  refine ⟨33412465186921471437293545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178199814330247847665565573 33412465186921471437293545)
  ·
    refine ⟨25059348890191103577970159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33412465186921471437293545 25059348890191103577970159)
    ·
      refine ⟨37589023335286655366955239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25059348890191103577970159 37589023335286655366955239)
      ·
        refine ⟨56383535002929983050432859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37589023335286655366955239 56383535002929983050432859)
        ·
          refine ⟨84575302504394974575649289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56383535002929983050432859 84575302504394974575649289)
          ·
            refine ⟨63431476878296230931736967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84575302504394974575649289 63431476878296230931736967)
            ·
              refine ⟨95147215317444346397605451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63431476878296230931736967 95147215317444346397605451)
              ·
                refine ⟨142720822976166519596408177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95147215317444346397605451 142720822976166519596408177)
                ·
                  refine ⟨107040617232124889697306133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142720822976166519596408177 107040617232124889697306133)
                  ·
                    refine ⟨5017528932755854204561225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107040617232124889697306133 5017528932755854204561225)
                    ·
                      refine ⟨3763146699566890653420919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017528932755854204561225 3763146699566890653420919)
                      ·
                        rfl

theorem cell23_7328702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_7328702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328702 prefixEnd_7328702 := by exact prefixLift 7328702
  have htrace : WordTrace (prefixWord ++ tailWord_7328702) baseStart_7328702 baseEnd_7328702 := by
    simpa [prefixWord, tailWord_7328702, baseEnd_7328702] using wordTrace_append hprefix tailTrace_7328702
  have hstable : (prefixWord ++ tailWord_7328702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328702).length < 2 ^ (prefixWord ++ tailWord_7328702).sum := by decide
  have hdescent : baseEnd_7328702 < baseStart_7328702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328722 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7328722 : Nat := 118140960795 + 7328722 * 2 ^ 59
def prefixEnd_7328722 : Nat := 4983230072969 + 3 ^ 40 * 7328722 * 2
def baseEnd_7328722 : Nat := 3763156969179980575170827

theorem tailTrace_7328722 : CollatzResearch.WordTrace tailWord_7328722 prefixEnd_7328722 3763156969179980575170827 := by
  unfold tailWord_7328722
  simp only [CollatzResearch.WordTrace]
  refine ⟨66825112738824828728519105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178200300636866209942717613 66825112738824828728519105)
  ·
    refine ⟨50118834554118621546389329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66825112738824828728519105 50118834554118621546389329)
    ·
      refine ⟨37589125915588966159791997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50118834554118621546389329 37589125915588966159791997)
      ·
        refine ⟨14095922218345862309921999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37589125915588966159791997 14095922218345862309921999)
        ·
          refine ⟨21143883327518793464882999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14095922218345862309921999 21143883327518793464882999)
          ·
            refine ⟨31715824991278190197324499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21143883327518793464882999 31715824991278190197324499)
            ·
              refine ⟨47573737486917285295986749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31715824991278190197324499 47573737486917285295986749)
              ·
                refine ⟨17840151557593981985995031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47573737486917285295986749 17840151557593981985995031)
                ·
                  refine ⟨26760227336390972978992547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17840151557593981985995031 26760227336390972978992547)
                  ·
                    refine ⟨40140341004586459468488821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26760227336390972978992547 40140341004586459468488821)
                    ·
                      refine ⟨3763156969179980575170827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40140341004586459468488821 3763156969179980575170827)
                      ·
                        rfl

theorem cell23_7328722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7328722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328722 prefixEnd_7328722 := by exact prefixLift 7328722
  have htrace : WordTrace (prefixWord ++ tailWord_7328722) baseStart_7328722 baseEnd_7328722 := by
    simpa [prefixWord, tailWord_7328722, baseEnd_7328722] using wordTrace_append hprefix tailTrace_7328722
  have hstable : (prefixWord ++ tailWord_7328722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328722).length < 2 ^ (prefixWord ++ tailWord_7328722).sum := by decide
  have hdescent : baseEnd_7328722 < baseStart_7328722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328746 : List Nat := [3, 1, 3, 1, 2, 4, 2, 1, 2, 4]
def baseStart_7328746 : Nat := 118140960795 + 7328746 * 2 ^ 59
def prefixEnd_7328746 : Nat := 4983230072969 + 3 ^ 40 * 7328746 * 2
def baseEnd_7328746 : Nat := 1254389764238562827090239

theorem tailTrace_7328746 : CollatzResearch.WordTrace tailWord_7328746 prefixEnd_7328746 1254389764238562827090239 := by
  unfold tailWord_7328746
  simp only [CollatzResearch.WordTrace]
  refine ⟨66825331576803091753237523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178200884204808244675300061 66825331576803091753237523)
  ·
    refine ⟨100237997365204637629856285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66825331576803091753237523 100237997365204637629856285)
    ·
      refine ⟨37589249011951739111196107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100237997365204637629856285 37589249011951739111196107)
      ·
        refine ⟨56383873517927608666794161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37589249011951739111196107 56383873517927608666794161)
        ·
          refine ⟨42287905138445706500095621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56383873517927608666794161 42287905138445706500095621)
          ·
            refine ⟨7928982213458569968767929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42287905138445706500095621 7928982213458569968767929)
            ·
              refine ⟨5946736660093927476575947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7928982213458569968767929 5946736660093927476575947)
              ·
                refine ⟨8920104990140891214863921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5946736660093927476575947 8920104990140891214863921)
                ·
                  refine ⟨6690078742605668411147941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8920104990140891214863921 6690078742605668411147941)
                  ·
                    refine ⟨1254389764238562827090239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6690078742605668411147941 1254389764238562827090239)
                    ·
                      rfl

theorem cell23_7328746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_7328746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328746 prefixEnd_7328746 := by exact prefixLift 7328746
  have htrace : WordTrace (prefixWord ++ tailWord_7328746) baseStart_7328746 baseEnd_7328746 := by
    simpa [prefixWord, tailWord_7328746, baseEnd_7328746] using wordTrace_append hprefix tailTrace_7328746
  have hstable : (prefixWord ++ tailWord_7328746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328746).length < 2 ^ (prefixWord ++ tailWord_7328746).sum := by decide
  have hdescent : baseEnd_7328746 < baseStart_7328746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328802 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_7328802 : Nat := 118140960795 + 7328802 * 2 ^ 59
def prefixEnd_7328802 : Nat := 4983230072969 + 3 ^ 40 * 7328802 * 2
def baseEnd_7328802 : Nat := 1254399349210780087390153

theorem tailTrace_7328802 : CollatzResearch.WordTrace tailWord_7328802 prefixEnd_7328802 1254399349210780087390153 := by
  unfold tailWord_7328802
  simp only [CollatzResearch.WordTrace]
  refine ⟨66825842198752372144247165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178202245863339659051325773 66825842198752372144247165)
  ·
    refine ⟨25059690824532139554092687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66825842198752372144247165 25059690824532139554092687)
    ·
      refine ⟨37589536236798209331139031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25059690824532139554092687 37589536236798209331139031)
      ·
        refine ⟨56384304355197313996708547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37589536236798209331139031 56384304355197313996708547)
        ·
          refine ⟨84576456532795970995062821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56384304355197313996708547 84576456532795970995062821)
          ·
            refine ⟨15858085599899244561574279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84576456532795970995062821 15858085599899244561574279)
            ·
              refine ⟨23787128399848866842361419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15858085599899244561574279 23787128399848866842361419)
              ·
                refine ⟨35680692599773300263542129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23787128399848866842361419 35680692599773300263542129)
                ·
                  refine ⟨26760519449829975197656597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35680692599773300263542129 26760519449829975197656597)
                  ·
                    refine ⟨1254399349210780087390153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26760519449829975197656597 1254399349210780087390153)
                    ·
                      rfl

theorem cell23_7328802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_7328802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328802 prefixEnd_7328802 := by exact prefixLift 7328802
  have htrace : WordTrace (prefixWord ++ tailWord_7328802) baseStart_7328802 baseEnd_7328802 := by
    simpa [prefixWord, tailWord_7328802, baseEnd_7328802] using wordTrace_append hprefix tailTrace_7328802
  have hstable : (prefixWord ++ tailWord_7328802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328802).length < 2 ^ (prefixWord ++ tailWord_7328802).sum := by decide
  have hdescent : baseEnd_7328802 < baseStart_7328802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328830 : List Nat := [4, 2, 1, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_7328830 : Nat := 118140960795 + 7328830 * 2 ^ 59
def prefixEnd_7328830 : Nat := 4983230072969 + 3 ^ 40 * 7328830 * 2
def baseEnd_7328830 : Nat := 3763212425090666152620331

theorem tailTrace_7328830 : CollatzResearch.WordTrace tailWord_7328830 prefixEnd_7328830 3763212425090666152620331 := by
  unfold tailWord_7328830
  simp only [CollatzResearch.WordTrace]
  refine ⟨33413048754863506169875993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178202926692605366239338629 33413048754863506169875993)
  ·
    refine ⟨25059786566147629627406995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33413048754863506169875993 25059786566147629627406995)
    ·
      refine ⟨37589679849221444441110493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25059786566147629627406995 37589679849221444441110493)
      ·
        refine ⟨14096129943458041665416435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37589679849221444441110493 14096129943458041665416435)
        ·
          refine ⟨21144194915187062498124653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14096129943458041665416435 21144194915187062498124653)
          ·
            refine ⟨7929073093195148436796745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21144194915187062498124653 7929073093195148436796745)
            ·
              refine ⟨5946804819896361327597559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7929073093195148436796745 5946804819896361327597559)
              ·
                refine ⟨8920207229844541991396339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5946804819896361327597559 8920207229844541991396339)
                ·
                  refine ⟨13380310844766812987094509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8920207229844541991396339 13380310844766812987094509)
                  ·
                    refine ⟨5017616566787554870160441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13380310844766812987094509 5017616566787554870160441)
                    ·
                      refine ⟨3763212425090666152620331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017616566787554870160441 3763212425090666152620331)
                      ·
                        rfl

theorem cell23_7328830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_7328830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328830 prefixEnd_7328830 := by exact prefixLift 7328830
  have htrace : WordTrace (prefixWord ++ tailWord_7328830) baseStart_7328830 baseEnd_7328830 := by
    simpa [prefixWord, tailWord_7328830, baseEnd_7328830] using wordTrace_append hprefix tailTrace_7328830
  have hstable : (prefixWord ++ tailWord_7328830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328830).length < 2 ^ (prefixWord ++ tailWord_7328830).sum := by decide
  have hdescent : baseEnd_7328830 < baseStart_7328830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328842 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_7328842 : Nat := 118140960795 + 7328842 * 2 ^ 59
def prefixEnd_7328842 : Nat := 4983230072969 + 3 ^ 40 * 7328842 * 2
def baseEnd_7328842 : Nat := 3763218586858520105670275

theorem tailTrace_7328842 : CollatzResearch.WordTrace tailWord_7328842 prefixEnd_7328842 3763218586858520105670275 := by
  unfold tailWord_7328842
  simp only [CollatzResearch.WordTrace]
  refine ⟨66826206928716143852111195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178203218476576383605629853 66826206928716143852111195)
  ·
    refine ⟨100239310393074215778166793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66826206928716143852111195 100239310393074215778166793)
    ·
      refine ⟨75179482794805661833625095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100239310393074215778166793 75179482794805661833625095)
      ·
        refine ⟨112769224192208492750437643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75179482794805661833625095 112769224192208492750437643)
        ·
          refine ⟨169153836288312739125656465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112769224192208492750437643 169153836288312739125656465)
          ·
            refine ⟨126865377216234554344242349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169153836288312739125656465 126865377216234554344242349)
            ·
              refine ⟨47574516456087957879090881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126865377216234554344242349 47574516456087957879090881)
              ·
                refine ⟨35680887342065968409318161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47574516456087957879090881 35680887342065968409318161)
                ·
                  refine ⟨26760665506549476306988621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35680887342065968409318161 26760665506549476306988621)
                  ·
                    refine ⟨10035249564956053615120733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26760665506549476306988621 10035249564956053615120733)
                    ·
                      refine ⟨3763218586858520105670275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10035249564956053615120733 3763218586858520105670275)
                      ·
                        rfl

theorem cell23_7328842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_7328842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328842 prefixEnd_7328842 := by exact prefixLift 7328842
  have htrace : WordTrace (prefixWord ++ tailWord_7328842) baseStart_7328842 baseEnd_7328842 := by
    simpa [prefixWord, tailWord_7328842, baseEnd_7328842] using wordTrace_append hprefix tailTrace_7328842
  have hstable : (prefixWord ++ tailWord_7328842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328842).length < 2 ^ (prefixWord ++ tailWord_7328842).sum := by decide
  have hdescent : baseEnd_7328842 < baseStart_7328842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328855 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_7328855 : Nat := 118140960795 + 7328855 * 2 ^ 59
def prefixEnd_7328855 : Nat := 4983230072969 + 3 ^ 40 * 7328855 * 2
def baseEnd_7328855 : Nat := 3763225262107028554807715

theorem tailTrace_7328855 : CollatzResearch.WordTrace tailWord_7328855 prefixEnd_7328855 3763225262107028554807715 := by
  unfold tailWord_7328855
  simp only [CollatzResearch.WordTrace]
  refine ⟨267305301863817478628668019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178203534575878319085778679 267305301863817478628668019)
  ·
    refine ⟨400957952795726217943002029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267305301863817478628668019 400957952795726217943002029)
    ·
      refine ⟨150359232298397331728625761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400957952795726217943002029 150359232298397331728625761)
      ·
        refine ⟨112769424223797998796469321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150359232298397331728625761 112769424223797998796469321)
        ·
          refine ⟨84577068167848499097351991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112769424223797998796469321 84577068167848499097351991)
          ·
            refine ⟨126865602251772748646027987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84577068167848499097351991 126865602251772748646027987)
            ·
              refine ⟨190298403377659122969041981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126865602251772748646027987 190298403377659122969041981)
              ·
                refine ⟨71361901266622171113390743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190298403377659122969041981 71361901266622171113390743)
                ·
                  refine ⟨107042851899933256670086115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71361901266622171113390743 107042851899933256670086115)
                  ·
                    refine ⟨160564277849899885005129173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107042851899933256670086115 160564277849899885005129173)
                    ·
                      refine ⟨3763225262107028554807715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160564277849899885005129173 3763225262107028554807715)
                      ·
                        rfl

theorem cell23_7328855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_7328855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328855 prefixEnd_7328855 := by exact prefixLift 7328855
  have htrace : WordTrace (prefixWord ++ tailWord_7328855) baseStart_7328855 baseEnd_7328855 := by
    simpa [prefixWord, tailWord_7328855, baseEnd_7328855] using wordTrace_append hprefix tailTrace_7328855
  have hstable : (prefixWord ++ tailWord_7328855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328855).length < 2 ^ (prefixWord ++ tailWord_7328855).sum := by decide
  have hdescent : baseEnd_7328855 < baseStart_7328855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328882 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_7328882 : Nat := 118140960795 + 7328882 * 2 ^ 59
def prefixEnd_7328882 : Nat := 4983230072969 + 3 ^ 40 * 7328882 * 2
def baseEnd_7328882 : Nat := 3763239126084699949170091

theorem tailTrace_7328882 : CollatzResearch.WordTrace tailWord_7328882 prefixEnd_7328882 3763239126084699949170091 := by
  unfold tailWord_7328882
  simp only [CollatzResearch.WordTrace]
  refine ⟨66826571658679915559975225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178204191089813108159933933 66826571658679915559975225)
  ·
    refine ⟨50119928744009936669981419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66826571658679915559975225 50119928744009936669981419)
    ·
      refine ⟨75179893116014905004972129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50119928744009936669981419 75179893116014905004972129)
      ·
        refine ⟨56384919837011178753729097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75179893116014905004972129 56384919837011178753729097)
        ·
          refine ⟨42288689877758384065296823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56384919837011178753729097 42288689877758384065296823)
          ·
            refine ⟨63433034816637576097945235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42288689877758384065296823 63433034816637576097945235)
            ·
              refine ⟨95149552224956364146917853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63433034816637576097945235 95149552224956364146917853)
              ·
                refine ⟨35681082084358636555094195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95149552224956364146917853 35681082084358636555094195)
                ·
                  refine ⟨53521623126537954832641293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35681082084358636555094195 53521623126537954832641293)
                  ·
                    refine ⟨20070608672451733062240485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53521623126537954832641293 20070608672451733062240485)
                    ·
                      refine ⟨3763239126084699949170091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20070608672451733062240485 3763239126084699949170091)
                      ·
                        rfl

theorem cell23_7328882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_7328882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328882 prefixEnd_7328882 := by exact prefixLift 7328882
  have htrace : WordTrace (prefixWord ++ tailWord_7328882) baseStart_7328882 baseEnd_7328882 := by
    simpa [prefixWord, tailWord_7328882, baseEnd_7328882] using wordTrace_append hprefix tailTrace_7328882
  have hstable : (prefixWord ++ tailWord_7328882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328882).length < 2 ^ (prefixWord ++ tailWord_7328882).sum := by decide
  have hdescent : baseEnd_7328882 < baseStart_7328882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328960 : List Nat := [2, 1, 1, 2, 6, 2, 2, 2, 1, 4]
def baseStart_7328960 : Nat := 118140960795 + 7328960 * 2 ^ 59
def prefixEnd_7328960 : Nat := 4983230072969 + 3 ^ 40 * 7328960 * 2
def baseEnd_7328960 : Nat := 1254426392525250214664911

theorem tailTrace_7328960 : CollatzResearch.WordTrace tailWord_7328960 prefixEnd_7328960 1254426392525250214664911 := by
  unfold tailWord_7328960
  simp only [CollatzResearch.WordTrace]
  refine ⟨133654565764218540780620167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178206087685624721040826889 133654565764218540780620167)
  ·
    refine ⟨200481848646327811170930251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133654565764218540780620167 200481848646327811170930251)
    ·
      refine ⟨300722772969491716756395377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200481848646327811170930251 300722772969491716756395377)
      ·
        refine ⟨225542079727118787567296533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300722772969491716756395377 225542079727118787567296533)
        ·
          refine ⟨10572284987208693167217025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 225542079727118787567296533 10572284987208693167217025)
          ·
            refine ⟨7929213740406519875412769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10572284987208693167217025 7929213740406519875412769)
            ·
              refine ⟨5946910305304889906559577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7929213740406519875412769 5946910305304889906559577)
              ·
                refine ⟨4460182728978667429919683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5946910305304889906559577 4460182728978667429919683)
                ·
                  refine ⟨6690274093468001144879525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4460182728978667429919683 6690274093468001144879525)
                  ·
                    refine ⟨1254426392525250214664911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6690274093468001144879525 1254426392525250214664911)
                    ·
                      rfl

theorem cell23_7328960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 1, 4].length) (baseStart_7328960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328960 prefixEnd_7328960 := by exact prefixLift 7328960
  have htrace : WordTrace (prefixWord ++ tailWord_7328960) baseStart_7328960 baseEnd_7328960 := by
    simpa [prefixWord, tailWord_7328960, baseEnd_7328960] using wordTrace_append hprefix tailTrace_7328960
  have hstable : (prefixWord ++ tailWord_7328960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328960).length < 2 ^ (prefixWord ++ tailWord_7328960).sum := by decide
  have hdescent : baseEnd_7328960 < baseStart_7328960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7328993 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 2, 3, 2]
def baseStart_7328993 : Nat := 118140960795 + 7328993 * 2 ^ 59
def prefixEnd_7328993 : Nat := 4983230072969 + 3 ^ 40 * 7328993 * 2
def baseEnd_7328993 : Nat := 3763296122437349014882081

theorem tailTrace_7328993 : CollatzResearch.WordTrace tailWord_7328993 prefixEnd_7328993 3763296122437349014882081 := by
  unfold tailWord_7328993
  simp only [CollatzResearch.WordTrace]
  refine ⟨267310335137317528197191633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178206890091545018798127755 267310335137317528197191633)
  ·
    refine ⟨200482751352988146147893725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267310335137317528197191633 200482751352988146147893725)
    ·
      refine ⟨75181031757370554805460147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200482751352988146147893725 75181031757370554805460147)
      ·
        refine ⟨112771547636055832208190221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75181031757370554805460147 112771547636055832208190221)
        ·
          refine ⟨42289330363520937078071333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112771547636055832208190221 42289330363520937078071333)
          ·
            refine ⟨7929249443160175702138375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42289330363520937078071333 7929249443160175702138375)
            ·
              refine ⟨11893874164740263553207563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7929249443160175702138375 11893874164740263553207563)
              ·
                refine ⟨17840811247110395329811345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11893874164740263553207563 17840811247110395329811345)
                ·
                  refine ⟨13380608435332796497358509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17840811247110395329811345 13380608435332796497358509)
                  ·
                    refine ⟨5017728163249798686509441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13380608435332796497358509 5017728163249798686509441)
                    ·
                      refine ⟨3763296122437349014882081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017728163249798686509441 3763296122437349014882081)
                      ·
                        rfl

theorem cell23_7328993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_7328993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7328993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7328993 prefixEnd_7328993 := by exact prefixLift 7328993
  have htrace : WordTrace (prefixWord ++ tailWord_7328993) baseStart_7328993 baseEnd_7328993 := by
    simpa [prefixWord, tailWord_7328993, baseEnd_7328993] using wordTrace_append hprefix tailTrace_7328993
  have hstable : (prefixWord ++ tailWord_7328993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7328993).length < 2 ^ (prefixWord ++ tailWord_7328993).sum := by decide
  have hdescent : baseEnd_7328993 < baseStart_7328993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7328993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329023 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 3, 2, 2]
def baseStart_7329023 : Nat := 118140960795 + 7329023 * 2 ^ 59
def prefixEnd_7329023 : Nat := 4983230072969 + 3 ^ 40 * 7329023 * 2
def baseEnd_7329023 : Nat := 3763311526856983897506943

theorem tailTrace_7329023 : CollatzResearch.WordTrace tailWord_7329023 prefixEnd_7329023 3763311526856983897506943 := by
  unfold tailWord_7329023
  simp only [CollatzResearch.WordTrace]
  refine ⟨267311429327208843320783723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178207619551472562213855815 267311429327208843320783723)
  ·
    refine ⟨400967143990813264981175585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267311429327208843320783723 400967143990813264981175585)
    ·
      refine ⟨300725357993109948735881689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400967143990813264981175585 300725357993109948735881689)
      ·
        refine ⟨225544018494832461551911267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300725357993109948735881689 225544018494832461551911267)
        ·
          refine ⟨338316027742248692327866901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225544018494832461551911267 338316027742248692327866901)
          ·
            refine ⟨15858563800417907452868761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 338316027742248692327866901 15858563800417907452868761)
            ·
              refine ⟨11893922850313430589651571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15858563800417907452868761 11893922850313430589651571)
              ·
                refine ⟨17840884275470145884477357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11893922850313430589651571 17840884275470145884477357)
                ·
                  refine ⟨6690331603301304706679009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17840884275470145884477357 6690331603301304706679009)
                  ·
                    refine ⟨5017748702475978530009257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6690331603301304706679009 5017748702475978530009257)
                    ·
                      refine ⟨3763311526856983897506943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017748702475978530009257 3763311526856983897506943)
                      ·
                        rfl

theorem cell23_7329023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 2, 2].length) (baseStart_7329023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329023 prefixEnd_7329023 := by exact prefixLift 7329023
  have htrace : WordTrace (prefixWord ++ tailWord_7329023) baseStart_7329023 baseEnd_7329023 := by
    simpa [prefixWord, tailWord_7329023, baseEnd_7329023] using wordTrace_append hprefix tailTrace_7329023
  have hstable : (prefixWord ++ tailWord_7329023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329023).length < 2 ^ (prefixWord ++ tailWord_7329023).sum := by decide
  have hdescent : baseEnd_7329023 < baseStart_7329023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329036 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 1, 2, 4]
def baseStart_7329036 : Nat := 118140960795 + 7329036 * 2 ^ 59
def prefixEnd_7329036 : Nat := 4983230072969 + 3 ^ 40 * 7329036 * 2
def baseEnd_7329036 : Nat := 3763318202105492346644383

theorem tailTrace_7329036 : CollatzResearch.WordTrace tailWord_7329036 prefixEnd_7329036 3763318202105492346644383 := by
  unfold tailWord_7329036
  simp only [CollatzResearch.WordTrace]
  refine ⟨133655951738080873270503481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178207935650774497694004641 133655951738080873270503481)
  ·
    refine ⟨100241963803560654952877611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133655951738080873270503481 100241963803560654952877611)
    ·
      refine ⟨150362945705340982429316417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100241963803560654952877611 150362945705340982429316417)
      ·
        refine ⟨112772209279005736821987313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150362945705340982429316417 112772209279005736821987313)
        ·
          refine ⟨84579156959254302616490485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112772209279005736821987313 84579156959254302616490485)
          ·
            refine ⟨7929295964930090870295983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84579156959254302616490485 7929295964930090870295983)
            ·
              refine ⟨11893943947395136305443975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7929295964930090870295983 11893943947395136305443975)
              ·
                refine ⟨17840915921092704458165963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11893943947395136305443975 17840915921092704458165963)
                ·
                  refine ⟨26761373881639056687248945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17840915921092704458165963 26761373881639056687248945)
                  ·
                    refine ⟨20071030411229292515436709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26761373881639056687248945 20071030411229292515436709)
                    ·
                      refine ⟨3763318202105492346644383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20071030411229292515436709 3763318202105492346644383)
                      ·
                        rfl

theorem cell23_7329036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_7329036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329036 prefixEnd_7329036 := by exact prefixLift 7329036
  have htrace : WordTrace (prefixWord ++ tailWord_7329036) baseStart_7329036 baseEnd_7329036 := by
    simpa [prefixWord, tailWord_7329036, baseEnd_7329036] using wordTrace_append hprefix tailTrace_7329036
  have hstable : (prefixWord ++ tailWord_7329036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329036).length < 2 ^ (prefixWord ++ tailWord_7329036).sum := by decide
  have hdescent : baseEnd_7329036 < baseStart_7329036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329049 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 4, 7, 2]
def baseStart_7329049 : Nat := 118140960795 + 7329049 * 2 ^ 59
def prefixEnd_7329049 : Nat := 4983230072969 + 3 ^ 40 * 7329049 * 2
def baseEnd_7329049 : Nat := 3763324877354000795781823

theorem tailTrace_7329049 : CollatzResearch.WordTrace tailWord_7329049 prefixEnd_7329049 3763324877354000795781823 := by
  unfold tailWord_7329049
  simp only [CollatzResearch.WordTrace]
  refine ⟨267312377625114649761230201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178208251750076433174153467 267312377625114649761230201)
  ·
    refine ⟨200484283218835987320922651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267312377625114649761230201 200484283218835987320922651)
    ·
      refine ⟨300726424828253980981383977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200484283218835987320922651 300726424828253980981383977)
      ·
        refine ⟨225544818621190485736037983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300726424828253980981383977 225544818621190485736037983)
        ·
          refine ⟨338317227931785728604056975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225544818621190485736037983 338317227931785728604056975)
          ·
            refine ⟨507475841897678592906085463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338317227931785728604056975 507475841897678592906085463)
            ·
              refine ⟨761213762846517889359128195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507475841897678592906085463 761213762846517889359128195)
              ·
                refine ⟨1141820644269776834038692293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761213762846517889359128195 1141820644269776834038692293)
                ·
                  refine ⟨214091370800583156382254805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1141820644269776834038692293 214091370800583156382254805)
                  ·
                    refine ⟨5017766503138667727709097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 214091370800583156382254805 5017766503138667727709097)
                    ·
                      refine ⟨3763324877354000795781823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017766503138667727709097 3763324877354000795781823)
                      ·
                        rfl

theorem cell23_7329049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 7, 2].length) (baseStart_7329049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329049 prefixEnd_7329049 := by exact prefixLift 7329049
  have htrace : WordTrace (prefixWord ++ tailWord_7329049) baseStart_7329049 baseEnd_7329049 := by
    simpa [prefixWord, tailWord_7329049, baseEnd_7329049] using wordTrace_append hprefix tailTrace_7329049
  have hstable : (prefixWord ++ tailWord_7329049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329049).length < 2 ^ (prefixWord ++ tailWord_7329049).sum := by decide
  have hdescent : baseEnd_7329049 < baseStart_7329049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
