import V185TrunkScan23Chunk0560

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3316168 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 3, 4]
def baseStart_3316168 : Nat := 118140960795 + 3316168 * 2 ^ 59
def prefixEnd_3316168 : Nat := 4983230072969 + 3 ^ 40 * 3316168 * 2
def baseEnd_3316168 : Nat := 567596038353028903716409

theorem tailTrace_3316168 : CollatzResearch.WordTrace tailWord_3316168 prefixEnd_3316168 567596038353028903716409 := by
  unfold tailWord_3316168
  simp only [CollatzResearch.WordTrace]
  refine ⟨60475291725048583624786579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80633722300064778166382105 60475291725048583624786579)
  ·
    refine ⟨90712937587572875437179869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60475291725048583624786579 90712937587572875437179869)
    ·
      refine ⟨34017351595339828288942451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90712937587572875437179869 34017351595339828288942451)
      ·
        refine ⟨51026027393009742433413677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34017351595339828288942451 51026027393009742433413677)
        ·
          refine ⟨19134760272378653412530129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51026027393009742433413677 19134760272378653412530129)
          ·
            refine ⟨14351070204283990059397597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19134760272378653412530129 14351070204283990059397597)
            ·
              refine ⟨5381651326606496272274099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14351070204283990059397597 5381651326606496272274099)
              ·
                refine ⟨8072476989909744408411149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381651326606496272274099 8072476989909744408411149)
                ·
                  refine ⟨3027178871216154153154181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8072476989909744408411149 3027178871216154153154181)
                  ·
                    refine ⟨567596038353028903716409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3027178871216154153154181 567596038353028903716409)
                    ·
                      rfl

theorem cell23_3316168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_3316168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316168 prefixEnd_3316168 := by exact prefixLift 3316168
  have htrace : WordTrace (prefixWord ++ tailWord_3316168) baseStart_3316168 baseEnd_3316168 := by
    simpa [prefixWord, tailWord_3316168, baseEnd_3316168] using wordTrace_append hprefix tailTrace_3316168
  have hstable : (prefixWord ++ tailWord_3316168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316168).length < 2 ^ (prefixWord ++ tailWord_3316168).sum := by decide
  have hdescent : baseEnd_3316168 < baseStart_3316168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316195 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 3]
def baseStart_3316195 : Nat := 118140960795 + 3316195 * 2 ^ 59
def prefixEnd_3316195 : Nat := 4983230072969 + 3 ^ 40 * 3316195 * 2
def baseEnd_3316195 : Nat := 1702801979036758105511603

theorem tailTrace_3316195 : CollatzResearch.WordTrace tailWord_3316195 prefixEnd_3316195 1702801979036758105511603 := by
  unfold tailWord_3316195
  simp only [CollatzResearch.WordTrace]
  refine ⟨120951568220999350860806039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80634378813999567240537359 120951568220999350860806039)
  ·
    refine ⟨181427352331499026291209059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120951568220999350860806039 181427352331499026291209059)
    ·
      refine ⟨272141028497248539436813589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181427352331499026291209059 272141028497248539436813589)
      ·
        refine ⟨12756610710808525286100637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 272141028497248539436813589 12756610710808525286100637)
        ·
          refine ⟨4783729016553196982287739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12756610710808525286100637 4783729016553196982287739)
          ·
            refine ⟨7175593524829795473431609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4783729016553196982287739 7175593524829795473431609)
            ·
              refine ⟨5381695143622346605073707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7175593524829795473431609 5381695143622346605073707)
              ·
                refine ⟨8072542715433519907610561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381695143622346605073707 8072542715433519907610561)
                ·
                  refine ⟨6054407036575139930707921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8072542715433519907610561 6054407036575139930707921)
                  ·
                    refine ⟨4540805277431354948030941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6054407036575139930707921 4540805277431354948030941)
                    ·
                      refine ⟨1702801979036758105511603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4540805277431354948030941 1702801979036758105511603)
                      ·
                        rfl

theorem cell23_3316195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_3316195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316195 prefixEnd_3316195 := by exact prefixLift 3316195
  have htrace : WordTrace (prefixWord ++ tailWord_3316195) baseStart_3316195 baseEnd_3316195 := by
    simpa [prefixWord, tailWord_3316195, baseEnd_3316195] using wordTrace_append hprefix tailTrace_3316195
  have hstable : (prefixWord ++ tailWord_3316195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316195).length < 2 ^ (prefixWord ++ tailWord_3316195).sum := by decide
  have hdescent : baseEnd_3316195 < baseStart_3316195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316218 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2]
def baseStart_3316218 : Nat := 118140960795 + 3316218 * 2 ^ 59
def prefixEnd_3316218 : Nat := 4983230072969 + 3 ^ 40 * 3316218 * 2
def baseEnd_3316218 : Nat := 1702813789091811515523997

theorem tailTrace_3316218 : CollatzResearch.WordTrace tailWord_3316218 prefixEnd_3316218 1702813789091811515523997 := by
  unfold tailWord_3316218
  simp only [CollatzResearch.WordTrace]
  refine ⟨30238101774979006447223327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80634938066610683859262205 30238101774979006447223327)
  ·
    refine ⟨45357152662468509670834991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30238101774979006447223327 45357152662468509670834991)
    ·
      refine ⟨68035728993702764506252487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45357152662468509670834991 68035728993702764506252487)
      ·
        refine ⟨102053593490554146759378731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68035728993702764506252487 102053593490554146759378731)
        ·
          refine ⟨153080390235831220139068097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102053593490554146759378731 153080390235831220139068097)
          ·
            refine ⟨114810292676873415104301073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153080390235831220139068097 114810292676873415104301073)
            ·
              refine ⟨86107719507655061328225805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114810292676873415104301073 86107719507655061328225805)
              ·
                refine ⟨32290394815370647998084677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86107719507655061328225805 32290394815370647998084677)
                ·
                  refine ⟨6054449027881996499640877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32290394815370647998084677 6054449027881996499640877)
                  ·
                    refine ⟨2270418385455748687365329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6054449027881996499640877 2270418385455748687365329)
                    ·
                      refine ⟨1702813789091811515523997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2270418385455748687365329 1702813789091811515523997)
                      ·
                        rfl

theorem cell23_3316218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2].length) (baseStart_3316218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316218 prefixEnd_3316218 := by exact prefixLift 3316218
  have htrace : WordTrace (prefixWord ++ tailWord_3316218) baseStart_3316218 baseEnd_3316218 := by
    simpa [prefixWord, tailWord_3316218, baseEnd_3316218] using wordTrace_append hprefix tailTrace_3316218
  have hstable : (prefixWord ++ tailWord_3316218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316218).length < 2 ^ (prefixWord ++ tailWord_3316218).sum := by decide
  have hdescent : baseEnd_3316218 < baseStart_3316218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316228 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_3316228 : Nat := 118140960795 + 3316228 * 2 ^ 59
def prefixEnd_3316228 : Nat := 4983230072969 + 3 ^ 40 * 3316228 * 2
def baseEnd_3316228 : Nat := 567606307966118825466317

theorem tailTrace_3316228 : CollatzResearch.WordTrace tailWord_3316228 prefixEnd_3316228 567606307966118825466317 := by
  unfold tailWord_3316228
  simp only [CollatzResearch.WordTrace]
  refine ⟨60476385914939898748378669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80635181219919864997838225 60476385914939898748378669)
  ·
    refine ⟨22678644718102462030642001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60476385914939898748378669 22678644718102462030642001)
    ·
      refine ⟨17008983538576846522981501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22678644718102462030642001 17008983538576846522981501)
      ·
        refine ⟨6378368826966317446118063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17008983538576846522981501 6378368826966317446118063)
        ·
          refine ⟨9567553240449476169177095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6378368826966317446118063 9567553240449476169177095)
          ·
            refine ⟨14351329860674214253765643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9567553240449476169177095 14351329860674214253765643)
            ·
              refine ⟨21526994791011321380648465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14351329860674214253765643 21526994791011321380648465)
              ·
                refine ⟨16145246093258491035486349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21526994791011321380648465 16145246093258491035486349)
                ·
                  refine ⟨6054467284971934138307381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16145246093258491035486349 6054467284971934138307381)
                  ·
                    refine ⟨567606307966118825466317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6054467284971934138307381 567606307966118825466317)
                    ·
                      rfl

theorem cell23_3316228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_3316228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316228 prefixEnd_3316228 := by exact prefixLift 3316228
  have htrace : WordTrace (prefixWord ++ tailWord_3316228) baseStart_3316228 baseEnd_3316228 := by
    simpa [prefixWord, tailWord_3316228, baseEnd_3316228] using wordTrace_append hprefix tailTrace_3316228
  have hstable : (prefixWord ++ tailWord_3316228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316228).length < 2 ^ (prefixWord ++ tailWord_3316228).sum := by decide
  have hdescent : baseEnd_3316228 < baseStart_3316228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316248 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 3, 1, 4]
def baseStart_3316248 : Nat := 118140960795 + 3316248 * 2 ^ 59
def prefixEnd_3316248 : Nat := 4983230072969 + 3 ^ 40 * 3316248 * 2
def baseEnd_3316248 : Nat := 1702829193511446398148859

theorem tailTrace_3316248 : CollatzResearch.WordTrace tailWord_3316248 prefixEnd_3316248 1702829193511446398148859 := by
  unfold tailWord_3316248
  simp only [CollatzResearch.WordTrace]
  refine ⟨60476750644903670456242699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80635667526538227274990265 60476750644903670456242699)
  ·
    refine ⟨90715125967355505684364049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60476750644903670456242699 90715125967355505684364049)
    ·
      refine ⟨68036344475516629263273037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90715125967355505684364049 68036344475516629263273037)
      ·
        refine ⟨25513629178318735973727389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68036344475516629263273037 25513629178318735973727389)
        ·
          refine ⟨9567610941869525990147771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25513629178318735973727389 9567610941869525990147771)
          ·
            refine ⟨14351416412804288985221657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9567610941869525990147771 14351416412804288985221657)
            ·
              refine ⟨10763562309603216738916243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14351416412804288985221657 10763562309603216738916243)
              ·
                refine ⟨16145343464404825108374365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10763562309603216738916243 16145343464404825108374365)
                ·
                  refine ⟨6054503799151809415640387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16145343464404825108374365 6054503799151809415640387)
                  ·
                    refine ⟨9081755698727714123460581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6054503799151809415640387 9081755698727714123460581)
                    ·
                      refine ⟨1702829193511446398148859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9081755698727714123460581 1702829193511446398148859)
                      ·
                        rfl

theorem cell23_3316248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_3316248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316248 prefixEnd_3316248 := by exact prefixLift 3316248
  have htrace : WordTrace (prefixWord ++ tailWord_3316248) baseStart_3316248 baseEnd_3316248 := by
    simpa [prefixWord, tailWord_3316248, baseEnd_3316248] using wordTrace_append hprefix tailTrace_3316248
  have hstable : (prefixWord ++ tailWord_3316248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316248).length < 2 ^ (prefixWord ++ tailWord_3316248).sum := by decide
  have hdescent : baseEnd_3316248 < baseStart_3316248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316252 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_3316252 : Nat := 118140960795 + 3316252 * 2 ^ 59
def prefixEnd_3316252 : Nat := 4983230072969 + 3 ^ 40 * 3316252 * 2
def baseEnd_3316252 : Nat := 1702831247434064382498841

theorem tailTrace_3316252 : CollatzResearch.WordTrace tailWord_3316252 prefixEnd_3316252 1702831247434064382498841 := by
  unfold tailWord_3316252
  simp only [CollatzResearch.WordTrace]
  refine ⟨60476823590896424797815505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80635764787861899730420673 60476823590896424797815505)
  ·
    refine ⟨45357617693172318598361629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60476823590896424797815505 45357617693172318598361629)
    ·
      refine ⟨17009106634939619474385611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45357617693172318598361629 17009106634939619474385611)
      ·
        refine ⟨25513659952409429211578417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17009106634939619474385611 25513659952409429211578417)
        ·
          refine ⟨19135244964307071908683813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25513659952409429211578417 19135244964307071908683813)
          ·
            refine ⟨3587858430807575982878215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19135244964307071908683813 3587858430807575982878215)
            ·
              refine ⟨5381787646211363974317323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587858430807575982878215 5381787646211363974317323)
              ·
                refine ⟨8072681469317045961475985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381787646211363974317323 8072681469317045961475985)
                ·
                  refine ⟨6054511101987784471106989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8072681469317045961475985 6054511101987784471106989)
                  ·
                    refine ⟨2270441663245419176665121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6054511101987784471106989 2270441663245419176665121)
                    ·
                      refine ⟨1702831247434064382498841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2270441663245419176665121 1702831247434064382498841)
                      ·
                        rfl

theorem cell23_3316252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_3316252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316252 prefixEnd_3316252 := by exact prefixLift 3316252
  have htrace : WordTrace (prefixWord ++ tailWord_3316252) baseStart_3316252 baseEnd_3316252 := by
    simpa [prefixWord, tailWord_3316252, baseEnd_3316252] using wordTrace_append hprefix tailTrace_3316252
  have hstable : (prefixWord ++ tailWord_3316252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316252).length < 2 ^ (prefixWord ++ tailWord_3316252).sum := by decide
  have hdescent : baseEnd_3316252 < baseStart_3316252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316258 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3316258 : Nat := 118140960795 + 3316258 * 2 ^ 59
def prefixEnd_3316258 : Nat := 4983230072969 + 3 ^ 40 * 3316258 * 2
def baseEnd_3316258 : Nat := 567611442772663786341271

theorem tailTrace_3316258 : CollatzResearch.WordTrace tailWord_3316258 prefixEnd_3316258 567611442772663786341271 := by
  unfold tailWord_3316258
  simp only [CollatzResearch.WordTrace]
  refine ⟨30238466504942778155087357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80635910679847408413566285 30238466504942778155087357)
  ·
    refine ⟨11339424939353541808157759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30238466504942778155087357 11339424939353541808157759)
    ·
      refine ⟨17009137409030312712236639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11339424939353541808157759 17009137409030312712236639)
      ·
        refine ⟨25513706113545469068354959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17009137409030312712236639 25513706113545469068354959)
        ·
          refine ⟨38270559170318203602532439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25513706113545469068354959 38270559170318203602532439)
          ·
            refine ⟨57405838755477305403798659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38270559170318203602532439 57405838755477305403798659)
            ·
              refine ⟨86108758133215958105697989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57405838755477305403798659 86108758133215958105697989)
              ·
                refine ⟨16145392149977992144818373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86108758133215958105697989 16145392149977992144818373)
                ·
                  refine ⟨3027261028120873527153445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16145392149977992144818373 3027261028120873527153445)
                  ·
                    refine ⟨567611442772663786341271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3027261028120873527153445 567611442772663786341271)
                    ·
                      rfl

theorem cell23_3316258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3316258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316258 prefixEnd_3316258 := by exact prefixLift 3316258
  have htrace : WordTrace (prefixWord ++ tailWord_3316258) baseStart_3316258 baseEnd_3316258 := by
    simpa [prefixWord, tailWord_3316258, baseEnd_3316258] using wordTrace_append hprefix tailTrace_3316258
  have hstable : (prefixWord ++ tailWord_3316258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316258).length < 2 ^ (prefixWord ++ tailWord_3316258).sum := by decide
  have hdescent : baseEnd_3316258 < baseStart_3316258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316282 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2]
def baseStart_3316282 : Nat := 118140960795 + 3316282 * 2 ^ 59
def prefixEnd_3316282 : Nat := 4983230072969 + 3 ^ 40 * 3316282 * 2
def baseEnd_3316282 : Nat := 1702846651853699265123703

theorem tailTrace_3316282 : CollatzResearch.WordTrace tailWord_3316282 prefixEnd_3316282 1702846651853699265123703 := by
  unfold tailWord_3316282
  simp only [CollatzResearch.WordTrace]
  refine ⟨30238685342921041179805775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80636494247789443146148733 30238685342921041179805775)
  ·
    refine ⟨45358028014381561769708663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30238685342921041179805775 45358028014381561769708663)
    ·
      refine ⟨68037042021572342654562995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45358028014381561769708663 68037042021572342654562995)
      ·
        refine ⟨102055563032358513981844493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68037042021572342654562995 102055563032358513981844493)
        ·
          refine ⟨38270836137134442743191685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102055563032358513981844493 38270836137134442743191685)
          ·
            refine ⟨7175781775712708014348441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38270836137134442743191685 7175781775712708014348441)
            ·
              refine ⟨5381836331784531010761331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7175781775712708014348441 5381836331784531010761331)
              ·
                refine ⟨8072754497676796516141997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381836331784531010761331 8072754497676796516141997)
                ·
                  refine ⟨3027282936628798693553249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8072754497676796516141997 3027282936628798693553249)
                  ·
                    refine ⟨2270462202471599020164937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3027282936628798693553249 2270462202471599020164937)
                    ·
                      refine ⟨1702846651853699265123703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2270462202471599020164937 1702846651853699265123703)
                      ·
                        rfl

theorem cell23_3316282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2].length) (baseStart_3316282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316282 prefixEnd_3316282 := by exact prefixLift 3316282
  have htrace : WordTrace (prefixWord ++ tailWord_3316282) baseStart_3316282 baseEnd_3316282 := by
    simpa [prefixWord, tailWord_3316282, baseEnd_3316282] using wordTrace_append hprefix tailTrace_3316282
  have hstable : (prefixWord ++ tailWord_3316282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316282).length < 2 ^ (prefixWord ++ tailWord_3316282).sum := by decide
  have hdescent : baseEnd_3316282 < baseStart_3316282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316295 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 1, 2, 4]
def baseStart_3316295 : Nat := 118140960795 + 3316295 * 2 ^ 59
def prefixEnd_3316295 : Nat := 4983230072969 + 3 ^ 40 * 3316295 * 2
def baseEnd_3316295 : Nat := 1702853327102207714261143

theorem tailTrace_3316295 : CollatzResearch.WordTrace tailWord_3316295 prefixEnd_3316295 1702853327102207714261143 := by
  unfold tailWord_3316295
  simp only [CollatzResearch.WordTrace]
  refine ⟨120955215520637067939446339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80636810347091378626297559 120955215520637067939446339)
  ·
    refine ⟨181432823280955601909169509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120955215520637067939446339 181432823280955601909169509)
    ·
      refine ⟨34018654365179175357969283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181432823280955601909169509 34018654365179175357969283)
      ·
        refine ⟨51027981547768763036953925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34018654365179175357969283 51027981547768763036953925)
        ·
          refine ⟨9567746540206643069428861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51027981547768763036953925 9567746540206643069428861)
          ·
            refine ⟨3587904952577491151035823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9567746540206643069428861 3587904952577491151035823)
            ·
              refine ⟨5381857428866236726553735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587904952577491151035823 5381857428866236726553735)
              ·
                refine ⟨8072786143299355089830603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381857428866236726553735 8072786143299355089830603)
                ·
                  refine ⟨12109179214949032634745905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8072786143299355089830603 12109179214949032634745905)
                  ·
                    refine ⟨9081884411211774476059429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12109179214949032634745905 9081884411211774476059429)
                    ·
                      refine ⟨1702853327102207714261143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9081884411211774476059429 1702853327102207714261143)
                      ·
                        rfl

theorem cell23_3316295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_3316295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316295 prefixEnd_3316295 := by exact prefixLift 3316295
  have htrace : WordTrace (prefixWord ++ tailWord_3316295) baseStart_3316295 baseEnd_3316295 := by
    simpa [prefixWord, tailWord_3316295, baseEnd_3316295] using wordTrace_append hprefix tailTrace_3316295
  have hstable : (prefixWord ++ tailWord_3316295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316295).length < 2 ^ (prefixWord ++ tailWord_3316295).sum := by decide
  have hdescent : baseEnd_3316295 < baseStart_3316295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316311 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_3316311 : Nat := 118140960795 + 3316311 * 2 ^ 59
def prefixEnd_3316311 : Nat := 4983230072969 + 3 ^ 40 * 3316311 * 2
def baseEnd_3316311 : Nat := 1702861542792679651661069

theorem tailTrace_3316311 : CollatzResearch.WordTrace tailWord_3316311 prefixEnd_3316311 1702861542792679651661069 := by
  unfold tailWord_3316311
  simp only [CollatzResearch.WordTrace]
  refine ⟨120955799088579102672028787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80637199392386068448019191 120955799088579102672028787)
  ·
    refine ⟨181433698632868654008043181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120955799088579102672028787 181433698632868654008043181)
    ·
      refine ⟨68037636987325745253016193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181433698632868654008043181 68037636987325745253016193)
      ·
        refine ⟨51028227740494308939762145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68037636987325745253016193 51028227740494308939762145)
        ·
          refine ⟨38271170805370731704821609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51028227740494308939762145 38271170805370731704821609)
          ·
            refine ⟨28703378104028048778616207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38271170805370731704821609 28703378104028048778616207)
            ·
              refine ⟨43055067156042073167924311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28703378104028048778616207 43055067156042073167924311)
              ·
                refine ⟨64582600734063109751886467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43055067156042073167924311 64582600734063109751886467)
                ·
                  refine ⟨96873901101094664627829701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64582600734063109751886467 96873901101094664627829701)
                  ·
                    refine ⟨18163856456455249617718069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96873901101094664627829701 18163856456455249617718069)
                    ·
                      refine ⟨1702861542792679651661069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18163856456455249617718069 1702861542792679651661069)
                      ·
                        rfl

theorem cell23_3316311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_3316311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316311 prefixEnd_3316311 := by exact prefixLift 3316311
  have htrace : WordTrace (prefixWord ++ tailWord_3316311) baseStart_3316311 baseEnd_3316311 := by
    simpa [prefixWord, tailWord_3316311, baseEnd_3316311] using wordTrace_append hprefix tailTrace_3316311
  have hstable : (prefixWord ++ tailWord_3316311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316311).length < 2 ^ (prefixWord ++ tailWord_3316311).sum := by decide
  have hdescent : baseEnd_3316311 < baseStart_3316311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316322 : List Nat := [3, 3, 2, 3, 2, 1, 9]
def baseStart_3316322 : Nat := 118140960795 + 3316322 * 2 ^ 59
def prefixEnd_3316322 : Nat := 4983230072969 + 3 ^ 40 * 3316322 * 2
def baseEnd_3316322 : Nat := 21023051741726902575599

theorem tailTrace_3316322 : CollatzResearch.WordTrace tailWord_3316322 prefixEnd_3316322 21023051741726902575599 := by
  unfold tailWord_3316322
  simp only [CollatzResearch.WordTrace]
  refine ⟨30239050072884812887669805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80637466861026167700452813 30239050072884812887669805)
  ·
    refine ⟨11339643777331804832876177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30239050072884812887669805 11339643777331804832876177)
    ·
      refine ⟨8504732832998853624657133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11339643777331804832876177 8504732832998853624657133)
      ·
        refine ⟨3189274812374570109246425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8504732832998853624657133 3189274812374570109246425)
        ·
          refine ⟨2391956109280927581934819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3189274812374570109246425 2391956109280927581934819)
          ·
            refine ⟨3587934163921391372902229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2391956109280927581934819 3587934163921391372902229)
            ·
              refine ⟨21023051741726902575599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3587934163921391372902229 21023051741726902575599)
              ·
                rfl

theorem cell23_3316322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 9].length) (baseStart_3316322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316322 prefixEnd_3316322 := by exact prefixLift 3316322
  have htrace : WordTrace (prefixWord ++ tailWord_3316322) baseStart_3316322 baseEnd_3316322 := by
    simpa [prefixWord, tailWord_3316322, baseEnd_3316322] using wordTrace_append hprefix tailTrace_3316322
  have hstable : (prefixWord ++ tailWord_3316322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316322).length < 2 ^ (prefixWord ++ tailWord_3316322).sum := by decide
  have hdescent : baseEnd_3316322 < baseStart_3316322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316331 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 2, 6]
def baseStart_3316331 : Nat := 118140960795 + 3316331 * 2 ^ 59
def prefixEnd_3316331 : Nat := 4983230072969 + 3 ^ 40 * 3316331 * 2
def baseEnd_3316331 : Nat := 567623937468589857803659

theorem tailTrace_3316331 : CollatzResearch.WordTrace tailWord_3316331 prefixEnd_3316331 567623937468589857803659 := by
  unfold tailWord_3316331
  simp only [CollatzResearch.WordTrace]
  refine ⟨120956528548506646087756847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80637685699004430725171231 120956528548506646087756847)
  ·
    refine ⟨181434792822759969131635271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120956528548506646087756847 181434792822759969131635271)
    ·
      refine ⟨272152189234139953697452907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181434792822759969131635271 272152189234139953697452907)
      ·
        refine ⟨408228283851209930546179361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272152189234139953697452907 408228283851209930546179361)
        ·
          refine ⟨306171212888407447909634521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408228283851209930546179361 306171212888407447909634521)
          ·
            refine ⟨229628409666305585932225891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306171212888407447909634521 229628409666305585932225891)
            ·
              refine ⟨344442614499458378898338837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229628409666305585932225891 344442614499458378898338837)
              ·
                refine ⟨16145747554662111510859633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 344442614499458378898338837 16145747554662111510859633)
                ·
                  refine ⟨12109310665996583633144725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16145747554662111510859633 12109310665996583633144725)
                  ·
                    refine ⟨567623937468589857803659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12109310665996583633144725 567623937468589857803659)
                    ·
                      rfl

theorem cell23_3316331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 6].length) (baseStart_3316331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316331 prefixEnd_3316331 := by exact prefixLift 3316331
  have htrace : WordTrace (prefixWord ++ tailWord_3316331) baseStart_3316331 baseEnd_3316331 := by
    simpa [prefixWord, tailWord_3316331, baseEnd_3316331] using wordTrace_append hprefix tailTrace_3316331
  have hstable : (prefixWord ++ tailWord_3316331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316331).length < 2 ^ (prefixWord ++ tailWord_3316331).sum := by decide
  have hdescent : baseEnd_3316331 < baseStart_3316331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316361 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 9]
def baseStart_3316361 : Nat := 118140960795 + 3316361 * 2 ^ 59
def prefixEnd_3316361 : Nat := 4983230072969 + 3 ^ 40 * 3316361 * 2
def baseEnd_3316361 : Nat := 189209690758378272892871

theorem tailTrace_3316361 : CollatzResearch.WordTrace tailWord_3316361 prefixEnd_3316361 189209690758378272892871 := by
  unfold tailWord_3316361
  simp only [CollatzResearch.WordTrace]
  refine ⟨120957622738397961211348937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80638415158931974140899291 120957622738397961211348937)
  ·
    refine ⟨90718217053798470908511703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120957622738397961211348937 90718217053798470908511703)
    ·
      refine ⟨136077325580697706362767555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90718217053798470908511703 136077325580697706362767555)
      ·
        refine ⟨204115988371046559544151333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136077325580697706362767555 204115988371046559544151333)
        ·
          refine ⟨38271747819571229914528375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204115988371046559544151333 38271747819571229914528375)
          ·
            refine ⟨57407621729356844871792563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38271747819571229914528375 57407621729356844871792563)
            ·
              refine ⟨86111432594035267307688845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57407621729356844871792563 86111432594035267307688845)
              ·
                refine ⟨32291787222763225240383317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86111432594035267307688845 32291787222763225240383317)
                ·
                  refine ⟨189209690758378272892871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32291787222763225240383317 189209690758378272892871)
                  ·
                    rfl

theorem cell23_3316361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 9].length) (baseStart_3316361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316361 prefixEnd_3316361 := by exact prefixLift 3316361
  have htrace : WordTrace (prefixWord ++ tailWord_3316361) baseStart_3316361 baseEnd_3316361 := by
    simpa [prefixWord, tailWord_3316361, baseEnd_3316361] using wordTrace_append hprefix tailTrace_3316361
  have hstable : (prefixWord ++ tailWord_3316361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316361).length < 2 ^ (prefixWord ++ tailWord_3316361).sum := by decide
  have hdescent : baseEnd_3316361 < baseStart_3316361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316372 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_3316372 : Nat := 118140960795 + 3316372 * 2 ^ 59
def prefixEnd_3316372 : Nat := 4983230072969 + 3 ^ 40 * 3316372 * 2
def baseEnd_3316372 : Nat := 1702892865112603912998289

theorem tailTrace_3316372 : CollatzResearch.WordTrace tailWord_3316372 prefixEnd_3316372 1702892865112603912998289 := by
  unfold tailWord_3316372
  simp only [CollatzResearch.WordTrace]
  refine ⟨60479011970679055044999685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80638682627572073393332913 60479011970679055044999685)
  ·
    refine ⟨11339814744502322820937441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60479011970679055044999685 11339814744502322820937441)
    ·
      refine ⟨8504861058376742115703081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11339814744502322820937441 8504861058376742115703081)
      ·
        refine ⟨6378645793782556586777311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8504861058376742115703081 6378645793782556586777311)
        ·
          refine ⟨9567968690673834880165967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6378645793782556586777311 9567968690673834880165967)
          ·
            refine ⟨14351953036010752320248951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9567968690673834880165967 14351953036010752320248951)
            ·
              refine ⟨21527929554016128480373427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14351953036010752320248951 21527929554016128480373427)
              ·
                refine ⟨32291894331024192720560141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21527929554016128480373427 32291894331024192720560141)
                ·
                  refine ⟨12109460374134072270210053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32291894331024192720560141 12109460374134072270210053)
                  ·
                    refine ⟨2270523820150138550664385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12109460374134072270210053 2270523820150138550664385)
                    ·
                      refine ⟨1702892865112603912998289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2270523820150138550664385 1702892865112603912998289)
                      ·
                        rfl

theorem cell23_3316372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_3316372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316372 prefixEnd_3316372 := by exact prefixLift 3316372
  have htrace : WordTrace (prefixWord ++ tailWord_3316372) baseStart_3316372 baseEnd_3316372 := by
    simpa [prefixWord, tailWord_3316372, baseEnd_3316372] using wordTrace_append hprefix tailTrace_3316372
  have hstable : (prefixWord ++ tailWord_3316372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316372).length < 2 ^ (prefixWord ++ tailWord_3316372).sum := by decide
  have hdescent : baseEnd_3316372 < baseStart_3316372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316405 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3316405 : Nat := 118140960795 + 3316405 * 2 ^ 59
def prefixEnd_3316405 : Nat := 4983230072969 + 3 ^ 40 * 3316405 * 2
def baseEnd_3316405 : Nat := 1702909809974202283885637

theorem tailTrace_3316405 : CollatzResearch.WordTrace tailWord_3316405 prefixEnd_3316405 1702909809974202283885637 := by
  unfold tailWord_3316405
  simp only [CollatzResearch.WordTrace]
  refine ⟨120959227550238556725950669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80639485033492371150633779 120959227550238556725950669)
  ·
    refine ⟨45359710331339458772231501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120959227550238556725950669 45359710331339458772231501)
    ·
      refine ⟨17009891374252297039586813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45359710331339458772231501 17009891374252297039586813)
      ·
        refine ⟨6378709265344611389845055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17009891374252297039586813 6378709265344611389845055)
        ·
          refine ⟨9568063898016917084767583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6378709265344611389845055 9568063898016917084767583)
          ·
            refine ⟨14352095847025375627151375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9568063898016917084767583 14352095847025375627151375)
            ·
              refine ⟨21528143770538063440727063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14352095847025375627151375 21528143770538063440727063)
              ·
                refine ⟨32292215655807095161090595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21528143770538063440727063 32292215655807095161090595)
                ·
                  refine ⟨48438323483710642741635893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32292215655807095161090595 48438323483710642741635893)
                  ·
                    refine ⟨4541092826597872757028365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48438323483710642741635893 4541092826597872757028365)
                    ·
                      refine ⟨1702909809974202283885637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4541092826597872757028365 1702909809974202283885637)
                      ·
                        rfl

theorem cell23_3316405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3316405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316405 prefixEnd_3316405 := by exact prefixLift 3316405
  have htrace : WordTrace (prefixWord ++ tailWord_3316405) baseStart_3316405 baseEnd_3316405 := by
    simpa [prefixWord, tailWord_3316405, baseEnd_3316405] using wordTrace_append hprefix tailTrace_3316405
  have hstable : (prefixWord ++ tailWord_3316405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316405).length < 2 ^ (prefixWord ++ tailWord_3316405).sum := by decide
  have hdescent : baseEnd_3316405 < baseStart_3316405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316406 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_3316406 : Nat := 118140960795 + 3316406 * 2 ^ 59
def prefixEnd_3316406 : Nat := 4983230072969 + 3 ^ 40 * 3316406 * 2
def baseEnd_3316406 : Nat := 1702910323454856779973133

theorem tailTrace_3316406 : CollatzResearch.WordTrace tailWord_3316406 prefixEnd_3316406 1702910323454856779973133 := by
  unfold tailWord_3316406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7559954001452183368546067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80639509348823289264491381 7559954001452183368546067)
  ·
    refine ⟨11339931002178275052819101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7559954001452183368546067 11339931002178275052819101)
    ·
      refine ⟨4252474125816853144807163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11339931002178275052819101 4252474125816853144807163)
      ·
        refine ⟨6378711188725279717210745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4252474125816853144807163 6378711188725279717210745)
        ·
          refine ⟨4784033391543959787908059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6378711188725279717210745 4784033391543959787908059)
          ·
            refine ⟨7176050087315939681862089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4784033391543959787908059 7176050087315939681862089)
            ·
              refine ⟨5382037565486954761396567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7176050087315939681862089 5382037565486954761396567)
              ·
                refine ⟨8073056348230432142094851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5382037565486954761396567 8073056348230432142094851)
                ·
                  refine ⟨12109584522345648213142277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8073056348230432142094851 12109584522345648213142277)
                  ·
                    refine ⟨2270547097939809039964177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12109584522345648213142277 2270547097939809039964177)
                    ·
                      refine ⟨1702910323454856779973133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2270547097939809039964177 1702910323454856779973133)
                      ·
                        rfl

theorem cell23_3316406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_3316406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316406 prefixEnd_3316406 := by exact prefixLift 3316406
  have htrace : WordTrace (prefixWord ++ tailWord_3316406) baseStart_3316406 baseEnd_3316406 := by
    simpa [prefixWord, tailWord_3316406, baseEnd_3316406] using wordTrace_append hprefix tailTrace_3316406
  have hstable : (prefixWord ++ tailWord_3316406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316406).length < 2 ^ (prefixWord ++ tailWord_3316406).sum := by decide
  have hdescent : baseEnd_3316406 < baseStart_3316406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316458 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_3316458 : Nat := 118140960795 + 3316458 * 2 ^ 59
def prefixEnd_3316458 : Nat := 4983230072969 + 3 ^ 40 * 3316458 * 2
def baseEnd_3316458 : Nat := 1702937024448890576522893

theorem tailTrace_3316458 : CollatzResearch.WordTrace tailWord_3316458 prefixEnd_3316458 1702937024448890576522893 := by
  unfold tailWord_3316458
  simp only [CollatzResearch.WordTrace]
  refine ⟨30240290154761636694407507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80640773746031031185086685 30240290154761636694407507)
  ·
    refine ⟨45360435232142455041611261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30240290154761636694407507 45360435232142455041611261)
    ·
      refine ⟨17010163212053420640604223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45360435232142455041611261 17010163212053420640604223)
      ·
        refine ⟨25515244818080130960906335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17010163212053420640604223 25515244818080130960906335)
        ·
          refine ⟨38272867227120196441359503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25515244818080130960906335 38272867227120196441359503)
          ·
            refine ⟨57409300840680294662039255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38272867227120196441359503 57409300840680294662039255)
            ·
              refine ⟨86113951261020441993058883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57409300840680294662039255 86113951261020441993058883)
              ·
                refine ⟨129170926891530662989588325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86113951261020441993058883 129170926891530662989588325)
                ·
                  refine ⟨24219548792161999310547811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129170926891530662989588325 24219548792161999310547811)
                  ·
                    refine ⟨36329323188242998965821717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24219548792161999310547811 36329323188242998965821717)
                    ·
                      refine ⟨1702937024448890576522893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36329323188242998965821717 1702937024448890576522893)
                      ·
                        rfl

theorem cell23_3316458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_3316458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316458 prefixEnd_3316458 := by exact prefixLift 3316458
  have htrace : WordTrace (prefixWord ++ tailWord_3316458) baseStart_3316458 baseEnd_3316458 := by
    simpa [prefixWord, tailWord_3316458, baseEnd_3316458] using wordTrace_append hprefix tailTrace_3316458
  have hstable : (prefixWord ++ tailWord_3316458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316458).length < 2 ^ (prefixWord ++ tailWord_3316458).sum := by decide
  have hdescent : baseEnd_3316458 < baseStart_3316458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316462 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_3316462 : Nat := 118140960795 + 3316462 * 2 ^ 59
def prefixEnd_3316462 : Nat := 4983230072969 + 3 ^ 40 * 3316462 * 2
def baseEnd_3316462 : Nat := 1702939078371508560872875

theorem tailTrace_3316462 : CollatzResearch.WordTrace tailWord_3316462 prefixEnd_3316462 1702939078371508560872875 := by
  unfold tailWord_3316462
  simp only [CollatzResearch.WordTrace]
  refine ⟨15120163313879006932596955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80640871007354703640517093 15120163313879006932596955)
  ·
    refine ⟨22680244970818510398895433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15120163313879006932596955 22680244970818510398895433)
    ·
      refine ⟨17010183728113882799171575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22680244970818510398895433 17010183728113882799171575)
      ·
        refine ⟨25515275592170824198757363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17010183728113882799171575 25515275592170824198757363)
        ·
          refine ⟨38272913388256236298136045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25515275592170824198757363 38272913388256236298136045)
          ·
            refine ⟨14352342520596088611801017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38272913388256236298136045 14352342520596088611801017)
            ·
              refine ⟨10764256890447066458850763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14352342520596088611801017 10764256890447066458850763)
              ·
                refine ⟨16146385335670599688276145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10764256890447066458850763 16146385335670599688276145)
                ·
                  refine ⟨12109789001752949766207109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16146385335670599688276145 12109789001752949766207109)
                  ·
                    refine ⟨2270585437828678081163833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12109789001752949766207109 2270585437828678081163833)
                    ·
                      refine ⟨1702939078371508560872875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2270585437828678081163833 1702939078371508560872875)
                      ·
                        rfl

theorem cell23_3316462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_3316462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316462 prefixEnd_3316462 := by exact prefixLift 3316462
  have htrace : WordTrace (prefixWord ++ tailWord_3316462) baseStart_3316462 baseEnd_3316462 := by
    simpa [prefixWord, tailWord_3316462, baseEnd_3316462] using wordTrace_append hprefix tailTrace_3316462
  have hstable : (prefixWord ++ tailWord_3316462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316462).length < 2 ^ (prefixWord ++ tailWord_3316462).sum := by decide
  have hdescent : baseEnd_3316462 < baseStart_3316462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316482 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_3316482 : Nat := 118140960795 + 3316482 * 2 ^ 59
def prefixEnd_3316482 : Nat := 4983230072969 + 3 ^ 40 * 3316482 * 2
def baseEnd_3316482 : Nat := 1702949347984598482622783

theorem tailTrace_3316482 : CollatzResearch.WordTrace tailWord_3316482 prefixEnd_3316482 1702949347984598482622783 := by
  unfold tailWord_3316482
  simp only [CollatzResearch.WordTrace]
  refine ⟨30240508992739899719125925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80641357313973065917669133 30240508992739899719125925)
  ·
    refine ⟨5670095436138731197336111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30240508992739899719125925 5670095436138731197336111)
    ·
      refine ⟨8505143154208096796004167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5670095436138731197336111 8505143154208096796004167)
      ·
        refine ⟨12757714731312145194006251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8505143154208096796004167 12757714731312145194006251)
        ·
          refine ⟨19136572096968217791009377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12757714731312145194006251 19136572096968217791009377)
          ·
            refine ⟨14352429072726163343257033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19136572096968217791009377 14352429072726163343257033)
            ·
              refine ⟨10764321804544622507442775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14352429072726163343257033 10764321804544622507442775)
              ·
                refine ⟨16146482706816933761164163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10764321804544622507442775 16146482706816933761164163)
                ·
                  refine ⟨24219724060225400641746245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16146482706816933761164163 24219724060225400641746245)
                  ·
                    refine ⟨4541198261292262620327421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24219724060225400641746245 4541198261292262620327421)
                    ·
                      refine ⟨1702949347984598482622783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4541198261292262620327421 1702949347984598482622783)
                      ·
                        rfl

theorem cell23_3316482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_3316482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316482 prefixEnd_3316482 := by exact prefixLift 3316482
  have htrace : WordTrace (prefixWord ++ tailWord_3316482) baseStart_3316482 baseEnd_3316482 := by
    simpa [prefixWord, tailWord_3316482, baseEnd_3316482] using wordTrace_append hprefix tailTrace_3316482
  have hstable : (prefixWord ++ tailWord_3316482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316482).length < 2 ^ (prefixWord ++ tailWord_3316482).sum := by decide
  have hdescent : baseEnd_3316482 < baseStart_3316482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316505 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 3, 5, 2]
def baseStart_3316505 : Nat := 118140960795 + 3316505 * 2 ^ 59
def prefixEnd_3316505 : Nat := 4983230072969 + 3 ^ 40 * 3316505 * 2
def baseEnd_3316505 : Nat := 1702961158039651892635177

theorem tailTrace_3316505 : CollatzResearch.WordTrace tailWord_3316505 prefixEnd_3316505 1702961158039651892635177 := by
  unfold tailWord_3316505
  simp only [CollatzResearch.WordTrace]
  refine ⟨120962874849876273804590969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80641916566584182536393979 120962874849876273804590969)
  ·
    refine ⟨90722156137407205353443227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120962874849876273804590969 90722156137407205353443227)
    ·
      refine ⟨136083234206110808030164841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90722156137407205353443227 136083234206110808030164841)
      ·
        refine ⟨102062425654583106022623631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136083234206110808030164841 102062425654583106022623631)
        ·
          refine ⟨153093638481874659033935447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102062425654583106022623631 153093638481874659033935447)
          ·
            refine ⟨229640457722811988550903171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153093638481874659033935447 229640457722811988550903171)
            ·
              refine ⟨344460686584217982826354757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229640457722811988550903171 344460686584217982826354757)
              ·
                refine ⟨64586378734540871779941517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344460686584217982826354757 64586378734540871779941517)
                ·
                  refine ⟨24219892025452826917478069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64586378734540871779941517 24219892025452826917478069)
                  ·
                    refine ⟨2270614877386202523513569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24219892025452826917478069 2270614877386202523513569)
                    ·
                      refine ⟨1702961158039651892635177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2270614877386202523513569 1702961158039651892635177)
                      ·
                        rfl

theorem cell23_3316505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 5, 2].length) (baseStart_3316505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316505 prefixEnd_3316505 := by exact prefixLift 3316505
  have htrace : WordTrace (prefixWord ++ tailWord_3316505) baseStart_3316505 baseEnd_3316505 := by
    simpa [prefixWord, tailWord_3316505, baseEnd_3316505] using wordTrace_append hprefix tailTrace_3316505
  have hstable : (prefixWord ++ tailWord_3316505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316505).length < 2 ^ (prefixWord ++ tailWord_3316505).sum := by decide
  have hdescent : baseEnd_3316505 < baseStart_3316505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316528 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 5, 6]
def baseStart_3316528 : Nat := 118140960795 + 3316528 * 2 ^ 59
def prefixEnd_3316528 : Nat := 4983230072969 + 3 ^ 40 * 3316528 * 2
def baseEnd_3316528 : Nat := 567657656031568434215857

theorem tailTrace_3316528 : CollatzResearch.WordTrace tailWord_3316528 prefixEnd_3316528 567657656031568434215857 := by
  unfold tailWord_3316528
  simp only [CollatzResearch.WordTrace]
  refine ⟨60481856864396474366339119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80642475819195299155118825 60481856864396474366339119)
  ·
    refine ⟨90722785296594711549508679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60481856864396474366339119 90722785296594711549508679)
    ·
      refine ⟨136084177944892067324263019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90722785296594711549508679 136084177944892067324263019)
      ·
        refine ⟨204126266917338100986394529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136084177944892067324263019 204126266917338100986394529)
        ·
          refine ⟨153094700188003575739795897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204126266917338100986394529 153094700188003575739795897)
          ·
            refine ⟨114821025141002681804846923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153094700188003575739795897 114821025141002681804846923)
            ·
              refine ⟨172231537711504022707270385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114821025141002681804846923 172231537711504022707270385)
              ·
                refine ⟨129173653283628017030452789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172231537711504022707270385 129173653283628017030452789)
                ·
                  refine ⟨12110029995340126596604949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129173653283628017030452789 12110029995340126596604949)
                  ·
                    refine ⟨567657656031568434215857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12110029995340126596604949 567657656031568434215857)
                    ·
                      rfl

theorem cell23_3316528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5, 6].length) (baseStart_3316528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316528 prefixEnd_3316528 := by exact prefixLift 3316528
  have htrace : WordTrace (prefixWord ++ tailWord_3316528) baseStart_3316528 baseEnd_3316528 := by
    simpa [prefixWord, tailWord_3316528, baseEnd_3316528] using wordTrace_append hprefix tailTrace_3316528
  have hstable : (prefixWord ++ tailWord_3316528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316528).length < 2 ^ (prefixWord ++ tailWord_3316528).sum := by decide
  have hdescent : baseEnd_3316528 < baseStart_3316528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316535 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 4]
def baseStart_3316535 : Nat := 118140960795 + 3316535 * 2 ^ 59
def prefixEnd_3316535 : Nat := 4983230072969 + 3 ^ 40 * 3316535 * 2
def baseEnd_3316535 : Nat := 1702976562459286775260039

theorem tailTrace_3316535 : CollatzResearch.WordTrace tailWord_3316535 prefixEnd_3316535 1702976562459286775260039 := by
  unfold tailWord_3316535
  simp only [CollatzResearch.WordTrace]
  refine ⟨120963969039767588928183059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80642646026511725952122039 120963969039767588928183059)
  ·
    refine ⟨181445953559651383392274589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120963969039767588928183059 181445953559651383392274589)
    ·
      refine ⟨68042232584869268772102971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181445953559651383392274589 68042232584869268772102971)
      ·
        refine ⟨102063348877303903158154457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68042232584869268772102971 102063348877303903158154457)
        ·
          refine ⟨76547511657977927368615843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102063348877303903158154457 76547511657977927368615843)
          ·
            refine ⟨114821267486966891052923765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76547511657977927368615843 114821267486966891052923765)
            ·
              refine ⟨10764493826903146036211603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114821267486966891052923765 10764493826903146036211603)
              ·
                refine ⟨16146740740354719054317405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10764493826903146036211603 16146740740354719054317405)
                ·
                  refine ⟨6055027777633019645369027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16146740740354719054317405 6055027777633019645369027)
                  ·
                    refine ⟨9082541666449529468053541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6055027777633019645369027 9082541666449529468053541)
                    ·
                      refine ⟨1702976562459286775260039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9082541666449529468053541 1702976562459286775260039)
                      ·
                        rfl

theorem cell23_3316535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_3316535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316535 prefixEnd_3316535 := by exact prefixLift 3316535
  have htrace : WordTrace (prefixWord ++ tailWord_3316535) baseStart_3316535 baseEnd_3316535 := by
    simpa [prefixWord, tailWord_3316535, baseEnd_3316535] using wordTrace_append hprefix tailTrace_3316535
  have hstable : (prefixWord ++ tailWord_3316535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316535).length < 2 ^ (prefixWord ++ tailWord_3316535).sum := by decide
  have hdescent : baseEnd_3316535 < baseStart_3316535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316565 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_3316565 : Nat := 118140960795 + 3316565 * 2 ^ 59
def prefixEnd_3316565 : Nat := 4983230072969 + 3 ^ 40 * 3316565 * 2
def baseEnd_3316565 : Nat := 1702991966878921657884901

theorem tailTrace_3316565 : CollatzResearch.WordTrace tailWord_3316565 prefixEnd_3316565 1702991966878921657884901 := by
  unfold tailWord_3316565
  simp only [CollatzResearch.WordTrace]
  refine ⟨120965063229658904051775149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80643375486439269367850099 120965063229658904051775149)
  ·
    refine ⟨45361898711122089019415681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120965063229658904051775149 45361898711122089019415681)
    ·
      refine ⟨34021424033341566764561761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45361898711122089019415681 34021424033341566764561761)
      ·
        refine ⟨25516068025006175073421321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34021424033341566764561761 25516068025006175073421321)
        ·
          refine ⟨19137051018754631305065991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25516068025006175073421321 19137051018754631305065991)
          ·
            refine ⟨28705576528131946957598987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19137051018754631305065991 28705576528131946957598987)
            ·
              refine ⟨43058364792197920436398481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28705576528131946957598987 43058364792197920436398481)
              ·
                refine ⟨32293773594148440327298861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43058364792197920436398481 32293773594148440327298861)
                ·
                  refine ⟨12110165097805665122737073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32293773594148440327298861 12110165097805665122737073)
                  ·
                    refine ⟨9082623823354248842052805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12110165097805665122737073 9082623823354248842052805)
                    ·
                      refine ⟨1702991966878921657884901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9082623823354248842052805 1702991966878921657884901)
                      ·
                        rfl

theorem cell23_3316565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_3316565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316565 prefixEnd_3316565 := by exact prefixLift 3316565
  have htrace : WordTrace (prefixWord ++ tailWord_3316565) baseStart_3316565 baseEnd_3316565 := by
    simpa [prefixWord, tailWord_3316565, baseEnd_3316565] using wordTrace_append hprefix tailTrace_3316565
  have hstable : (prefixWord ++ tailWord_3316565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316565).length < 2 ^ (prefixWord ++ tailWord_3316565).sum := by decide
  have hdescent : baseEnd_3316565 < baseStart_3316565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316602 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3]
def baseStart_3316602 : Nat := 118140960795 + 3316602 * 2 ^ 59
def prefixEnd_3316602 : Nat := 4983230072969 + 3 ^ 40 * 3316602 * 2
def baseEnd_3316602 : Nat := 1703010965663138013122231

theorem tailTrace_3316602 : CollatzResearch.WordTrace tailWord_3316602 prefixEnd_3316602 1703010965663138013122231 := by
  unfold tailWord_3316602
  simp only [CollatzResearch.WordTrace]
  refine ⟨30241603182631214842718015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80644275153683239580581373 30241603182631214842718015)
  ·
    refine ⟨45362404773946822264077023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30241603182631214842718015 45362404773946822264077023)
    ·
      refine ⟨68043607160920233396115535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45362404773946822264077023 68043607160920233396115535)
      ·
        refine ⟨102065410741380350094173303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68043607160920233396115535 102065410741380350094173303)
        ·
          refine ⟨153098116112070525141259955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102065410741380350094173303 153098116112070525141259955)
          ·
            refine ⟨229647174168105787711889933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153098116112070525141259955 229647174168105787711889933)
            ·
              refine ⟨86117690313039670391958725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229647174168105787711889933 86117690313039670391958725)
              ·
                refine ⟨16147066933694938198492261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86117690313039670391958725 16147066933694938198492261)
                ·
                  refine ⟨3027575050067800912217299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16147066933694938198492261 3027575050067800912217299)
                  ·
                    refine ⟨4541362575101701368325949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3027575050067800912217299 4541362575101701368325949)
                    ·
                      refine ⟨1703010965663138013122231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4541362575101701368325949 1703010965663138013122231)
                      ·
                        rfl

theorem cell23_3316602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_3316602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316602 prefixEnd_3316602 := by exact prefixLift 3316602
  have htrace : WordTrace (prefixWord ++ tailWord_3316602) baseStart_3316602 baseEnd_3316602 := by
    simpa [prefixWord, tailWord_3316602, baseEnd_3316602] using wordTrace_append hprefix tailTrace_3316602
  have hstable : (prefixWord ++ tailWord_3316602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316602).length < 2 ^ (prefixWord ++ tailWord_3316602).sum := by decide
  have hdescent : baseEnd_3316602 < baseStart_3316602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316619 : List Nat := [1, 1, 1, 1, 4, 2, 5, 2, 2, 1, 3]
def baseStart_3316619 : Nat := 118140960795 + 3316619 * 2 ^ 59
def prefixEnd_3316619 : Nat := 4983230072969 + 3 ^ 40 * 3316619 * 2
def baseEnd_3316619 : Nat := 1703019694834264446609653

theorem tailTrace_3316619 : CollatzResearch.WordTrace tailWord_3316619 prefixEnd_3316619 1703019694834264446609653 := by
  unfold tailWord_3316619
  simp only [CollatzResearch.WordTrace]
  refine ⟨120967032771463271274240911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80644688514308847516160607 120967032771463271274240911)
  ·
    refine ⟨181450549157194906911361367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120967032771463271274240911 181450549157194906911361367)
    ·
      refine ⟨272175823735792360367042051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181450549157194906911361367 272175823735792360367042051)
      ·
        refine ⟨408263735603688540550563077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272175823735792360367042051 408263735603688540550563077)
        ·
          refine ⟨76549450425691601353230577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 408263735603688540550563077 76549450425691601353230577)
          ·
            refine ⟨57412087819268701014922933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76549450425691601353230577 57412087819268701014922933)
            ·
              refine ⟨5382383233056440720149025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57412087819268701014922933 5382383233056440720149025)
              ·
                refine ⟨4036787424792330540111769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5382383233056440720149025 4036787424792330540111769)
                ·
                  refine ⟨3027590568594247905083827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4036787424792330540111769 3027590568594247905083827)
                  ·
                    refine ⟨4541385852891371857625741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3027590568594247905083827 4541385852891371857625741)
                    ·
                      refine ⟨1703019694834264446609653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4541385852891371857625741 1703019694834264446609653)
                      ·
                        rfl

theorem cell23_3316619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 1, 3].length) (baseStart_3316619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316619 prefixEnd_3316619 := by exact prefixLift 3316619
  have htrace : WordTrace (prefixWord ++ tailWord_3316619) baseStart_3316619 baseEnd_3316619 := by
    simpa [prefixWord, tailWord_3316619, baseEnd_3316619] using wordTrace_append hprefix tailTrace_3316619
  have hstable : (prefixWord ++ tailWord_3316619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316619).length < 2 ^ (prefixWord ++ tailWord_3316619).sum := by decide
  have hdescent : baseEnd_3316619 < baseStart_3316619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316630 : List Nat := [5, 3, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3316630 : Nat := 118140960795 + 3316630 * 2 ^ 59
def prefixEnd_3316630 : Nat := 4983230072969 + 3 ^ 40 * 3316630 * 2
def baseEnd_3316630 : Nat := 567675114373821301190701

theorem tailTrace_3316630 : CollatzResearch.WordTrace tailWord_3316630 prefixEnd_3316630 567675114373821301190701 := by
  unfold tailWord_3316630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7560464623401463759555709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80644955982948946768594229 7560464623401463759555709)
  ·
    refine ⟨2835174233775548909833391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7560464623401463759555709 2835174233775548909833391)
    ·
      refine ⟨4252761350663323364750087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2835174233775548909833391 4252761350663323364750087)
      ·
        refine ⟨6379142025994985047125131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4252761350663323364750087 6379142025994985047125131)
        ·
          refine ⟨9568713038992477570687697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6379142025994985047125131 9568713038992477570687697)
          ·
            refine ⟨7176534779244358178015773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9568713038992477570687697 7176534779244358178015773)
            ·
              refine ⟨2691200542216634316755915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7176534779244358178015773 2691200542216634316755915)
              ·
                refine ⟨4036800813324951475133873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691200542216634316755915 4036800813324951475133873)
                ·
                  refine ⟨3027600609993713606350405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4036800813324951475133873 3027600609993713606350405)
                  ·
                    refine ⟨567675114373821301190701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3027600609993713606350405 567675114373821301190701)
                    ·
                      rfl

theorem cell23_3316630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3316630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316630 prefixEnd_3316630 := by exact prefixLift 3316630
  have htrace : WordTrace (prefixWord ++ tailWord_3316630) baseStart_3316630 baseEnd_3316630 := by
    simpa [prefixWord, tailWord_3316630, baseEnd_3316630] using wordTrace_append hprefix tailTrace_3316630
  have hstable : (prefixWord ++ tailWord_3316630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316630).length < 2 ^ (prefixWord ++ tailWord_3316630).sum := by decide
  have hdescent : baseEnd_3316630 < baseStart_3316630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316636 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3316636 : Nat := 118140960795 + 3316636 * 2 ^ 59
def prefixEnd_3316636 : Nat := 4983230072969 + 3 ^ 40 * 3316636 * 2
def baseEnd_3316636 : Nat := 1703028424005390880097075

theorem tailTrace_3316636 : CollatzResearch.WordTrace tailWord_3316636 prefixEnd_3316636 1703028424005390880097075 := by
  unfold tailWord_3316636
  simp only [CollatzResearch.WordTrace]
  refine ⟨60483826406200841588804881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80645101874934455451739841 60483826406200841588804881)
  ·
    refine ⟨45362869804650631191603661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60483826406200841588804881 45362869804650631191603661)
    ·
      refine ⟨17011076176743986696851373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45362869804650631191603661 17011076176743986696851373)
      ·
        refine ⟨6379153566278995011319265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17011076176743986696851373 6379153566278995011319265)
        ·
          refine ⟨4784365174709246258489449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6379153566278995011319265 4784365174709246258489449)
          ·
            refine ⟨3588273881031934693867087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4784365174709246258489449 3588273881031934693867087)
            ·
              refine ⟨5382410821547902040800631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3588273881031934693867087 5382410821547902040800631)
              ·
                refine ⟨8073616232321853061200947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5382410821547902040800631 8073616232321853061200947)
                ·
                  refine ⟨12110424348482779591801421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8073616232321853061200947 12110424348482779591801421)
                  ·
                    refine ⟨4541409130681042346925533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12110424348482779591801421 4541409130681042346925533)
                    ·
                      refine ⟨1703028424005390880097075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4541409130681042346925533 1703028424005390880097075)
                      ·
                        rfl

theorem cell23_3316636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3316636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316636 prefixEnd_3316636 := by exact prefixLift 3316636
  have htrace : WordTrace (prefixWord ++ tailWord_3316636) baseStart_3316636 baseEnd_3316636 := by
    simpa [prefixWord, tailWord_3316636, baseEnd_3316636] using wordTrace_append hprefix tailTrace_3316636
  have hstable : (prefixWord ++ tailWord_3316636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316636).length < 2 ^ (prefixWord ++ tailWord_3316636).sum := by decide
  have hdescent : baseEnd_3316636 < baseStart_3316636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316655 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 4]
def baseStart_3316655 : Nat := 118140960795 + 3316655 * 2 ^ 59
def prefixEnd_3316655 : Nat := 4983230072969 + 3 ^ 40 * 3316655 * 2
def baseEnd_3316655 : Nat := 1703038180137826305759487

theorem tailTrace_3316655 : CollatzResearch.WordTrace tailWord_3316655 prefixEnd_3316655 1703038180137826305759487 := by
  unfold tailWord_3316655
  simp only [CollatzResearch.WordTrace]
  refine ⟨120968345799332849422551419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80645563866221899615034279 120968345799332849422551419)
  ·
    refine ⟨181452518698999274133827129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120968345799332849422551419 181452518698999274133827129)
    ·
      refine ⟨136089389024249455600370347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181452518698999274133827129 136089389024249455600370347)
      ·
        refine ⟨204134083536374183400555521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136089389024249455600370347 204134083536374183400555521)
        ·
          refine ⟨153100562652280637550416641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204134083536374183400555521 153100562652280637550416641)
          ·
            refine ⟨114825421989210478162812481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153100562652280637550416641 114825421989210478162812481)
            ·
              refine ⟨86119066491907858622109361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114825421989210478162812481 86119066491907858622109361)
              ·
                refine ⟨64589299868930893966582021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86119066491907858622109361 64589299868930893966582021)
                ·
                  refine ⟨12110493725424542618734129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64589299868930893966582021 12110493725424542618734129)
                  ·
                    refine ⟨9082870294068406964050597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12110493725424542618734129 9082870294068406964050597)
                    ·
                      refine ⟨1703038180137826305759487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9082870294068406964050597 1703038180137826305759487)
                      ·
                        rfl

theorem cell23_3316655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_3316655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316655 prefixEnd_3316655 := by exact prefixLift 3316655
  have htrace : WordTrace (prefixWord ++ tailWord_3316655) baseStart_3316655 baseEnd_3316655 := by
    simpa [prefixWord, tailWord_3316655, baseEnd_3316655] using wordTrace_append hprefix tailTrace_3316655
  have hstable : (prefixWord ++ tailWord_3316655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316655).length < 2 ^ (prefixWord ++ tailWord_3316655).sum := by decide
  have hdescent : baseEnd_3316655 < baseStart_3316655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316693 : List Nat := [1, 3, 2, 3, 3, 1, 1, 3, 2, 2, 2]
def baseStart_3316693 : Nat := 118140960795 + 3316693 * 2 ^ 59
def prefixEnd_3316693 : Nat := 4983230072969 + 3 ^ 40 * 3316693 * 2
def baseEnd_3316693 : Nat := 1703057692402697157084313

theorem tailTrace_3316693 : CollatzResearch.WordTrace tailWord_3316693 prefixEnd_3316693 1703057692402697157084313 := by
  unfold tailWord_3316693
  simp only [CollatzResearch.WordTrace]
  refine ⟨120969731773195181912434733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80646487848796787941623155 120969731773195181912434733)
  ·
    refine ⟨45363649414948193217163025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120969731773195181912434733 45363649414948193217163025)
    ·
      refine ⟨34022737061211144912872269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45363649414948193217163025 34022737061211144912872269)
      ·
        refine ⟨12758526397954179342327101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34022737061211144912872269 12758526397954179342327101)
        ·
          refine ⟨4784447399232817253372663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12758526397954179342327101 4784447399232817253372663)
          ·
            refine ⟨7176671098849225880058995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4784447399232817253372663 7176671098849225880058995)
            ·
              refine ⟨10765006648273838820088493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7176671098849225880058995 10765006648273838820088493)
              ·
                refine ⟨4036877493102689557533185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10765006648273838820088493 4036877493102689557533185)
                ·
                  refine ⟨3027658119827017168149889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4036877493102689557533185 3027658119827017168149889)
                  ·
                    refine ⟨2270743589870262876112417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3027658119827017168149889 2270743589870262876112417)
                    ·
                      refine ⟨1703057692402697157084313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2270743589870262876112417 1703057692402697157084313)
                      ·
                        rfl

theorem cell23_3316693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_3316693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316693 prefixEnd_3316693 := by exact prefixLift 3316693
  have htrace : WordTrace (prefixWord ++ tailWord_3316693) baseStart_3316693 baseEnd_3316693 := by
    simpa [prefixWord, tailWord_3316693, baseEnd_3316693] using wordTrace_append hprefix tailTrace_3316693
  have hstable : (prefixWord ++ tailWord_3316693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316693).length < 2 ^ (prefixWord ++ tailWord_3316693).sum := by decide
  have hdescent : baseEnd_3316693 < baseStart_3316693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316695 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 1, 7]
def baseStart_3316695 : Nat := 118140960795 + 3316695 * 2 ^ 59
def prefixEnd_3316695 : Nat := 4983230072969 + 3 ^ 40 * 3316695 * 2
def baseEnd_3316695 : Nat := 567686239788002049753101

theorem tailTrace_3316695 : CollatzResearch.WordTrace tailWord_3316695 prefixEnd_3316695 567686239788002049753101 := by
  unfold tailWord_3316695
  simp only [CollatzResearch.WordTrace]
  refine ⟨120969804719187936254007539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80646536479458624169338359 120969804719187936254007539)
  ·
    refine ⟨181454707078781904381011309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120969804719187936254007539 181454707078781904381011309)
    ·
      refine ⟨68045515154543214142879241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181454707078781904381011309 68045515154543214142879241)
      ·
        refine ⟨51034136365907410607159431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68045515154543214142879241 51034136365907410607159431)
        ·
          refine ⟨76551204548861115910739147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51034136365907410607159431 76551204548861115910739147)
          ·
            refine ⟨114826806823291673866108721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76551204548861115910739147 114826806823291673866108721)
            ·
              refine ⟨86120105117468755399581541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114826806823291673866108721 86120105117468755399581541)
              ·
                refine ⟨16147519709525391637421539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86120105117468755399581541 16147519709525391637421539)
                ·
                  refine ⟨24221279564288087456132309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16147519709525391637421539 24221279564288087456132309)
                  ·
                    refine ⟨567686239788002049753101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24221279564288087456132309 567686239788002049753101)
                    ·
                      rfl

theorem cell23_3316695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_3316695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316695 prefixEnd_3316695 := by exact prefixLift 3316695
  have htrace : WordTrace (prefixWord ++ tailWord_3316695) baseStart_3316695 baseEnd_3316695 := by
    simpa [prefixWord, tailWord_3316695, baseEnd_3316695] using wordTrace_append hprefix tailTrace_3316695
  have hstable : (prefixWord ++ tailWord_3316695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316695).length < 2 ^ (prefixWord ++ tailWord_3316695).sum := by decide
  have hdescent : baseEnd_3316695 < baseStart_3316695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316705 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_3316705 : Nat := 118140960795 + 3316705 * 2 ^ 59
def prefixEnd_3316705 : Nat := 4983230072969 + 3 ^ 40 * 3316705 * 2
def baseEnd_3316705 : Nat := 1703063854170551110134257

theorem tailTrace_3316705 : CollatzResearch.WordTrace tailWord_3316705 prefixEnd_3316705 1703063854170551110134257 := by
  unfold tailWord_3316705
  simp only [CollatzResearch.WordTrace]
  refine ⟨120970169449151707961871569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80646779632767805307914379 120970169449151707961871569)
  ·
    refine ⟨90727627086863780971403677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120970169449151707961871569 90727627086863780971403677)
    ·
      refine ⟨34022860157573917864276379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90727627086863780971403677 34022860157573917864276379)
      ·
        refine ⟨51034290236360876796414569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34022860157573917864276379 51034290236360876796414569)
        ·
          refine ⟨38275717677270657597310927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51034290236360876796414569 38275717677270657597310927)
          ·
            refine ⟨57413576515905986395966391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38275717677270657597310927 57413576515905986395966391)
            ·
              refine ⟨86120364773858979593949587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57413576515905986395966391 86120364773858979593949587)
              ·
                refine ⟨129180547160788469390924381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86120364773858979593949587 129180547160788469390924381)
                ·
                  refine ⟨48442705185295676021596643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129180547160788469390924381 48442705185295676021596643)
                  ·
                    refine ⟨72664057777943514032394965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48442705185295676021596643 72664057777943514032394965)
                    ·
                      refine ⟨1703063854170551110134257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72664057777943514032394965 1703063854170551110134257)
                      ·
                        rfl

theorem cell23_3316705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_3316705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316705 prefixEnd_3316705 := by exact prefixLift 3316705
  have htrace : WordTrace (prefixWord ++ tailWord_3316705) baseStart_3316705 baseEnd_3316705 := by
    simpa [prefixWord, tailWord_3316705, baseEnd_3316705] using wordTrace_append hprefix tailTrace_3316705
  have hstable : (prefixWord ++ tailWord_3316705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316705).length < 2 ^ (prefixWord ++ tailWord_3316705).sum := by decide
  have hdescent : baseEnd_3316705 < baseStart_3316705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316712 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 2, 5]
def baseStart_3316712 : Nat := 118140960795 + 3316712 * 2 ^ 59
def prefixEnd_3316712 : Nat := 4983230072969 + 3 ^ 40 * 3316712 * 2
def baseEnd_3316712 : Nat := 567689149511710860915575

theorem tailTrace_3316712 : CollatzResearch.WordTrace tailWord_3316712 prefixEnd_3316712 567689149511710860915575 := by
  unfold tailWord_3316712
  simp only [CollatzResearch.WordTrace]
  refine ⟨60485212380063174078688195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80646949840084232104917593 60485212380063174078688195)
  ·
    refine ⟨90727818570094761118032293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60485212380063174078688195 90727818570094761118032293)
    ·
      refine ⟨17011465981892767709631055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90727818570094761118032293 17011465981892767709631055)
      ·
        refine ⟨25517198972839151564446583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17011465981892767709631055 25517198972839151564446583)
        ·
          refine ⟨38275798459258727346669875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25517198972839151564446583 38275798459258727346669875)
          ·
            refine ⟨57413697688888091020004813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38275798459258727346669875 57413697688888091020004813)
            ·
              refine ⟨21530136633333034132501805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57413697688888091020004813 21530136633333034132501805)
              ·
                refine ⟨8073801237499887799688177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21530136633333034132501805 8073801237499887799688177)
                ·
                  refine ⟨6055350928124915849766133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8073801237499887799688177 6055350928124915849766133)
                  ·
                    refine ⟨567689149511710860915575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6055350928124915849766133 567689149511710860915575)
                    ·
                      rfl

theorem cell23_3316712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_3316712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316712 prefixEnd_3316712 := by exact prefixLift 3316712
  have htrace : WordTrace (prefixWord ++ tailWord_3316712) baseStart_3316712 baseEnd_3316712 := by
    simpa [prefixWord, tailWord_3316712, baseEnd_3316712] using wordTrace_append hprefix tailTrace_3316712
  have hstable : (prefixWord ++ tailWord_3316712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316712).length < 2 ^ (prefixWord ++ tailWord_3316712).sum := by decide
  have hdescent : baseEnd_3316712 < baseStart_3316712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316755 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 10]
def baseStart_3316755 : Nat := 118140960795 + 3316755 * 2 ^ 59
def prefixEnd_3316755 : Nat := 4983230072969 + 3 ^ 40 * 3316755 * 2
def baseEnd_3316755 : Nat := 189232169800363990501003

theorem tailTrace_3316755 : CollatzResearch.WordTrace tailWord_3316755 prefixEnd_3316755 189232169800363990501003 := by
  unfold tailWord_3316755
  simp only [CollatzResearch.WordTrace]
  refine ⟨120971993098970566501191719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80647995399313711000794479 120971993098970566501191719)
  ·
    refine ⟨181457989648455849751787579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120971993098970566501191719 181457989648455849751787579)
    ·
      refine ⟨272186984472683774627681369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181457989648455849751787579 272186984472683774627681369)
      ·
        refine ⟨204140238354512830970761027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272186984472683774627681369 204140238354512830970761027)
        ·
          refine ⟨306210357531769246456141541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204140238354512830970761027 306210357531769246456141541)
          ·
            refine ⟨57414442037206733710526539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 306210357531769246456141541 57414442037206733710526539)
            ·
              refine ⟨86121663055810100565789809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57414442037206733710526539 86121663055810100565789809)
              ·
                refine ⟨64591247291857575424342357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86121663055810100565789809 64591247291857575424342357)
                ·
                  refine ⟨189232169800363990501003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 64591247291857575424342357 189232169800363990501003)
                  ·
                    rfl

theorem cell23_3316755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 10].length) (baseStart_3316755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316755 prefixEnd_3316755 := by exact prefixLift 3316755
  have htrace : WordTrace (prefixWord ++ tailWord_3316755) baseStart_3316755 baseEnd_3316755 := by
    simpa [prefixWord, tailWord_3316755, baseEnd_3316755] using wordTrace_append hprefix tailTrace_3316755
  have hstable : (prefixWord ++ tailWord_3316755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316755).length < 2 ^ (prefixWord ++ tailWord_3316755).sum := by decide
  have hdescent : baseEnd_3316755 < baseStart_3316755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316759 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 5, 4]
def baseStart_3316759 : Nat := 118140960795 + 3316759 * 2 ^ 59
def prefixEnd_3316759 : Nat := 4983230072969 + 3 ^ 40 * 3316759 * 2
def baseEnd_3316759 : Nat := 567697194041964632953003

theorem tailTrace_3316759 : CollatzResearch.WordTrace tailWord_3316759 prefixEnd_3316759 567697194041964632953003 := by
  unfold tailWord_3316759
  simp only [CollatzResearch.WordTrace]
  refine ⟨120972138990956075184337331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80648092660637383456224887 120972138990956075184337331)
  ·
    refine ⟨181458208486434112776505997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120972138990956075184337331 181458208486434112776505997)
    ·
      refine ⟨68046828182412792291189749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181458208486434112776505997 68046828182412792291189749)
      ·
        refine ⟨6379390142101199277299039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68046828182412792291189749 6379390142101199277299039)
        ·
          refine ⟨9569085213151798915948559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6379390142101199277299039 9569085213151798915948559)
          ·
            refine ⟨14353627819727698373922839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9569085213151798915948559 14353627819727698373922839)
            ·
              refine ⟨21530441729591547560884259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14353627819727698373922839 21530441729591547560884259)
              ·
                refine ⟨32295662594387321341326389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21530441729591547560884259 32295662594387321341326389)
                ·
                  refine ⟨3027718368223811375749349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32295662594387321341326389 3027718368223811375749349)
                  ·
                    refine ⟨567697194041964632953003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3027718368223811375749349 567697194041964632953003)
                    ·
                      rfl

theorem cell23_3316759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_3316759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316759 prefixEnd_3316759 := by exact prefixLift 3316759
  have htrace : WordTrace (prefixWord ++ tailWord_3316759) baseStart_3316759 baseEnd_3316759 := by
    simpa [prefixWord, tailWord_3316759, baseEnd_3316759] using wordTrace_append hprefix tailTrace_3316759
  have hstable : (prefixWord ++ tailWord_3316759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316759).length < 2 ^ (prefixWord ++ tailWord_3316759).sum := by decide
  have hdescent : baseEnd_3316759 < baseStart_3316759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316769 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_3316769 : Nat := 118140960795 + 3316769 * 2 ^ 59
def prefixEnd_3316769 : Nat := 4983230072969 + 3 ^ 40 * 3316769 * 2
def baseEnd_3316769 : Nat := 1703096716932438859733963

theorem tailTrace_3316769 : CollatzResearch.WordTrace tailWord_3316769 prefixEnd_3316769 1703096716932438859733963 := by
  unfold tailWord_3316769
  simp only [CollatzResearch.WordTrace]
  refine ⟨120972503720919846892201361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80648335813946564594800907 120972503720919846892201361)
  ·
    refine ⟨90729377790689885169151021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120972503720919846892201361 90729377790689885169151021)
    ·
      refine ⟨34023516671508706938431633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90729377790689885169151021 34023516671508706938431633)
      ·
        refine ⟨25517637503631530203823725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34023516671508706938431633 25517637503631530203823725)
        ·
          refine ⟨9569114063861823826433897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25517637503631530203823725 9569114063861823826433897)
          ·
            refine ⟨7176835547896367869825423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9569114063861823826433897 7176835547896367869825423)
            ·
              refine ⟨10765253321844551804738135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7176835547896367869825423 10765253321844551804738135)
              ·
                refine ⟨16147879982766827707107203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10765253321844551804738135 16147879982766827707107203)
                ·
                  refine ⟨24221819974150241560660805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16147879982766827707107203 24221819974150241560660805)
                  ·
                    refine ⟨4541591245153170292623901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24221819974150241560660805 4541591245153170292623901)
                    ·
                      refine ⟨1703096716932438859733963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4541591245153170292623901 1703096716932438859733963)
                      ·
                        rfl

theorem cell23_3316769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_3316769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316769 prefixEnd_3316769 := by exact prefixLift 3316769
  have htrace : WordTrace (prefixWord ++ tailWord_3316769) baseStart_3316769 baseEnd_3316769 := by
    simpa [prefixWord, tailWord_3316769, baseEnd_3316769] using wordTrace_append hprefix tailTrace_3316769
  have hstable : (prefixWord ++ tailWord_3316769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316769).length < 2 ^ (prefixWord ++ tailWord_3316769).sum := by decide
  have hdescent : baseEnd_3316769 < baseStart_3316769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316792 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_3316792 : Nat := 118140960795 + 3316792 * 2 ^ 59
def prefixEnd_3316792 : Nat := 4983230072969 + 3 ^ 40 * 3316792 * 2
def baseEnd_3316792 : Nat := 1703108526987492269746357

theorem tailTrace_3316792 : CollatzResearch.WordTrace tailWord_3316792 prefixEnd_3316792 1703108526987492269746357 := by
  unfold tailWord_3316792
  simp only [CollatzResearch.WordTrace]
  refine ⟨60486671299918260910144315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80648895066557681213525753 60486671299918260910144315)
  ·
    refine ⟨90730006949877391365216473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60486671299918260910144315 90730006949877391365216473)
    ·
      refine ⟨68047505212408043523912355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90730006949877391365216473 68047505212408043523912355)
      ·
        refine ⟨102071257818612065285868533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68047505212408043523912355 102071257818612065285868533)
        ·
          refine ⟨9569180420494881120550175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102071257818612065285868533 9569180420494881120550175)
          ·
            refine ⟨14353770630742321680825263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9569180420494881120550175 14353770630742321680825263)
            ·
              refine ⟨21530655946113482521237895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14353770630742321680825263 21530655946113482521237895)
              ·
                refine ⟨32295983919170223781856843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21530655946113482521237895 32295983919170223781856843)
                ·
                  refine ⟨48443975878755335672785265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32295983919170223781856843 48443975878755335672785265)
                  ·
                    refine ⟨36332981909066501754588949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48443975878755335672785265 36332981909066501754588949)
                    ·
                      refine ⟨1703108526987492269746357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36332981909066501754588949 1703108526987492269746357)
                      ·
                        rfl

theorem cell23_3316792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_3316792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316792 prefixEnd_3316792 := by exact prefixLift 3316792
  have htrace : WordTrace (prefixWord ++ tailWord_3316792) baseStart_3316792 baseEnd_3316792 := by
    simpa [prefixWord, tailWord_3316792, baseEnd_3316792] using wordTrace_append hprefix tailTrace_3316792
  have hstable : (prefixWord ++ tailWord_3316792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316792).length < 2 ^ (prefixWord ++ tailWord_3316792).sum := by decide
  have hdescent : baseEnd_3316792 < baseStart_3316792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316809 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 6, 3, 2]
def baseStart_3316809 : Nat := 118140960795 + 3316809 * 2 ^ 59
def prefixEnd_3316809 : Nat := 4983230072969 + 3 ^ 40 * 3316809 * 2
def baseEnd_3316809 : Nat := 1703117256158618703233779

theorem tailTrace_3316809 : CollatzResearch.WordTrace tailWord_3316809 prefixEnd_3316809 1703117256158618703233779 := by
  unfold tailWord_3316809
  simp only [CollatzResearch.WordTrace]
  refine ⟨120973962640774933723657481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80649308427183289149104987 120973962640774933723657481)
  ·
    refine ⟨90730471980581200292743111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120973962640774933723657481 90730471980581200292743111)
    ·
      refine ⟨136095707970871800439114667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90730471980581200292743111 136095707970871800439114667)
      ·
        refine ⟨204143561956307700658672001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136095707970871800439114667 204143561956307700658672001)
        ·
          refine ⟨153107671467230775494004001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204143561956307700658672001 153107671467230775494004001)
          ·
            refine ⟨114830753600423081620503001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153107671467230775494004001 114830753600423081620503001)
            ·
              refine ⟨86123065200317311215377251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114830753600423081620503001 86123065200317311215377251)
              ·
                refine ⟨129184597800475966823065877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86123065200317311215377251 129184597800475966823065877)
                ·
                  refine ⟨6055528021897310944831213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129184597800475966823065877 6055528021897310944831213)
                  ·
                    refine ⟨2270823008211491604311705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6055528021897310944831213 2270823008211491604311705)
                    ·
                      refine ⟨1703117256158618703233779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2270823008211491604311705 1703117256158618703233779)
                      ·
                        rfl

theorem cell23_3316809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 3, 2].length) (baseStart_3316809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316809 prefixEnd_3316809 := by exact prefixLift 3316809
  have htrace : WordTrace (prefixWord ++ tailWord_3316809) baseStart_3316809 baseEnd_3316809 := by
    simpa [prefixWord, tailWord_3316809, baseEnd_3316809] using wordTrace_append hprefix tailTrace_3316809
  have hstable : (prefixWord ++ tailWord_3316809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316809).length < 2 ^ (prefixWord ++ tailWord_3316809).sum := by decide
  have hdescent : baseEnd_3316809 < baseStart_3316809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316832 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 3, 6]
def baseStart_3316832 : Nat := 118140960795 + 3316832 * 2 ^ 59
def prefixEnd_3316832 : Nat := 4983230072969 + 3 ^ 40 * 3316832 * 2
def baseEnd_3316832 : Nat := 567709688737890704415391

theorem tailTrace_3316832 : CollatzResearch.WordTrace tailWord_3316832 prefixEnd_3316832 567709688737890704415391 := by
  unfold tailWord_3316832
  simp only [CollatzResearch.WordTrace]
  refine ⟨60487400759845804325872375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80649867679794405767829833 60487400759845804325872375)
  ·
    refine ⟨90731101139768706488808563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60487400759845804325872375 90731101139768706488808563)
    ·
      refine ⟨136096651709653059733212845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90731101139768706488808563 136096651709653059733212845)
      ·
        refine ⟨51036244391119897399954817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136096651709653059733212845 51036244391119897399954817)
        ·
          refine ⟨38277183293339923049966113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51036244391119897399954817 38277183293339923049966113)
          ·
            refine ⟨28707887470004942287474585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38277183293339923049966113 28707887470004942287474585)
            ·
              refine ⟨21530915602503706715605939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28707887470004942287474585 21530915602503706715605939)
              ·
                refine ⟨32296373403755560073408909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21530915602503706715605939 32296373403755560073408909)
                ·
                  refine ⟨12111140026408335027528341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32296373403755560073408909 12111140026408335027528341)
                  ·
                    refine ⟨567709688737890704415391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12111140026408335027528341 567709688737890704415391)
                    ·
                      rfl

theorem cell23_3316832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3, 6].length) (baseStart_3316832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316832 prefixEnd_3316832 := by exact prefixLift 3316832
  have htrace : WordTrace (prefixWord ++ tailWord_3316832) baseStart_3316832 baseEnd_3316832 := by
    simpa [prefixWord, tailWord_3316832, baseEnd_3316832] using wordTrace_append hprefix tailTrace_3316832
  have hstable : (prefixWord ++ tailWord_3316832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316832).length < 2 ^ (prefixWord ++ tailWord_3316832).sum := by decide
  have hdescent : baseEnd_3316832 < baseStart_3316832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316833 : List Nat := [1, 2, 3, 1, 1, 2, 5, 3, 1, 1, 3]
def baseStart_3316833 : Nat := 118140960795 + 3316833 * 2 ^ 59
def prefixEnd_3316833 : Nat := 4983230072969 + 3 ^ 40 * 3316833 * 2
def baseEnd_3316833 : Nat := 1703129579694326609333669

theorem tailTrace_3316833 : CollatzResearch.WordTrace tailWord_3316833 prefixEnd_3316833 1703129579694326609333669 := by
  unfold tailWord_3316833
  simp only [CollatzResearch.WordTrace]
  refine ⟨120974837992687985822531153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80649891995125323881687435 120974837992687985822531153)
  ·
    refine ⟨90731128494515989366898365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120974837992687985822531153 90731128494515989366898365)
    ·
      refine ⟨34024173185443496012586887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90731128494515989366898365 34024173185443496012586887)
      ·
        refine ⟨51036259778165244018880331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34024173185443496012586887 51036259778165244018880331)
        ·
          refine ⟨76554389667247866028320497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51036259778165244018880331 76554389667247866028320497)
          ·
            refine ⟨57415792250435899521240373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76554389667247866028320497 57415792250435899521240373)
            ·
              refine ⟨5382730523478365580116285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57415792250435899521240373 5382730523478365580116285)
              ·
                refine ⟨2018523946304387092543607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5382730523478365580116285 2018523946304387092543607)
                ·
                  refine ⟨3027785919456580638815411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2018523946304387092543607 3027785919456580638815411)
                  ·
                    refine ⟨4541678879184870958223117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3027785919456580638815411 4541678879184870958223117)
                    ·
                      refine ⟨1703129579694326609333669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4541678879184870958223117 1703129579694326609333669)
                      ·
                        rfl

theorem cell23_3316833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_3316833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316833 prefixEnd_3316833 := by exact prefixLift 3316833
  have htrace : WordTrace (prefixWord ++ tailWord_3316833) baseStart_3316833 baseEnd_3316833 := by
    simpa [prefixWord, tailWord_3316833, baseEnd_3316833] using wordTrace_append hprefix tailTrace_3316833
  have hstable : (prefixWord ++ tailWord_3316833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316833).length < 2 ^ (prefixWord ++ tailWord_3316833).sum := by decide
  have hdescent : baseEnd_3316833 < baseStart_3316833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316850 : List Nat := [3, 2, 1, 2, 2, 1, 5, 2, 1, 1, 3]
def baseStart_3316850 : Nat := 118140960795 + 3316850 * 2 ^ 59
def prefixEnd_3316850 : Nat := 4983230072969 + 3 ^ 40 * 3316850 * 2
def baseEnd_3316850 : Nat := 1703138308865453042821091

theorem tailTrace_3316850 : CollatzResearch.WordTrace tailWord_3316850 prefixEnd_3316850 1703138308865453042821091 := by
  unfold tailWord_3316850
  simp only [CollatzResearch.WordTrace]
  refine ⟨30243864508406599431475001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80650305355750931817266669 30243864508406599431475001)
  ·
    refine ⟨22682898381304949573606251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30243864508406599431475001 22682898381304949573606251)
    ·
      refine ⟨34024347571957424360409377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22682898381304949573606251 34024347571957424360409377)
      ·
        refine ⟨25518260678968068270307033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34024347571957424360409377 25518260678968068270307033)
        ·
          refine ⟨19138695509226051202730275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25518260678968068270307033 19138695509226051202730275)
          ·
            refine ⟨28708043263839076804095413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19138695509226051202730275 28708043263839076804095413)
            ·
              refine ⟨2691379055984913450383945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28708043263839076804095413 2691379055984913450383945)
              ·
                refine ⟨2018534291988685087787959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2691379055984913450383945 2018534291988685087787959)
                ·
                  refine ⟨3027801437983027631681939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2018534291988685087787959 3027801437983027631681939)
                  ·
                    refine ⟨4541702156974541447522909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3027801437983027631681939 4541702156974541447522909)
                    ·
                      refine ⟨1703138308865453042821091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4541702156974541447522909 1703138308865453042821091)
                      ·
                        rfl

theorem cell23_3316850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_3316850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316850 prefixEnd_3316850 := by exact prefixLift 3316850
  have htrace : WordTrace (prefixWord ++ tailWord_3316850) baseStart_3316850 baseEnd_3316850 := by
    simpa [prefixWord, tailWord_3316850, baseEnd_3316850] using wordTrace_append hprefix tailTrace_3316850
  have hstable : (prefixWord ++ tailWord_3316850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316850).length < 2 ^ (prefixWord ++ tailWord_3316850).sum := by decide
  have hdescent : baseEnd_3316850 < baseStart_3316850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316893 : List Nat := [1, 4, 2, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_3316893 : Nat := 118140960795 + 3316893 * 2 ^ 59
def prefixEnd_3316893 : Nat := 4983230072969 + 3 ^ 40 * 3316893 * 2
def baseEnd_3316893 : Nat := 1703160388533596374583393

theorem tailTrace_3316893 : CollatzResearch.WordTrace tailWord_3316893 prefixEnd_3316893 1703160388533596374583393 := by
  unfold tailWord_3316893
  simp only [CollatzResearch.WordTrace]
  refine ⟨120977026372470616069715333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80651350914980410713143555 120977026372470616069715333)
  ·
    refine ⟨22683192444838240513071625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120977026372470616069715333 22683192444838240513071625)
    ·
      refine ⟨17012394333628680384803719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22683192444838240513071625 17012394333628680384803719)
      ·
        refine ⟨25518591500443020577205579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17012394333628680384803719 25518591500443020577205579)
        ·
          refine ⟨38277887250664530865808369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25518591500443020577205579 38277887250664530865808369)
          ·
            refine ⟨28708415437998398149356277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38277887250664530865808369 28708415437998398149356277)
            ·
              refine ⟨2691413947312349826502151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28708415437998398149356277 2691413947312349826502151)
              ·
                refine ⟨4037120920968524739753227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691413947312349826502151 4037120920968524739753227)
                ·
                  refine ⟨6055681381452787109629841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4037120920968524739753227 6055681381452787109629841)
                  ·
                    refine ⟨4541761036089590332222381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6055681381452787109629841 4541761036089590332222381)
                    ·
                      refine ⟨1703160388533596374583393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4541761036089590332222381 1703160388533596374583393)
                      ·
                        rfl

theorem cell23_3316893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_3316893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316893 prefixEnd_3316893 := by exact prefixLift 3316893
  have htrace : WordTrace (prefixWord ++ tailWord_3316893) baseStart_3316893 baseEnd_3316893 := by
    simpa [prefixWord, tailWord_3316893, baseEnd_3316893] using wordTrace_append hprefix tailTrace_3316893
  have hstable : (prefixWord ++ tailWord_3316893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316893).length < 2 ^ (prefixWord ++ tailWord_3316893).sum := by decide
  have hdescent : baseEnd_3316893 < baseStart_3316893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316930 : List Nat := [3, 5, 1, 1, 2, 1, 3, 7]
def baseStart_3316930 : Nat := 118140960795 + 3316930 * 2 ^ 59
def prefixEnd_3316930 : Nat := 4983230072969 + 3 ^ 40 * 3316930 * 2
def baseEnd_3316930 : Nat := 63080718048807878882249

theorem tailTrace_3316930 : CollatzResearch.WordTrace tailWord_3316930 prefixEnd_3316930 63080718048807878882249 := by
  unfold tailWord_3316930
  simp only [CollatzResearch.WordTrace]
  refine ⟨30244593968334142847203061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80652250582224380925874829 30244593968334142847203061)
  ·
    refine ⟨2835430684531325891925287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30244593968334142847203061 2835430684531325891925287)
    ·
      refine ⟨4253146026796988837887931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2835430684531325891925287 4253146026796988837887931)
      ·
        refine ⟨6379719040195483256831897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4253146026796988837887931 6379719040195483256831897)
        ·
          refine ⟨4784789280146612442623923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6379719040195483256831897 4784789280146612442623923)
          ·
            refine ⟨7177183920219918663935885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4784789280146612442623923 7177183920219918663935885)
            ·
              refine ⟨2691443970082469498975957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7177183920219918663935885 2691443970082469498975957)
              ·
                refine ⟨63080718048807878882249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2691443970082469498975957 63080718048807878882249)
                ·
                  rfl

theorem cell23_3316930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 7].length) (baseStart_3316930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316930 prefixEnd_3316930 := by exact prefixLift 3316930
  have htrace : WordTrace (prefixWord ++ tailWord_3316930) baseStart_3316930 baseEnd_3316930 := by
    simpa [prefixWord, tailWord_3316930, baseEnd_3316930] using wordTrace_append hprefix tailTrace_3316930
  have hstable : (prefixWord ++ tailWord_3316930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316930).length < 2 ^ (prefixWord ++ tailWord_3316930).sum := by decide
  have hdescent : baseEnd_3316930 < baseStart_3316930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316941 : List Nat := [1, 6, 2, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_3316941 : Nat := 118140960795 + 3316941 * 2 ^ 59
def prefixEnd_3316941 : Nat := 4983230072969 + 3 ^ 40 * 3316941 * 2
def baseEnd_3316941 : Nat := 1703185035605012186783173

theorem tailTrace_3316941 : CollatzResearch.WordTrace tailWord_3316941 prefixEnd_3316941 1703185035605012186783173 := by
  unfold tailWord_3316941
  simp only [CollatzResearch.WordTrace]
  refine ⟨120978777076296720267462677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80652518050864480178308451 120978777076296720267462677)
  ·
    refine ⟨5670880175451408762537313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120978777076296720267462677 5670880175451408762537313)
    ·
      refine ⟨4253160131588556571902985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5670880175451408762537313 4253160131588556571902985)
      ·
        refine ⟨3189870098691417428927239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4253160131588556571902985 3189870098691417428927239)
        ·
          refine ⟨4784805148037126143390859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3189870098691417428927239 4784805148037126143390859)
          ·
            refine ⟨7177207722055689215086289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4784805148037126143390859 7177207722055689215086289)
            ·
              refine ⟨5382905791541766911314717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7177207722055689215086289 5382905791541766911314717)
              ·
                refine ⟨2018589671828162591743019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5382905791541766911314717 2018589671828162591743019)
                ·
                  refine ⟨3027884507742243887614529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2018589671828162591743019 3027884507742243887614529)
                  ·
                    refine ⟨2270913380806682915710897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3027884507742243887614529 2270913380806682915710897)
                    ·
                      refine ⟨1703185035605012186783173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2270913380806682915710897 1703185035605012186783173)
                      ·
                        rfl

theorem cell23_3316941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_3316941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316941 prefixEnd_3316941 := by exact prefixLift 3316941
  have htrace : WordTrace (prefixWord ++ tailWord_3316941) baseStart_3316941 baseEnd_3316941 := by
    simpa [prefixWord, tailWord_3316941, baseEnd_3316941] using wordTrace_append hprefix tailTrace_3316941
  have hstable : (prefixWord ++ tailWord_3316941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316941).length < 2 ^ (prefixWord ++ tailWord_3316941).sum := by decide
  have hdescent : baseEnd_3316941 < baseStart_3316941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316957 : List Nat := [1, 4, 3, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_3316957 : Nat := 118140960795 + 3316957 * 2 ^ 59
def prefixEnd_3316957 : Nat := 4983230072969 + 3 ^ 40 * 3316957 * 2
def baseEnd_3316957 : Nat := 1703193251295484124183099

theorem tailTrace_3316957 : CollatzResearch.WordTrace tailWord_3316957 prefixEnd_3316957 1703193251295484124183099 := by
  unfold tailWord_3316957
  simp only [CollatzResearch.WordTrace]
  refine ⟨120979360644238755000045125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80652907096159170000030083 120979360644238755000045125)
  ·
    refine ⟨22683630120794766562508461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120979360644238755000045125 22683630120794766562508461)
    ·
      refine ⟨8506361295298037460940673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22683630120794766562508461 8506361295298037460940673)
      ·
        refine ⟨6379770971473528095705505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8506361295298037460940673 6379770971473528095705505)
        ·
          refine ⟨4784828228605146071779129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6379770971473528095705505 4784828228605146071779129)
          ·
            refine ⟨3588621171453859553834347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4784828228605146071779129 3588621171453859553834347)
            ·
              refine ⟨5382931757180789330751521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3588621171453859553834347 5382931757180789330751521)
              ·
                refine ⟨4037198817885591998063641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5382931757180789330751521 4037198817885591998063641)
                ·
                  refine ⟨3027899113414193998547731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4037198817885591998063641 3027899113414193998547731)
                  ·
                    refine ⟨4541848670121290997821597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3027899113414193998547731 4541848670121290997821597)
                    ·
                      refine ⟨1703193251295484124183099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4541848670121290997821597 1703193251295484124183099)
                      ·
                        rfl

theorem cell23_3316957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_3316957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316957 prefixEnd_3316957 := by exact prefixLift 3316957
  have htrace : WordTrace (prefixWord ++ tailWord_3316957) baseStart_3316957 baseEnd_3316957 := by
    simpa [prefixWord, tailWord_3316957, baseEnd_3316957] using wordTrace_append hprefix tailTrace_3316957
  have hstable : (prefixWord ++ tailWord_3316957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316957).length < 2 ^ (prefixWord ++ tailWord_3316957).sum := by decide
  have hdescent : baseEnd_3316957 < baseStart_3316957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316959 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 4]
def baseStart_3316959 : Nat := 118140960795 + 3316959 * 2 ^ 59
def prefixEnd_3316959 : Nat := 4983230072969 + 3 ^ 40 * 3316959 * 2
def baseEnd_3316959 : Nat := 1703194278256793116358089

theorem tailTrace_3316959 : CollatzResearch.WordTrace tailWord_3316959 prefixEnd_3316959 1703194278256793116358089 := by
  unfold tailWord_3316959
  simp only [CollatzResearch.WordTrace]
  refine ⟨120979433590231509341617931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80652955726821006227745287 120979433590231509341617931)
  ·
    refine ⟨181469150385347264012426897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120979433590231509341617931 181469150385347264012426897)
    ·
      refine ⟨136101862789010448009320173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181469150385347264012426897 136101862789010448009320173)
      ·
        refine ⟨51038198545878918003495065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136101862789010448009320173 51038198545878918003495065)
        ·
          refine ⟨38278648909409188502621299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51038198545878918003495065 38278648909409188502621299)
          ·
            refine ⟨57417973364113782753931949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38278648909409188502621299 57417973364113782753931949)
            ·
              refine ⟨21531740011542668532724481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57417973364113782753931949 21531740011542668532724481)
              ·
                refine ⟨16148805008657001399543361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21531740011542668532724481 16148805008657001399543361)
                ·
                  refine ⟨12111603756492751049657521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16148805008657001399543361 12111603756492751049657521)
                  ·
                    refine ⟨9083702817369563287243141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12111603756492751049657521 9083702817369563287243141)
                    ·
                      refine ⟨1703194278256793116358089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9083702817369563287243141 1703194278256793116358089)
                      ·
                        rfl

theorem cell23_3316959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_3316959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3316959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3316959 prefixEnd_3316959 := by exact prefixLift 3316959
  have htrace : WordTrace (prefixWord ++ tailWord_3316959) baseStart_3316959 baseEnd_3316959 := by
    simpa [prefixWord, tailWord_3316959, baseEnd_3316959] using wordTrace_append hprefix tailTrace_3316959
  have hstable : (prefixWord ++ tailWord_3316959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316959).length < 2 ^ (prefixWord ++ tailWord_3316959).sum := by decide
  have hdescent : baseEnd_3316959 < baseStart_3316959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317003 : List Nat := [1, 1, 1, 1, 5, 5, 1, 3, 5]
def baseStart_3317003 : Nat := 118140960795 + 3317003 * 2 ^ 59
def prefixEnd_3317003 : Nat := 4983230072969 + 3 ^ 40 * 3317003 * 2
def baseEnd_3317003 : Nat := 189246319045065660467543

theorem tailTrace_3317003 : CollatzResearch.WordTrace tailWord_3317003 prefixEnd_3317003 189246319045065660467543 := by
  unfold tailWord_3317003
  simp only [CollatzResearch.WordTrace]
  refine ⟨120981038402072104856219663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80654025601381403237479775 120981038402072104856219663)
  ·
    refine ⟨181471557603108157284329495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120981038402072104856219663 181471557603108157284329495)
    ·
      refine ⟨272207336404662235926494243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181471557603108157284329495 272207336404662235926494243)
      ·
        refine ⟨408311004606993353889741365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272207336404662235926494243 408311004606993353889741365)
        ·
          refine ⟨38279156681905626927163253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 408311004606993353889741365 38279156681905626927163253)
          ·
            refine ⟨3588670938928652524421555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38279156681905626927163253 3588670938928652524421555)
            ·
              refine ⟨5383006408392978786632333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3588670938928652524421555 5383006408392978786632333)
              ·
                refine ⟨2018627403147367044987125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5383006408392978786632333 2018627403147367044987125)
                ·
                  refine ⟨189246319045065660467543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2018627403147367044987125 189246319045065660467543)
                  ·
                    rfl

theorem cell23_3317003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 5].length) (baseStart_3317003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317003 prefixEnd_3317003 := by exact prefixLift 3317003
  have htrace : WordTrace (prefixWord ++ tailWord_3317003) baseStart_3317003 baseEnd_3317003 := by
    simpa [prefixWord, tailWord_3317003, baseEnd_3317003] using wordTrace_append hprefix tailTrace_3317003
  have hstable : (prefixWord ++ tailWord_3317003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317003).length < 2 ^ (prefixWord ++ tailWord_3317003).sum := by decide
  have hdescent : baseEnd_3317003 < baseStart_3317003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317009 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_3317009 : Nat := 118140960795 + 3317009 * 2 ^ 59
def prefixEnd_3317009 : Nat := 4983230072969 + 3 ^ 40 * 3317009 * 2
def baseEnd_3317009 : Nat := 1703219952289517920732859

theorem tailTrace_3317009 : CollatzResearch.WordTrace tailWord_3317009 prefixEnd_3317009 1703219952289517920732859 := by
  unfold tailWord_3317009
  simp only [CollatzResearch.WordTrace]
  refine ⟨120981257240050367880938081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80654171493366911920625387 120981257240050367880938081)
  ·
    refine ⟨90735942930037775910703561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120981257240050367880938081 90735942930037775910703561)
    ·
      refine ⟨68051957197528331933027671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90735942930037775910703561 68051957197528331933027671)
      ·
        refine ⟨102077935796292497899541507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68051957197528331933027671 102077935796292497899541507)
        ·
          refine ⟨153116903694438746849312261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102077935796292497899541507 153116903694438746849312261)
          ·
            refine ⟨28709419442707265034246049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153116903694438746849312261 28709419442707265034246049)
            ·
              refine ⟨21532064582030448775684537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28709419442707265034246049 21532064582030448775684537)
              ·
                refine ⟨16149048436522836581763403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21532064582030448775684537 16149048436522836581763403)
                ·
                  refine ⟨24223572654784254872645105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16149048436522836581763403 24223572654784254872645105)
                  ·
                    refine ⟨18167679491088191154483829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24223572654784254872645105 18167679491088191154483829)
                    ·
                      refine ⟨1703219952289517920732859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18167679491088191154483829 1703219952289517920732859)
                      ·
                        rfl

theorem cell23_3317009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_3317009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317009 prefixEnd_3317009 := by exact prefixLift 3317009
  have htrace : WordTrace (prefixWord ++ tailWord_3317009) baseStart_3317009 baseEnd_3317009 := by
    simpa [prefixWord, tailWord_3317009, baseEnd_3317009] using wordTrace_append hprefix tailTrace_3317009
  have hstable : (prefixWord ++ tailWord_3317009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317009).length < 2 ^ (prefixWord ++ tailWord_3317009).sum := by decide
  have hdescent : baseEnd_3317009 < baseStart_3317009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317016 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 2, 5]
def baseStart_3317016 : Nat := 118140960795 + 3317016 * 2 ^ 59
def prefixEnd_3317016 : Nat := 4983230072969 + 3 ^ 40 * 3317016 * 2
def baseEnd_3317016 : Nat := 567741182218033131115109

theorem tailTrace_3317016 : CollatzResearch.WordTrace tailWord_3317016 prefixEnd_3317016 567741182218033131115109 := by
  unfold tailWord_3317016
  simp only [CollatzResearch.WordTrace]
  refine ⟨60490756275512504038221451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80654341700683338717628601 60490756275512504038221451)
  ·
    refine ⟨90736134413268756057332177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60490756275512504038221451 90736134413268756057332177)
    ·
      refine ⟨68052100809951567042999133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90736134413268756057332177 68052100809951567042999133)
      ·
        refine ⟨25519537803731837641124675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68052100809951567042999133 25519537803731837641124675)
        ·
          refine ⟨38279306705597756461687013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25519537803731837641124675 38279306705597756461687013)
          ·
            refine ⟨7177370007299579336566315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38279306705597756461687013 7177370007299579336566315)
            ·
              refine ⟨10766055010949369004849473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7177370007299579336566315 10766055010949369004849473)
              ·
                refine ⟨8074541258212026753637105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10766055010949369004849473 8074541258212026753637105)
                ·
                  refine ⟨6055905943659020065227829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8074541258212026753637105 6055905943659020065227829)
                  ·
                    refine ⟨567741182218033131115109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6055905943659020065227829 567741182218033131115109)
                    ·
                      rfl

theorem cell23_3317016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_3317016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317016 prefixEnd_3317016 := by exact prefixLift 3317016
  have htrace : WordTrace (prefixWord ++ tailWord_3317016) baseStart_3317016 baseEnd_3317016 := by
    simpa [prefixWord, tailWord_3317016, baseEnd_3317016] using wordTrace_append hprefix tailTrace_3317016
  have hstable : (prefixWord ++ tailWord_3317016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317016).length < 2 ^ (prefixWord ++ tailWord_3317016).sum := by decide
  have hdescent : baseEnd_3317016 < baseStart_3317016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317036 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 1, 6, 2]
def baseStart_3317036 : Nat := 118140960795 + 3317036 * 2 ^ 59
def prefixEnd_3317036 : Nat := 4983230072969 + 3 ^ 40 * 3317036 * 2
def baseEnd_3317036 : Nat := 1703233816267189315095235

theorem tailTrace_3317036 : CollatzResearch.WordTrace tailWord_3317036 prefixEnd_3317036 1703233816267189315095235 := by
  unfold tailWord_3317036
  simp only [CollatzResearch.WordTrace]
  refine ⟨60491121005476275746085481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80654828007301700994780641 60491121005476275746085481)
  ·
    refine ⟨45368340754107206809564111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60491121005476275746085481 45368340754107206809564111)
    ·
      refine ⟨68052511131160810214346167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45368340754107206809564111 68052511131160810214346167)
      ·
        refine ⟨102078766696741215321519251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68052511131160810214346167 102078766696741215321519251)
        ·
          refine ⟨153118150045111822982278877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102078766696741215321519251 153118150045111822982278877)
          ·
            refine ⟨57419306266916933618354579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153118150045111822982278877 57419306266916933618354579)
            ·
              refine ⟨86128959400375400427531869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57419306266916933618354579 86128959400375400427531869)
              ·
                refine ⟨32298359775140775160324451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86128959400375400427531869 32298359775140775160324451)
                ·
                  refine ⟨48447539662711162740486677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32298359775140775160324451 48447539662711162740486677)
                  ·
                    refine ⟨2270978421689585753460313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48447539662711162740486677 2270978421689585753460313)
                    ·
                      refine ⟨1703233816267189315095235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2270978421689585753460313 1703233816267189315095235)
                      ·
                        rfl

theorem cell23_3317036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 6, 2].length) (baseStart_3317036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317036 prefixEnd_3317036 := by exact prefixLift 3317036
  have htrace : WordTrace (prefixWord ++ tailWord_3317036) baseStart_3317036 baseEnd_3317036 := by
    simpa [prefixWord, tailWord_3317036, baseEnd_3317036] using wordTrace_append hprefix tailTrace_3317036
  have hstable : (prefixWord ++ tailWord_3317036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317036).length < 2 ^ (prefixWord ++ tailWord_3317036).sum := by decide
  have hdescent : baseEnd_3317036 < baseStart_3317036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317103 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 3, 1, 3]
def baseStart_3317103 : Nat := 118140960795 + 3317103 * 2 ^ 59
def prefixEnd_3317103 : Nat := 4983230072969 + 3 ^ 40 * 3317103 * 2
def baseEnd_3317103 : Nat := 1703268219471040552957427

theorem tailTrace_3317103 : CollatzResearch.WordTrace tailWord_3317103 prefixEnd_3317103 1703268219471040552957427 := by
  unfold tailWord_3317103
  simp only [CollatzResearch.WordTrace]
  refine ⟨120984685701709821934859963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80656457134473214623239975 120984685701709821934859963)
  ·
    refine ⟨181477028552564732902289945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120984685701709821934859963 181477028552564732902289945)
    ·
      refine ⟨136107771414423549676717459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181477028552564732902289945 136107771414423549676717459)
      ·
        refine ⟨204161657121635324515076189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136107771414423549676717459 204161657121635324515076189)
        ·
          refine ⟨76560621420613246693153571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204161657121635324515076189 76560621420613246693153571)
          ·
            refine ⟨114840932130919870039730357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76560621420613246693153571 114840932130919870039730357)
            ·
              refine ⟨10766337387273737816224721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114840932130919870039730357 10766337387273737816224721)
              ·
                refine ⟨8074753040455303362168541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10766337387273737816224721 8074753040455303362168541)
                ·
                  refine ⟨3028032390170738760813203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8074753040455303362168541 3028032390170738760813203)
                  ·
                    refine ⟨4542048585256108141219805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3028032390170738760813203 4542048585256108141219805)
                    ·
                      refine ⟨1703268219471040552957427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4542048585256108141219805 1703268219471040552957427)
                      ·
                        rfl

theorem cell23_3317103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 1, 3].length) (baseStart_3317103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317103 prefixEnd_3317103 := by exact prefixLift 3317103
  have htrace : WordTrace (prefixWord ++ tailWord_3317103) baseStart_3317103 baseEnd_3317103 := by
    simpa [prefixWord, tailWord_3317103, baseEnd_3317103] using wordTrace_append hprefix tailTrace_3317103
  have hstable : (prefixWord ++ tailWord_3317103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317103).length < 2 ^ (prefixWord ++ tailWord_3317103).sum := by decide
  have hdescent : baseEnd_3317103 < baseStart_3317103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317106 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_3317106 : Nat := 118140960795 + 3317106 * 2 ^ 59
def prefixEnd_3317106 : Nat := 4983230072969 + 3 ^ 40 * 3317106 * 2
def baseEnd_3317106 : Nat := 567756586637668013739971

theorem tailTrace_3317106 : CollatzResearch.WordTrace tailWord_3317106 prefixEnd_3317106 567756586637668013739971 := by
  unfold tailWord_3317106
  simp only [CollatzResearch.WordTrace]
  refine ⟨30246198780174738361804793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80656530080465968964812781 30246198780174738361804793)
  ·
    refine ⟨22684649085131053771353595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30246198780174738361804793 22684649085131053771353595)
    ·
      refine ⟨34026973627696580657030393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22684649085131053771353595 34026973627696580657030393)
      ·
        refine ⟨25520230220772435492772795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34026973627696580657030393 25520230220772435492772795)
        ·
          refine ⟨38280345331158653239159193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25520230220772435492772795 38280345331158653239159193)
          ·
            refine ⟨28710258998368989929369395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38280345331158653239159193 28710258998368989929369395)
            ·
              refine ⟨43065388497553484894054093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28710258998368989929369395 43065388497553484894054093)
              ·
                refine ⟨16149520686582556835270285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43065388497553484894054093 16149520686582556835270285)
                ·
                  refine ⟨6056070257468458813226357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16149520686582556835270285 6056070257468458813226357)
                  ·
                    refine ⟨567756586637668013739971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6056070257468458813226357 567756586637668013739971)
                    ·
                      rfl

theorem cell23_3317106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_3317106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317106 prefixEnd_3317106 := by exact prefixLift 3317106
  have htrace : WordTrace (prefixWord ++ tailWord_3317106) baseStart_3317106 baseEnd_3317106 := by
    simpa [prefixWord, tailWord_3317106, baseEnd_3317106] using wordTrace_append hprefix tailTrace_3317106
  have hstable : (prefixWord ++ tailWord_3317106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317106).length < 2 ^ (prefixWord ++ tailWord_3317106).sum := by decide
  have hdescent : baseEnd_3317106 < baseStart_3317106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317123 : List Nat := [1, 1, 1, 3, 5, 2, 1, 3, 1, 5]
def baseStart_3317123 : Nat := 118140960795 + 3317123 * 2 ^ 59
def prefixEnd_3317123 : Nat := 4983230072969 + 3 ^ 40 * 3317123 * 2
def baseEnd_3317123 : Nat := 567759496361376824902445

theorem tailTrace_3317123 : CollatzResearch.WordTrace tailWord_3317123 prefixEnd_3317123 567759496361376824902445 := by
  unfold tailWord_3317123
  simp only [CollatzResearch.WordTrace]
  refine ⟨120985415161637365350588023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80656943441091576900392015 120985415161637365350588023)
  ·
    refine ⟨181478122742456048025882035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120985415161637365350588023 181478122742456048025882035)
    ·
      refine ⟨272217184113684072038823053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181478122742456048025882035 272217184113684072038823053)
      ·
        refine ⟨102081444042631527014558645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272217184113684072038823053 102081444042631527014558645)
        ·
          refine ⟨9570135378996705657614873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102081444042631527014558645 9570135378996705657614873)
          ·
            refine ⟨7177601534247529243211155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9570135378996705657614873 7177601534247529243211155)
            ·
              refine ⟨10766402301371293864816733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7177601534247529243211155 10766402301371293864816733)
              ·
                refine ⟨4037400863014235199306275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10766402301371293864816733 4037400863014235199306275)
                ·
                  refine ⟨6056101294521352798959413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4037400863014235199306275 6056101294521352798959413)
                  ·
                    refine ⟨567759496361376824902445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6056101294521352798959413 567759496361376824902445)
                    ·
                      rfl

theorem cell23_3317123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 5].length) (baseStart_3317123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317123 prefixEnd_3317123 := by exact prefixLift 3317123
  have htrace : WordTrace (prefixWord ++ tailWord_3317123) baseStart_3317123 baseEnd_3317123 := by
    simpa [prefixWord, tailWord_3317123, baseEnd_3317123] using wordTrace_append hprefix tailTrace_3317123
  have hstable : (prefixWord ++ tailWord_3317123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317123).length < 2 ^ (prefixWord ++ tailWord_3317123).sum := by decide
  have hdescent : baseEnd_3317123 < baseStart_3317123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317180 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3317180 : Nat := 118140960795 + 3317180 * 2 ^ 59
def prefixEnd_3317180 : Nat := 4983230072969 + 3 ^ 40 * 3317180 * 2
def baseEnd_3317180 : Nat := 1703307757481436751694573

theorem tailTrace_3317180 : CollatzResearch.WordTrace tailWord_3317180 prefixEnd_3317180 1703307757481436751694573 := by
  unfold tailWord_3317180
  simp only [CollatzResearch.WordTrace]
  refine ⟨60493747061215432042706497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80658329414953909390275329 60493747061215432042706497)
  ·
    refine ⟨45370310295911574032029873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60493747061215432042706497 45370310295911574032029873)
    ·
      refine ⟨34027732721933680524022405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45370310295911574032029873 34027732721933680524022405)
      ·
        refine ⟨6380199885362565098254201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34027732721933680524022405 6380199885362565098254201)
        ·
          refine ⟨4785149914021923823690651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6380199885362565098254201 4785149914021923823690651)
          ·
            refine ⟨7177724871032885735535977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4785149914021923823690651 7177724871032885735535977)
            ·
              refine ⟨5383293653274664301651983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7177724871032885735535977 5383293653274664301651983)
              ·
                refine ⟨8074940479911996452477975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5383293653274664301651983 8074940479911996452477975)
                ·
                  refine ⟨12112410719867994678716963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8074940479911996452477975 12112410719867994678716963)
                  ·
                    refine ⟨18168616079801992018075445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12112410719867994678716963 18168616079801992018075445)
                    ·
                      refine ⟨1703307757481436751694573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18168616079801992018075445 1703307757481436751694573)
                      ·
                        rfl

theorem cell23_3317180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3317180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317180 prefixEnd_3317180 := by exact prefixLift 3317180
  have htrace : WordTrace (prefixWord ++ tailWord_3317180) baseStart_3317180 baseEnd_3317180 := by
    simpa [prefixWord, tailWord_3317180, baseEnd_3317180] using wordTrace_append hprefix tailTrace_3317180
  have hstable : (prefixWord ++ tailWord_3317180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317180).length < 2 ^ (prefixWord ++ tailWord_3317180).sum := by decide
  have hdescent : baseEnd_3317180 < baseStart_3317180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317204 : List Nat := [2, 4, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_3317204 : Nat := 118140960795 + 3317204 * 2 ^ 59
def prefixEnd_3317204 : Nat := 4983230072969 + 3 ^ 40 * 3317204 * 2
def baseEnd_3317204 : Nat := 567773360339048219264821

theorem tailTrace_3317204 : CollatzResearch.WordTrace tailWord_3317204 prefixEnd_3317204 567773360339048219264821 := by
  unfold tailWord_3317204
  simp only [CollatzResearch.WordTrace]
  refine ⟨60494184737171958092143333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80658912982895944122857777 60494184737171958092143333)
  ·
    refine ⟨11342659638219742142276875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60494184737171958092143333 11342659638219742142276875)
    ·
      refine ⟨17013989457329613213415313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11342659638219742142276875 17013989457329613213415313)
      ·
        refine ⟨12760492092997209910061485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17013989457329613213415313 12760492092997209910061485)
        ·
          refine ⟨4785184534873953716273057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12760492092997209910061485 4785184534873953716273057)
          ·
            refine ⟨3588888401155465287204793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4785184534873953716273057 3588888401155465287204793)
            ·
              refine ⟨2691666300866598965403595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3588888401155465287204793 2691666300866598965403595)
              ·
                refine ⟨4037499451299898448105393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691666300866598965403595 4037499451299898448105393)
                ·
                  refine ⟨3028124588474923836079045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4037499451299898448105393 3028124588474923836079045)
                  ·
                    refine ⟨567773360339048219264821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3028124588474923836079045 567773360339048219264821)
                    ·
                      rfl

theorem cell23_3317204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_3317204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317204 prefixEnd_3317204 := by exact prefixLift 3317204
  have htrace : WordTrace (prefixWord ++ tailWord_3317204) baseStart_3317204 baseEnd_3317204 := by
    simpa [prefixWord, tailWord_3317204, baseEnd_3317204] using wordTrace_append hprefix tailTrace_3317204
  have hstable : (prefixWord ++ tailWord_3317204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317204).length < 2 ^ (prefixWord ++ tailWord_3317204).sum := by decide
  have hdescent : baseEnd_3317204 < baseStart_3317204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317216 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 4]
def baseStart_3317216 : Nat := 118140960795 + 3317216 * 2 ^ 59
def prefixEnd_3317216 : Nat := 4983230072969 + 3 ^ 40 * 3317216 * 2
def baseEnd_3317216 : Nat := 1703326242784998610844407

theorem tailTrace_3317216 : CollatzResearch.WordTrace tailWord_3317216 prefixEnd_3317216 1703326242784998610844407 := by
  unfold tailWord_3317216
  simp only [CollatzResearch.WordTrace]
  refine ⟨60494403575150221116861751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80659204766866961489149001 60494403575150221116861751)
  ·
    refine ⟨90741605362725331675292627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60494403575150221116861751 90741605362725331675292627)
    ·
      refine ⟨136112408044087997512938941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90741605362725331675292627 136112408044087997512938941)
      ·
        refine ⟨51042153016532999067352103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136112408044087997512938941 51042153016532999067352103)
        ·
          refine ⟨76563229524799498601028155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51042153016532999067352103 76563229524799498601028155)
          ·
            refine ⟨114844844287199247901542233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76563229524799498601028155 114844844287199247901542233)
            ·
              refine ⟨86133633215399435926156675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114844844287199247901542233 86133633215399435926156675)
              ·
                refine ⟨129200449823099153889235013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86133633215399435926156675 129200449823099153889235013)
                ·
                  refine ⟨24225084341831091354231565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129200449823099153889235013 24225084341831091354231565)
                  ·
                    refine ⟨9084406628186659257836837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24225084341831091354231565 9084406628186659257836837)
                    ·
                      refine ⟨1703326242784998610844407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9084406628186659257836837 1703326242784998610844407)
                      ·
                        rfl

theorem cell23_3317216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_3317216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317216 prefixEnd_3317216 := by exact prefixLift 3317216
  have htrace : WordTrace (prefixWord ++ tailWord_3317216) baseStart_3317216 baseEnd_3317216 := by
    simpa [prefixWord, tailWord_3317216, baseEnd_3317216] using wordTrace_append hprefix tailTrace_3317216
  have hstable : (prefixWord ++ tailWord_3317216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317216).length < 2 ^ (prefixWord ++ tailWord_3317216).sum := by decide
  have hdescent : baseEnd_3317216 < baseStart_3317216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317250 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3317250 : Nat := 118140960795 + 3317250 * 2 ^ 59
def prefixEnd_3317250 : Nat := 4983230072969 + 3 ^ 40 * 3317250 * 2
def baseEnd_3317250 : Nat := 1703343701127251477819251

theorem tailTrace_3317250 : CollatzResearch.WordTrace tailWord_3317250 prefixEnd_3317250 1703343701127251477819251 := by
  unfold tailWord_3317250
  simp only [CollatzResearch.WordTrace]
  refine ⟨30247511808044316510115301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80660031488118177360307469 30247511808044316510115301)
  ·
    refine ⟨5671408464008309345646619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30247511808044316510115301 5671408464008309345646619)
    ·
      refine ⟨8507112696012464018469929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5671408464008309345646619 8507112696012464018469929)
      ·
        refine ⟨6380334522009348013852447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8507112696012464018469929 6380334522009348013852447)
        ·
          refine ⟨9570501783014022020778671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6380334522009348013852447 9570501783014022020778671)
          ·
            refine ⟨14355752674521033031168007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9570501783014022020778671 14355752674521033031168007)
            ·
              refine ⟨21533629011781549546752011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14355752674521033031168007 21533629011781549546752011)
              ·
                refine ⟨32300443517672324320128017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21533629011781549546752011 32300443517672324320128017)
                ·
                  refine ⟨24225332638254243240096013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32300443517672324320128017 24225332638254243240096013)
                  ·
                    refine ⟨9084499739345341215036005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24225332638254243240096013 9084499739345341215036005)
                    ·
                      refine ⟨1703343701127251477819251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9084499739345341215036005 1703343701127251477819251)
                      ·
                        rfl

theorem cell23_3317250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3317250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317250 prefixEnd_3317250 := by exact prefixLift 3317250
  have htrace : WordTrace (prefixWord ++ tailWord_3317250) baseStart_3317250 baseEnd_3317250 := by
    simpa [prefixWord, tailWord_3317250, baseEnd_3317250] using wordTrace_append hprefix tailTrace_3317250
  have hstable : (prefixWord ++ tailWord_3317250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317250).length < 2 ^ (prefixWord ++ tailWord_3317250).sum := by decide
  have hdescent : baseEnd_3317250 < baseStart_3317250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317267 : List Nat := [1, 1, 1, 2, 1, 6, 2, 3, 2, 2, 2]
def baseStart_3317267 : Nat := 118140960795 + 3317267 * 2 ^ 59
def prefixEnd_3317267 : Nat := 4983230072969 + 3 ^ 40 * 3317267 * 2
def baseEnd_3317267 : Nat := 1703352430298377911306673

theorem tailTrace_3317267 : CollatzResearch.WordTrace tailWord_3317267 prefixEnd_3317267 1703352430298377911306673 := by
  unfold tailWord_3317267
  simp only [CollatzResearch.WordTrace]
  refine ⟨120990667273115677943830055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80660444848743785295886703 120990667273115677943830055)
  ·
    refine ⟨181486000909673516915745083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120990667273115677943830055 181486000909673516915745083)
    ·
      refine ⟨272229001364510275373617625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181486000909673516915745083 272229001364510275373617625)
      ·
        refine ⟨204171751023382706530213219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272229001364510275373617625 204171751023382706530213219)
        ·
          refine ⟨306257626535074059795319829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204171751023382706530213219 306257626535074059795319829)
          ·
            refine ⟨14355826243831596552905617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 306257626535074059795319829 14355826243831596552905617)
            ·
              refine ⟨10766869682873697414679213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14355826243831596552905617 10766869682873697414679213)
              ·
                refine ⟨4037576131077636530504705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10766869682873697414679213 4037576131077636530504705)
                ·
                  refine ⟨3028182098308227397878529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4037576131077636530504705 3028182098308227397878529)
                  ·
                    refine ⟨2271136573731170548408897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3028182098308227397878529 2271136573731170548408897)
                    ·
                      refine ⟨1703352430298377911306673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2271136573731170548408897 1703352430298377911306673)
                      ·
                        rfl

theorem cell23_3317267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 2, 2].length) (baseStart_3317267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317267 prefixEnd_3317267 := by exact prefixLift 3317267
  have htrace : WordTrace (prefixWord ++ tailWord_3317267) baseStart_3317267 baseEnd_3317267 := by
    simpa [prefixWord, tailWord_3317267, baseEnd_3317267] using wordTrace_append hprefix tailTrace_3317267
  have hstable : (prefixWord ++ tailWord_3317267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317267).length < 2 ^ (prefixWord ++ tailWord_3317267).sum := by decide
  have hdescent : baseEnd_3317267 < baseStart_3317267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317288 : List Nat := [2, 1, 5, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_3317288 : Nat := 118140960795 + 3317288 * 2 ^ 59
def prefixEnd_3317288 : Nat := 4983230072969 + 3 ^ 40 * 3317288 * 2
def baseEnd_3317288 : Nat := 1703363213392122329144077

theorem tailTrace_3317288 : CollatzResearch.WordTrace tailWord_3317288 prefixEnd_3317288 1703363213392122329144077 := by
  unfold tailWord_3317288
  simp only [CollatzResearch.WordTrace]
  refine ⟨60495716603019799265172259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80660955470693065686896345 60495716603019799265172259)
  ·
    refine ⟨90743574904529698897758389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60495716603019799265172259 90743574904529698897758389)
    ·
      refine ⟨8507210147299659271664849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90743574904529698897758389 8507210147299659271664849)
      ·
        refine ⟨6380407610474744453748637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8507210147299659271664849 6380407610474744453748637)
        ·
          refine ⟨2392652853928029170155739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6380407610474744453748637 2392652853928029170155739)
          ·
            refine ⟨3588979280892043755233609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392652853928029170155739 3588979280892043755233609)
            ·
              refine ⟨2691734460669032816425207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3588979280892043755233609 2691734460669032816425207)
              ·
                refine ⟨4037601691003549224637811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691734460669032816425207 4037601691003549224637811)
                ·
                  refine ⟨6056402536505323836956717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4037601691003549224637811 6056402536505323836956717)
                  ·
                    refine ⟨2271150951189496438858769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6056402536505323836956717 2271150951189496438858769)
                    ·
                      refine ⟨1703363213392122329144077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2271150951189496438858769 1703363213392122329144077)
                      ·
                        rfl

theorem cell23_3317288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_3317288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317288 prefixEnd_3317288 := by exact prefixLift 3317288
  have htrace : WordTrace (prefixWord ++ tailWord_3317288) baseStart_3317288 baseEnd_3317288 := by
    simpa [prefixWord, tailWord_3317288, baseEnd_3317288] using wordTrace_append hprefix tailTrace_3317288
  have hstable : (prefixWord ++ tailWord_3317288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317288).length < 2 ^ (prefixWord ++ tailWord_3317288).sum := by decide
  have hdescent : baseEnd_3317288 < baseStart_3317288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317313 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3317313 : Nat := 118140960795 + 3317313 * 2 ^ 59
def prefixEnd_3317313 : Nat := 4983230072969 + 3 ^ 40 * 3317313 * 2
def baseEnd_3317313 : Nat := 1703376050408484731331461

theorem tailTrace_3317313 : CollatzResearch.WordTrace tailWord_3317313 prefixEnd_3317313 1703376050408484731331461 := by
  unfold tailWord_3317313
  simp only [CollatzResearch.WordTrace]
  refine ⟨120992345030949027800004593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80661563353966018533336395 120992345030949027800004593)
  ·
    refine ⟨90744258773211770850003445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120992345030949027800004593 90744258773211770850003445)
    ·
      refine ⟨8507274259988603517187823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90744258773211770850003445 8507274259988603517187823)
      ·
        refine ⟨12760911389982905275781735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8507274259988603517187823 12760911389982905275781735)
        ·
          refine ⟨19141367084974357913672603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12760911389982905275781735 19141367084974357913672603)
          ·
            refine ⟨28712050627461536870508905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19141367084974357913672603 28712050627461536870508905)
            ·
              refine ⟨21534037970596152652881679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28712050627461536870508905 21534037970596152652881679)
              ·
                refine ⟨32301056955894228979322519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21534037970596152652881679 32301056955894228979322519)
                ·
                  refine ⟨48451585433841343468983779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32301056955894228979322519 48451585433841343468983779)
                  ·
                    refine ⟨72677378150762015203475669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48451585433841343468983779 72677378150762015203475669)
                    ·
                      refine ⟨1703376050408484731331461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72677378150762015203475669 1703376050408484731331461)
                      ·
                        rfl

theorem cell23_3317313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3317313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317313 prefixEnd_3317313 := by exact prefixLift 3317313
  have htrace : WordTrace (prefixWord ++ tailWord_3317313) baseStart_3317313 baseEnd_3317313 := by
    simpa [prefixWord, tailWord_3317313, baseEnd_3317313] using wordTrace_append hprefix tailTrace_3317313
  have hstable : (prefixWord ++ tailWord_3317313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317313).length < 2 ^ (prefixWord ++ tailWord_3317313).sum := by decide
  have hdescent : baseEnd_3317313 < baseStart_3317313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317318 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_3317318 : Nat := 118140960795 + 3317318 * 2 ^ 59
def prefixEnd_3317318 : Nat := 4983230072969 + 3 ^ 40 * 3317318 * 2
def baseEnd_3317318 : Nat := 1703378617811757211768939

theorem tailTrace_3317318 : CollatzResearch.WordTrace tailWord_3317318 prefixEnd_3317318 1703378617811757211768939 := by
  unfold tailWord_3317318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781016481122841051685519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80661684930620609102624405 3781016481122841051685519)
  ·
    refine ⟨5671524721684261577528279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3781016481122841051685519 5671524721684261577528279)
    ·
      refine ⟨8507287082526392366292419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5671524721684261577528279 8507287082526392366292419)
      ·
        refine ⟨12760930623789588549438629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8507287082526392366292419 12760930623789588549438629)
        ·
          refine ⟨2392674491960547853019743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12760930623789588549438629 2392674491960547853019743)
          ·
            refine ⟨3589011737940821779529615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392674491960547853019743 3589011737940821779529615)
            ·
              refine ⟨5383517606911232669294423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589011737940821779529615 5383517606911232669294423)
              ·
                refine ⟨8075276410366849003941635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5383517606911232669294423 8075276410366849003941635)
                ·
                  refine ⟨12112914615550273505912453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8075276410366849003941635 12112914615550273505912453)
                  ·
                    refine ⟨2271171490415676282358585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12112914615550273505912453 2271171490415676282358585)
                    ·
                      refine ⟨1703378617811757211768939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2271171490415676282358585 1703378617811757211768939)
                      ·
                        rfl

theorem cell23_3317318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_3317318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317318 prefixEnd_3317318 := by exact prefixLift 3317318
  have htrace : WordTrace (prefixWord ++ tailWord_3317318) baseStart_3317318 baseEnd_3317318 := by
    simpa [prefixWord, tailWord_3317318, baseEnd_3317318] using wordTrace_append hprefix tailTrace_3317318
  have hstable : (prefixWord ++ tailWord_3317318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317318).length < 2 ^ (prefixWord ++ tailWord_3317318).sum := by decide
  have hdescent : baseEnd_3317318 < baseStart_3317318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317340 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_3317340 : Nat := 118140960795 + 3317340 * 2 ^ 59
def prefixEnd_3317340 : Nat := 4983230072969 + 3 ^ 40 * 3317340 * 2
def baseEnd_3317340 : Nat := 1703389914386156125693837

theorem tailTrace_3317340 : CollatzResearch.WordTrace tailWord_3317340 prefixEnd_3317340 1703389914386156125693837 := by
  unfold tailWord_3317340
  simp only [CollatzResearch.WordTrace]
  refine ⟨60496664900925605705618737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80662219867900807607491649 60496664900925605705618737)
  ·
    refine ⟨45372498675694204279214053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60496664900925605705618737 45372498675694204279214053)
    ·
      refine ⟨8507343501692663302352635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45372498675694204279214053 8507343501692663302352635)
      ·
        refine ⟨12761015252538994953528953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8507343501692663302352635 12761015252538994953528953)
        ·
          refine ⟨9570761439404246215146715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12761015252538994953528953 9570761439404246215146715)
          ·
            refine ⟨14356142159106369322720073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9570761439404246215146715 14356142159106369322720073)
            ·
              refine ⟨10767106619329776992040055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14356142159106369322720073 10767106619329776992040055)
              ·
                refine ⟨16150659928994665488060083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10767106619329776992040055 16150659928994665488060083)
                ·
                  refine ⟨24225989893491998232090125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16150659928994665488060083 24225989893491998232090125)
                  ·
                    refine ⟨9084746210059499337033797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24225989893491998232090125 9084746210059499337033797)
                    ·
                      refine ⟨1703389914386156125693837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9084746210059499337033797 1703389914386156125693837)
                      ·
                        rfl

theorem cell23_3317340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_3317340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317340 prefixEnd_3317340 := by exact prefixLift 3317340
  have htrace : WordTrace (prefixWord ++ tailWord_3317340) baseStart_3317340 baseEnd_3317340 := by
    simpa [prefixWord, tailWord_3317340, baseEnd_3317340] using wordTrace_append hprefix tailTrace_3317340
  have hstable : (prefixWord ++ tailWord_3317340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317340).length < 2 ^ (prefixWord ++ tailWord_3317340).sum := by decide
  have hdescent : baseEnd_3317340 < baseStart_3317340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317341 : List Nat := [1, 4, 4, 2, 1, 2, 1, 3, 5]
def baseStart_3317341 : Nat := 118140960795 + 3317341 * 2 ^ 59
def prefixEnd_3317341 : Nat := 4983230072969 + 3 ^ 40 * 3317341 * 2
def baseEnd_3317341 : Nat := 189265603096312291309037

theorem tailTrace_3317341 : CollatzResearch.WordTrace tailWord_3317341 prefixEnd_3317341 189265603096312291309037 := by
  unfold tailWord_3317341
  simp only [CollatzResearch.WordTrace]
  refine ⟨120993366274847588582023877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80662244183231725721349251 120993366274847588582023877)
  ·
    refine ⟨22686256176533922859129477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120993366274847588582023877 22686256176533922859129477)
    ·
      refine ⟨4253673033100110536086777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22686256176533922859129477 4253673033100110536086777)
      ·
        refine ⟨3190254774825082902065083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4253673033100110536086777 3190254774825082902065083)
        ·
          refine ⟨4785382162237624353097625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3190254774825082902065083 4785382162237624353097625)
          ·
            refine ⟨3589036621678218264823219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4785382162237624353097625 3589036621678218264823219)
            ·
              refine ⟨5383554932517327397234829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589036621678218264823219 5383554932517327397234829)
              ·
                refine ⟨2018833099693997773963061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5383554932517327397234829 2018833099693997773963061)
                ·
                  refine ⟨189265603096312291309037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2018833099693997773963061 189265603096312291309037)
                  ·
                    rfl

theorem cell23_3317341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_3317341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317341 prefixEnd_3317341 := by exact prefixLift 3317341
  have htrace : WordTrace (prefixWord ++ tailWord_3317341) baseStart_3317341 baseEnd_3317341 := by
    simpa [prefixWord, tailWord_3317341, baseEnd_3317341] using wordTrace_append hprefix tailTrace_3317341
  have hstable : (prefixWord ++ tailWord_3317341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317341).length < 2 ^ (prefixWord ++ tailWord_3317341).sum := by decide
  have hdescent : baseEnd_3317341 < baseStart_3317341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317357 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_3317357 : Nat := 118140960795 + 3317357 * 2 ^ 59
def prefixEnd_3317357 : Nat := 4983230072969 + 3 ^ 40 * 3317357 * 2
def baseEnd_3317357 : Nat := 1703398643557282559181259

theorem tailTrace_3317357 : CollatzResearch.WordTrace tailWord_3317357 prefixEnd_3317357 1703398643557282559181259 := by
  unfold tailWord_3317357
  simp only [CollatzResearch.WordTrace]
  refine ⟨120993949842789623314606325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80662633228526415543070883 120993949842789623314606325)
  ·
    refine ⟨11343182797761527185744343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120993949842789623314606325 11343182797761527185744343)
    ·
      refine ⟨17014774196642290778616515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11343182797761527185744343 17014774196642290778616515)
      ·
        refine ⟨25522161294963436167924773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17014774196642290778616515 25522161294963436167924773)
        ·
          refine ⟨4785405242805644281485895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25522161294963436167924773 4785405242805644281485895)
          ·
            refine ⟨7178107864208466422228843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4785405242805644281485895 7178107864208466422228843)
            ·
              refine ⟨10767161796312699633343265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7178107864208466422228843 10767161796312699633343265)
              ·
                refine ⟨8075371347234524725007449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10767161796312699633343265 8075371347234524725007449)
                ·
                  refine ⟨6056528510425893543755587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8075371347234524725007449 6056528510425893543755587)
                  ·
                    refine ⟨9084792765638840315633381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6056528510425893543755587 9084792765638840315633381)
                    ·
                      refine ⟨1703398643557282559181259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9084792765638840315633381 1703398643557282559181259)
                      ·
                        rfl

theorem cell23_3317357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_3317357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317357 prefixEnd_3317357 := by exact prefixLift 3317357
  have htrace : WordTrace (prefixWord ++ tailWord_3317357) baseStart_3317357 baseEnd_3317357 := by
    simpa [prefixWord, tailWord_3317357, baseEnd_3317357] using wordTrace_append hprefix tailTrace_3317357
  have hstable : (prefixWord ++ tailWord_3317357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317357).length < 2 ^ (prefixWord ++ tailWord_3317357).sum := by decide
  have hdescent : baseEnd_3317357 < baseStart_3317357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317360 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 3]
def baseStart_3317360 : Nat := 118140960795 + 3317360 * 2 ^ 59
def prefixEnd_3317360 : Nat := 4983230072969 + 3 ^ 40 * 3317360 * 2
def baseEnd_3317360 : Nat := 1703400183999246047443745

theorem tailTrace_3317360 : CollatzResearch.WordTrace tailWord_3317360 prefixEnd_3317360 1703400183999246047443745 := by
  unfold tailWord_3317360
  simp only [CollatzResearch.WordTrace]
  refine ⟨60497029630889377413482767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80662706174519169884643689 60497029630889377413482767)
  ·
    refine ⟨90745544446334066120224151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60497029630889377413482767 90745544446334066120224151)
    ·
      refine ⟨136118316669501099180336227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90745544446334066120224151 136118316669501099180336227)
      ·
        refine ⟨204177475004251648770504341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136118316669501099180336227 204177475004251648770504341)
        ·
          refine ⟨9570819140824296036117391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 204177475004251648770504341 9570819140824296036117391)
          ·
            refine ⟨14356228711236444054176087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9570819140824296036117391 14356228711236444054176087)
            ·
              refine ⟨21534343066854666081264131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14356228711236444054176087 21534343066854666081264131)
              ·
                refine ⟨32301514600281999121896197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21534343066854666081264131 32301514600281999121896197)
                ·
                  refine ⟨6056533987552874835355537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32301514600281999121896197 6056533987552874835355537)
                  ·
                    refine ⟨4542400490664656126516653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6056533987552874835355537 4542400490664656126516653)
                    ·
                      refine ⟨1703400183999246047443745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4542400490664656126516653 1703400183999246047443745)
                      ·
                        rfl

theorem cell23_3317360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 3].length) (baseStart_3317360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317360 prefixEnd_3317360 := by exact prefixLift 3317360
  have htrace : WordTrace (prefixWord ++ tailWord_3317360) baseStart_3317360 baseEnd_3317360 := by
    simpa [prefixWord, tailWord_3317360, baseEnd_3317360] using wordTrace_append hprefix tailTrace_3317360
  have hstable : (prefixWord ++ tailWord_3317360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317360).length < 2 ^ (prefixWord ++ tailWord_3317360).sum := by decide
  have hdescent : baseEnd_3317360 < baseStart_3317360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317394 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_3317394 : Nat := 118140960795 + 3317394 * 2 ^ 59
def prefixEnd_3317394 : Nat := 4983230072969 + 3 ^ 40 * 3317394 * 2
def baseEnd_3317394 : Nat := 1703417642341498914418589

theorem tailTrace_3317394 : CollatzResearch.WordTrace tailWord_3317394 prefixEnd_3317394 1703417642341498914418589 := by
  unfold tailWord_3317394
  simp only [CollatzResearch.WordTrace]
  refine ⟨30248824835913894658425809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80663532895770385755802157 30248824835913894658425809)
  ·
    refine ⟨22686618626935420993819357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30248824835913894658425809 22686618626935420993819357)
    ·
      refine ⟨8507481985100782872682259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22686618626935420993819357 8507481985100782872682259)
      ·
        refine ⟨12761222977651174309023389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8507481985100782872682259 12761222977651174309023389)
        ·
          refine ⟨4785458616619190365883771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12761222977651174309023389 4785458616619190365883771)
          ·
            refine ⟨7178187924928785548825657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4785458616619190365883771 7178187924928785548825657)
            ·
              refine ⟨5383640943696589161619243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7178187924928785548825657 5383640943696589161619243)
              ·
                refine ⟨8075461415544883742428865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5383640943696589161619243 8075461415544883742428865)
                ·
                  refine ⟨6056596061658662806821649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8075461415544883742428865 6056596061658662806821649)
                  ·
                    refine ⟨4542447046243997105116237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6056596061658662806821649 4542447046243997105116237)
                    ·
                      refine ⟨1703417642341498914418589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4542447046243997105116237 1703417642341498914418589)
                      ·
                        rfl

theorem cell23_3317394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_3317394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317394 prefixEnd_3317394 := by exact prefixLift 3317394
  have htrace : WordTrace (prefixWord ++ tailWord_3317394) baseStart_3317394 baseEnd_3317394 := by
    simpa [prefixWord, tailWord_3317394, baseEnd_3317394] using wordTrace_append hprefix tailTrace_3317394
  have hstable : (prefixWord ++ tailWord_3317394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317394).length < 2 ^ (prefixWord ++ tailWord_3317394).sum := by decide
  have hdescent : baseEnd_3317394 < baseStart_3317394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317423 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 3, 6]
def baseStart_3317423 : Nat := 118140960795 + 3317423 * 2 ^ 59
def prefixEnd_3317423 : Nat := 4983230072969 + 3 ^ 40 * 3317423 * 2
def baseEnd_3317423 : Nat := 567810844426826433651985

theorem tailTrace_3317423 : CollatzResearch.WordTrace tailWord_3317423 prefixEnd_3317423 567810844426826433651985 := by
  unfold tailWord_3317423
  simp only [CollatzResearch.WordTrace]
  refine ⟨120996357060550516586508923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80664238040367011057672615 120996357060550516586508923)
  ·
    refine ⟨181494535590825774879763385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120996357060550516586508923 181494535590825774879763385)
    ·
      refine ⟨136120901693119331159822539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181494535590825774879763385 136120901693119331159822539)
      ·
        refine ⟨204181352539678996739733809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136120901693119331159822539 204181352539678996739733809)
        ·
          refine ⟨153136014404759247554800357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204181352539678996739733809 153136014404759247554800357)
          ·
            refine ⟨28713002700892358916525067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153136014404759247554800357 28713002700892358916525067)
            ·
              refine ⟨43069504051338538374787601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28713002700892358916525067 43069504051338538374787601)
              ·
                refine ⟨32302128038503903781090701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43069504051338538374787601 32302128038503903781090701)
                ·
                  refine ⟨12113298014438963917909013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32302128038503903781090701 12113298014438963917909013)
                  ·
                    refine ⟨567810844426826433651985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12113298014438963917909013 567810844426826433651985)
                    ·
                      rfl

theorem cell23_3317423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 6].length) (baseStart_3317423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317423 prefixEnd_3317423 := by exact prefixLift 3317423
  have htrace : WordTrace (prefixWord ++ tailWord_3317423) baseStart_3317423 baseEnd_3317423 := by
    simpa [prefixWord, tailWord_3317423, baseEnd_3317423] using wordTrace_append hprefix tailTrace_3317423
  have hstable : (prefixWord ++ tailWord_3317423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317423).length < 2 ^ (prefixWord ++ tailWord_3317423).sum := by decide
  have hdescent : baseEnd_3317423 < baseStart_3317423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317440 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 1, 6]
def baseStart_3317440 : Nat := 118140960795 + 3317440 * 2 ^ 59
def prefixEnd_3317440 : Nat := 4983230072969 + 3 ^ 40 * 3317440 * 2
def baseEnd_3317440 : Nat := 567813754150535244814459

theorem tailTrace_3317440 : CollatzResearch.WordTrace tailWord_3317440 prefixEnd_3317440 567813754150535244814459 := by
  unfold tailWord_3317440
  simp only [CollatzResearch.WordTrace]
  refine ⟨60498488550744464244938887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80664651400992618993251849 60498488550744464244938887)
  ·
    refine ⟨90747732826116696367408331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60498488550744464244938887 90747732826116696367408331)
    ·
      refine ⟨136121599239175044551112497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90747732826116696367408331 136121599239175044551112497)
      ·
        refine ⟨102091199429381283413334373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136121599239175044551112497 102091199429381283413334373)
        ·
          refine ⟨19142099893008990640000195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102091199429381283413334373 19142099893008990640000195)
          ·
            refine ⟨28713149839513485960000293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19142099893008990640000195 28713149839513485960000293)
            ·
              refine ⟨5383715594908778617500055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28713149839513485960000293 5383715594908778617500055)
              ·
                refine ⟨8075573392363167926250083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5383715594908778617500055 8075573392363167926250083)
                ·
                  refine ⟨12113360088544751889375125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8075573392363167926250083 12113360088544751889375125)
                  ·
                    refine ⟨567813754150535244814459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12113360088544751889375125 567813754150535244814459)
                    ·
                      rfl

theorem cell23_3317440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 1, 6].length) (baseStart_3317440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317440 prefixEnd_3317440 := by exact prefixLift 3317440
  have htrace : WordTrace (prefixWord ++ tailWord_3317440) baseStart_3317440 baseEnd_3317440 := by
    simpa [prefixWord, tailWord_3317440, baseEnd_3317440] using wordTrace_append hprefix tailTrace_3317440
  have hstable : (prefixWord ++ tailWord_3317440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317440).length < 2 ^ (prefixWord ++ tailWord_3317440).sum := by decide
  have hdescent : baseEnd_3317440 < baseStart_3317440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317483 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 1, 9]
def baseStart_3317483 : Nat := 118140960795 + 3317483 * 2 ^ 59
def prefixEnd_3317483 : Nat := 4983230072969 + 3 ^ 40 * 3317483 * 2
def baseEnd_3317483 : Nat := 567821114039916355401893

theorem tailTrace_3317483 : CollatzResearch.WordTrace tailWord_3317483 prefixEnd_3317483 567821114039916355401893 := by
  unfold tailWord_3317483
  simp only [CollatzResearch.WordTrace]
  refine ⟨120998545440333146833693103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80665696960222097889128735 120998545440333146833693103)
  ·
    refine ⟨181497818160499720250539655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120998545440333146833693103 181497818160499720250539655)
    ·
      refine ⟨272246727240749580375809483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181497818160499720250539655 272246727240749580375809483)
      ·
        refine ⟨408370090861124370563714225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272246727240749580375809483 408370090861124370563714225)
        ·
          refine ⟨306277568145843277922785669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408370090861124370563714225 306277568145843277922785669)
          ·
            refine ⟨57427044027345614610522313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 306277568145843277922785669 57427044027345614610522313)
            ·
              refine ⟨43070283020509210957891735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57427044027345614610522313 43070283020509210957891735)
              ·
                refine ⟨64605424530763816436837603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43070283020509210957891735 64605424530763816436837603)
                ·
                  refine ⟨96908136796145724655256405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64605424530763816436837603 96908136796145724655256405)
                  ·
                    refine ⟨567821114039916355401893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 96908136796145724655256405 567821114039916355401893)
                    ·
                      rfl

theorem cell23_3317483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 9].length) (baseStart_3317483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317483 prefixEnd_3317483 := by exact prefixLift 3317483
  have htrace : WordTrace (prefixWord ++ tailWord_3317483) baseStart_3317483 baseEnd_3317483 := by
    simpa [prefixWord, tailWord_3317483, baseEnd_3317483] using wordTrace_append hprefix tailTrace_3317483
  have hstable : (prefixWord ++ tailWord_3317483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317483).length < 2 ^ (prefixWord ++ tailWord_3317483).sum := by decide
  have hdescent : baseEnd_3317483 < baseStart_3317483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317494 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_3317494 : Nat := 118140960795 + 3317494 * 2 ^ 59
def prefixEnd_3317494 : Nat := 4983230072969 + 3 ^ 40 * 3317494 * 2
def baseEnd_3317494 : Nat := 1703468990406948523168129

theorem tailTrace_3317494 : CollatzResearch.WordTrace tailWord_3317494 prefixEnd_3317494 1703468990406948523168129 := by
  unfold tailWord_3317494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7562434165205830982021471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80665964428862197141562357 7562434165205830982021471)
  ·
    refine ⟨11343651247808746473032207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7562434165205830982021471 11343651247808746473032207)
    ·
      refine ⟨17015476871713119709548311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11343651247808746473032207 17015476871713119709548311)
      ·
        refine ⟨25523215307569679564322467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17015476871713119709548311 25523215307569679564322467)
        ·
          refine ⟨38284822961354519346483701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25523215307569679564322467 38284822961354519346483701)
          ·
            refine ⟨3589202152626986188732847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38284822961354519346483701 3589202152626986188732847)
            ·
              refine ⟨5383803228940479283099271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589202152626986188732847 5383803228940479283099271)
              ·
                refine ⟨8075704843410718924648907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5383803228940479283099271 8075704843410718924648907)
                ·
                  refine ⟨12113557265116078386973361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8075704843410718924648907 12113557265116078386973361)
                  ·
                    refine ⟨9085167948837058790230021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12113557265116078386973361 9085167948837058790230021)
                    ·
                      refine ⟨1703468990406948523168129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9085167948837058790230021 1703468990406948523168129)
                      ·
                        rfl

theorem cell23_3317494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_3317494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317494 prefixEnd_3317494 := by exact prefixLift 3317494
  have htrace : WordTrace (prefixWord ++ tailWord_3317494) baseStart_3317494 baseEnd_3317494 := by
    simpa [prefixWord, tailWord_3317494, baseEnd_3317494] using wordTrace_append hprefix tailTrace_3317494
  have hstable : (prefixWord ++ tailWord_3317494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317494).length < 2 ^ (prefixWord ++ tailWord_3317494).sum := by decide
  have hdescent : baseEnd_3317494 < baseStart_3317494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317507 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 3, 3, 2]
def baseStart_3317507 : Nat := 118140960795 + 3317507 * 2 ^ 59
def prefixEnd_3317507 : Nat := 4983230072969 + 3 ^ 40 * 3317507 * 2
def baseEnd_3317507 : Nat := 1703475665655456972305569

theorem tailTrace_3317507 : CollatzResearch.WordTrace tailWord_3317507 prefixEnd_3317507 1703475665655456972305569 := by
  unfold tailWord_3317507
  simp only [CollatzResearch.WordTrace]
  refine ⟨120999420792246198932566775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80666280528164132621711183 120999420792246198932566775)
  ·
    refine ⟨181499131188369298398850163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120999420792246198932566775 181499131188369298398850163)
    ·
      refine ⟨272248696782553947598275245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181499131188369298398850163 272248696782553947598275245)
      ·
        refine ⟨102093261293457730349353217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272248696782553947598275245 102093261293457730349353217)
        ·
          refine ⟨76569945970093297762014913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102093261293457730349353217 76569945970093297762014913)
          ·
            refine ⟨57427459477569973321511185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76569945970093297762014913 57427459477569973321511185)
            ·
              refine ⟨43070594608177479991133389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57427459477569973321511185 43070594608177479991133389)
              ·
                refine ⟨16151472978066554996675021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43070594608177479991133389 16151472978066554996675021)
                ·
                  refine ⟨6056802366774958123753133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16151472978066554996675021 6056802366774958123753133)
                  ·
                    refine ⟨2271300887540609296407425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6056802366774958123753133 2271300887540609296407425)
                    ·
                      refine ⟨1703475665655456972305569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2271300887540609296407425 1703475665655456972305569)
                      ·
                        rfl

theorem cell23_3317507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 3, 2].length) (baseStart_3317507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317507 prefixEnd_3317507 := by exact prefixLift 3317507
  have htrace : WordTrace (prefixWord ++ tailWord_3317507) baseStart_3317507 baseEnd_3317507 := by
    simpa [prefixWord, tailWord_3317507, baseEnd_3317507] using wordTrace_append hprefix tailTrace_3317507
  have hstable : (prefixWord ++ tailWord_3317507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317507).length < 2 ^ (prefixWord ++ tailWord_3317507).sum := by decide
  have hdescent : baseEnd_3317507 < baseStart_3317507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317558 : List Nat := [5, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_3317558 : Nat := 118140960795 + 3317558 * 2 ^ 59
def prefixEnd_3317558 : Nat := 4983230072969 + 3 ^ 40 * 3317558 * 2
def baseEnd_3317558 : Nat := 1703501853168836272767835

theorem tailTrace_3317558 : CollatzResearch.WordTrace tailWord_3317558 prefixEnd_3317558 1703501853168836272767835 := by
  unfold tailWord_3317558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7562580057191339665167083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80667520610040956428448885 7562580057191339665167083)
  ·
    refine ⟨11343870085787009497750625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7562580057191339665167083 11343870085787009497750625)
    ·
      refine ⟨8507902564340257123312969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11343870085787009497750625 8507902564340257123312969)
      ·
        refine ⟨6380926923255192842484727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8507902564340257123312969 6380926923255192842484727)
        ·
          refine ⟨9571390384882789263727091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6380926923255192842484727 9571390384882789263727091)
          ·
            refine ⟨14357085577324183895590637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9571390384882789263727091 14357085577324183895590637)
            ·
              refine ⟨5383907091496568960846489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14357085577324183895590637 5383907091496568960846489)
              ·
                refine ⟨4037930318622426720634867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5383907091496568960846489 4037930318622426720634867)
                ·
                  refine ⟨6056895477933640080952301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4037930318622426720634867 6056895477933640080952301)
                  ·
                    refine ⟨2271335804225115030357113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6056895477933640080952301 2271335804225115030357113)
                    ·
                      refine ⟨1703501853168836272767835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2271335804225115030357113 1703501853168836272767835)
                      ·
                        rfl

theorem cell23_3317558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_3317558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317558 prefixEnd_3317558 := by exact prefixLift 3317558
  have htrace : WordTrace (prefixWord ++ tailWord_3317558) baseStart_3317558 baseEnd_3317558 := by
    simpa [prefixWord, tailWord_3317558, baseEnd_3317558] using wordTrace_append hprefix tailTrace_3317558
  have hstable : (prefixWord ++ tailWord_3317558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317558).length < 2 ^ (prefixWord ++ tailWord_3317558).sum := by decide
  have hdescent : baseEnd_3317558 < baseStart_3317558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317577 : List Nat := [1, 2, 1, 1, 2, 4, 2, 5, 5]
def baseStart_3317577 : Nat := 118140960795 + 3317577 * 2 ^ 59
def prefixEnd_3317577 : Nat := 4983230072969 + 3 ^ 40 * 3317577 * 2
def baseEnd_3317577 : Nat := 189279067700141299825583

theorem tailTrace_3317577 : CollatzResearch.WordTrace tailWord_3317577 prefixEnd_3317577 189279067700141299825583 := by
  unfold tailWord_3317577
  simp only [CollatzResearch.WordTrace]
  refine ⟨121001973901992600887614985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80667982601328400591743323 121001973901992600887614985)
  ·
    refine ⟨90751480426494450665711239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121001973901992600887614985 90751480426494450665711239)
    ·
      refine ⟨136127220639741675998566859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90751480426494450665711239 136127220639741675998566859)
      ·
        refine ⟨204190830959612513997850289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136127220639741675998566859 204190830959612513997850289)
        ·
          refine ⟨153143123219709385498387717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204190830959612513997850289 153143123219709385498387717)
          ·
            refine ⟨28714335603695509780947697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153143123219709385498387717 28714335603695509780947697)
            ·
              refine ⟨21535751702771632335710773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28714335603695509780947697 21535751702771632335710773)
              ·
                refine ⟨2018976722134840531472885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21535751702771632335710773 2018976722134840531472885)
                ·
                  refine ⟨189279067700141299825583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2018976722134840531472885 189279067700141299825583)
                  ·
                    rfl

theorem cell23_3317577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 5].length) (baseStart_3317577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317577 prefixEnd_3317577 := by exact prefixLift 3317577
  have htrace : WordTrace (prefixWord ++ tailWord_3317577) baseStart_3317577 baseEnd_3317577 := by
    simpa [prefixWord, tailWord_3317577, baseEnd_3317577] using wordTrace_append hprefix tailTrace_3317577
  have hstable : (prefixWord ++ tailWord_3317577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317577).length < 2 ^ (prefixWord ++ tailWord_3317577).sum := by decide
  have hdescent : baseEnd_3317577 < baseStart_3317577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317588 : List Nat := [2, 4, 1, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_3317588 : Nat := 118140960795 + 3317588 * 2 ^ 59
def prefixEnd_3317588 : Nat := 4983230072969 + 3 ^ 40 * 3317588 * 2
def baseEnd_3317588 : Nat := 1703517257588471155392697

theorem tailTrace_3317588 : CollatzResearch.WordTrace tailWord_3317588 prefixEnd_3317588 1703517257588471155392697 := by
  unfold tailWord_3317588
  simp only [CollatzResearch.WordTrace]
  refine ⟨60501187552476374883132709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80668250069968499844176945 60501187552476374883132709)
  ·
    refine ⟨11343972666089320290587383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60501187552476374883132709 11343972666089320290587383)
    ·
      refine ⟨17015958999133980435881075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11343972666089320290587383 17015958999133980435881075)
      ·
        refine ⟨25523938498700970653821613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17015958999133980435881075 25523938498700970653821613)
        ·
          refine ⟨9571476937012863995183105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25523938498700970653821613 9571476937012863995183105)
          ·
            refine ⟨7178607702759647996387329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9571476937012863995183105 7178607702759647996387329)
            ·
              refine ⟨5383955777069735997290497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7178607702759647996387329 5383955777069735997290497)
              ·
                refine ⟨4037966832802301997967873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5383955777069735997290497 4037966832802301997967873)
                ·
                  refine ⟨3028475124601726498475905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4037966832802301997967873 3028475124601726498475905)
                  ·
                    refine ⟨2271356343451294873856929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3028475124601726498475905 2271356343451294873856929)
                    ·
                      refine ⟨1703517257588471155392697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2271356343451294873856929 1703517257588471155392697)
                      ·
                        rfl

theorem cell23_3317588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_3317588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317588 prefixEnd_3317588 := by exact prefixLift 3317588
  have htrace : WordTrace (prefixWord ++ tailWord_3317588) baseStart_3317588 baseEnd_3317588 := by
    simpa [prefixWord, tailWord_3317588, baseEnd_3317588] using wordTrace_append hprefix tailTrace_3317588
  have hstable : (prefixWord ++ tailWord_3317588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317588).length < 2 ^ (prefixWord ++ tailWord_3317588).sum := by decide
  have hdescent : baseEnd_3317588 < baseStart_3317588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317604 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_3317604 : Nat := 118140960795 + 3317604 * 2 ^ 59
def prefixEnd_3317604 : Nat := 4983230072969 + 3 ^ 40 * 3317604 * 2
def baseEnd_3317604 : Nat := 1703525473278943092792623

theorem tailTrace_3317604 : CollatzResearch.WordTrace tailWord_3317604 prefixEnd_3317604 1703525473278943092792623 := by
  unfold tailWord_3317604
  simp only [CollatzResearch.WordTrace]
  refine ⟨60501479336447392249423933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80668639115263189665898577 60501479336447392249423933)
  ·
    refine ⟨22688054751167772093533975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60501479336447392249423933 22688054751167772093533975)
    ·
      refine ⟨34032082126751658140300963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22688054751167772093533975 34032082126751658140300963)
      ·
        refine ⟨51048123190127487210451445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34032082126751658140300963 51048123190127487210451445)
        ·
          refine ⟨4785761549074451925979823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51048123190127487210451445 4785761549074451925979823)
          ·
            refine ⟨7178642323611677888969735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4785761549074451925979823 7178642323611677888969735)
            ·
              refine ⟨10767963485417516833454603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7178642323611677888969735 10767963485417516833454603)
              ·
                refine ⟨16151945228126275250181905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10767963485417516833454603 16151945228126275250181905)
                ·
                  refine ⟨12113958921094706437636429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16151945228126275250181905 12113958921094706437636429)
                  ·
                    refine ⟨4542734595410514914113661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12113958921094706437636429 4542734595410514914113661)
                    ·
                      refine ⟨1703525473278943092792623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4542734595410514914113661 1703525473278943092792623)
                      ·
                        rfl

theorem cell23_3317604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_3317604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317604 prefixEnd_3317604 := by exact prefixLift 3317604
  have htrace : WordTrace (prefixWord ++ tailWord_3317604) baseStart_3317604 baseEnd_3317604 := by
    simpa [prefixWord, tailWord_3317604, baseEnd_3317604] using wordTrace_append hprefix tailTrace_3317604
  have hstable : (prefixWord ++ tailWord_3317604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317604).length < 2 ^ (prefixWord ++ tailWord_3317604).sum := by decide
  have hdescent : baseEnd_3317604 < baseStart_3317604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317627 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 3, 6, 2]
def baseStart_3317627 : Nat := 118140960795 + 3317627 * 2 ^ 59
def prefixEnd_3317627 : Nat := 4983230072969 + 3 ^ 40 * 3317627 * 2
def baseEnd_3317627 : Nat := 1703537283333996502805017

theorem tailTrace_3317627 : CollatzResearch.WordTrace tailWord_3317627 prefixEnd_3317627 1703537283333996502805017 := by
  unfold tailWord_3317627
  simp only [CollatzResearch.WordTrace]
  refine ⟨121003797551811459426935135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80669198367874306284623423 121003797551811459426935135)
  ·
    refine ⟨181505696327717189140402703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121003797551811459426935135 181505696327717189140402703)
    ·
      refine ⟨272258544491575783710604055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181505696327717189140402703 272258544491575783710604055)
      ·
        refine ⟨408387816737363675565906083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272258544491575783710604055 408387816737363675565906083)
        ·
          refine ⟨612581725106045513348859125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408387816737363675565906083 612581725106045513348859125)
          ·
            refine ⟨57429536728691766876455543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 612581725106045513348859125 57429536728691766876455543)
            ·
              refine ⟨86144305093037650314683315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57429536728691766876455543 86144305093037650314683315)
              ·
                refine ⟨129216457639556475472024973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86144305093037650314683315 129216457639556475472024973)
                ·
                  refine ⟨48456171614833678302009365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129216457639556475472024973 48456171614833678302009365)
                  ·
                    refine ⟨2271383044445328670406689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48456171614833678302009365 2271383044445328670406689)
                    ·
                      refine ⟨1703537283333996502805017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2271383044445328670406689 1703537283333996502805017)
                      ·
                        rfl

theorem cell23_3317627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 6, 2].length) (baseStart_3317627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317627 prefixEnd_3317627 := by exact prefixLift 3317627
  have htrace : WordTrace (prefixWord ++ tailWord_3317627) baseStart_3317627 baseEnd_3317627 := by
    simpa [prefixWord, tailWord_3317627, baseEnd_3317627] using wordTrace_append hprefix tailTrace_3317627
  have hstable : (prefixWord ++ tailWord_3317627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317627).length < 2 ^ (prefixWord ++ tailWord_3317627).sum := by decide
  have hdescent : baseEnd_3317627 < baseStart_3317627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317637 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 5, 4]
def baseStart_3317637 : Nat := 118140960795 + 3317637 * 2 ^ 59
def prefixEnd_3317637 : Nat := 4983230072969 + 3 ^ 40 * 3317637 * 2
def baseEnd_3317637 : Nat := 567847472713513821226657

theorem tailTrace_3317637 : CollatzResearch.WordTrace tailWord_3317637 prefixEnd_3317637 567847472713513821226657 := by
  unfold tailWord_3317637
  simp only [CollatzResearch.WordTrace]
  refine ⟨121004162281775231134799165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80669441521183487423199443 121004162281775231134799165)
  ·
    refine ⟨45376560855665711675549687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121004162281775231134799165 45376560855665711675549687)
    ·
      refine ⟨68064841283498567513324531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45376560855665711675549687 68064841283498567513324531)
      ·
        refine ⟨102097261925247851269986797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68064841283498567513324531 102097261925247851269986797)
        ·
          refine ⟨38286473221967944226245049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102097261925247851269986797 38286473221967944226245049)
          ·
            refine ⟨28714854916475958169683787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38286473221967944226245049 28714854916475958169683787)
            ·
              refine ⟨43072282374713937254525681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28714854916475958169683787 43072282374713937254525681)
              ·
                refine ⟨32304211781035452940894261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43072282374713937254525681 32304211781035452940894261)
                ·
                  refine ⟨3028519854472073713208837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32304211781035452940894261 3028519854472073713208837)
                  ·
                    refine ⟨567847472713513821226657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3028519854472073713208837 567847472713513821226657)
                    ·
                      rfl

theorem cell23_3317637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_3317637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317637 prefixEnd_3317637 := by exact prefixLift 3317637
  have htrace : WordTrace (prefixWord ++ tailWord_3317637) baseStart_3317637 baseEnd_3317637 := by
    simpa [prefixWord, tailWord_3317637, baseEnd_3317637] using wordTrace_append hprefix tailTrace_3317637
  have hstable : (prefixWord ++ tailWord_3317637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317637).length < 2 ^ (prefixWord ++ tailWord_3317637).sum := by decide
  have hdescent : baseEnd_3317637 < baseStart_3317637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317680 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 4, 9]
def baseStart_3317680 : Nat := 118140960795 + 3317680 * 2 ^ 59
def prefixEnd_3317680 : Nat := 4983230072969 + 3 ^ 40 * 3317680 * 2
def baseEnd_3317680 : Nat := 567854832602894931814091

theorem tailTrace_3317680 : CollatzResearch.WordTrace tailWord_3317680 prefixEnd_3317680 567854832602894931814091 := by
  unfold tailWord_3317680
  simp only [CollatzResearch.WordTrace]
  refine ⟨60502865310309724739307247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80670487080412966319076329 60502865310309724739307247)
  ·
    refine ⟨90754297965464587108960871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60502865310309724739307247 90754297965464587108960871)
    ·
      refine ⟨136131446948196880663441307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90754297965464587108960871 136131446948196880663441307)
      ·
        refine ⟨204197170422295320995161961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136131446948196880663441307 204197170422295320995161961)
        ·
          refine ⟨153147877816721490746371471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204197170422295320995161961 153147877816721490746371471)
          ·
            refine ⟨229721816725082236119557207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153147877816721490746371471 229721816725082236119557207)
            ·
              refine ⟨344582725087623354179335811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229721816725082236119557207 344582725087623354179335811)
              ·
                refine ⟨516874087631435031269003717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344582725087623354179335811 516874087631435031269003717)
                ·
                  refine ⟨96913891430894068362938197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 516874087631435031269003717 96913891430894068362938197)
                  ·
                    refine ⟨567854832602894931814091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 96913891430894068362938197 567854832602894931814091)
                    ·
                      rfl

theorem cell23_3317680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_3317680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317680 prefixEnd_3317680 := by exact prefixLift 3317680
  have htrace : WordTrace (prefixWord ++ tailWord_3317680) baseStart_3317680 baseEnd_3317680 := by
    simpa [prefixWord, tailWord_3317680, baseEnd_3317680] using wordTrace_append hprefix tailTrace_3317680
  have hstable : (prefixWord ++ tailWord_3317680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317680).length < 2 ^ (prefixWord ++ tailWord_3317680).sum := by decide
  have hdescent : baseEnd_3317680 < baseStart_3317680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317731 : List Nat := [1, 1, 1, 6, 1, 4, 1, 2, 1, 5]
def baseStart_3317731 : Nat := 118140960795 + 3317731 * 2 ^ 59
def prefixEnd_3317731 : Nat := 4983230072969 + 3 ^ 40 * 3317731 * 2
def baseEnd_3317731 : Nat := 567863561774021365301513

theorem tailTrace_3317731 : CollatzResearch.WordTrace tailWord_3317731 prefixEnd_3317731 567863561774021365301513 := by
  unfold tailWord_3317731
  simp only [CollatzResearch.WordTrace]
  refine ⟨121007590743434685188721047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80671727162289790125814031 121007590743434685188721047)
  ·
    refine ⟨181511386115152027783081571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121007590743434685188721047 181511386115152027783081571)
    ·
      refine ⟨272267079172728041674622357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181511386115152027783081571 272267079172728041674622357)
      ·
        refine ⟨12762519336221626953497923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 272267079172728041674622357 12762519336221626953497923)
        ·
          refine ⟨19143779004332440430246885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12762519336221626953497923 19143779004332440430246885)
          ·
            refine ⟨3589458563312332580671291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19143779004332440430246885 3589458563312332580671291)
            ·
              refine ⟨5384187844968498871006937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589458563312332580671291 5384187844968498871006937)
              ·
                refine ⟨4038140883726374153255203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5384187844968498871006937 4038140883726374153255203)
                ·
                  refine ⟨6057211325589561229882805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4038140883726374153255203 6057211325589561229882805)
                  ·
                    refine ⟨567863561774021365301513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6057211325589561229882805 567863561774021365301513)
                    ·
                      rfl

theorem cell23_3317731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 5].length) (baseStart_3317731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317731 prefixEnd_3317731 := by exact prefixLift 3317731
  have htrace : WordTrace (prefixWord ++ tailWord_3317731) baseStart_3317731 baseEnd_3317731 := by
    simpa [prefixWord, tailWord_3317731, baseEnd_3317731] using wordTrace_append hprefix tailTrace_3317731
  have hstable : (prefixWord ++ tailWord_3317731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317731).length < 2 ^ (prefixWord ++ tailWord_3317731).sum := by decide
  have hdescent : baseEnd_3317731 < baseStart_3317731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317761 : List Nat := [1, 2, 4, 1, 2, 1, 4, 2, 2, 4]
def baseStart_3317761 : Nat := 118140960795 + 3317761 * 2 ^ 59
def prefixEnd_3317761 : Nat := 4983230072969 + 3 ^ 40 * 3317761 * 2
def baseEnd_3317761 : Nat := 567868696580566326176467

theorem tailTrace_3317761 : CollatzResearch.WordTrace tailWord_3317761 prefixEnd_3317761 567868696580566326176467 := by
  unfold tailWord_3317761
  simp only [CollatzResearch.WordTrace]
  refine ⟨121008684933326000312313137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80672456622217333541542091 121008684933326000312313137)
  ·
    refine ⟨90756513699994500234234853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121008684933326000312313137 90756513699994500234234853)
    ·
      refine ⟨17016846318748968793919035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90756513699994500234234853 17016846318748968793919035)
      ·
        refine ⟨25525269478123453190878553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17016846318748968793919035 25525269478123453190878553)
        ·
          refine ⟨19143952108592589893158915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25525269478123453190878553 19143952108592589893158915)
          ·
            refine ⟨28715928162888884839738373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19143952108592589893158915 28715928162888884839738373)
            ·
              refine ⟨5384236530541665907450945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28715928162888884839738373 5384236530541665907450945)
              ·
                refine ⟨4038177397906249430588209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5384236530541665907450945 4038177397906249430588209)
                ·
                  refine ⟨3028633048429687072941157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4038177397906249430588209 3028633048429687072941157)
                  ·
                    refine ⟨567868696580566326176467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3028633048429687072941157 567868696580566326176467)
                    ·
                      rfl

theorem cell23_3317761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_3317761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317761 prefixEnd_3317761 := by exact prefixLift 3317761
  have htrace : WordTrace (prefixWord ++ tailWord_3317761) baseStart_3317761 baseEnd_3317761 := by
    simpa [prefixWord, tailWord_3317761, baseEnd_3317761] using wordTrace_append hprefix tailTrace_3317761
  have hstable : (prefixWord ++ tailWord_3317761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317761).length < 2 ^ (prefixWord ++ tailWord_3317761).sum := by decide
  have hdescent : baseEnd_3317761 < baseStart_3317761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317781 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_3317781 : Nat := 118140960795 + 3317781 * 2 ^ 59
def prefixEnd_3317781 : Nat := 4983230072969 + 3 ^ 40 * 3317781 * 2
def baseEnd_3317781 : Nat := 1703616359354788900279309

theorem tailTrace_3317781 : CollatzResearch.WordTrace tailWord_3317781 prefixEnd_3317781 1703616359354788900279309 := by
  unfold tailWord_3317781
  simp only [CollatzResearch.WordTrace]
  refine ⟨121009414393253543728041197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80672942928835695818694131 121009414393253543728041197)
  ·
    refine ⟨45378530397470078898015449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121009414393253543728041197 45378530397470078898015449)
    ·
      refine ⟨34033897798102559173511587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45378530397470078898015449 34033897798102559173511587)
      ·
        refine ⟨51050846697153838760267381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34033897798102559173511587 51050846697153838760267381)
        ·
          refine ⟨4786016877858172383775067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51050846697153838760267381 4786016877858172383775067)
          ·
            refine ⟨7179025316787258575662601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4786016877858172383775067 7179025316787258575662601)
            ·
              refine ⟨5384268987590443931746951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7179025316787258575662601 5384268987590443931746951)
              ·
                refine ⟨8076403481385665897620427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5384268987590443931746951 8076403481385665897620427)
                ·
                  refine ⟨12114605222078498846430641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8076403481385665897620427 12114605222078498846430641)
                  ·
                    refine ⟨9085953916558874134822981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12114605222078498846430641 9085953916558874134822981)
                    ·
                      refine ⟨1703616359354788900279309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9085953916558874134822981 1703616359354788900279309)
                      ·
                        rfl

theorem cell23_3317781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_3317781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317781 prefixEnd_3317781 := by exact prefixLift 3317781
  have htrace : WordTrace (prefixWord ++ tailWord_3317781) baseStart_3317781 baseEnd_3317781 := by
    simpa [prefixWord, tailWord_3317781, baseEnd_3317781] using wordTrace_append hprefix tailTrace_3317781
  have hstable : (prefixWord ++ tailWord_3317781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317781).length < 2 ^ (prefixWord ++ tailWord_3317781).sum := by decide
  have hdescent : baseEnd_3317781 < baseStart_3317781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317802 : List Nat := [3, 1, 4, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_3317802 : Nat := 118140960795 + 3317802 * 2 ^ 59
def prefixEnd_3317802 : Nat := 4983230072969 + 3 ^ 40 * 3317802 * 2
def baseEnd_3317802 : Nat := 1703627142448533318116713

theorem tailTrace_3317802 : CollatzResearch.WordTrace tailWord_3317802 prefixEnd_3317802 1703627142448533318116713 := by
  unfold tailWord_3317802
  simp only [CollatzResearch.WordTrace]
  refine ⟨30252545081544366078638915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80673453550784976209703773 30252545081544366078638915)
  ·
    refine ⟨45378817622316549117958373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30252545081544366078638915 45378817622316549117958373)
    ·
      refine ⟨8508528304184352959617195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45378817622316549117958373 8508528304184352959617195)
      ·
        refine ⟨12762792456276529439425793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8508528304184352959617195 12762792456276529439425793)
        ·
          refine ⟨9572094342207397079569345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12762792456276529439425793 9572094342207397079569345)
          ·
            refine ⟨7179070756655547809677009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9572094342207397079569345 7179070756655547809677009)
            ·
              refine ⟨5384303067491660857257757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7179070756655547809677009 5384303067491660857257757)
              ·
                refine ⟨2019113650309372821471659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5384303067491660857257757 2019113650309372821471659)
                ·
                  refine ⟨3028670475464059232207489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019113650309372821471659 3028670475464059232207489)
                  ·
                    refine ⟨2271502856598044424155617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3028670475464059232207489 2271502856598044424155617)
                    ·
                      refine ⟨1703627142448533318116713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2271502856598044424155617 1703627142448533318116713)
                      ·
                        rfl

theorem cell23_3317802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_3317802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317802 prefixEnd_3317802 := by exact prefixLift 3317802
  have htrace : WordTrace (prefixWord ++ tailWord_3317802) baseStart_3317802 baseEnd_3317802 := by
    simpa [prefixWord, tailWord_3317802, baseEnd_3317802] using wordTrace_append hprefix tailTrace_3317802
  have hstable : (prefixWord ++ tailWord_3317802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317802).length < 2 ^ (prefixWord ++ tailWord_3317802).sum := by decide
  have hdescent : baseEnd_3317802 < baseStart_3317802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317807 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 4]
def baseStart_3317807 : Nat := 118140960795 + 3317807 * 2 ^ 59
def prefixEnd_3317807 : Nat := 4983230072969 + 3 ^ 40 * 3317807 * 2
def baseEnd_3317807 : Nat := 1703629709851805798554189

theorem tailTrace_3317807 : CollatzResearch.WordTrace tailWord_3317807 prefixEnd_3317807 1703629709851805798554189 := by
  unfold tailWord_3317807
  simp only [CollatzResearch.WordTrace]
  refine ⟨121010362691159350168487675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80673575127439566778991783 121010362691159350168487675)
  ·
    refine ⟨181515544036739025252731513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121010362691159350168487675 181515544036739025252731513)
    ·
      refine ⟨136136658027554268939548635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181515544036739025252731513 136136658027554268939548635)
      ·
        refine ⟨204204987041331403409322953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136136658027554268939548635 204204987041331403409322953)
        ·
          refine ⟨153153740280998552556992215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204204987041331403409322953 153153740280998552556992215)
          ·
            refine ⟨229730610421497828835488323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153153740280998552556992215 229730610421497828835488323)
            ·
              refine ⟨344595915632246743253232485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229730610421497828835488323 344595915632246743253232485)
              ·
                refine ⟨64611734181046264359981091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344595915632246743253232485 64611734181046264359981091)
                ·
                  refine ⟨96917601271569396539971637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64611734181046264359981091 96917601271569396539971637)
                  ·
                    refine ⟨9086025119209630925622341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96917601271569396539971637 9086025119209630925622341)
                    ·
                      refine ⟨1703629709851805798554189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9086025119209630925622341 1703629709851805798554189)
                      ·
                        rfl

theorem cell23_3317807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_3317807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317807 prefixEnd_3317807 := by exact prefixLift 3317807
  have htrace : WordTrace (prefixWord ++ tailWord_3317807) baseStart_3317807 baseEnd_3317807 := by
    simpa [prefixWord, tailWord_3317807, baseEnd_3317807] using wordTrace_append hprefix tailTrace_3317807
  have hstable : (prefixWord ++ tailWord_3317807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317807).length < 2 ^ (prefixWord ++ tailWord_3317807).sum := by decide
  have hdescent : baseEnd_3317807 < baseStart_3317807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317812 : List Nat := [2, 5, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_3317812 : Nat := 118140960795 + 3317812 * 2 ^ 59
def prefixEnd_3317812 : Nat := 4983230072969 + 3 ^ 40 * 3317812 * 2
def baseEnd_3317812 : Nat := 567877425751692759663889

theorem tailTrace_3317812 : CollatzResearch.WordTrace tailWord_3317812 prefixEnd_3317812 567877425751692759663889 := by
  unfold tailWord_3317812
  simp only [CollatzResearch.WordTrace]
  refine ⟨60505272528070618011209845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80673696704094157348279793 60505272528070618011209845)
  ·
    refine ⟨5672369299506620438550923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60505272528070618011209845 5672369299506620438550923)
    ·
      refine ⟨8508553949259930657826385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5672369299506620438550923 8508553949259930657826385)
      ·
        refine ⟨6381415461944947993369789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8508553949259930657826385 6381415461944947993369789)
        ·
          refine ⟨2393030798229355497513671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6381415461944947993369789 2393030798229355497513671)
          ·
            refine ⟨3589546197344033246270507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393030798229355497513671 3589546197344033246270507)
            ·
              refine ⟨5384319296016049869405761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589546197344033246270507 5384319296016049869405761)
              ·
                refine ⟨4038239472012037402054321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5384319296016049869405761 4038239472012037402054321)
                ·
                  refine ⟨3028679604009028051540741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4038239472012037402054321 3028679604009028051540741)
                  ·
                    refine ⟨567877425751692759663889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3028679604009028051540741 567877425751692759663889)
                    ·
                      rfl

theorem cell23_3317812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_3317812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317812 prefixEnd_3317812 := by exact prefixLift 3317812
  have htrace : WordTrace (prefixWord ++ tailWord_3317812) baseStart_3317812 baseEnd_3317812 := by
    simpa [prefixWord, tailWord_3317812, baseEnd_3317812] using wordTrace_append hprefix tailTrace_3317812
  have hstable : (prefixWord ++ tailWord_3317812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317812).length < 2 ^ (prefixWord ++ tailWord_3317812).sum := by decide
  have hdescent : baseEnd_3317812 < baseStart_3317812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317827 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 5]
def baseStart_3317827 : Nat := 118140960795 + 3317827 * 2 ^ 59
def prefixEnd_3317827 : Nat := 4983230072969 + 3 ^ 40 * 3317827 * 2
def baseEnd_3317827 : Nat := 1703639979464895720304097

theorem tailTrace_3317827 : CollatzResearch.WordTrace tailWord_3317827 prefixEnd_3317827 1703639979464895720304097 := by
  unfold tailWord_3317827
  simp only [CollatzResearch.WordTrace]
  refine ⟨121011092151086893584215735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80674061434057929056143823 121011092151086893584215735)
  ·
    refine ⟨181516638226630340376323603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121011092151086893584215735 181516638226630340376323603)
    ·
      refine ⟨272274957339945510564485405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181516638226630340376323603 272274957339945510564485405)
      ·
        refine ⟨102103109002479566461682027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272274957339945510564485405 102103109002479566461682027)
        ·
          refine ⟨153154663503719349692523041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102103109002479566461682027 153154663503719349692523041)
          ·
            refine ⟨114865997627789512269392281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153154663503719349692523041 114865997627789512269392281)
            ·
              refine ⟨86149498220842134202044211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114865997627789512269392281 86149498220842134202044211)
              ·
                refine ⟨129224247331263201303066317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86149498220842134202044211 129224247331263201303066317)
                ·
                  refine ⟨48459092749223700488649869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129224247331263201303066317 48459092749223700488649869)
                  ·
                    refine ⟨18172159780958887683243701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48459092749223700488649869 18172159780958887683243701)
                    ·
                      refine ⟨1703639979464895720304097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18172159780958887683243701 1703639979464895720304097)
                      ·
                        rfl

theorem cell23_3317827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_3317827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317827 prefixEnd_3317827 := by exact prefixLift 3317827
  have htrace : WordTrace (prefixWord ++ tailWord_3317827) baseStart_3317827 baseEnd_3317827 := by
    simpa [prefixWord, tailWord_3317827, baseEnd_3317827] using wordTrace_append hprefix tailTrace_3317827
  have hstable : (prefixWord ++ tailWord_3317827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317827).length < 2 ^ (prefixWord ++ tailWord_3317827).sum := by decide
  have hdescent : baseEnd_3317827 < baseStart_3317827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317844 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_3317844 : Nat := 118140960795 + 3317844 * 2 ^ 59
def prefixEnd_3317844 : Nat := 4983230072969 + 3 ^ 40 * 3317844 * 2
def baseEnd_3317844 : Nat := 1703648708636022153791519

theorem tailTrace_3317844 : CollatzResearch.WordTrace tailWord_3317844 prefixEnd_3317844 1703648708636022153791519 := by
  unfold tailWord_3317844
  simp only [CollatzResearch.WordTrace]
  refine ⟨60505856096012652743792293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80674474794683536991723057 60505856096012652743792293)
  ·
    refine ⟨11344848018002372389461055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60505856096012652743792293 11344848018002372389461055)
    ·
      refine ⟨17017272027003558584191583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11344848018002372389461055 17017272027003558584191583)
      ·
        refine ⟨25525908040505337876287375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17017272027003558584191583 25525908040505337876287375)
        ·
          refine ⟨38288862060758006814431063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25525908040505337876287375 38288862060758006814431063)
          ·
            refine ⟨57433293091137010221646595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38288862060758006814431063 57433293091137010221646595)
            ·
              refine ⟨86149939636705515332469893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57433293091137010221646595 86149939636705515332469893)
              ·
                refine ⟨16153113681882284124838105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86149939636705515332469893 16153113681882284124838105)
                ·
                  refine ⟨12114835261411713093628579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16153113681882284124838105 12114835261411713093628579)
                  ·
                    refine ⟨18172252892117569640442869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12114835261411713093628579 18172252892117569640442869)
                    ·
                      refine ⟨1703648708636022153791519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18172252892117569640442869 1703648708636022153791519)
                      ·
                        rfl

theorem cell23_3317844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_3317844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317844 prefixEnd_3317844 := by exact prefixLift 3317844
  have htrace : WordTrace (prefixWord ++ tailWord_3317844) baseStart_3317844 baseEnd_3317844 := by
    simpa [prefixWord, tailWord_3317844, baseEnd_3317844] using wordTrace_append hprefix tailTrace_3317844
  have hstable : (prefixWord ++ tailWord_3317844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317844).length < 2 ^ (prefixWord ++ tailWord_3317844).sum := by decide
  have hdescent : baseEnd_3317844 < baseStart_3317844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317867 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 6]
def baseStart_3317867 : Nat := 118140960795 + 3317867 * 2 ^ 59
def prefixEnd_3317867 : Nat := 4983230072969 + 3 ^ 40 * 3317867 * 2
def baseEnd_3317867 : Nat := 1703660518691075563803913

theorem tailTrace_3317867 : CollatzResearch.WordTrace tailWord_3317867 prefixEnd_3317867 1703660518691075563803913 := by
  unfold tailWord_3317867
  simp only [CollatzResearch.WordTrace]
  refine ⟨121012551070941980415671855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80675034047294653610447903 121012551070941980415671855)
  ·
    refine ⟨181518826606412970623507783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121012551070941980415671855 181518826606412970623507783)
    ·
      refine ⟨272278239909619455935261675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181518826606412970623507783 272278239909619455935261675)
      ·
        refine ⟨408417359864429183902892513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272278239909619455935261675 408417359864429183902892513)
        ·
          refine ⟨306313019898321887927169385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408417359864429183902892513 306313019898321887927169385)
          ·
            refine ⟨229734764923741415945377039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306313019898321887927169385 229734764923741415945377039)
            ·
              refine ⟨344602147385612123918065559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229734764923741415945377039 344602147385612123918065559)
              ·
                refine ⟨516903221078418185877098339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344602147385612123918065559 516903221078418185877098339)
                ·
                  refine ⟨775354831617627278815647509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516903221078418185877098339 775354831617627278815647509)
                  ·
                    refine ⟨36344757732076278694483477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 775354831617627278815647509 36344757732076278694483477)
                    ·
                      refine ⟨1703660518691075563803913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36344757732076278694483477 1703660518691075563803913)
                      ·
                        rfl

theorem cell23_3317867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_3317867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317867 prefixEnd_3317867 := by exact prefixLift 3317867
  have htrace : WordTrace (prefixWord ++ tailWord_3317867) baseStart_3317867 baseEnd_3317867 := by
    simpa [prefixWord, tailWord_3317867, baseEnd_3317867] using wordTrace_append hprefix tailTrace_3317867
  have hstable : (prefixWord ++ tailWord_3317867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317867).length < 2 ^ (prefixWord ++ tailWord_3317867).sum := by decide
  have hdescent : baseEnd_3317867 < baseStart_3317867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317881 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 7]
def baseStart_3317881 : Nat := 118140960795 + 3317881 * 2 ^ 59
def prefixEnd_3317881 : Nat := 4983230072969 + 3 ^ 40 * 3317881 * 2
def baseEnd_3317881 : Nat := 189296411935582056558761

theorem tailTrace_3317881 : CollatzResearch.WordTrace tailWord_3317881 prefixEnd_3317881 189296411935582056558761 := by
  unfold tailWord_3317881
  simp only [CollatzResearch.WordTrace]
  refine ⟨121013061692891260806681497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80675374461927507204454331 121013061692891260806681497)
  ·
    refine ⟨90759796269668445605011123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121013061692891260806681497 90759796269668445605011123)
    ·
      refine ⟨136139694404502668407516685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90759796269668445605011123 136139694404502668407516685)
      ·
        refine ⟨51052385401688500652818757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136139694404502668407516685 51052385401688500652818757)
        ·
          refine ⟨9572322262816593872403517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51052385401688500652818757 9572322262816593872403517)
          ·
            refine ⟨3589620848556222702151319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9572322262816593872403517 3589620848556222702151319)
            ·
              refine ⟨5384431272834334053226979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589620848556222702151319 5384431272834334053226979)
              ·
                refine ⟨8076646909251501079840469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5384431272834334053226979 8076646909251501079840469)
                ·
                  refine ⟨189296411935582056558761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8076646909251501079840469 189296411935582056558761)
                  ·
                    rfl

theorem cell23_3317881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 7].length) (baseStart_3317881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317881 prefixEnd_3317881 := by exact prefixLift 3317881
  have htrace : WordTrace (prefixWord ++ tailWord_3317881) baseStart_3317881 baseEnd_3317881 := by
    simpa [prefixWord, tailWord_3317881, baseEnd_3317881] using wordTrace_append hprefix tailTrace_3317881
  have hstable : (prefixWord ++ tailWord_3317881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317881).length < 2 ^ (prefixWord ++ tailWord_3317881).sum := by decide
  have hdescent : baseEnd_3317881 < baseStart_3317881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317991 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3317991 : Nat := 118140960795 + 3317991 * 2 ^ 59
def prefixEnd_3317991 : Nat := 4983230072969 + 3 ^ 40 * 3317991 * 2
def baseEnd_3317991 : Nat := 1703724190292233078653343

theorem tailTrace_3317991 : CollatzResearch.WordTrace tailWord_3317991 prefixEnd_3317991 1703724190292233078653343 := by
  unfold tailWord_3317991
  simp only [CollatzResearch.WordTrace]
  refine ⟨121017073722492749593185827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80678049148328499728790551 121017073722492749593185827)
  ·
    refine ⟨181525610583739124389778741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121017073722492749593185827 181525610583739124389778741)
    ·
      refine ⟨17018025992225542911541757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181525610583739124389778741 17018025992225542911541757)
      ·
        refine ⟨6381759747084578591828159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17018025992225542911541757 6381759747084578591828159)
        ·
          refine ⟨9572639620626867887742239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6381759747084578591828159 9572639620626867887742239)
          ·
            refine ⟨14358959430940301831613359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9572639620626867887742239 14358959430940301831613359)
            ·
              refine ⟨21538439146410452747420039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14358959430940301831613359 21538439146410452747420039)
              ·
                refine ⟨32307658719615679121130059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21538439146410452747420039 32307658719615679121130059)
                ·
                  refine ⟨48461488079423518681695089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32307658719615679121130059 48461488079423518681695089)
                  ·
                    refine ⟨36346116059567639011271317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48461488079423518681695089 36346116059567639011271317)
                    ·
                      refine ⟨1703724190292233078653343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36346116059567639011271317 1703724190292233078653343)
                      ·
                        rfl

theorem cell23_3317991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3317991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3317991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3317991 prefixEnd_3317991 := by exact prefixLift 3317991
  have htrace : WordTrace (prefixWord ++ tailWord_3317991) baseStart_3317991 baseEnd_3317991 := by
    simpa [prefixWord, tailWord_3317991, baseEnd_3317991] using wordTrace_append hprefix tailTrace_3317991
  have hstable : (prefixWord ++ tailWord_3317991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317991).length < 2 ^ (prefixWord ++ tailWord_3317991).sum := by decide
  have hdescent : baseEnd_3317991 < baseStart_3317991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318048 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 4, 4]
def baseStart_3318048 : Nat := 118140960795 + 3318048 * 2 ^ 59
def prefixEnd_3318048 : Nat := 4983230072969 + 3 ^ 40 * 3318048 * 2
def baseEnd_3318048 : Nat := 567917819563179785213527

theorem tailTrace_3318048 : CollatzResearch.WordTrace tailWord_3318048 prefixEnd_3318048 567917819563179785213527 := by
  unfold tailWord_3318048
  simp only [CollatzResearch.WordTrace]
  refine ⟨60509576341643124164005399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80679435122190832218673865 60509576341643124164005399)
  ·
    refine ⟨90764364512464686246008099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60509576341643124164005399 90764364512464686246008099)
    ·
      refine ⟨136146546768697029369012149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90764364512464686246008099 136146546768697029369012149)
      ·
        refine ⟨12763738759565346503344889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136146546768697029369012149 12763738759565346503344889)
        ·
          refine ⟨9572804069674009877508667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12763738759565346503344889 9572804069674009877508667)
          ·
            refine ⟨14359206104511014816263001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9572804069674009877508667 14359206104511014816263001)
            ·
              refine ⟨10769404578383261112197251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14359206104511014816263001 10769404578383261112197251)
              ·
                refine ⟨16154106867574891668295877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10769404578383261112197251 16154106867574891668295877)
                ·
                  refine ⟨3028895037670292187805477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16154106867574891668295877 3028895037670292187805477)
                  ·
                    refine ⟨567917819563179785213527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3028895037670292187805477 567917819563179785213527)
                    ·
                      rfl

theorem cell23_3318048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 4, 4].length) (baseStart_3318048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318048 prefixEnd_3318048 := by exact prefixLift 3318048
  have htrace : WordTrace (prefixWord ++ tailWord_3318048) baseStart_3318048 baseEnd_3318048 := by
    simpa [prefixWord, tailWord_3318048, baseEnd_3318048] using wordTrace_append hprefix tailTrace_3318048
  have hstable : (prefixWord ++ tailWord_3318048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318048).length < 2 ^ (prefixWord ++ tailWord_3318048).sum := by decide
  have hdescent : baseEnd_3318048 < baseStart_3318048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318065 : List Nat := [1, 2, 2, 3, 4, 1, 1, 3, 2, 4]
def baseStart_3318065 : Nat := 118140960795 + 3318065 * 2 ^ 59
def prefixEnd_3318065 : Nat := 4983230072969 + 3 ^ 40 * 3318065 * 2
def baseEnd_3318065 : Nat := 567920729286888596376001

theorem tailTrace_3318065 : CollatzResearch.WordTrace tailWord_3318065 prefixEnd_3318065 567920729286888596376001 := by
  unfold tailWord_3318065
  simp only [CollatzResearch.WordTrace]
  refine ⟨121019772724224660231379649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80679848482816440154253099 121019772724224660231379649)
  ·
    refine ⟨90764829543168495173534737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121019772724224660231379649 90764829543168495173534737)
    ·
      refine ⟨68073622157376371380151053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90764829543168495173534737 68073622157376371380151053)
      ·
        refine ⟨25527608309016139267556645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68073622157376371380151053 25527608309016139267556645)
        ·
          refine ⟨4786426557940526112666871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25527608309016139267556645 4786426557940526112666871)
          ·
            refine ⟨7179639836910789169000307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4786426557940526112666871 7179639836910789169000307)
            ·
              refine ⟨10769459755366183753500461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7179639836910789169000307 10769459755366183753500461)
              ·
                refine ⟨4038547408262318907562673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10769459755366183753500461 4038547408262318907562673)
                ·
                  refine ⟨3028910556196739180672005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4038547408262318907562673 3028910556196739180672005)
                  ·
                    refine ⟨567920729286888596376001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3028910556196739180672005 567920729286888596376001)
                    ·
                      rfl

theorem cell23_3318065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_3318065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318065 prefixEnd_3318065 := by exact prefixLift 3318065
  have htrace : WordTrace (prefixWord ++ tailWord_3318065) baseStart_3318065 baseEnd_3318065 := by
    simpa [prefixWord, tailWord_3318065, baseEnd_3318065] using wordTrace_append hprefix tailTrace_3318065
  have hstable : (prefixWord ++ tailWord_3318065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318065).length < 2 ^ (prefixWord ++ tailWord_3318065).sum := by decide
  have hdescent : baseEnd_3318065 < baseStart_3318065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318068 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_3318068 : Nat := 118140960795 + 3318068 * 2 ^ 59
def prefixEnd_3318068 : Nat := 4983230072969 + 3 ^ 40 * 3318068 * 2
def baseEnd_3318068 : Nat := 1703763728302629277390489

theorem tailTrace_3318068 : CollatzResearch.WordTrace tailWord_3318068 prefixEnd_3318068 1703763728302629277390489 := by
  unfold tailWord_3318068
  simp only [CollatzResearch.WordTrace]
  refine ⟨60509941071606895871869429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80679921428809194495825905 60509941071606895871869429)
  ·
    refine ⟨5672806975463146487987759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60509941071606895871869429 5672806975463146487987759)
    ·
      refine ⟨8509210463194719731981639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5672806975463146487987759 8509210463194719731981639)
      ·
        refine ⟨12763815694792079597972459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8509210463194719731981639 12763815694792079597972459)
        ·
          refine ⟨19145723542188119396958689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12763815694792079597972459 19145723542188119396958689)
          ·
            refine ⟨14359292656641089547719017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19145723542188119396958689 14359292656641089547719017)
            ·
              refine ⟨10769469492480817160789263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14359292656641089547719017 10769469492480817160789263)
              ·
                refine ⟨16154204238721225741183895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10769469492480817160789263 16154204238721225741183895)
                ·
                  refine ⟨24231306358081838611775843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16154204238721225741183895 24231306358081838611775843)
                  ·
                    refine ⟨36346959537122757917663765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24231306358081838611775843 36346959537122757917663765)
                    ·
                      refine ⟨1703763728302629277390489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36346959537122757917663765 1703763728302629277390489)
                      ·
                        rfl

theorem cell23_3318068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_3318068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318068 prefixEnd_3318068 := by exact prefixLift 3318068
  have htrace : WordTrace (prefixWord ++ tailWord_3318068) baseStart_3318068 baseEnd_3318068 := by
    simpa [prefixWord, tailWord_3318068, baseEnd_3318068] using wordTrace_append hprefix tailTrace_3318068
  have hstable : (prefixWord ++ tailWord_3318068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318068).length < 2 ^ (prefixWord ++ tailWord_3318068).sum := by decide
  have hdescent : baseEnd_3318068 < baseStart_3318068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318071 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 3]
def baseStart_3318071 : Nat := 118140960795 + 3318071 * 2 ^ 59
def prefixEnd_3318071 : Nat := 4983230072969 + 3 ^ 40 * 3318071 * 2
def baseEnd_3318071 : Nat := 1703765268744592765652975

theorem tailTrace_3318071 : CollatzResearch.WordTrace tailWord_3318071 prefixEnd_3318071 1703765268744592765652975 := by
  unfold tailWord_3318071
  simp only [CollatzResearch.WordTrace]
  refine ⟨121019991562202923256098067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80679994374801948837398711 121019991562202923256098067)
  ·
    refine ⟨181529987343304384884147101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121019991562202923256098067 181529987343304384884147101)
    ·
      refine ⟨68073745253739144331555163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181529987343304384884147101 68073745253739144331555163)
      ·
        refine ⟨102110617880608716497332745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68073745253739144331555163 102110617880608716497332745)
        ·
          refine ⟨76582963410456537372999559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102110617880608716497332745 76582963410456537372999559)
          ·
            refine ⟨114874445115684806059499339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76582963410456537372999559 114874445115684806059499339)
            ·
              refine ⟨172311667673527209089249009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114874445115684806059499339 172311667673527209089249009)
              ·
                refine ⟨129233750755145406816936757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172311667673527209089249009 129233750755145406816936757)
                ·
                  refine ⟨12115664133294881889087821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129233750755145406816936757 12115664133294881889087821)
                  ·
                    refine ⟨4543374049985580708407933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12115664133294881889087821 4543374049985580708407933)
                    ·
                      refine ⟨1703765268744592765652975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4543374049985580708407933 1703765268744592765652975)
                      ·
                        rfl

theorem cell23_3318071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_3318071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318071 prefixEnd_3318071 := by exact prefixLift 3318071
  have htrace : WordTrace (prefixWord ++ tailWord_3318071) baseStart_3318071 baseEnd_3318071 := by
    simpa [prefixWord, tailWord_3318071, baseEnd_3318071] using wordTrace_append hprefix tailTrace_3318071
  have hstable : (prefixWord ++ tailWord_3318071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318071).length < 2 ^ (prefixWord ++ tailWord_3318071).sum := by decide
  have hdescent : baseEnd_3318071 < baseStart_3318071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318088 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 6, 1, 3]
def baseStart_3318088 : Nat := 118140960795 + 3318088 * 2 ^ 59
def prefixEnd_3318088 : Nat := 4983230072969 + 3 ^ 40 * 3318088 * 2
def baseEnd_3318088 : Nat := 1703773997915719199140397

theorem tailTrace_3318088 : CollatzResearch.WordTrace tailWord_3318088 prefixEnd_3318088 1703773997915719199140397 := by
  unfold tailWord_3318088
  simp only [CollatzResearch.WordTrace]
  refine ⟨60510305801570667579733459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80680407735427556772977945 60510305801570667579733459)
  ·
    refine ⟨90765458702356001369600189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60510305801570667579733459 90765458702356001369600189)
    ·
      refine ⟨34037047013383500513600071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90765458702356001369600189 34037047013383500513600071)
      ·
        refine ⟨51055570520075250770400107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34037047013383500513600071 51055570520075250770400107)
        ·
          refine ⟨76583355780112876155600161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51055570520075250770400107 76583355780112876155600161)
          ·
            refine ⟨57437516835084657116700121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76583355780112876155600161 57437516835084657116700121)
            ·
              refine ⟨43078137626313492837525091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57437516835084657116700121 43078137626313492837525091)
              ·
                refine ⟨64617206439470239256287637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43078137626313492837525091 64617206439470239256287637)
                ·
                  refine ⟨3028931551850167465138483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64617206439470239256287637 3028931551850167465138483)
                  ·
                    refine ⟨4543397327775251197707725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3028931551850167465138483 4543397327775251197707725)
                    ·
                      refine ⟨1703773997915719199140397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4543397327775251197707725 1703773997915719199140397)
                      ·
                        rfl

theorem cell23_3318088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_3318088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318088 prefixEnd_3318088 := by exact prefixLift 3318088
  have htrace : WordTrace (prefixWord ++ tailWord_3318088) baseStart_3318088 baseEnd_3318088 := by
    simpa [prefixWord, tailWord_3318088, baseEnd_3318088] using wordTrace_append hprefix tailTrace_3318088
  have hstable : (prefixWord ++ tailWord_3318088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318088).length < 2 ^ (prefixWord ++ tailWord_3318088).sum := by decide
  have hdescent : baseEnd_3318088 < baseStart_3318088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318111 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 4]
def baseStart_3318111 : Nat := 118140960795 + 3318111 * 2 ^ 59
def prefixEnd_3318111 : Nat := 4983230072969 + 3 ^ 40 * 3318111 * 2
def baseEnd_3318111 : Nat := 1703785807970772609152791

theorem tailTrace_3318111 : CollatzResearch.WordTrace tailWord_3318111 prefixEnd_3318111 1703785807970772609152791 := by
  unfold tailWord_3318111
  simp only [CollatzResearch.WordTrace]
  refine ⟨121021450482058010087554187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80680966988038673391702791 121021450482058010087554187)
  ·
    refine ⟨181532175723087015131331281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121021450482058010087554187 181532175723087015131331281)
    ·
      refine ⟨136149131792315261348498461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181532175723087015131331281 136149131792315261348498461)
      ·
        refine ⟨51055924422118223005686923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136149131792315261348498461 51055924422118223005686923)
        ·
          refine ⟨76583886633177334508530385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51055924422118223005686923 76583886633177334508530385)
          ·
            refine ⟨57437914974883000881397789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76583886633177334508530385 57437914974883000881397789)
            ·
              refine ⟨21539218115581125330524171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57437914974883000881397789 21539218115581125330524171)
              ·
                refine ⟨32308827173371687995786257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21539218115581125330524171 32308827173371687995786257)
                ·
                  refine ⟨24231620380028765996839693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32308827173371687995786257 24231620380028765996839693)
                  ·
                    refine ⟨9086857642510787248814885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24231620380028765996839693 9086857642510787248814885)
                    ·
                      refine ⟨1703785807970772609152791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9086857642510787248814885 1703785807970772609152791)
                      ·
                        rfl

theorem cell23_3318111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_3318111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318111 prefixEnd_3318111 := by exact prefixLift 3318111
  have htrace : WordTrace (prefixWord ++ tailWord_3318111) baseStart_3318111 baseEnd_3318111 := by
    simpa [prefixWord, tailWord_3318111, baseEnd_3318111] using wordTrace_append hprefix tailTrace_3318111
  have hstable : (prefixWord ++ tailWord_3318111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318111).length < 2 ^ (prefixWord ++ tailWord_3318111).sum := by decide
  have hdescent : baseEnd_3318111 < baseStart_3318111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318121 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 2, 6]
def baseStart_3318121 : Nat := 118140960795 + 3318121 * 2 ^ 59
def prefixEnd_3318121 : Nat := 4983230072969 + 3 ^ 40 * 3318121 * 2
def baseEnd_3318121 : Nat := 567930314259105856675915

theorem tailTrace_3318121 : CollatzResearch.WordTrace tailWord_3318121 prefixEnd_3318121 567930314259105856675915 := by
  unfold tailWord_3318121
  simp only [CollatzResearch.WordTrace]
  refine ⟨121021815212021781795418217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80681210141347854530278811 121021815212021781795418217)
  ·
    refine ⟨90766361409016336346563663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121021815212021781795418217 90766361409016336346563663)
    ·
      refine ⟨136149542113524504519845495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90766361409016336346563663 136149542113524504519845495)
      ·
        refine ⟨204224313170286756779768243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136149542113524504519845495 204224313170286756779768243)
        ·
          refine ⟨306336469755430135169652365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204224313170286756779768243 306336469755430135169652365)
          ·
            refine ⟨114876176158286300688619637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306336469755430135169652365 114876176158286300688619637)
            ·
              refine ⟨10769641514839340689558091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114876176158286300688619637 10769641514839340689558091)
              ·
                refine ⟨16154462272259011034337137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10769641514839340689558091 16154462272259011034337137)
                ·
                  refine ⟨12115846704194258275752853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16154462272259011034337137 12115846704194258275752853)
                  ·
                    refine ⟨567930314259105856675915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12115846704194258275752853 567930314259105856675915)
                    ·
                      rfl

theorem cell23_3318121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 6].length) (baseStart_3318121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318121 prefixEnd_3318121 := by exact prefixLift 3318121
  have htrace : WordTrace (prefixWord ++ tailWord_3318121) baseStart_3318121 baseEnd_3318121 := by
    simpa [prefixWord, tailWord_3318121, baseEnd_3318121] using wordTrace_append hprefix tailTrace_3318121
  have hstable : (prefixWord ++ tailWord_3318121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318121).length < 2 ^ (prefixWord ++ tailWord_3318121).sum := by decide
  have hdescent : baseEnd_3318121 < baseStart_3318121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318122 : List Nat := [3, 1, 3, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3318122 : Nat := 118140960795 + 3318122 * 2 ^ 59
def prefixEnd_3318122 : Nat := 4983230072969 + 3 ^ 40 * 3318122 * 2
def baseEnd_3318122 : Nat := 1703791456257972066115241

theorem tailTrace_3318122 : CollatzResearch.WordTrace tailWord_3318122 prefixEnd_3318122 1703791456257972066115241 := by
  unfold tailWord_3318122
  simp only [CollatzResearch.WordTrace]
  refine ⟨30255462921254539741551155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80681234456678772644136413 30255462921254539741551155)
  ·
    refine ⟨45383194381881809612326733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30255462921254539741551155 45383194381881809612326733)
    ·
      refine ⟨17018697893205678604622525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45383194381881809612326733 17018697893205678604622525)
      ·
        refine ⟨6382011709952129476733447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17018697893205678604622525 6382011709952129476733447)
        ·
          refine ⟨9573017564928194215100171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6382011709952129476733447 9573017564928194215100171)
          ·
            refine ⟨14359526347392291322650257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9573017564928194215100171 14359526347392291322650257)
            ·
              refine ⟨10769644760544218491987693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14359526347392291322650257 10769644760544218491987693)
              ·
                refine ⟨4038616785204081934495385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10769644760544218491987693 4038616785204081934495385)
                ·
                  refine ⟨3028962588903061450871539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4038616785204081934495385 3028962588903061450871539)
                  ·
                    refine ⟨4543443883354592176307309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3028962588903061450871539 4543443883354592176307309)
                    ·
                      refine ⟨1703791456257972066115241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4543443883354592176307309 1703791456257972066115241)
                      ·
                        rfl

theorem cell23_3318122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3318122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318122 prefixEnd_3318122 := by exact prefixLift 3318122
  have htrace : WordTrace (prefixWord ++ tailWord_3318122) baseStart_3318122 baseEnd_3318122 := by
    simpa [prefixWord, tailWord_3318122, baseEnd_3318122] using wordTrace_append hprefix tailTrace_3318122
  have hstable : (prefixWord ++ tailWord_3318122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318122).length < 2 ^ (prefixWord ++ tailWord_3318122).sum := by decide
  have hdescent : baseEnd_3318122 < baseStart_3318122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318151 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 9]
def baseStart_3318151 : Nat := 118140960795 + 3318151 * 2 ^ 59
def prefixEnd_3318151 : Nat := 4983230072969 + 3 ^ 40 * 3318151 * 2
def baseEnd_3318151 : Nat := 189311816355216939183623

theorem tailTrace_3318151 : CollatzResearch.WordTrace tailWord_3318151 prefixEnd_3318151 189311816355216939183623 := by
  unfold tailWord_3318151
  simp only [CollatzResearch.WordTrace]
  refine ⟨121022909401913096919010307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80681939601275397946006871 121022909401913096919010307)
  ·
    refine ⟨181534364102869645378515461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121022909401913096919010307 181534364102869645378515461)
    ·
      refine ⟨34037693269288058508471649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181534364102869645378515461 34037693269288058508471649)
      ·
        refine ⟨25528269951966043881353737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34037693269288058508471649 25528269951966043881353737)
        ·
          refine ⟨19146202463974532911015303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25528269951966043881353737 19146202463974532911015303)
          ·
            refine ⟨28719303695961799366522955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19146202463974532911015303 28719303695961799366522955)
            ·
              refine ⟨43078955543942699049784433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28719303695961799366522955 43078955543942699049784433)
              ·
                refine ⟨32309216657957024287338325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43078955543942699049784433 32309216657957024287338325)
                ·
                  refine ⟨189311816355216939183623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32309216657957024287338325 189311816355216939183623)
                  ·
                    rfl

theorem cell23_3318151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 9].length) (baseStart_3318151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318151 prefixEnd_3318151 := by exact prefixLift 3318151
  have htrace : WordTrace (prefixWord ++ tailWord_3318151) baseStart_3318151 baseEnd_3318151 := by
    simpa [prefixWord, tailWord_3318151, baseEnd_3318151] using wordTrace_append hprefix tailTrace_3318151
  have hstable : (prefixWord ++ tailWord_3318151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318151).length < 2 ^ (prefixWord ++ tailWord_3318151).sum := by decide
  have hdescent : baseEnd_3318151 < baseStart_3318151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318168 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 7]
def baseStart_3318168 : Nat := 118140960795 + 3318168 * 2 ^ 59
def prefixEnd_3318168 : Nat := 4983230072969 + 3 ^ 40 * 3318168 * 2
def baseEnd_3318168 : Nat := 189312786263119876237781

theorem tailTrace_3318168 : CollatzResearch.WordTrace tailWord_3318168 prefixEnd_3318168 189312786263119876237781 := by
  unfold tailWord_3318168
  simp only [CollatzResearch.WordTrace]
  refine ⟨60511764721425754411189579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80682352961901005881586105 60511764721425754411189579)
  ·
    refine ⟨90767647082138631616784369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60511764721425754411189579 90767647082138631616784369)
    ·
      refine ⟨68075735311603973712588277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90767647082138631616784369 68075735311603973712588277)
      ·
        refine ⟨6382100185462872535555151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68075735311603973712588277 6382100185462872535555151)
        ·
          refine ⟨9573150278194308803332727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6382100185462872535555151 9573150278194308803332727)
          ·
            refine ⟨14359725417291463204999091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9573150278194308803332727 14359725417291463204999091)
            ·
              refine ⟨21539588125937194807498637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14359725417291463204999091 21539588125937194807498637)
              ·
                refine ⟨8077345547226448052811989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21539588125937194807498637 8077345547226448052811989)
                ·
                  refine ⟨189312786263119876237781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8077345547226448052811989 189312786263119876237781)
                  ·
                    rfl

theorem cell23_3318168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 7].length) (baseStart_3318168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318168 prefixEnd_3318168 := by exact prefixLift 3318168
  have htrace : WordTrace (prefixWord ++ tailWord_3318168) baseStart_3318168 baseEnd_3318168 := by
    simpa [prefixWord, tailWord_3318168, baseEnd_3318168] using wordTrace_append hprefix tailTrace_3318168
  have hstable : (prefixWord ++ tailWord_3318168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318168).length < 2 ^ (prefixWord ++ tailWord_3318168).sum := by decide
  have hdescent : baseEnd_3318168 < baseStart_3318168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318179 : List Nat := [1, 1, 1, 4, 1, 5, 3, 1, 2, 2, 2]
def baseStart_3318179 : Nat := 118140960795 + 3318179 * 2 ^ 59
def prefixEnd_3318179 : Nat := 4983230072969 + 3 ^ 40 * 3318179 * 2
def baseEnd_3318179 : Nat := 1703820724655278343102479

theorem tailTrace_3318179 : CollatzResearch.WordTrace tailWord_3318179 prefixEnd_3318179 1703820724655278343102479 := by
  unfold tailWord_3318179
  simp only [CollatzResearch.WordTrace]
  refine ⟨121023930645811657701029591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80682620430541105134019727 121023930645811657701029591)
  ·
    refine ⟨181535895968717486551544387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121023930645811657701029591 181535895968717486551544387)
    ·
      refine ⟨272303843953076229827316581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181535895968717486551544387 272303843953076229827316581)
      ·
        refine ⟨51056970741201793092621859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272303843953076229827316581 51056970741201793092621859)
        ·
          refine ⟨76585456111802689638932789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51056970741201793092621859 76585456111802689638932789)
          ·
            refine ⟨7179886510481502153649949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76585456111802689638932789 7179886510481502153649949)
            ·
              refine ⟨2692457441430563307618731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7179886510481502153649949 2692457441430563307618731)
              ·
                refine ⟨4038686162145844961428097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692457441430563307618731 4038686162145844961428097)
                ·
                  refine ⟨3029014621609383721071073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4038686162145844961428097 3029014621609383721071073)
                  ·
                    refine ⟨2271760966207037790803305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3029014621609383721071073 2271760966207037790803305)
                    ·
                      refine ⟨1703820724655278343102479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2271760966207037790803305 1703820724655278343102479)
                      ·
                        rfl

theorem cell23_3318179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_3318179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318179 prefixEnd_3318179 := by exact prefixLift 3318179
  have htrace : WordTrace (prefixWord ++ tailWord_3318179) baseStart_3318179 baseEnd_3318179 := by
    simpa [prefixWord, tailWord_3318179, baseEnd_3318179] using wordTrace_append hprefix tailTrace_3318179
  have hstable : (prefixWord ++ tailWord_3318179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318179).length < 2 ^ (prefixWord ++ tailWord_3318179).sum := by decide
  have hdescent : baseEnd_3318179 < baseStart_3318179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318181 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 3, 7]
def baseStart_3318181 : Nat := 118140960795 + 3318181 * 2 ^ 59
def prefixEnd_3318181 : Nat := 4983230072969 + 3 ^ 40 * 3318181 * 2
def baseEnd_3318181 : Nat := 567940583872195778425823

theorem tailTrace_3318181 : CollatzResearch.WordTrace tailWord_3318181 prefixEnd_3318181 567940583872195778425823 := by
  unfold tailWord_3318181
  simp only [CollatzResearch.WordTrace]
  refine ⟨121024003591804412042602397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80682669061202941361734931 121024003591804412042602397)
  ·
    refine ⟨45384001346926654515975899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121024003591804412042602397 45384001346926654515975899)
    ·
      refine ⟨68076002020389981773963849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45384001346926654515975899 68076002020389981773963849)
      ·
        refine ⟨51057001515292486330472887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68076002020389981773963849 51057001515292486330472887)
        ·
          refine ⟨76585502272938729495709331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51057001515292486330472887 76585502272938729495709331)
          ·
            refine ⟨114878253409408094243563997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76585502272938729495709331 114878253409408094243563997)
            ·
              refine ⟨43079345028528035341336499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114878253409408094243563997 43079345028528035341336499)
              ·
                refine ⟨64619017542792053012004749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43079345028528035341336499 64619017542792053012004749)
                ·
                  refine ⟨24232131578547019879501781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64619017542792053012004749 24232131578547019879501781)
                  ·
                    refine ⟨567940583872195778425823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24232131578547019879501781 567940583872195778425823)
                    ·
                      rfl

theorem cell23_3318181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_3318181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318181 prefixEnd_3318181 := by exact prefixLift 3318181
  have htrace : WordTrace (prefixWord ++ tailWord_3318181) baseStart_3318181 baseEnd_3318181 := by
    simpa [prefixWord, tailWord_3318181, baseEnd_3318181] using wordTrace_append hprefix tailTrace_3318181
  have hstable : (prefixWord ++ tailWord_3318181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318181).length < 2 ^ (prefixWord ++ tailWord_3318181).sum := by decide
  have hdescent : baseEnd_3318181 < baseStart_3318181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318191 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 5]
def baseStart_3318191 : Nat := 118140960795 + 3318191 * 2 ^ 59
def prefixEnd_3318191 : Nat := 4983230072969 + 3 ^ 40 * 3318191 * 2
def baseEnd_3318191 : Nat := 1703826886423132296152423

theorem tailTrace_3318191 : CollatzResearch.WordTrace tailWord_3318191 prefixEnd_3318191 1703826886423132296152423 := by
  unfold tailWord_3318191
  simp only [CollatzResearch.WordTrace]
  refine ⟨121024368321768183750466427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80682912214512122500310951 121024368321768183750466427)
  ·
    refine ⟨181536552482652275625699641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121024368321768183750466427 181536552482652275625699641)
    ·
      refine ⟨136152414361989206719274731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181536552482652275625699641 136152414361989206719274731)
      ·
        refine ⟨204228621542983810078912097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136152414361989206719274731 204228621542983810078912097)
        ·
          refine ⟨153171466157237857559184073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204228621542983810078912097 153171466157237857559184073)
          ·
            refine ⟨114878599617928393169388055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153171466157237857559184073 114878599617928393169388055)
            ·
              refine ⟨172317899426892589754082083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114878599617928393169388055 172317899426892589754082083)
              ·
                refine ⟨258476849140338884631123125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172317899426892589754082083 258476849140338884631123125)
                ·
                  refine ⟨24232204606906770434167793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 258476849140338884631123125 24232204606906770434167793)
                  ·
                    refine ⟨18174153455180077825625845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24232204606906770434167793 18174153455180077825625845)
                    ·
                      refine ⟨1703826886423132296152423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18174153455180077825625845 1703826886423132296152423)
                      ·
                        rfl

theorem cell23_3318191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_3318191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318191 prefixEnd_3318191 := by exact prefixLift 3318191
  have htrace : WordTrace (prefixWord ++ tailWord_3318191) baseStart_3318191 baseEnd_3318191 := by
    simpa [prefixWord, tailWord_3318191, baseEnd_3318191] using wordTrace_append hprefix tailTrace_3318191
  have hstable : (prefixWord ++ tailWord_3318191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318191).length < 2 ^ (prefixWord ++ tailWord_3318191).sum := by decide
  have hdescent : baseEnd_3318191 < baseStart_3318191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318279 : List Nat := [1, 1, 4, 3, 3, 1, 1, 4, 1, 4]
def baseStart_3318279 : Nat := 118140960795 + 3318279 * 2 ^ 59
def prefixEnd_3318279 : Nat := 4983230072969 + 3 ^ 40 * 3318279 * 2
def baseEnd_3318279 : Nat := 567957357573575983950673

theorem tailTrace_3318279 : CollatzResearch.WordTrace tailWord_3318279 prefixEnd_3318279 567957357573575983950673 := by
  unfold tailWord_3318279
  simp only [CollatzResearch.WordTrace]
  refine ⟨121027577945449374779669891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80685051963632916519779927 121027577945449374779669891)
  ·
    refine ⟨181541366918174062169504837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121027577945449374779669891 181541366918174062169504837)
    ·
      refine ⟨34039006297157636656782157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181541366918174062169504837 34039006297157636656782157)
      ·
        refine ⟨12764627361434113746293309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34039006297157636656782157 12764627361434113746293309)
        ·
          refine ⟨4786735260537792654859991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12764627361434113746293309 4786735260537792654859991)
          ·
            refine ⟨7180102890806688982289987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4786735260537792654859991 7180102890806688982289987)
            ·
              refine ⟨10770154336210033473434981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7180102890806688982289987 10770154336210033473434981)
              ·
                refine ⟨2019403938039381276269059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10770154336210033473434981 2019403938039381276269059)
                ·
                  refine ⟨3029105907059071914403589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019403938039381276269059 3029105907059071914403589)
                  ·
                    refine ⟨567957357573575983950673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3029105907059071914403589 567957357573575983950673)
                    ·
                      rfl

theorem cell23_3318279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_3318279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318279 prefixEnd_3318279 := by exact prefixLift 3318279
  have htrace : WordTrace (prefixWord ++ tailWord_3318279) baseStart_3318279 baseEnd_3318279 := by
    simpa [prefixWord, tailWord_3318279, baseEnd_3318279] using wordTrace_append hprefix tailTrace_3318279
  have hstable : (prefixWord ++ tailWord_3318279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318279).length < 2 ^ (prefixWord ++ tailWord_3318279).sum := by decide
  have hdescent : baseEnd_3318279 < baseStart_3318279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318292 : List Nat := [2, 4, 3, 1, 1, 1, 2, 3, 6]
def baseStart_3318292 : Nat := 118140960795 + 3318292 * 2 ^ 59
def prefixEnd_3318292 : Nat := 4983230072969 + 3 ^ 40 * 3318292 * 2
def baseEnd_3318292 : Nat := 189319860885470711221051

theorem tailTrace_3318292 : CollatzResearch.WordTrace tailWord_3318292 prefixEnd_3318292 189319860885470711221051 := by
  unfold tailWord_3318292
  simp only [CollatzResearch.WordTrace]
  refine ⟨60514026047201138999946565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80685368062934851999928753 60514026047201138999946565)
  ·
    refine ⟨11346379883850213562489981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60514026047201138999946565 11346379883850213562489981)
    ·
      refine ⟨4254892456443830085933743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11346379883850213562489981 4254892456443830085933743)
      ·
        refine ⟨6382338684665745128900615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4254892456443830085933743 6382338684665745128900615)
        ·
          refine ⟨9573508026998617693350923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6382338684665745128900615 9573508026998617693350923)
          ·
            refine ⟨14360262040497926540026385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9573508026998617693350923 14360262040497926540026385)
            ·
              refine ⟨10770196530373444905019789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14360262040497926540026385 10770196530373444905019789)
              ·
                refine ⟨4038823698890041839382421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10770196530373444905019789 4038823698890041839382421)
                ·
                  refine ⟨189319860885470711221051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4038823698890041839382421 189319860885470711221051)
                  ·
                    rfl

theorem cell23_3318292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_3318292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318292 prefixEnd_3318292 := by exact prefixLift 3318292
  have htrace : WordTrace (prefixWord ++ tailWord_3318292) baseStart_3318292 baseEnd_3318292 := by
    simpa [prefixWord, tailWord_3318292, baseEnd_3318292] using wordTrace_append hprefix tailTrace_3318292
  have hstable : (prefixWord ++ tailWord_3318292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318292).length < 2 ^ (prefixWord ++ tailWord_3318292).sum := by decide
  have hdescent : baseEnd_3318292 < baseStart_3318292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318305 : List Nat := [1, 2, 3, 2, 2, 1, 2, 4, 1, 5]
def baseStart_3318305 : Nat := 118140960795 + 3318305 * 2 ^ 59
def prefixEnd_3318305 : Nat := 4983230072969 + 3 ^ 40 * 3318305 * 2
def baseEnd_3318305 : Nat := 567961807739248283375633

theorem tailTrace_3318305 : CollatzResearch.WordTrace tailWord_3318305 prefixEnd_3318305 567961807739248283375633 := by
  unfold tailWord_3318305
  simp only [CollatzResearch.WordTrace]
  refine ⟨121028526243355181220116369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80685684162236787480077579 121028526243355181220116369)
  ·
    refine ⟨90771394682516385915087277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121028526243355181220116369 90771394682516385915087277)
    ·
      refine ⟨34039273005943644718157729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90771394682516385915087277 34039273005943644718157729)
      ·
        refine ⟨25529454754457733538618297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34039273005943644718157729 25529454754457733538618297)
        ·
          refine ⟨19147091065843300153963723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25529454754457733538618297 19147091065843300153963723)
          ·
            refine ⟨28720636598764950230945585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19147091065843300153963723 28720636598764950230945585)
            ·
              refine ⟨21540477449073712673209189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28720636598764950230945585 21540477449073712673209189)
              ·
                refine ⟨4038839521701321126226723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21540477449073712673209189 4038839521701321126226723)
                ·
                  refine ⟨6058259282551981689340085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4038839521701321126226723 6058259282551981689340085)
                  ·
                    refine ⟨567961807739248283375633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6058259282551981689340085 567961807739248283375633)
                    ·
                      rfl

theorem cell23_3318305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_3318305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318305 prefixEnd_3318305 := by exact prefixLift 3318305
  have htrace : WordTrace (prefixWord ++ tailWord_3318305) baseStart_3318305 baseEnd_3318305 := by
    simpa [prefixWord, tailWord_3318305, baseEnd_3318305] using wordTrace_append hprefix tailTrace_3318305
  have hstable : (prefixWord ++ tailWord_3318305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318305).length < 2 ^ (prefixWord ++ tailWord_3318305).sum := by decide
  have hdescent : baseEnd_3318305 < baseStart_3318305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318322 : List Nat := [3, 2, 1, 1, 2, 1, 6, 1, 1, 5]
def baseStart_3318322 : Nat := 118140960795 + 3318322 * 2 ^ 59
def prefixEnd_3318322 : Nat := 4983230072969 + 3 ^ 40 * 3318322 * 2
def baseEnd_3318322 : Nat := 567964717462957094538107

theorem tailTrace_3318322 : CollatzResearch.WordTrace tailWord_3318322 prefixEnd_3318322 567964717462957094538107 := by
  unfold tailWord_3318322
  simp only [CollatzResearch.WordTrace]
  refine ⟨30257286571073398280871305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80686097522862395415656813 30257286571073398280871305)
  ·
    refine ⟨22692964928305048710653479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30257286571073398280871305 22692964928305048710653479)
    ·
      refine ⟨34039447392457573065980219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22692964928305048710653479 34039447392457573065980219)
      ·
        refine ⟨51059171088686359598970329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34039447392457573065980219 51059171088686359598970329)
        ·
          refine ⟨38294378316514769699227747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51059171088686359598970329 38294378316514769699227747)
          ·
            refine ⟨57441567474772154548841621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38294378316514769699227747 57441567474772154548841621)
            ·
              refine ⟨2692573475379944744476951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57441567474772154548841621 2692573475379944744476951)
              ·
                refine ⟨4038860213069917116715427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692573475379944744476951 4038860213069917116715427)
                ·
                  refine ⟨6058290319604875675073141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4038860213069917116715427 6058290319604875675073141)
                  ·
                    refine ⟨567964717462957094538107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6058290319604875675073141 567964717462957094538107)
                    ·
                      rfl

theorem cell23_3318322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_3318322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318322 prefixEnd_3318322 := by exact prefixLift 3318322
  have htrace : WordTrace (prefixWord ++ tailWord_3318322) baseStart_3318322 baseEnd_3318322 := by
    simpa [prefixWord, tailWord_3318322, baseEnd_3318322] using wordTrace_append hprefix tailTrace_3318322
  have hstable : (prefixWord ++ tailWord_3318322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318322).length < 2 ^ (prefixWord ++ tailWord_3318322).sum := by decide
  have hdescent : baseEnd_3318322 < baseStart_3318322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318335 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 4, 4]
def baseStart_3318335 : Nat := 118140960795 + 3318335 * 2 ^ 59
def prefixEnd_3318335 : Nat := 4983230072969 + 3 ^ 40 * 3318335 * 2
def baseEnd_3318335 : Nat := 567966942545793244250587

theorem tailTrace_3318335 : CollatzResearch.WordTrace tailWord_3318335 prefixEnd_3318335 567966942545793244250587 := by
  unfold tailWord_3318335
  simp only [CollatzResearch.WordTrace]
  refine ⟨121029620433246496343708459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80686413622164330895805639 121029620433246496343708459)
  ·
    refine ⟨181544430649869744515562689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121029620433246496343708459 181544430649869744515562689)
    ·
      refine ⟨136158322987402308386672017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181544430649869744515562689 136158322987402308386672017)
      ·
        refine ⟨102118742240551731290004013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136158322987402308386672017 102118742240551731290004013)
        ·
          refine ⟨38294528340206899233751505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102118742240551731290004013 38294528340206899233751505)
          ·
            refine ⟨28720896255155174425313629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38294528340206899233751505 28720896255155174425313629)
            ·
              refine ⟨10770336095683190409492611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28720896255155174425313629 10770336095683190409492611)
              ·
                refine ⟨16155504143524785614238917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10770336095683190409492611 16155504143524785614238917)
                ·
                  refine ⟨3029157026910897302669797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16155504143524785614238917 3029157026910897302669797)
                  ·
                    refine ⟨567966942545793244250587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3029157026910897302669797 567966942545793244250587)
                    ·
                      rfl

theorem cell23_3318335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 4].length) (baseStart_3318335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318335 prefixEnd_3318335 := by exact prefixLift 3318335
  have htrace : WordTrace (prefixWord ++ tailWord_3318335) baseStart_3318335 baseEnd_3318335 := by
    simpa [prefixWord, tailWord_3318335, baseEnd_3318335] using wordTrace_append hprefix tailTrace_3318335
  have hstable : (prefixWord ++ tailWord_3318335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318335).length < 2 ^ (prefixWord ++ tailWord_3318335).sum := by decide
  have hdescent : baseEnd_3318335 < baseStart_3318335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318348 : List Nat := [2, 2, 1, 3, 1, 2, 2, 10]
def baseStart_3318348 : Nat := 118140960795 + 3318348 * 2 ^ 59
def prefixEnd_3318348 : Nat := 4983230072969 + 3 ^ 40 * 3318348 * 2
def baseEnd_3318348 : Nat := 63107685292069932662563

theorem tailTrace_3318348 : CollatzResearch.WordTrace tailWord_3318348 prefixEnd_3318348 63107685292069932662563 := by
  unfold tailWord_3318348
  simp only [CollatzResearch.WordTrace]
  refine ⟨60515047291099699781965849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80686729721466266375954465 60515047291099699781965849)
  ·
    refine ⟨45386285468324774836474387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60515047291099699781965849 45386285468324774836474387)
    ·
      refine ⟨68079428202487162254711581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45386285468324774836474387 68079428202487162254711581)
      ·
        refine ⟨25529785575932685845516843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68079428202487162254711581 25529785575932685845516843)
        ·
          refine ⟨38294678363899028768275265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25529785575932685845516843 38294678363899028768275265)
          ·
            refine ⟨28721008772924271576206449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38294678363899028768275265 28721008772924271576206449)
            ·
              refine ⟨21540756579693203682154837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28721008772924271576206449 21540756579693203682154837)
              ·
                refine ⟨63107685292069932662563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21540756579693203682154837 63107685292069932662563)
                ·
                  rfl

theorem cell23_3318348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 10].length) (baseStart_3318348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318348 prefixEnd_3318348 := by exact prefixLift 3318348
  have htrace : WordTrace (prefixWord ++ tailWord_3318348) baseStart_3318348 baseEnd_3318348 := by
    simpa [prefixWord, tailWord_3318348, baseEnd_3318348] using wordTrace_append hprefix tailTrace_3318348
  have hstable : (prefixWord ++ tailWord_3318348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318348).length < 2 ^ (prefixWord ++ tailWord_3318348).sum := by decide
  have hdescent : baseEnd_3318348 < baseStart_3318348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318370 : List Nat := [3, 3, 2, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3318370 : Nat := 118140960795 + 3318370 * 2 ^ 59
def prefixEnd_3318370 : Nat := 4983230072969 + 3 ^ 40 * 3318370 * 2
def baseEnd_3318370 : Nat := 1703918799460287095814101

theorem tailTrace_3318370 : CollatzResearch.WordTrace tailWord_3318370 prefixEnd_3318370 1703918799460287095814101 := by
  unfold tailWord_3318370
  simp only [CollatzResearch.WordTrace]
  refine ⟨30257724247029924330308141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80687264658746464880821709 30257724247029924330308141)
  ·
    refine ⟨11346646592636221623865553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30257724247029924330308141 11346646592636221623865553)
    ·
      refine ⟨8509984944477166217899165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11346646592636221623865553 8509984944477166217899165)
      ·
        refine ⟨3191244354178937331712187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8509984944477166217899165 3191244354178937331712187)
        ·
          refine ⟨4786866531268405997568281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191244354178937331712187 4786866531268405997568281)
          ·
            refine ⟨3590149898451304498176211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4786866531268405997568281 3590149898451304498176211)
            ·
              refine ⟨5385224847676956747264317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590149898451304498176211 5385224847676956747264317)
              ·
                refine ⟨2019459317878858780224119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5385224847676956747264317 2019459317878858780224119)
                ·
                  refine ⟨3029188976818288170336179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019459317878858780224119 3029188976818288170336179)
                  ·
                    refine ⟨4543783465227432255504269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3029188976818288170336179 4543783465227432255504269)
                    ·
                      refine ⟨1703918799460287095814101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4543783465227432255504269 1703918799460287095814101)
                      ·
                        rfl

theorem cell23_3318370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3318370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318370 prefixEnd_3318370 := by exact prefixLift 3318370
  have htrace : WordTrace (prefixWord ++ tailWord_3318370) baseStart_3318370 baseEnd_3318370 := by
    simpa [prefixWord, tailWord_3318370, baseEnd_3318370] using wordTrace_append hprefix tailTrace_3318370
  have hstable : (prefixWord ++ tailWord_3318370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318370).length < 2 ^ (prefixWord ++ tailWord_3318370).sum := by decide
  have hdescent : baseEnd_3318370 < baseStart_3318370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318375 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_3318375 : Nat := 118140960795 + 3318375 * 2 ^ 59
def prefixEnd_3318375 : Nat := 4983230072969 + 3 ^ 40 * 3318375 * 2
def baseEnd_3318375 : Nat := 1703921366863559576251577

theorem tailTrace_3318375 : CollatzResearch.WordTrace tailWord_3318375 prefixEnd_3318375 1703921366863559576251577 := by
  unfold tailWord_3318375
  simp only [CollatzResearch.WordTrace]
  refine ⟨121031079353101583175164579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80687386235401055450109719 121031079353101583175164579)
  ·
    refine ⟨181546619029652374762746869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121031079353101583175164579 181546619029652374762746869)
    ·
      refine ⟨17019995534029910134007519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181546619029652374762746869 17019995534029910134007519)
      ·
        refine ⟨25529993301044865201011279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17019995534029910134007519 25529993301044865201011279)
        ·
          refine ⟨38294989951567297801516919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25529993301044865201011279 38294989951567297801516919)
          ·
            refine ⟨57442484927350946702275379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38294989951567297801516919 57442484927350946702275379)
            ·
              refine ⟨86163727391026420053413069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57442484927350946702275379 86163727391026420053413069)
              ·
                refine ⟨32311397771634907520029901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86163727391026420053413069 32311397771634907520029901)
                ·
                  refine ⟨12116774164363090320011213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32311397771634907520029901 12116774164363090320011213)
                  ·
                    refine ⟨4543790311636158870004205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12116774164363090320011213 4543790311636158870004205)
                    ·
                      refine ⟨1703921366863559576251577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4543790311636158870004205 1703921366863559576251577)
                      ·
                        rfl

theorem cell23_3318375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_3318375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318375 prefixEnd_3318375 := by exact prefixLift 3318375
  have htrace : WordTrace (prefixWord ++ tailWord_3318375) baseStart_3318375 baseEnd_3318375 := by
    simpa [prefixWord, tailWord_3318375, baseEnd_3318375] using wordTrace_append hprefix tailTrace_3318375
  have hstable : (prefixWord ++ tailWord_3318375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318375).length < 2 ^ (prefixWord ++ tailWord_3318375).sum := by decide
  have hdescent : baseEnd_3318375 < baseStart_3318375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318393 : List Nat := [1, 2, 1, 3, 3, 3, 3, 2, 1, 2, 2]
def baseStart_3318393 : Nat := 118140960795 + 3318393 * 2 ^ 59
def prefixEnd_3318393 : Nat := 4983230072969 + 3 ^ 40 * 3318393 * 2
def baseEnd_3318393 : Nat := 1703930609515340505826495

theorem tailTrace_3318393 : CollatzResearch.WordTrace tailWord_3318393 prefixEnd_3318393 1703930609515340505826495 := by
  unfold tailWord_3318393
  simp only [CollatzResearch.WordTrace]
  refine ⟨121031735867036372249319833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80687823911357581499546555 121031735867036372249319833)
  ·
    refine ⟨90773801900277279186989875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121031735867036372249319833 90773801900277279186989875)
    ·
      refine ⟨136160702850415918780484813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90773801900277279186989875 136160702850415918780484813)
      ·
        refine ⟨51060263568905969542681805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136160702850415918780484813 51060263568905969542681805)
        ·
          refine ⟨19147598838339738578505677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51060263568905969542681805 19147598838339738578505677)
          ·
            refine ⟨7180349564377401966939629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19147598838339738578505677 7180349564377401966939629)
            ·
              refine ⟨2692631086641525737602361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7180349564377401966939629 2692631086641525737602361)
              ·
                refine ⟨2019473314981144303201771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2692631086641525737602361 2019473314981144303201771)
                ·
                  refine ⟨3029209972471716454802657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019473314981144303201771 3029209972471716454802657)
                  ·
                    refine ⟨2271907479353787341101993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3029209972471716454802657 2271907479353787341101993)
                    ·
                      refine ⟨1703930609515340505826495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2271907479353787341101993 1703930609515340505826495)
                      ·
                        rfl

theorem cell23_3318393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_3318393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318393 prefixEnd_3318393 := by exact prefixLift 3318393
  have htrace : WordTrace (prefixWord ++ tailWord_3318393) baseStart_3318393 baseEnd_3318393 := by
    simpa [prefixWord, tailWord_3318393, baseEnd_3318393] using wordTrace_append hprefix tailTrace_3318393
  have hstable : (prefixWord ++ tailWord_3318393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318393).length < 2 ^ (prefixWord ++ tailWord_3318393).sum := by decide
  have hdescent : baseEnd_3318393 < baseStart_3318393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318436 : List Nat := [2, 3, 1, 2, 2, 1, 5, 1, 1, 3, 2]
def baseStart_3318436 : Nat := 118140960795 + 3318436 * 2 ^ 59
def prefixEnd_3318436 : Nat := 4983230072969 + 3 ^ 40 * 3318436 * 2
def baseEnd_3318436 : Nat := 1703952689183483837588797

theorem tailTrace_3318436 : CollatzResearch.WordTrace tailWord_3318436 prefixEnd_3318436 1703952689183483837588797 := by
  unfold tailWord_3318436
  simp only [CollatzResearch.WordTrace]
  refine ⟨60516652102940295296567581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80688869470587060395423441 60516652102940295296567581)
  ·
    refine ⟨22693744538602610736212843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60516652102940295296567581 22693744538602610736212843)
    ·
      refine ⟨34040616807903916104319265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22693744538602610736212843 34040616807903916104319265)
      ·
        refine ⟨25530462605927937078239449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34040616807903916104319265 25530462605927937078239449)
        ·
          refine ⟨19147846954445952808679587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25530462605927937078239449 19147846954445952808679587)
          ·
            refine ⟨28721770431668929213019381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19147846954445952808679587 28721770431668929213019381)
            ·
              refine ⟨2692665977968962113720567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28721770431668929213019381 2692665977968962113720567)
              ·
                refine ⟨4038998966953443170580851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692665977968962113720567 4038998966953443170580851)
                ·
                  refine ⟨6058498450430164755871277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4038998966953443170580851 6058498450430164755871277)
                  ·
                    refine ⟨2271936918911311783451729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6058498450430164755871277 2271936918911311783451729)
                    ·
                      refine ⟨1703952689183483837588797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2271936918911311783451729 1703952689183483837588797)
                      ·
                        rfl

theorem cell23_3318436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_3318436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318436 prefixEnd_3318436 := by exact prefixLift 3318436
  have htrace : WordTrace (prefixWord ++ tailWord_3318436) baseStart_3318436 baseEnd_3318436 := by
    simpa [prefixWord, tailWord_3318436, baseEnd_3318436] using wordTrace_append hprefix tailTrace_3318436
  have hstable : (prefixWord ++ tailWord_3318436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318436).length < 2 ^ (prefixWord ++ tailWord_3318436).sum := by decide
  have hdescent : baseEnd_3318436 < baseStart_3318436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318462 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_3318462 : Nat := 118140960795 + 3318462 * 2 ^ 59
def prefixEnd_3318462 : Nat := 4983230072969 + 3 ^ 40 * 3318462 * 2
def baseEnd_3318462 : Nat := 1703966039680500735863677

theorem tailTrace_3318462 : CollatzResearch.WordTrace tailWord_3318462 prefixEnd_3318462 1703966039680500735863677 := by
  unfold tailWord_3318462
  simp only [CollatzResearch.WordTrace]
  refine ⟨15129281562973299629197705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80689501669190931355721093 15129281562973299629197705)
  ·
    refine ⟨11346961172229974721898279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15129281562973299629197705 11346961172229974721898279)
    ·
      refine ⟨17020441758344962082847419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11346961172229974721898279 17020441758344962082847419)
      ·
        refine ⟨25530662637517443124271129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17020441758344962082847419 25530662637517443124271129)
        ·
          refine ⟨19147996978138082343203347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25530662637517443124271129 19147996978138082343203347)
          ·
            refine ⟨28721995467207123514805021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19147996978138082343203347 28721995467207123514805021)
            ·
              refine ⟨10770748300202671318051883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28721995467207123514805021 10770748300202671318051883)
              ·
                refine ⟨16156122450304006977077825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10770748300202671318051883 16156122450304006977077825)
                ·
                  refine ⟨12117091837728005232808369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16156122450304006977077825 12117091837728005232808369)
                  ·
                    refine ⟨9087818878296003924606277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12117091837728005232808369 9087818878296003924606277)
                    ·
                      refine ⟨1703966039680500735863677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9087818878296003924606277 1703966039680500735863677)
                      ·
                        rfl

theorem cell23_3318462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_3318462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318462 prefixEnd_3318462 := by exact prefixLift 3318462
  have htrace : WordTrace (prefixWord ++ tailWord_3318462) baseStart_3318462 baseEnd_3318462 := by
    simpa [prefixWord, tailWord_3318462, baseEnd_3318462] using wordTrace_append hprefix tailTrace_3318462
  have hstable : (prefixWord ++ tailWord_3318462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318462).length < 2 ^ (prefixWord ++ tailWord_3318462).sum := by decide
  have hdescent : baseEnd_3318462 < baseStart_3318462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318517 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_3318517 : Nat := 118140960795 + 3318517 * 2 ^ 59
def prefixEnd_3318517 : Nat := 4983230072969 + 3 ^ 40 * 3318517 * 2
def baseEnd_3318517 : Nat := 1703994281116498020675925

theorem tailTrace_3318517 : CollatzResearch.WordTrace tailWord_3318517 prefixEnd_3318517 1703994281116498020675925 := by
  unfold tailWord_3318517
  simp only [CollatzResearch.WordTrace]
  refine ⟨121036258518587141426833805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80690839012391427617889203 121036258518587141426833805)
  ·
    refine ⟨45388596944470178035062677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121036258518587141426833805 45388596944470178035062677)
    ·
      refine ⟨2127590481772039595393563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45388596944470178035062677 2127590481772039595393563)
      ·
        refine ⟨3191385722658059393090345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127590481772039595393563 3191385722658059393090345)
        ·
          refine ⟨2393539291993544544817759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3191385722658059393090345 2393539291993544544817759)
          ·
            refine ⟨3590308937990316817226639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393539291993544544817759 3590308937990316817226639)
            ·
              refine ⟨5385463406985475225839959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590308937990316817226639 5385463406985475225839959)
              ·
                refine ⟨8078195110478212838759939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385463406985475225839959 8078195110478212838759939)
                ·
                  refine ⟨12117292665717319258139909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8078195110478212838759939 12117292665717319258139909)
                  ·
                    refine ⟨2271992374821997360901233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12117292665717319258139909 2271992374821997360901233)
                    ·
                      refine ⟨1703994281116498020675925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2271992374821997360901233 1703994281116498020675925)
                      ·
                        rfl

theorem cell23_3318517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_3318517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318517 prefixEnd_3318517 := by exact prefixLift 3318517
  have htrace : WordTrace (prefixWord ++ tailWord_3318517) baseStart_3318517 baseEnd_3318517 := by
    simpa [prefixWord, tailWord_3318517, baseEnd_3318517] using wordTrace_append hprefix tailTrace_3318517
  have hstable : (prefixWord ++ tailWord_3318517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318517).length < 2 ^ (prefixWord ++ tailWord_3318517).sum := by decide
  have hdescent : baseEnd_3318517 < baseStart_3318517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318545 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 8]
def baseStart_3318545 : Nat := 118140960795 + 3318545 * 2 ^ 59
def prefixEnd_3318545 : Nat := 4983230072969 + 3 ^ 40 * 3318545 * 2
def baseEnd_3318545 : Nat := 189334295397202656791755

theorem tailTrace_3318545 : CollatzResearch.WordTrace tailWord_3318545 prefixEnd_3318545 189334295397202656791755 := by
  unfold tailWord_3318545
  simp only [CollatzResearch.WordTrace]
  refine ⟨121037279762485702208853089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80691519841657134805902059 121037279762485702208853089)
  ·
    refine ⟨90777959821864276656639817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121037279762485702208853089 90777959821864276656639817)
    ·
      refine ⟨68083469866398207492479863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90777959821864276656639817 68083469866398207492479863)
      ·
        refine ⟨102125204799597311238719795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68083469866398207492479863 102125204799597311238719795)
        ·
          refine ⟨153187807199395966858079693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102125204799597311238719795 153187807199395966858079693)
          ·
            refine ⟨57445427699773487571779885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153187807199395966858079693 57445427699773487571779885)
            ·
              refine ⟨21542035387415057839417457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57445427699773487571779885 21542035387415057839417457)
              ·
                refine ⟨16156526540561293379563093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21542035387415057839417457 16156526540561293379563093)
                ·
                  refine ⟨189334295397202656791755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16156526540561293379563093 189334295397202656791755)
                  ·
                    rfl

theorem cell23_3318545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 8].length) (baseStart_3318545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318545 prefixEnd_3318545 := by exact prefixLift 3318545
  have htrace : WordTrace (prefixWord ++ tailWord_3318545) baseStart_3318545 baseEnd_3318545 := by
    simpa [prefixWord, tailWord_3318545, baseEnd_3318545] using wordTrace_append hprefix tailTrace_3318545
  have hstable : (prefixWord ++ tailWord_3318545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318545).length < 2 ^ (prefixWord ++ tailWord_3318545).sum := by decide
  have hdescent : baseEnd_3318545 < baseStart_3318545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318559 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 3]
def baseStart_3318559 : Nat := 118140960795 + 3318559 * 2 ^ 59
def prefixEnd_3318559 : Nat := 4983230072969 + 3 ^ 40 * 3318559 * 2
def baseEnd_3318559 : Nat := 1704015847303986856350731

theorem tailTrace_3318559 : CollatzResearch.WordTrace tailWord_3318559 prefixEnd_3318559 1704015847303986856350731 := by
  unfold tailWord_3318559
  simp only [CollatzResearch.WordTrace]
  refine ⟨121037790384434982599862731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80691860256289988399908487 121037790384434982599862731)
  ·
    refine ⟨181556685576652473899794097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121037790384434982599862731 181556685576652473899794097)
    ·
      refine ⟨136167514182489355424845573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181556685576652473899794097 136167514182489355424845573)
      ·
        refine ⟨25531408909216754142158545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136167514182489355424845573 25531408909216754142158545)
        ·
          refine ⟨19148556681912565606618909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25531408909216754142158545 19148556681912565606618909)
          ·
            refine ⟨7180708755717212102482091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19148556681912565606618909 7180708755717212102482091)
            ·
              refine ⟨10771063133575818153723137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7180708755717212102482091 10771063133575818153723137)
              ·
                refine ⟨8078297350181863615292353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10771063133575818153723137 8078297350181863615292353)
                ·
                  refine ⟨6058723012636397711469265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8078297350181863615292353 6058723012636397711469265)
                  ·
                    refine ⟨4544042259477298283601949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6058723012636397711469265 4544042259477298283601949)
                    ·
                      refine ⟨1704015847303986856350731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4544042259477298283601949 1704015847303986856350731)
                      ·
                        rfl

theorem cell23_3318559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_3318559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318559 prefixEnd_3318559 := by exact prefixLift 3318559
  have htrace : WordTrace (prefixWord ++ tailWord_3318559) baseStart_3318559 baseEnd_3318559 := by
    simpa [prefixWord, tailWord_3318559, baseEnd_3318559] using wordTrace_append hprefix tailTrace_3318559
  have hstable : (prefixWord ++ tailWord_3318559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318559).length < 2 ^ (prefixWord ++ tailWord_3318559).sum := by decide
  have hdescent : baseEnd_3318559 < baseStart_3318559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318562 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 8]
def baseStart_3318562 : Nat := 118140960795 + 3318562 * 2 ^ 59
def prefixEnd_3318562 : Nat := 4983230072969 + 3 ^ 40 * 3318562 * 2
def baseEnd_3318562 : Nat := 189335265305105593845913

theorem tailTrace_3318562 : CollatzResearch.WordTrace tailWord_3318562 prefixEnd_3318562 189335265305105593845913 := by
  unfold tailWord_3318562
  simp only [CollatzResearch.WordTrace]
  refine ⟨30259474950856028528055485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80691933202282742741481293 30259474950856028528055485)
  ·
    refine ⟨11347303106571010698020807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30259474950856028528055485 11347303106571010698020807)
    ·
      refine ⟨17020954659856516047031211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11347303106571010698020807 17020954659856516047031211)
      ·
        refine ⟨25531431989784774070546817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17020954659856516047031211 25531431989784774070546817)
        ·
          refine ⟨19148573992338580552910113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25531431989784774070546817 19148573992338580552910113)
          ·
            refine ⟨14361430494253935414682585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19148573992338580552910113 14361430494253935414682585)
            ·
              refine ⟨10771072870690451561011939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14361430494253935414682585 10771072870690451561011939)
              ·
                refine ⟨16156609306035677341517909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10771072870690451561011939 16156609306035677341517909)
                ·
                  refine ⟨189335265305105593845913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16156609306035677341517909 189335265305105593845913)
                  ·
                    rfl

theorem cell23_3318562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_3318562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318562 prefixEnd_3318562 := by exact prefixLift 3318562
  have htrace : WordTrace (prefixWord ++ tailWord_3318562) baseStart_3318562 baseEnd_3318562 := by
    simpa [prefixWord, tailWord_3318562, baseEnd_3318562] using wordTrace_append hprefix tailTrace_3318562
  have hstable : (prefixWord ++ tailWord_3318562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318562).length < 2 ^ (prefixWord ++ tailWord_3318562).sum := by decide
  have hdescent : baseEnd_3318562 < baseStart_3318562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318579 : List Nat := [1, 1, 1, 2, 6, 1, 4, 1, 6]
def baseStart_3318579 : Nat := 118140960795 + 3318579 * 2 ^ 59
def prefixEnd_3318579 : Nat := 4983230072969 + 3 ^ 40 * 3318579 * 2
def baseEnd_3318579 : Nat := 189336235213008530900071

theorem tailTrace_3318579 : CollatzResearch.WordTrace tailWord_3318579 prefixEnd_3318579 189336235213008530900071 := by
  unfold tailWord_3318579
  simp only [CollatzResearch.WordTrace]
  refine ⟨121038519844362526015590791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80692346562908350677060527 121038519844362526015590791)
  ·
    refine ⟨181557779766543789023386187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121038519844362526015590791 181557779766543789023386187)
    ·
      refine ⟨272336669649815683535079281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181557779766543789023386187 272336669649815683535079281)
      ·
        refine ⟨204252502237361762651309461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272336669649815683535079281 204252502237361762651309461)
        ·
          refine ⟨9574336042376332624280131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 204252502237361762651309461 9574336042376332624280131)
          ·
            refine ⟨14361504063564498936420197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9574336042376332624280131 14361504063564498936420197)
            ·
              refine ⟨2692782011918343550578787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14361504063564498936420197 2692782011918343550578787)
              ·
                refine ⟨4039173017877515325868181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692782011918343550578787 4039173017877515325868181)
                ·
                  refine ⟨189336235213008530900071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4039173017877515325868181 189336235213008530900071)
                  ·
                    rfl

theorem cell23_3318579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 6].length) (baseStart_3318579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318579 prefixEnd_3318579 := by exact prefixLift 3318579
  have htrace : WordTrace (prefixWord ++ tailWord_3318579) baseStart_3318579 baseEnd_3318579 := by
    simpa [prefixWord, tailWord_3318579, baseEnd_3318579] using wordTrace_append hprefix tailTrace_3318579
  have hstable : (prefixWord ++ tailWord_3318579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318579).length < 2 ^ (prefixWord ++ tailWord_3318579).sum := by decide
  have hdescent : baseEnd_3318579 < baseStart_3318579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318593 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3318593 : Nat := 118140960795 + 3318593 * 2 ^ 59
def prefixEnd_3318593 : Nat := 4983230072969 + 3 ^ 40 * 3318593 * 2
def baseEnd_3318593 : Nat := 1704033305646239723325575

theorem tailTrace_3318593 : CollatzResearch.WordTrace tailWord_3318593 prefixEnd_3318593 1704033305646239723325575 := by
  unfold tailWord_3318593
  simp only [CollatzResearch.WordTrace]
  refine ⟨121039030466311806406600433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80692686977541204271066955 121039030466311806406600433)
  ·
    refine ⟨90779272849733854804950325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121039030466311806406600433 90779272849733854804950325)
    ·
      refine ⟨8510556829662548887964093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90779272849733854804950325 8510556829662548887964093)
      ·
        refine ⟨3191458811123455832986535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8510556829662548887964093 3191458811123455832986535)
        ·
          refine ⟨4787188216685183749479803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191458811123455832986535 4787188216685183749479803)
          ·
            refine ⟨7180782325027775624219705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4787188216685183749479803 7180782325027775624219705)
            ·
              refine ⟨5385586743770831718164779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7180782325027775624219705 5385586743770831718164779)
              ·
                refine ⟨8078380115656247577247169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385586743770831718164779 8078380115656247577247169)
                ·
                  refine ⟨6058785086742185682935377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8078380115656247577247169 6058785086742185682935377)
                  ·
                    refine ⟨4544088815056639262201533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6058785086742185682935377 4544088815056639262201533)
                    ·
                      refine ⟨1704033305646239723325575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4544088815056639262201533 1704033305646239723325575)
                      ·
                        rfl

theorem cell23_3318593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3318593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318593 prefixEnd_3318593 := by exact prefixLift 3318593
  have htrace : WordTrace (prefixWord ++ tailWord_3318593) baseStart_3318593 baseEnd_3318593 := by
    simpa [prefixWord, tailWord_3318593, baseEnd_3318593] using wordTrace_append hprefix tailTrace_3318593
  have hstable : (prefixWord ++ tailWord_3318593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318593).length < 2 ^ (prefixWord ++ tailWord_3318593).sum := by decide
  have hdescent : baseEnd_3318593 < baseStart_3318593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318642 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_3318642 : Nat := 118140960795 + 3318642 * 2 ^ 59
def prefixEnd_3318642 : Nat := 4983230072969 + 3 ^ 40 * 3318642 * 2
def baseEnd_3318642 : Nat := 1704058466198310031612849

theorem tailTrace_3318642 : CollatzResearch.WordTrace tailWord_3318642 prefixEnd_3318642 1704058466198310031612849 := by
  unfold tailWord_3318642
  simp only [CollatzResearch.WordTrace]
  refine ⟨30260204410783571943783545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80693878428756191850089453 30260204410783571943783545)
  ·
    refine ⟨22695153308087678957837659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30260204410783571943783545 22695153308087678957837659)
    ·
      refine ⟨34042729962131518436756489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22695153308087678957837659 34042729962131518436756489)
      ·
        refine ⟨25532047471598638827567367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34042729962131518436756489 25532047471598638827567367)
        ·
          refine ⟨38298071207397958241351051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25532047471598638827567367 38298071207397958241351051)
          ·
            refine ⟨57447106811096937362026577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38298071207397958241351051 57447106811096937362026577)
            ·
              refine ⟨43085330108322703021519933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57447106811096937362026577 43085330108322703021519933)
              ·
                refine ⟨16156998790621013633069975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43085330108322703021519933 16156998790621013633069975)
                ·
                  refine ⟨24235498185931520449604963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16156998790621013633069975 24235498185931520449604963)
                  ·
                    refine ⟨36353247278897280674407445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24235498185931520449604963 36353247278897280674407445)
                    ·
                      refine ⟨1704058466198310031612849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36353247278897280674407445 1704058466198310031612849)
                      ·
                        rfl

theorem cell23_3318642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_3318642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318642 prefixEnd_3318642 := by exact prefixLift 3318642
  have htrace : WordTrace (prefixWord ++ tailWord_3318642) baseStart_3318642 baseEnd_3318642 := by
    simpa [prefixWord, tailWord_3318642, baseEnd_3318642] using wordTrace_append hprefix tailTrace_3318642
  have hstable : (prefixWord ++ tailWord_3318642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318642).length < 2 ^ (prefixWord ++ tailWord_3318642).sum := by decide
  have hdescent : baseEnd_3318642 < baseStart_3318642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318646 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3318646 : Nat := 118140960795 + 3318646 * 2 ^ 59
def prefixEnd_3318646 : Nat := 4983230072969 + 3 ^ 40 * 3318646 * 2
def baseEnd_3318646 : Nat := 1704060520120928015962831

theorem tailTrace_3318646 : CollatzResearch.WordTrace tailWord_3318646 prefixEnd_3318646 1704060520120928015962831 := by
  unfold tailWord_3318646
  simp only [CollatzResearch.WordTrace]
  refine ⟨7565060220944987278642487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80693975690079864305519861 7565060220944987278642487)
  ·
    refine ⟨11347590331417480917963731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7565060220944987278642487 11347590331417480917963731)
    ·
      refine ⟨17021385497126221376945597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11347590331417480917963731 17021385497126221376945597)
      ·
        refine ⟨6383019561422333016354599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17021385497126221376945597 6383019561422333016354599)
        ·
          refine ⟨9574529342133499524531899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6383019561422333016354599 9574529342133499524531899)
          ·
            refine ⟨14361794013200249286797849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9574529342133499524531899 14361794013200249286797849)
            ·
              refine ⟨10771345509900186965098387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14361794013200249286797849 10771345509900186965098387)
              ·
                refine ⟨16157018264850280447647581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10771345509900186965098387 16157018264850280447647581)
                ·
                  refine ⟨6058881849318855167867843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16157018264850280447647581 6058881849318855167867843)
                  ·
                    refine ⟨9088322773978282751801765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6058881849318855167867843 9088322773978282751801765)
                    ·
                      refine ⟨1704060520120928015962831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9088322773978282751801765 1704060520120928015962831)
                      ·
                        rfl

theorem cell23_3318646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3318646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318646 prefixEnd_3318646 := by exact prefixLift 3318646
  have htrace : WordTrace (prefixWord ++ tailWord_3318646) baseStart_3318646 baseEnd_3318646 := by
    simpa [prefixWord, tailWord_3318646, baseEnd_3318646] using wordTrace_append hprefix tailTrace_3318646
  have hstable : (prefixWord ++ tailWord_3318646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318646).length < 2 ^ (prefixWord ++ tailWord_3318646).sum := by decide
  have hdescent : baseEnd_3318646 < baseStart_3318646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318649 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 3, 2, 3]
def baseStart_3318649 : Nat := 118140960795 + 3318649 * 2 ^ 59
def prefixEnd_3318649 : Nat := 4983230072969 + 3 ^ 40 * 3318649 * 2
def baseEnd_3318649 : Nat := 1704062060562891504225317

theorem tailTrace_3318649 : CollatzResearch.WordTrace tailWord_3318649 prefixEnd_3318649 1704062060562891504225317 := by
  unfold tailWord_3318649
  simp only [CollatzResearch.WordTrace]
  refine ⟨121041072954108927970639001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80694048636072618647092667 121041072954108927970639001)
  ·
    refine ⟨90780804715581695977979251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121041072954108927970639001 90780804715581695977979251)
    ·
      refine ⟨136171207073372543966968877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90780804715581695977979251 136171207073372543966968877)
      ·
        refine ⟨51064202652514703987613329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136171207073372543966968877 51064202652514703987613329)
        ·
          refine ⟨38298151989386027990709997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51064202652514703987613329 38298151989386027990709997)
          ·
            refine ⟨14361806996019760496516249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38298151989386027990709997 14361806996019760496516249)
            ·
              refine ⟨10771355247014820372387187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14361806996019760496516249 10771355247014820372387187)
              ·
                refine ⟨16157032870522230558580781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10771355247014820372387187 16157032870522230558580781)
                ·
                  refine ⟨6058887326445836459467793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16157032870522230558580781 6058887326445836459467793)
                  ·
                    refine ⟨4544165494834377344600845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6058887326445836459467793 4544165494834377344600845)
                    ·
                      refine ⟨1704062060562891504225317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4544165494834377344600845 1704062060562891504225317)
                      ·
                        rfl

theorem cell23_3318649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_3318649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318649 prefixEnd_3318649 := by exact prefixLift 3318649
  have htrace : WordTrace (prefixWord ++ tailWord_3318649) baseStart_3318649 baseEnd_3318649 := by
    simpa [prefixWord, tailWord_3318649, baseEnd_3318649] using wordTrace_append hprefix tailTrace_3318649
  have hstable : (prefixWord ++ tailWord_3318649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318649).length < 2 ^ (prefixWord ++ tailWord_3318649).sum := by decide
  have hdescent : baseEnd_3318649 < baseStart_3318649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318663 : List Nat := [1, 1, 4, 2, 3, 3, 2, 1, 1, 1, 4]
def baseStart_3318663 : Nat := 118140960795 + 3318663 * 2 ^ 59
def prefixEnd_3318663 : Nat := 4983230072969 + 3 ^ 40 * 3318663 * 2
def baseEnd_3318663 : Nat := 1704069249292054449450253

theorem tailTrace_3318663 : CollatzResearch.WordTrace tailWord_3318663 prefixEnd_3318663 1704069249292054449450253 := by
  unfold tailWord_3318663
  simp only [CollatzResearch.WordTrace]
  refine ⟨121041583576058208361648643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80694389050705472241099095 121041583576058208361648643)
  ·
    refine ⟨181562375364087312542472965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121041583576058208361648643 181562375364087312542472965)
    ·
      refine ⟨34042945380766371101713681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181562375364087312542472965 34042945380766371101713681)
      ·
        refine ⟨25532209035574778326285261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34042945380766371101713681 25532209035574778326285261)
        ·
          refine ⟨9574578388340541872356973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25532209035574778326285261 9574578388340541872356973)
          ·
            refine ⟨3590466895627703202133865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9574578388340541872356973 3590466895627703202133865)
            ·
              refine ⟨2692850171720777401600399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3590466895627703202133865 2692850171720777401600399)
              ·
                refine ⟨4039275257581166102400599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2692850171720777401600399 4039275257581166102400599)
                ·
                  refine ⟨6058912886371749153600899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4039275257581166102400599 6058912886371749153600899)
                  ·
                    refine ⟨9088369329557623730401349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6058912886371749153600899 9088369329557623730401349)
                    ·
                      refine ⟨1704069249292054449450253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9088369329557623730401349 1704069249292054449450253)
                      ·
                        rfl

theorem cell23_3318663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_3318663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318663 prefixEnd_3318663 := by exact prefixLift 3318663
  have htrace : WordTrace (prefixWord ++ tailWord_3318663) baseStart_3318663 baseEnd_3318663 := by
    simpa [prefixWord, tailWord_3318663, baseEnd_3318663] using wordTrace_append hprefix tailTrace_3318663
  have hstable : (prefixWord ++ tailWord_3318663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318663).length < 2 ^ (prefixWord ++ tailWord_3318663).sum := by decide
  have hdescent : baseEnd_3318663 < baseStart_3318663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318757 : List Nat := [1, 3, 1, 6, 1, 2, 1, 2, 1, 3, 2]
def baseStart_3318757 : Nat := 118140960795 + 3318757 * 2 ^ 59
def prefixEnd_3318757 : Nat := 4983230072969 + 3 ^ 40 * 3318757 * 2
def baseEnd_3318757 : Nat := 1704117516473577081674821

theorem tailTrace_3318757 : CollatzResearch.WordTrace tailWord_3318757 prefixEnd_3318757 1704117516473577081674821 := by
  unfold tailWord_3318757
  simp only [CollatzResearch.WordTrace]
  refine ⟨121045012037717662415570525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80696674691811774943713683 121045012037717662415570525)
  ·
    refine ⟨45391879514144123405838947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121045012037717662415570525 45391879514144123405838947)
    ·
      refine ⟨68087819271216185108758421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45391879514144123405838947 68087819271216185108758421)
      ·
        refine ⟨3191616528338258676973051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68087819271216185108758421 3191616528338258676973051)
        ·
          refine ⟨4787424792507388015459577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191616528338258676973051 4787424792507388015459577)
          ·
            refine ⟨3590568594380541011594683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4787424792507388015459577 3590568594380541011594683)
            ·
              refine ⟨5385852891570811517392025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590568594380541011594683 5385852891570811517392025)
              ·
                refine ⟨4039389668678108638044019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5385852891570811517392025 4039389668678108638044019)
                ·
                  refine ⟨6059084503017162957066029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4039389668678108638044019 6059084503017162957066029)
                  ·
                    refine ⟨2272156688631436108899761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6059084503017162957066029 2272156688631436108899761)
                    ·
                      refine ⟨1704117516473577081674821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2272156688631436108899761 1704117516473577081674821)
                      ·
                        rfl

theorem cell23_3318757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_3318757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318757 prefixEnd_3318757 := by exact prefixLift 3318757
  have htrace : WordTrace (prefixWord ++ tailWord_3318757) baseStart_3318757 baseEnd_3318757 := by
    simpa [prefixWord, tailWord_3318757, baseEnd_3318757] using wordTrace_append hprefix tailTrace_3318757
  have hstable : (prefixWord ++ tailWord_3318757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318757).length < 2 ^ (prefixWord ++ tailWord_3318757).sum := by decide
  have hdescent : baseEnd_3318757 < baseStart_3318757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318770 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 1, 4, 2]
def baseStart_3318770 : Nat := 118140960795 + 3318770 * 2 ^ 59
def prefixEnd_3318770 : Nat := 4983230072969 + 3 ^ 40 * 3318770 * 2
def baseEnd_3318770 : Nat := 1704124191722085530812261

theorem tailTrace_3318770 : CollatzResearch.WordTrace tailWord_3318770 prefixEnd_3318770 1704124191722085530812261 := by
  unfold tailWord_3318770
  simp only [CollatzResearch.WordTrace]
  refine ⟨30261371546667641408948441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80696990791113710423862509 30261371546667641408948441)
  ·
    refine ⟨22696028660000731056711331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30261371546667641408948441 22696028660000731056711331)
    ·
      refine ⟨34044042990001096585066997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22696028660000731056711331 34044042990001096585066997)
      ·
        refine ⟨3191629030312602804850031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34044042990001096585066997 3191629030312602804850031)
        ·
          refine ⟨4787443545468904207275047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191629030312602804850031 4787443545468904207275047)
          ·
            refine ⟨7181165318203356310912571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4787443545468904207275047 7181165318203356310912571)
            ·
              refine ⟨10771747977305034466368857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7181165318203356310912571 10771747977305034466368857)
              ·
                refine ⟨8078810982978775849776643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10771747977305034466368857 8078810982978775849776643)
                ·
                  refine ⟨12118216474468163774664965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8078810982978775849776643 12118216474468163774664965)
                  ·
                    refine ⟨2272165588962780707749681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12118216474468163774664965 2272165588962780707749681)
                    ·
                      refine ⟨1704124191722085530812261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2272165588962780707749681 1704124191722085530812261)
                      ·
                        rfl

theorem cell23_3318770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_3318770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318770 prefixEnd_3318770 := by exact prefixLift 3318770
  have htrace : WordTrace (prefixWord ++ tailWord_3318770) baseStart_3318770 baseEnd_3318770 := by
    simpa [prefixWord, tailWord_3318770, baseEnd_3318770] using wordTrace_append hprefix tailTrace_3318770
  have hstable : (prefixWord ++ tailWord_3318770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318770).length < 2 ^ (prefixWord ++ tailWord_3318770).sum := by decide
  have hdescent : baseEnd_3318770 < baseStart_3318770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318789 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 2, 5]
def baseStart_3318789 : Nat := 118140960795 + 3318789 * 2 ^ 59
def prefixEnd_3318789 : Nat := 4983230072969 + 3 ^ 40 * 3318789 * 2
def baseEnd_3318789 : Nat := 568044649284840318824891

theorem tailTrace_3318789 : CollatzResearch.WordTrace tailWord_3318789 prefixEnd_3318789 568044649284840318824891 := by
  unfold tailWord_3318789
  simp only [CollatzResearch.WordTrace]
  refine ⟨121046179173601731880735421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80697452782401154587156947 121046179173601731880735421)
  ·
    refine ⟨45392317190100649455275783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121046179173601731880735421 45392317190100649455275783)
    ·
      refine ⟨68088475785150974182913675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45392317190100649455275783 68088475785150974182913675)
      ·
        refine ⟨102132713677726461274370513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68088475785150974182913675 102132713677726461274370513)
        ·
          refine ⟨76599535258294845955777885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102132713677726461274370513 76599535258294845955777885)
          ·
            refine ⟨28724825721860567233416707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76599535258294845955777885 28724825721860567233416707)
            ·
              refine ⟨43087238582790850850125061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28724825721860567233416707 43087238582790850850125061)
              ·
                refine ⟨8078857234273284534398449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43087238582790850850125061 8078857234273284534398449)
                ·
                  refine ⟨6059142925704963400798837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8078857234273284534398449 6059142925704963400798837)
                  ·
                    refine ⟨568044649284840318824891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6059142925704963400798837 568044649284840318824891)
                    ·
                      rfl

theorem cell23_3318789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_3318789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318789 prefixEnd_3318789 := by exact prefixLift 3318789
  have htrace : WordTrace (prefixWord ++ tailWord_3318789) baseStart_3318789 baseEnd_3318789 := by
    simpa [prefixWord, tailWord_3318789, baseEnd_3318789] using wordTrace_append hprefix tailTrace_3318789
  have hstable : (prefixWord ++ tailWord_3318789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318789).length < 2 ^ (prefixWord ++ tailWord_3318789).sum := by decide
  have hdescent : baseEnd_3318789 < baseStart_3318789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318796 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 2, 5, 2]
def baseStart_3318796 : Nat := 118140960795 + 3318796 * 2 ^ 59
def prefixEnd_3318796 : Nat := 4983230072969 + 3 ^ 40 * 3318796 * 2
def baseEnd_3318796 : Nat := 1704137542219102429087141

theorem tailTrace_3318796 : CollatzResearch.WordTrace tailWord_3318796 prefixEnd_3318796 1704137542219102429087141 := by
  unfold tailWord_3318796
  simp only [CollatzResearch.WordTrace]
  refine ⟨60523217242288186038120121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80697622989717581384160161 60523217242288186038120121)
  ·
    refine ⟨45392412931716139528590091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60523217242288186038120121 45392412931716139528590091)
    ·
      refine ⟨68088619397574209292885137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45392412931716139528590091 68088619397574209292885137)
      ·
        refine ⟨51066464548180656969663853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68088619397574209292885137 51066464548180656969663853)
        ·
          refine ⟨19149924205567746363623945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51066464548180656969663853 19149924205567746363623945)
          ·
            refine ⟨14362443154175809772717959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19149924205567746363623945 14362443154175809772717959)
            ·
              refine ⟨21543664731263714659076939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14362443154175809772717959 21543664731263714659076939)
              ·
                refine ⟨32315497096895571988615409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21543664731263714659076939 32315497096895571988615409)
                ·
                  refine ⟨24236622822671678991461557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32315497096895571988615409 24236622822671678991461557)
                  ·
                    refine ⟨2272183389625469905449521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24236622822671678991461557 2272183389625469905449521)
                    ·
                      refine ⟨1704137542219102429087141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2272183389625469905449521 1704137542219102429087141)
                      ·
                        rfl

theorem cell23_3318796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_3318796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318796 prefixEnd_3318796 := by exact prefixLift 3318796
  have htrace : WordTrace (prefixWord ++ tailWord_3318796) baseStart_3318796 baseEnd_3318796 := by
    simpa [prefixWord, tailWord_3318796, baseEnd_3318796] using wordTrace_append hprefix tailTrace_3318796
  have hstable : (prefixWord ++ tailWord_3318796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318796).length < 2 ^ (prefixWord ++ tailWord_3318796).sum := by decide
  have hdescent : baseEnd_3318796 < baseStart_3318796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318809 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 4, 1, 4]
def baseStart_3318809 : Nat := 118140960795 + 3318809 * 2 ^ 59
def prefixEnd_3318809 : Nat := 4983230072969 + 3 ^ 40 * 3318809 * 2
def baseEnd_3318809 : Nat := 1704144217467610878224581

theorem tailTrace_3318809 : CollatzResearch.WordTrace tailWord_3318809 prefixEnd_3318809 1704144217467610878224581 := by
  unfold tailWord_3318809
  simp only [CollatzResearch.WordTrace]
  refine ⟨121046908633529275296463481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80697939089019516864308987 121046908633529275296463481)
  ·
    refine ⟨90785181475146956472347611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121046908633529275296463481 90785181475146956472347611)
    ·
      refine ⟨136177772212720434708521417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90785181475146956472347611 136177772212720434708521417)
      ·
        refine ⟨102133329159540326031391063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136177772212720434708521417 102133329159540326031391063)
        ·
          refine ⟨153199993739310489047086595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102133329159540326031391063 153199993739310489047086595)
          ·
            refine ⟨229799990608965733570629893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153199993739310489047086595 229799990608965733570629893)
            ·
              refine ⟨43087498239181075044493105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229799990608965733570629893 43087498239181075044493105)
              ·
                refine ⟨32315623679385806283369829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43087498239181075044493105 32315623679385806283369829)
                ·
                  refine ⟨6059179439884838678131843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32315623679385806283369829 6059179439884838678131843)
                  ·
                    refine ⟨9088769159827258017197765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6059179439884838678131843 9088769159827258017197765)
                    ·
                      refine ⟨1704144217467610878224581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9088769159827258017197765 1704144217467610878224581)
                      ·
                        rfl

theorem cell23_3318809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_3318809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318809 prefixEnd_3318809 := by exact prefixLift 3318809
  have htrace : WordTrace (prefixWord ++ tailWord_3318809) baseStart_3318809 baseEnd_3318809 := by
    simpa [prefixWord, tailWord_3318809, baseEnd_3318809] using wordTrace_append hprefix tailTrace_3318809
  have hstable : (prefixWord ++ tailWord_3318809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318809).length < 2 ^ (prefixWord ++ tailWord_3318809).sum := by decide
  have hdescent : baseEnd_3318809 < baseStart_3318809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318823 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3318823 : Nat := 118140960795 + 3318823 * 2 ^ 59
def prefixEnd_3318823 : Nat := 4983230072969 + 3 ^ 40 * 3318823 * 2
def baseEnd_3318823 : Nat := 568050468732257941149839

theorem tailTrace_3318823 : CollatzResearch.WordTrace tailWord_3318823 prefixEnd_3318823 568050468732257941149839 := by
  unfold tailWord_3318823
  simp only [CollatzResearch.WordTrace]
  refine ⟨121047419255478555687473123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80698279503652370458315415 121047419255478555687473123)
  ·
    refine ⟨181571128883217833531209685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121047419255478555687473123 181571128883217833531209685)
    ·
      refine ⟨4255573333200417973387727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 181571128883217833531209685 4255573333200417973387727)
      ·
        refine ⟨6383359999800626960081591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4255573333200417973387727 6383359999800626960081591)
        ·
          refine ⟨9575039999700940440122387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6383359999800626960081591 9575039999700940440122387)
          ·
            refine ⟨14362559999551410660183581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9575039999700940440122387 14362559999551410660183581)
            ·
              refine ⟨5385959999831778997568843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14362559999551410660183581 5385959999831778997568843)
              ·
                refine ⟨8078939999747668496353265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385959999831778997568843 8078939999747668496353265)
                ·
                  refine ⟨6059204999810751372264949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8078939999747668496353265 6059204999810751372264949)
                  ·
                    refine ⟨568050468732257941149839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6059204999810751372264949 568050468732257941149839)
                    ·
                      rfl

theorem cell23_3318823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3318823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318823 prefixEnd_3318823 := by exact prefixLift 3318823
  have htrace : WordTrace (prefixWord ++ tailWord_3318823) baseStart_3318823 baseEnd_3318823 := by
    simpa [prefixWord, tailWord_3318823, baseEnd_3318823] using wordTrace_append hprefix tailTrace_3318823
  have hstable : (prefixWord ++ tailWord_3318823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318823).length < 2 ^ (prefixWord ++ tailWord_3318823).sum := by decide
  have hdescent : baseEnd_3318823 < baseStart_3318823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318853 : List Nat := [1, 3, 1, 1, 1, 3, 4, 4, 1, 4]
def baseStart_3318853 : Nat := 118140960795 + 3318853 * 2 ^ 59
def prefixEnd_3318853 : Nat := 4983230072969 + 3 ^ 40 * 3318853 * 2
def baseEnd_3318853 : Nat := 568055603538802902024793

theorem tailTrace_3318853 : CollatzResearch.WordTrace tailWord_3318853 prefixEnd_3318853 568055603538802902024793 := by
  unfold tailWord_3318853
  simp only [CollatzResearch.WordTrace]
  refine ⟨121048513445369870811065213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80699008963579913874043475 121048513445369870811065213)
  ·
    refine ⟨45393192542013701554149455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121048513445369870811065213 45393192542013701554149455)
    ·
      refine ⟨68089788813020552331224183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45393192542013701554149455 68089788813020552331224183)
      ·
        refine ⟨102134683219530828496836275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68089788813020552331224183 102134683219530828496836275)
        ·
          refine ⟨153202024829296242745254413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102134683219530828496836275 153202024829296242745254413)
          ·
            refine ⟨57450759310986091029470405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153202024829296242745254413 57450759310986091029470405)
            ·
              refine ⟨10772017370809892068025701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57450759310986091029470405 10772017370809892068025701)
              ·
                refine ⟨2019753257026854762754819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10772017370809892068025701 2019753257026854762754819)
                ·
                  refine ⟨3029629885540282144132229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019753257026854762754819 3029629885540282144132229)
                  ·
                    refine ⟨568055603538802902024793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3029629885540282144132229 568055603538802902024793)
                    ·
                      rfl

theorem cell23_3318853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_3318853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318853 prefixEnd_3318853 := by exact prefixLift 3318853
  have htrace : WordTrace (prefixWord ++ tailWord_3318853) baseStart_3318853 baseEnd_3318853 := by
    simpa [prefixWord, tailWord_3318853, baseEnd_3318853] using wordTrace_append hprefix tailTrace_3318853
  have hstable : (prefixWord ++ tailWord_3318853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318853).length < 2 ^ (prefixWord ++ tailWord_3318853).sum := by decide
  have hdescent : baseEnd_3318853 < baseStart_3318853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318859 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 3]
def baseStart_3318859 : Nat := 118140960795 + 3318859 * 2 ^ 59
def prefixEnd_3318859 : Nat := 4983230072969 + 3 ^ 40 * 3318859 * 2
def baseEnd_3318859 : Nat := 1704169891500335682599351

theorem tailTrace_3318859 : CollatzResearch.WordTrace tailWord_3318859 prefixEnd_3318859 1704169891500335682599351 := by
  unfold tailWord_3318859
  simp only [CollatzResearch.WordTrace]
  refine ⟨121048732283348133835783631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80699154855565422557189087 121048732283348133835783631)
  ·
    refine ⟨181573098425022200753675447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121048732283348133835783631 181573098425022200753675447)
    ·
      refine ⟨272359647637533301130513171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181573098425022200753675447 272359647637533301130513171)
      ·
        refine ⟨408539471456299951695769757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272359647637533301130513171 408539471456299951695769757)
        ·
          refine ⟨153202301796112481885913659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 408539471456299951695769757 153202301796112481885913659)
          ·
            refine ⟨229803452694168722828870489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153202301796112481885913659 229803452694168722828870489)
            ·
              refine ⟨172352589520626542121652867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229803452694168722828870489 172352589520626542121652867)
              ·
                refine ⟨258528884280939813182479301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172352589520626542121652867 258528884280939813182479301)
                ·
                  refine ⟨48474165802676214971714869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 258528884280939813182479301 48474165802676214971714869)
                  ·
                    refine ⟨4544453044000895153598269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48474165802676214971714869 4544453044000895153598269)
                    ·
                      refine ⟨1704169891500335682599351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4544453044000895153598269 1704169891500335682599351)
                      ·
                        rfl

theorem cell23_3318859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 3].length) (baseStart_3318859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318859 prefixEnd_3318859 := by exact prefixLift 3318859
  have htrace : WordTrace (prefixWord ++ tailWord_3318859) baseStart_3318859 baseEnd_3318859 := by
    simpa [prefixWord, tailWord_3318859, baseEnd_3318859] using wordTrace_append hprefix tailTrace_3318859
  have hstable : (prefixWord ++ tailWord_3318859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318859).length < 2 ^ (prefixWord ++ tailWord_3318859).sum := by decide
  have hdescent : baseEnd_3318859 < baseStart_3318859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318869 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_3318869 : Nat := 118140960795 + 3318869 * 2 ^ 59
def prefixEnd_3318869 : Nat := 4983230072969 + 3 ^ 40 * 3318869 * 2
def baseEnd_3318869 : Nat := 1704175026306880643474305

theorem tailTrace_3318869 : CollatzResearch.WordTrace tailWord_3318869 prefixEnd_3318869 1704175026306880643474305 := by
  unfold tailWord_3318869
  simp only [CollatzResearch.WordTrace]
  refine ⟨121049097013311905543647661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80699398008874603695765107 121049097013311905543647661)
  ·
    refine ⟨45393411379991964578867873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121049097013311905543647661 45393411379991964578867873)
    ·
      refine ⟨34045058534993973434150905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45393411379991964578867873 34045058534993973434150905)
      ·
        refine ⟨25533793901245480075613179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34045058534993973434150905 25533793901245480075613179)
        ·
          refine ⟨38300690851868220113419769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25533793901245480075613179 38300690851868220113419769)
          ·
            refine ⟨28725518138901165085064827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38300690851868220113419769 28725518138901165085064827)
            ·
              refine ⟨43088277208351747627597241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28725518138901165085064827 43088277208351747627597241)
              ·
                refine ⟨32316207906263810720697931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43088277208351747627597241 32316207906263810720697931)
                ·
                  refine ⟨48474311859395716081046897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32316207906263810720697931 48474311859395716081046897)
                  ·
                    refine ⟨36355733894546787060785173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48474311859395716081046897 36355733894546787060785173)
                    ·
                      refine ⟨1704175026306880643474305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36355733894546787060785173 1704175026306880643474305)
                      ·
                        rfl

theorem cell23_3318869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_3318869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318869 prefixEnd_3318869 := by exact prefixLift 3318869
  have htrace : WordTrace (prefixWord ++ tailWord_3318869) baseStart_3318869 baseEnd_3318869 := by
    simpa [prefixWord, tailWord_3318869, baseEnd_3318869] using wordTrace_append hprefix tailTrace_3318869
  have hstable : (prefixWord ++ tailWord_3318869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318869).length < 2 ^ (prefixWord ++ tailWord_3318869).sum := by decide
  have hdescent : baseEnd_3318869 < baseStart_3318869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318876 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_3318876 : Nat := 118140960795 + 3318876 * 2 ^ 59
def prefixEnd_3318876 : Nat := 4983230072969 + 3 ^ 40 * 3318876 * 2
def baseEnd_3318876 : Nat := 1704178620671462116086773

theorem tailTrace_3318876 : CollatzResearch.WordTrace tailWord_3318876 prefixEnd_3318876 1704178620671462116086773 := by
  unfold tailWord_3318876
  simp only [CollatzResearch.WordTrace]
  refine ⟨60524676162143272869576241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80699568216191030492768321 60524676162143272869576241)
  ·
    refine ⟨45393507121607454652182181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60524676162143272869576241 45393507121607454652182181)
    ·
      refine ⟨8511282585301397747284159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45393507121607454652182181 8511282585301397747284159)
      ·
        refine ⟨12766923877952096620926239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8511282585301397747284159 12766923877952096620926239)
        ·
          refine ⟨19150385816928144931389359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12766923877952096620926239 19150385816928144931389359)
          ·
            refine ⟨28725578725392217397084039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19150385816928144931389359 28725578725392217397084039)
            ·
              refine ⟨43088368088088326095626059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28725578725392217397084039 43088368088088326095626059)
              ·
                refine ⟨64632552132132489143439089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43088368088088326095626059 64632552132132489143439089)
                ·
                  refine ⟨48474414099099366857579317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64632552132132489143439089 48474414099099366857579317)
                  ·
                    refine ⟨4544476321790565642898061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48474414099099366857579317 4544476321790565642898061)
                    ·
                      refine ⟨1704178620671462116086773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4544476321790565642898061 1704178620671462116086773)
                      ·
                        rfl

theorem cell23_3318876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_3318876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318876 prefixEnd_3318876 := by exact prefixLift 3318876
  have htrace : WordTrace (prefixWord ++ tailWord_3318876) baseStart_3318876 baseEnd_3318876 := by
    simpa [prefixWord, tailWord_3318876, baseEnd_3318876] using wordTrace_append hprefix tailTrace_3318876
  have hstable : (prefixWord ++ tailWord_3318876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318876).length < 2 ^ (prefixWord ++ tailWord_3318876).sum := by decide
  have hdescent : baseEnd_3318876 < baseStart_3318876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318896 : List Nat := [2, 1, 1, 1, 5, 1, 1, 5, 1, 5]
def baseStart_3318896 : Nat := 118140960795 + 3318896 * 2 ^ 59
def prefixEnd_3318896 : Nat := 4983230072969 + 3 ^ 40 * 3318896 * 2
def baseEnd_3318896 : Nat := 568062963428184012612227

theorem tailTrace_3318896 : CollatzResearch.WordTrace tailWord_3318896 prefixEnd_3318896 568062963428184012612227 := by
  unfold tailWord_3318896
  simp only [CollatzResearch.WordTrace]
  refine ⟨60525040892107044577440271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80700054522809392769920361 60525040892107044577440271)
  ·
    refine ⟨90787561338160566866160407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60525040892107044577440271 90787561338160566866160407)
    ·
      refine ⟨136181342007240850299240611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90787561338160566866160407 136181342007240850299240611)
      ·
        refine ⟨204272013010861275448860917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136181342007240850299240611 204272013010861275448860917)
        ·
          refine ⟨19150501219768244573330711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204272013010861275448860917 19150501219768244573330711)
          ·
            refine ⟨28725751829652366859996067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19150501219768244573330711 28725751829652366859996067)
            ·
              refine ⟨43088627744478550289994101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28725751829652366859996067 43088627744478550289994101)
              ·
                refine ⟨4039558851044864089686947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43088627744478550289994101 4039558851044864089686947)
                ·
                  refine ⟨6059338276567296134530421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4039558851044864089686947 6059338276567296134530421)
                  ·
                    refine ⟨568062963428184012612227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6059338276567296134530421 568062963428184012612227)
                    ·
                      rfl

theorem cell23_3318896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 1, 5].length) (baseStart_3318896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318896 prefixEnd_3318896 := by exact prefixLift 3318896
  have htrace : WordTrace (prefixWord ++ tailWord_3318896) baseStart_3318896 baseEnd_3318896 := by
    simpa [prefixWord, tailWord_3318896, baseEnd_3318896] using wordTrace_append hprefix tailTrace_3318896
  have hstable : (prefixWord ++ tailWord_3318896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318896).length < 2 ^ (prefixWord ++ tailWord_3318896).sum := by decide
  have hdescent : baseEnd_3318896 < baseStart_3318896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318903 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 2, 3, 2]
def baseStart_3318903 : Nat := 118140960795 + 3318903 * 2 ^ 59
def prefixEnd_3318903 : Nat := 4983230072969 + 3 ^ 40 * 3318903 * 2
def baseEnd_3318903 : Nat := 1704192484649133510449149

theorem tailTrace_3318903 : CollatzResearch.WordTrace tailWord_3318903 prefixEnd_3318903 1704192484649133510449149 := by
  unfold tailWord_3318903
  simp only [CollatzResearch.WordTrace]
  refine ⟨121050337095188729350385363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80700224730125819566923575 121050337095188729350385363)
  ·
    refine ⟨181575505642783094025578045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121050337095188729350385363 181575505642783094025578045)
    ·
      refine ⟨68090814616043660259591767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181575505642783094025578045 68090814616043660259591767)
      ·
        refine ⟨102136221924065490389387651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68090814616043660259591767 102136221924065490389387651)
        ·
          refine ⟨153204332886098235584081477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102136221924065490389387651 153204332886098235584081477)
          ·
            refine ⟨28725812416143419172015277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153204332886098235584081477 28725812416143419172015277)
            ·
              refine ⟨10772179656053782189505729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28725812416143419172015277 10772179656053782189505729)
              ·
                refine ⟨8079134742040336642129297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10772179656053782189505729 8079134742040336642129297)
                ·
                  refine ⟨6059351056530252481596973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8079134742040336642129297 6059351056530252481596973)
                  ·
                    refine ⟨2272256646198844680598865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6059351056530252481596973 2272256646198844680598865)
                    ·
                      refine ⟨1704192484649133510449149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2272256646198844680598865 1704192484649133510449149)
                      ·
                        rfl

theorem cell23_3318903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 3, 2].length) (baseStart_3318903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318903 prefixEnd_3318903 := by exact prefixLift 3318903
  have htrace : WordTrace (prefixWord ++ tailWord_3318903) baseStart_3318903 baseEnd_3318903 := by
    simpa [prefixWord, tailWord_3318903, baseEnd_3318903] using wordTrace_append hprefix tailTrace_3318903
  have hstable : (prefixWord ++ tailWord_3318903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318903).length < 2 ^ (prefixWord ++ tailWord_3318903).sum := by decide
  have hdescent : baseEnd_3318903 < baseStart_3318903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318930 : List Nat := [3, 2, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3318930 : Nat := 118140960795 + 3318930 * 2 ^ 59
def prefixEnd_3318930 : Nat := 4983230072969 + 3 ^ 40 * 3318930 * 2
def baseEnd_3318930 : Nat := 568068782875601634937175

theorem tailTrace_3318930 : CollatzResearch.WordTrace tailWord_3318930 prefixEnd_3318930 568068782875601634937175 := by
  unfold tailWord_3318930
  simp only [CollatzResearch.WordTrace]
  refine ⟨30262830466522728240404561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80700881244060608641078829 30262830466522728240404561)
  ·
    refine ⟨22697122849892046180303421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30262830466522728240404561 22697122849892046180303421)
    ·
      refine ⟨8511421068709517317613783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22697122849892046180303421 8511421068709517317613783)
      ·
        refine ⟨12767131603064275976420675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8511421068709517317613783 12767131603064275976420675)
        ·
          refine ⟨19150697404596413964631013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12767131603064275976420675 19150697404596413964631013)
          ·
            refine ⟨3590755763361827618368315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19150697404596413964631013 3590755763361827618368315)
            ·
              refine ⟨5386133645042741427552473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590755763361827618368315 5386133645042741427552473)
              ·
                refine ⟨4039600233782056070664355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5386133645042741427552473 4039600233782056070664355)
                ·
                  refine ⟨6059400350673084105996533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4039600233782056070664355 6059400350673084105996533)
                  ·
                    refine ⟨568068782875601634937175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6059400350673084105996533 568068782875601634937175)
                    ·
                      rfl

theorem cell23_3318930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3318930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318930 prefixEnd_3318930 := by exact prefixLift 3318930
  have htrace : WordTrace (prefixWord ++ tailWord_3318930) baseStart_3318930 baseEnd_3318930 := by
    simpa [prefixWord, tailWord_3318930, baseEnd_3318930] using wordTrace_append hprefix tailTrace_3318930
  have hstable : (prefixWord ++ tailWord_3318930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318930).length < 2 ^ (prefixWord ++ tailWord_3318930).sum := by decide
  have hdescent : baseEnd_3318930 < baseStart_3318930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318943 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 1, 6]
def baseStart_3318943 : Nat := 118140960795 + 3318943 * 2 ^ 59
def prefixEnd_3318943 : Nat := 4983230072969 + 3 ^ 40 * 3318943 * 2
def baseEnd_3318943 : Nat := 568071007958437784649655

theorem tailTrace_3318943 : CollatzResearch.WordTrace tailWord_3318943 prefixEnd_3318943 568071007958437784649655 := by
  unfold tailWord_3318943
  simp only [CollatzResearch.WordTrace]
  refine ⟨121051796015043816181841483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80701197343362544121227655 121051796015043816181841483)
  ·
    refine ⟨181577694022565724272762225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121051796015043816181841483 181577694022565724272762225)
    ·
      refine ⟨136183270516924293204571669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181577694022565724272762225 136183270516924293204571669)
      ·
        refine ⟨6383590805480826243964297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136183270516924293204571669 6383590805480826243964297)
        ·
          refine ⟨4787693104110619682973223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6383590805480826243964297 4787693104110619682973223)
          ·
            refine ⟨7181539656165929524459835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4787693104110619682973223 7181539656165929524459835)
            ·
              refine ⟨10772309484248894286689753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7181539656165929524459835 10772309484248894286689753)
              ·
                refine ⟨8079232113186670715017315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10772309484248894286689753 8079232113186670715017315)
                ·
                  refine ⟨12118848169780006072525973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8079232113186670715017315 12118848169780006072525973)
                  ·
                    refine ⟨568071007958437784649655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12118848169780006072525973 568071007958437784649655)
                    ·
                      rfl

theorem cell23_3318943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 6].length) (baseStart_3318943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318943 prefixEnd_3318943 := by exact prefixLift 3318943
  have htrace : WordTrace (prefixWord ++ tailWord_3318943) baseStart_3318943 baseEnd_3318943 := by
    simpa [prefixWord, tailWord_3318943, baseEnd_3318943] using wordTrace_append hprefix tailTrace_3318943
  have hstable : (prefixWord ++ tailWord_3318943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318943).length < 2 ^ (prefixWord ++ tailWord_3318943).sum := by decide
  have hdescent : baseEnd_3318943 < baseStart_3318943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318967 : List Nat := [1, 1, 3, 1, 4, 1, 3, 4, 1, 2, 2]
def baseStart_3318967 : Nat := 118140960795 + 3318967 * 2 ^ 59
def prefixEnd_3318967 : Nat := 4983230072969 + 3 ^ 40 * 3318967 * 2
def baseEnd_3318967 : Nat := 1704225347411021260048855

theorem tailTrace_3318967 : CollatzResearch.WordTrace tailWord_3318967 prefixEnd_3318967 1704225347411021260048855 := by
  unfold tailWord_3318967
  simp only [CollatzResearch.WordTrace]
  refine ⟨121052671366956868280715155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80701780911304578853810103 121052671366956868280715155)
  ·
    refine ⟨181579007050435302421072733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121052671366956868280715155 181579007050435302421072733)
    ·
      refine ⟨68092127643913238407902275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181579007050435302421072733 68092127643913238407902275)
      ·
        refine ⟨102138191465869857611853413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68092127643913238407902275 102138191465869857611853413)
        ·
          refine ⟨19150910899850598302222515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102138191465869857611853413 19150910899850598302222515)
          ·
            refine ⟨28726366349775897453333773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19150910899850598302222515 28726366349775897453333773)
            ·
              refine ⟨10772387381165961545000165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28726366349775897453333773 10772387381165961545000165)
              ·
                refine ⟨2019822633968617789687531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10772387381165961545000165 2019822633968617789687531)
                ·
                  refine ⟨3029733950952926684531297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019822633968617789687531 3029733950952926684531297)
                  ·
                    refine ⟨2272300463214695013398473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3029733950952926684531297 2272300463214695013398473)
                    ·
                      refine ⟨1704225347411021260048855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2272300463214695013398473 1704225347411021260048855)
                      ·
                        rfl

theorem cell23_3318967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 1, 2, 2].length) (baseStart_3318967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318967 prefixEnd_3318967 := by exact prefixLift 3318967
  have htrace : WordTrace (prefixWord ++ tailWord_3318967) baseStart_3318967 baseEnd_3318967 := by
    simpa [prefixWord, tailWord_3318967, baseEnd_3318967] using wordTrace_append hprefix tailTrace_3318967
  have hstable : (prefixWord ++ tailWord_3318967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318967).length < 2 ^ (prefixWord ++ tailWord_3318967).sum := by decide
  have hdescent : baseEnd_3318967 < baseStart_3318967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3318980 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_3318980 : Nat := 118140960795 + 3318980 * 2 ^ 59
def prefixEnd_3318980 : Nat := 4983230072969 + 3 ^ 40 * 3318980 * 2
def baseEnd_3318980 : Nat := 1704232022659529709186295

theorem tailTrace_3318980 : CollatzResearch.WordTrace tailWord_3318980 prefixEnd_3318980 1704232022659529709186295 := by
  unfold tailWord_3318980
  simp only [CollatzResearch.WordTrace]
  refine ⟨60526572757954885750469197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80702097010606514333958929 60526572757954885750469197)
  ·
    refine ⟨22697464784233082156425949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60526572757954885750469197 22697464784233082156425949)
    ·
      refine ⟨8511549294087405808659731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22697464784233082156425949 8511549294087405808659731)
      ·
        refine ⟨12767323941131108712989597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8511549294087405808659731 12767323941131108712989597)
        ·
          refine ⟨4787746477924165767371099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12767323941131108712989597 4787746477924165767371099)
          ·
            refine ⟨7181619716886248651056649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4787746477924165767371099 7181619716886248651056649)
            ·
              refine ⟨5386214787664686488292487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7181619716886248651056649 5386214787664686488292487)
              ·
                refine ⟨8079322181497029732438731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5386214787664686488292487 8079322181497029732438731)
                ·
                  refine ⟨12118983272245544598658097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8079322181497029732438731 12118983272245544598658097)
                  ·
                    refine ⟨9089237454184158448993573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12118983272245544598658097 9089237454184158448993573)
                    ·
                      refine ⟨1704232022659529709186295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9089237454184158448993573 1704232022659529709186295)
                      ·
                        rfl

theorem cell23_3318980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_3318980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3318980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3318980 prefixEnd_3318980 := by exact prefixLift 3318980
  have htrace : WordTrace (prefixWord ++ tailWord_3318980) baseStart_3318980 baseEnd_3318980 := by
    simpa [prefixWord, tailWord_3318980, baseEnd_3318980] using wordTrace_append hprefix tailTrace_3318980
  have hstable : (prefixWord ++ tailWord_3318980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3318980).length < 2 ^ (prefixWord ++ tailWord_3318980).sum := by decide
  have hdescent : baseEnd_3318980 < baseStart_3318980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3318980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319016 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 4, 6]
def baseStart_3319016 : Nat := 118140960795 + 3319016 * 2 ^ 59
def prefixEnd_3319016 : Nat := 4983230072969 + 3 ^ 40 * 3319016 * 2
def baseEnd_3319016 : Nat := 568083502654363856112043

theorem tailTrace_3319016 : CollatzResearch.WordTrace tailWord_3319016 prefixEnd_3319016 568083502654363856112043 := by
  unfold tailWord_3319016
  simp only [CollatzResearch.WordTrace]
  refine ⟨60527229271889674824624451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80702972362519566432832601 60527229271889674824624451)
  ·
    refine ⟨90790843907834512236936677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60527229271889674824624451 90790843907834512236936677)
    ·
      refine ⟨17023283232718971044425627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90790843907834512236936677 17023283232718971044425627)
      ·
        refine ⟨25534924849078456566638441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17023283232718971044425627 25534924849078456566638441)
        ·
          refine ⟨19151193636808842424978831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25534924849078456566638441 19151193636808842424978831)
          ·
            refine ⟨28726790455213263637468247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19151193636808842424978831 28726790455213263637468247)
            ·
              refine ⟨43090185682819895456202371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28726790455213263637468247 43090185682819895456202371)
              ·
                refine ⟨64635278524229843184303557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43090185682819895456202371 64635278524229843184303557)
                ·
                  refine ⟨12119114723293095597056917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64635278524229843184303557 12119114723293095597056917)
                  ·
                    refine ⟨568083502654363856112043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12119114723293095597056917 568083502654363856112043)
                    ·
                      rfl

theorem cell23_3319016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_3319016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319016 prefixEnd_3319016 := by exact prefixLift 3319016
  have htrace : WordTrace (prefixWord ++ tailWord_3319016) baseStart_3319016 baseEnd_3319016 := by
    simpa [prefixWord, tailWord_3319016, baseEnd_3319016] using wordTrace_append hprefix tailTrace_3319016
  have hstable : (prefixWord ++ tailWord_3319016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319016).length < 2 ^ (prefixWord ++ tailWord_3319016).sum := by decide
  have hdescent : baseEnd_3319016 < baseStart_3319016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319080 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 7]
def baseStart_3319080 : Nat := 118140960795 + 3319080 * 2 ^ 59
def prefixEnd_3319080 : Nat := 4983230072969 + 3 ^ 40 * 3319080 * 2
def baseEnd_3319080 : Nat := 189364818969442146437315

theorem tailTrace_3319080 : CollatzResearch.WordTrace tailWord_3319080 prefixEnd_3319080 189364818969442146437315 := by
  unfold tailWord_3319080
  simp only [CollatzResearch.WordTrace]
  refine ⟨60528396407773744289789347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80704528543698325719719129 60528396407773744289789347)
  ·
    refine ⟨90792594611660616434684021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60528396407773744289789347 90792594611660616434684021)
    ·
      refine ⟨8511805744843182790751627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90792594611660616434684021 8511805744843182790751627)
      ·
        refine ⟨12767708617264774186127441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8511805744843182790751627 12767708617264774186127441)
        ·
          refine ⟨9575781462948580639595581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12767708617264774186127441 9575781462948580639595581)
          ·
            refine ⟨3590918048605717739848343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9575781462948580639595581 3590918048605717739848343)
            ·
              refine ⟨5386377072908576609772515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590918048605717739848343 5386377072908576609772515)
              ·
                refine ⟨8079565609362864914658773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5386377072908576609772515 8079565609362864914658773)
                ·
                  refine ⟨189364818969442146437315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8079565609362864914658773 189364818969442146437315)
                  ·
                    rfl

theorem cell23_3319080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 7].length) (baseStart_3319080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319080 prefixEnd_3319080 := by exact prefixLift 3319080
  have htrace : WordTrace (prefixWord ++ tailWord_3319080) baseStart_3319080 baseEnd_3319080 := by
    simpa [prefixWord, tailWord_3319080, baseEnd_3319080] using wordTrace_append hprefix tailTrace_3319080
  have hstable : (prefixWord ++ tailWord_3319080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319080).length < 2 ^ (prefixWord ++ tailWord_3319080).sum := by decide
  have hdescent : baseEnd_3319080 < baseStart_3319080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319113 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 2, 1, 4]
def baseStart_3319113 : Nat := 118140960795 + 3319113 * 2 ^ 59
def prefixEnd_3319113 : Nat := 4983230072969 + 3 ^ 40 * 3319113 * 2
def baseEnd_3319113 : Nat := 1704300315586577688823183

theorem tailTrace_3319113 : CollatzResearch.WordTrace tailWord_3319113 prefixEnd_3319113 1704300315586577688823183 := by
  unfold tailWord_3319113
  simp only [CollatzResearch.WordTrace]
  refine ⟨121057996424427935215529993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80705330949618623477019995 121057996424427935215529993)
  ·
    refine ⟨90793497318320951411647495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121057996424427935215529993 90793497318320951411647495)
    ·
      refine ⟨136190245977481427117471243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90793497318320951411647495 136190245977481427117471243)
      ·
        refine ⟨204285368966222140676206865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136190245977481427117471243 204285368966222140676206865)
        ·
          refine ⟨153214026724666605507155149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204285368966222140676206865 153214026724666605507155149)
          ·
            refine ⟨57455260021749977065183181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153214026724666605507155149 57455260021749977065183181)
            ·
              refine ⟨21545722508156241399443693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57455260021749977065183181 21545722508156241399443693)
              ·
                refine ⟨8079645940558590524791385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21545722508156241399443693 8079645940558590524791385)
                ·
                  refine ⟨6059734455418942893593539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8079645940558590524791385 6059734455418942893593539)
                  ·
                    refine ⟨9089601683128414340390309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6059734455418942893593539 9089601683128414340390309)
                    ·
                      refine ⟨1704300315586577688823183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9089601683128414340390309 1704300315586577688823183)
                      ·
                        rfl

theorem cell23_3319113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_3319113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319113 prefixEnd_3319113 := by exact prefixLift 3319113
  have htrace : WordTrace (prefixWord ++ tailWord_3319113) baseStart_3319113 baseEnd_3319113 := by
    simpa [prefixWord, tailWord_3319113, baseEnd_3319113] using wordTrace_append hprefix tailTrace_3319113
  have hstable : (prefixWord ++ tailWord_3319113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319113).length < 2 ^ (prefixWord ++ tailWord_3319113).sum := by decide
  have hdescent : baseEnd_3319113 < baseStart_3319113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319153 : List Nat := [1, 2, 2, 2, 1, 2, 4, 3, 6]
def baseStart_3319153 : Nat := 118140960795 + 3319153 * 2 ^ 59
def prefixEnd_3319153 : Nat := 4983230072969 + 3 ^ 40 * 3319153 * 2
def baseEnd_3319153 : Nat := 189368983868084170258111

theorem tailTrace_3319153 : CollatzResearch.WordTrace tailWord_3319153 prefixEnd_3319153 189368983868084170258111 := by
  unfold tailWord_3319153
  simp only [CollatzResearch.WordTrace]
  refine ⟨121059455344283022046986113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80706303562855348031324075 121059455344283022046986113)
  ·
    refine ⟨90794591508212266535239585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121059455344283022046986113 90794591508212266535239585)
    ·
      refine ⟨68095943631159199901429689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90794591508212266535239585 68095943631159199901429689)
      ·
        refine ⟨51071957723369399926072267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68095943631159199901429689 51071957723369399926072267)
        ·
          refine ⟨76607936585054099889108401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51071957723369399926072267 76607936585054099889108401)
          ·
            refine ⟨57455952438790574916831301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76607936585054099889108401 57455952438790574916831301)
            ·
              refine ⟨10772991082273232796905869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57455952438790574916831301 10772991082273232796905869)
              ·
                refine ⟨4039871655852462298839701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10772991082273232796905869 4039871655852462298839701)
                ·
                  refine ⟨189368983868084170258111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4039871655852462298839701 189368983868084170258111)
                  ·
                    rfl

theorem cell23_3319153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 6].length) (baseStart_3319153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319153 prefixEnd_3319153 := by exact prefixLift 3319153
  have htrace : WordTrace (prefixWord ++ tailWord_3319153) baseStart_3319153 baseEnd_3319153 := by
    simpa [prefixWord, tailWord_3319153, baseEnd_3319153] using wordTrace_append hprefix tailTrace_3319153
  have hstable : (prefixWord ++ tailWord_3319153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319153).length < 2 ^ (prefixWord ++ tailWord_3319153).sum := by decide
  have hdescent : baseEnd_3319153 < baseStart_3319153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319157 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 3, 4]
def baseStart_3319157 : Nat := 118140960795 + 3319157 * 2 ^ 59
def prefixEnd_3319157 : Nat := 4983230072969 + 3 ^ 40 * 3319157 * 2
def baseEnd_3319157 : Nat := 568107636245125172224327

theorem tailTrace_3319157 : CollatzResearch.WordTrace tailWord_3319157 prefixEnd_3319157 568107636245125172224327 := by
  unfold tailWord_3319157
  simp only [CollatzResearch.WordTrace]
  refine ⟨121059601236268530730131725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80706400824179020486754483 121059601236268530730131725)
  ·
    refine ⟨45397350463600699023799397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121059601236268530730131725 45397350463600699023799397)
    ·
      refine ⟨8512003211925131066962387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45397350463600699023799397 8512003211925131066962387)
      ·
        refine ⟨12768004817887696600443581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8512003211925131066962387 12768004817887696600443581)
        ·
          refine ⟨4788001806707886225166343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12768004817887696600443581 4788001806707886225166343)
          ·
            refine ⟨7182002710061829337749515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4788001806707886225166343 7182002710061829337749515)
            ·
              refine ⟨10773004065092744006624273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7182002710061829337749515 10773004065092744006624273)
              ·
                refine ⟨8079753048819558004968205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10773004065092744006624273 8079753048819558004968205)
                ·
                  refine ⟨3029907393307334251863077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8079753048819558004968205 3029907393307334251863077)
                  ·
                    refine ⟨568107636245125172224327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3029907393307334251863077 568107636245125172224327)
                    ·
                      rfl

theorem cell23_3319157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_3319157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319157 prefixEnd_3319157 := by exact prefixLift 3319157
  have htrace : WordTrace (prefixWord ++ tailWord_3319157) baseStart_3319157 baseEnd_3319157 := by
    simpa [prefixWord, tailWord_3319157, baseEnd_3319157] using wordTrace_append hprefix tailTrace_3319157
  have hstable : (prefixWord ++ tailWord_3319157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319157).length < 2 ^ (prefixWord ++ tailWord_3319157).sum := by decide
  have hdescent : baseEnd_3319157 < baseStart_3319157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319180 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 5, 1, 3]
def baseStart_3319180 : Nat := 118140960795 + 3319180 * 2 ^ 59
def prefixEnd_3319180 : Nat := 4983230072969 + 3 ^ 40 * 3319180 * 2
def baseEnd_3319180 : Nat := 1704334718790428926685375

theorem tailTrace_3319180 : CollatzResearch.WordTrace tailWord_3319180 prefixEnd_3319180 1704334718790428926685375 := by
  unfold tailWord_3319180
  simp only [CollatzResearch.WordTrace]
  refine ⟨60530220057592602829109497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80706960076790137105479329 60530220057592602829109497)
  ·
    refine ⟨45397665043194452121832123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60530220057592602829109497 45397665043194452121832123)
    ·
      refine ⟨68096497564791678182748185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45397665043194452121832123 68096497564791678182748185)
      ·
        refine ⟨51072373173593758637061139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68096497564791678182748185 51072373173593758637061139)
        ·
          refine ⟨76608559760390637955591709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51072373173593758637061139 76608559760390637955591709)
          ·
            refine ⟨28728209910146489233346891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76608559760390637955591709 28728209910146489233346891)
            ·
              refine ⟨43092314865219733850020337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28728209910146489233346891 43092314865219733850020337)
              ·
                refine ⟨32319236148914800387515253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43092314865219733850020337 32319236148914800387515253)
                ·
                  refine ⟨3029928388960762536329555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32319236148914800387515253 3029928388960762536329555)
                  ·
                    refine ⟨4544892583441143804494333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3029928388960762536329555 4544892583441143804494333)
                    ·
                      refine ⟨1704334718790428926685375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4544892583441143804494333 1704334718790428926685375)
                      ·
                        rfl

theorem cell23_3319180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_3319180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319180 prefixEnd_3319180 := by exact prefixLift 3319180
  have htrace : WordTrace (prefixWord ++ tailWord_3319180) baseStart_3319180 baseEnd_3319180 := by
    simpa [prefixWord, tailWord_3319180, baseEnd_3319180] using wordTrace_append hprefix tailTrace_3319180
  have hstable : (prefixWord ++ tailWord_3319180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319180).length < 2 ^ (prefixWord ++ tailWord_3319180).sum := by decide
  have hdescent : baseEnd_3319180 < baseStart_3319180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319197 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_3319197 : Nat := 118140960795 + 3319197 * 2 ^ 59
def prefixEnd_3319197 : Nat := 4983230072969 + 3 ^ 40 * 3319197 * 2
def baseEnd_3319197 : Nat := 1704343447961555360172797

theorem tailTrace_3319197 : CollatzResearch.WordTrace tailWord_3319197 prefixEnd_3319197 1704343447961555360172797 := by
  unfold tailWord_3319197
  simp only [CollatzResearch.WordTrace]
  refine ⟨121061060156123617561587845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80707373437415745041058563 121061060156123617561587845)
  ·
    refine ⟨22698948779273178292797721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121061060156123617561587845 22698948779273178292797721)
    ·
      refine ⟨17024211584454883719598291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22698948779273178292797721 17024211584454883719598291)
      ·
        refine ⟨25536317376682325579397437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17024211584454883719598291 25536317376682325579397437)
        ·
          refine ⟨9576119016255872092274039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25536317376682325579397437 9576119016255872092274039)
          ·
            refine ⟨14364178524383808138411059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9576119016255872092274039 14364178524383808138411059)
            ·
              refine ⟨21546267786575712207616589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14364178524383808138411059 21546267786575712207616589)
              ·
                refine ⟨8079850419965892077856221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21546267786575712207616589 8079850419965892077856221)
                ·
                  refine ⟨3029943907487209529196083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8079850419965892077856221 3029943907487209529196083)
                  ·
                    refine ⟨4544915861230814293794125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3029943907487209529196083 4544915861230814293794125)
                    ·
                      refine ⟨1704343447961555360172797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4544915861230814293794125 1704343447961555360172797)
                      ·
                        rfl

theorem cell23_3319197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_3319197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319197 prefixEnd_3319197 := by exact prefixLift 3319197
  have htrace : WordTrace (prefixWord ++ tailWord_3319197) baseStart_3319197 baseEnd_3319197 := by
    simpa [prefixWord, tailWord_3319197, baseEnd_3319197] using wordTrace_append hprefix tailTrace_3319197
  have hstable : (prefixWord ++ tailWord_3319197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319197).length < 2 ^ (prefixWord ++ tailWord_3319197).sum := by decide
  have hdescent : baseEnd_3319197 < baseStart_3319197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319223 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_3319223 : Nat := 118140960795 + 3319223 * 2 ^ 59
def prefixEnd_3319223 : Nat := 4983230072969 + 3 ^ 40 * 3319223 * 2
def baseEnd_3319223 : Nat := 1704356798458572258447677

theorem tailTrace_3319223 : CollatzResearch.WordTrace tailWord_3319223 prefixEnd_3319223 1704356798458572258447677 := by
  unfold tailWord_3319223
  simp only [CollatzResearch.WordTrace]
  refine ⟨121062008454029424002034323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80708005636019616001356215 121062008454029424002034323)
  ·
    refine ⟨181593012681044136003051485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121062008454029424002034323 181593012681044136003051485)
    ·
      refine ⟨68097379755391551001144307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181593012681044136003051485 68097379755391551001144307)
      ·
        refine ⟨102146069633087326501716461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68097379755391551001144307 102146069633087326501716461)
        ·
          refine ⟨38304776112407747438143673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102146069633087326501716461 38304776112407747438143673)
          ·
            refine ⟨28728582084305810578607755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38304776112407747438143673 28728582084305810578607755)
            ·
              refine ⟨43092873126458715867911633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28728582084305810578607755 43092873126458715867911633)
              ·
                refine ⟨32319654844844036900933725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43092873126458715867911633 32319654844844036900933725)
                ·
                  refine ⟨12119870566816513837850147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32319654844844036900933725 12119870566816513837850147)
                  ·
                    refine ⟨18179805850224770756775221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12119870566816513837850147 18179805850224770756775221)
                    ·
                      refine ⟨1704356798458572258447677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18179805850224770756775221 1704356798458572258447677)
                      ·
                        rfl

theorem cell23_3319223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_3319223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319223 prefixEnd_3319223 := by exact prefixLift 3319223
  have htrace : WordTrace (prefixWord ++ tailWord_3319223) baseStart_3319223 baseEnd_3319223 := by
    simpa [prefixWord, tailWord_3319223, baseEnd_3319223] using wordTrace_append hprefix tailTrace_3319223
  have hstable : (prefixWord ++ tailWord_3319223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319223).length < 2 ^ (prefixWord ++ tailWord_3319223).sum := by decide
  have hdescent : baseEnd_3319223 < baseStart_3319223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319240 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_3319240 : Nat := 118140960795 + 3319240 * 2 ^ 59
def prefixEnd_3319240 : Nat := 4983230072969 + 3 ^ 40 * 3319240 * 2
def baseEnd_3319240 : Nat := 1704365527629698691935099

theorem tailTrace_3319240 : CollatzResearch.WordTrace tailWord_3319240 prefixEnd_3319240 1704365527629698691935099 := by
  unfold tailWord_3319240
  simp only [CollatzResearch.WordTrace]
  refine ⟨60531314247483917952701587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80708418996645223936935449 60531314247483917952701587)
  ·
    refine ⟨90796971371225876929052381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60531314247483917952701587 90796971371225876929052381)
    ·
      refine ⟨34048864264209703848394643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90796971371225876929052381 34048864264209703848394643)
      ·
        refine ⟨51073296396314555772591965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34048864264209703848394643 51073296396314555772591965)
        ·
          refine ⟨19152486148617958414721987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51073296396314555772591965 19152486148617958414721987)
          ·
            refine ⟨28728729222926937622082981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19152486148617958414721987 28728729222926937622082981)
            ·
              refine ⟨5386636729298800804140559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28728729222926937622082981 5386636729298800804140559)
              ·
                refine ⟨8079955093948201206210839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5386636729298800804140559 8079955093948201206210839)
                ·
                  refine ⟨12119932640922301809316259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8079955093948201206210839 12119932640922301809316259)
                  ·
                    refine ⟨18179898961383452713974389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12119932640922301809316259 18179898961383452713974389)
                    ·
                      refine ⟨1704365527629698691935099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18179898961383452713974389 1704365527629698691935099)
                      ·
                        rfl

theorem cell23_3319240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_3319240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319240 prefixEnd_3319240 := by exact prefixLift 3319240
  have htrace : WordTrace (prefixWord ++ tailWord_3319240) baseStart_3319240 baseEnd_3319240 := by
    simpa [prefixWord, tailWord_3319240, baseEnd_3319240] using wordTrace_append hprefix tailTrace_3319240
  have hstable : (prefixWord ++ tailWord_3319240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319240).length < 2 ^ (prefixWord ++ tailWord_3319240).sum := by decide
  have hdescent : baseEnd_3319240 < baseStart_3319240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319263 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 6]
def baseStart_3319263 : Nat := 118140960795 + 3319263 * 2 ^ 59
def prefixEnd_3319263 : Nat := 4983230072969 + 3 ^ 40 * 3319263 * 2
def baseEnd_3319263 : Nat := 1704377337684752101947493

theorem tailTrace_3319263 : CollatzResearch.WordTrace tailWord_3319263 prefixEnd_3319263 1704377337684752101947493 := by
  unfold tailWord_3319263
  simp only [CollatzResearch.WordTrace]
  refine ⟨121063467373884510833490443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80708978249256340555660295 121063467373884510833490443)
  ·
    refine ⟨181595201060826766250235665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121063467373884510833490443 181595201060826766250235665)
    ·
      refine ⟨136196400795620074687676749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181595201060826766250235665 136196400795620074687676749)
      ·
        refine ⟨51073650298357528007878781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136196400795620074687676749 51073650298357528007878781)
        ·
          refine ⟨19152618861884073002954543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51073650298357528007878781 19152618861884073002954543)
          ·
            refine ⟨28728928292826109504431815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19152618861884073002954543 28728928292826109504431815)
            ·
              refine ⟨43093392439239164256647723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28728928292826109504431815 43093392439239164256647723)
              ·
                refine ⟨64640088658858746384971585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43093392439239164256647723 64640088658858746384971585)
                ·
                  refine ⟨48480066494144059788728689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64640088658858746384971585 48480066494144059788728689)
                  ·
                    refine ⟨36360049870608044841546517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48480066494144059788728689 36360049870608044841546517)
                    ·
                      refine ⟨1704377337684752101947493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36360049870608044841546517 1704377337684752101947493)
                      ·
                        rfl

theorem cell23_3319263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_3319263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319263 prefixEnd_3319263 := by exact prefixLift 3319263
  have htrace : WordTrace (prefixWord ++ tailWord_3319263) baseStart_3319263 baseEnd_3319263 := by
    simpa [prefixWord, tailWord_3319263, baseEnd_3319263] using wordTrace_append hprefix tailTrace_3319263
  have hstable : (prefixWord ++ tailWord_3319263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319263).length < 2 ^ (prefixWord ++ tailWord_3319263).sum := by decide
  have hdescent : baseEnd_3319263 < baseStart_3319263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319283 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 5]
def baseStart_3319283 : Nat := 118140960795 + 3319283 * 2 ^ 59
def prefixEnd_3319283 : Nat := 4983230072969 + 3 ^ 40 * 3319283 * 2
def baseEnd_3319283 : Nat := 1704387607297842023697401

theorem tailTrace_3319283 : CollatzResearch.WordTrace tailWord_3319283 prefixEnd_3319283 1704387607297842023697401 := by
  unfold tailWord_3319283
  simp only [CollatzResearch.WordTrace]
  refine ⟨121064196833812054249218503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80709464555874702832812335 121064196833812054249218503)
  ·
    refine ⟨181596295250718081373827755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121064196833812054249218503 181596295250718081373827755)
    ·
      refine ⟨272394442876077122060741633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181596295250718081373827755 272394442876077122060741633)
      ·
        refine ⟨204295832157057841545556225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272394442876077122060741633 204295832157057841545556225)
        ·
          refine ⟨153221874117793381159167169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204295832157057841545556225 153221874117793381159167169)
          ·
            refine ⟨114916405588345035869375377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153221874117793381159167169 114916405588345035869375377)
            ·
              refine ⟨86187304191258776902031533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114916405588345035869375377 86187304191258776902031533)
              ·
                refine ⟨32320239071722041338261825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86187304191258776902031533 32320239071722041338261825)
                ·
                  refine ⟨24240179303791531003696369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32320239071722041338261825 24240179303791531003696369)
                  ·
                    refine ⟨18180134477843648252772277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24240179303791531003696369 18180134477843648252772277)
                    ·
                      refine ⟨1704387607297842023697401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18180134477843648252772277 1704387607297842023697401)
                      ·
                        rfl

theorem cell23_3319283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_3319283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319283 prefixEnd_3319283 := by exact prefixLift 3319283
  have htrace : WordTrace (prefixWord ++ tailWord_3319283) baseStart_3319283 baseEnd_3319283 := by
    simpa [prefixWord, tailWord_3319283, baseEnd_3319283] using wordTrace_append hprefix tailTrace_3319283
  have hstable : (prefixWord ++ tailWord_3319283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319283).length < 2 ^ (prefixWord ++ tailWord_3319283).sum := by decide
  have hdescent : baseEnd_3319283 < baseStart_3319283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319327 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 1, 4, 2]
def baseStart_3319327 : Nat := 118140960795 + 3319327 * 2 ^ 59
def prefixEnd_3319327 : Nat := 4983230072969 + 3 ^ 40 * 3319327 * 2
def baseEnd_3319327 : Nat := 1704410200446639851547199

theorem tailTrace_3319327 : CollatzResearch.WordTrace tailWord_3319327 prefixEnd_3319327 1704410200446639851547199 := by
  unfold tailWord_3319327
  simp only [CollatzResearch.WordTrace]
  refine ⟨121065801645652649763820235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80710534430435099842546823 121065801645652649763820235)
  ·
    refine ⟨181598702468478974645730353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121065801645652649763820235 181598702468478974645730353)
    ·
      refine ⟨136199026851359230984297765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181598702468478974645730353 136199026851359230984297765)
      ·
        refine ⟨25537317534629855809555831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136199026851359230984297765 25537317534629855809555831)
        ·
          refine ⟨38305976301944783714333747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25537317534629855809555831 38305976301944783714333747)
          ·
            refine ⟨57458964452917175571500621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38305976301944783714333747 57458964452917175571500621)
            ·
              refine ⟨21547111669843940839312733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57458964452917175571500621 21547111669843940839312733)
              ·
                refine ⟨8080166876191477814742275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21547111669843940839312733 8080166876191477814742275)
                ·
                  refine ⟨12120250314287216722113413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8080166876191477814742275 12120250314287216722113413)
                  ·
                    refine ⟨2272546933928853135396265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12120250314287216722113413 2272546933928853135396265)
                    ·
                      refine ⟨1704410200446639851547199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2272546933928853135396265 1704410200446639851547199)
                      ·
                        rfl

theorem cell23_3319327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_3319327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319327 prefixEnd_3319327 := by exact prefixLift 3319327
  have htrace : WordTrace (prefixWord ++ tailWord_3319327) baseStart_3319327 baseEnd_3319327 := by
    simpa [prefixWord, tailWord_3319327, baseEnd_3319327] using wordTrace_append hprefix tailTrace_3319327
  have hstable : (prefixWord ++ tailWord_3319327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319327).length < 2 ^ (prefixWord ++ tailWord_3319327).sum := by decide
  have hdescent : baseEnd_3319327 < baseStart_3319327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319330 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_3319330 : Nat := 118140960795 + 3319330 * 2 ^ 59
def prefixEnd_3319330 : Nat := 4983230072969 + 3 ^ 40 * 3319330 * 2
def baseEnd_3319330 : Nat := 1704411740888603339809685

theorem tailTrace_3319330 : CollatzResearch.WordTrace tailWord_3319330 prefixEnd_3319330 1704411740888603339809685 := by
  unfold tailWord_3319330
  simp only [CollatzResearch.WordTrace]
  refine ⟨30266477766160445319044861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80710607376427854184119629 30266477766160445319044861)
  ·
    refine ⟨11349929162310166994641823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30266477766160445319044861 11349929162310166994641823)
    ·
      refine ⟨17024893743465250491962735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11349929162310166994641823 17024893743465250491962735)
      ·
        refine ⟨25537340615197875737944103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17024893743465250491962735 25537340615197875737944103)
        ·
          refine ⟨38306010922796813606916155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25537340615197875737944103 38306010922796813606916155)
          ·
            refine ⟨57459016384195220410374233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38306010922796813606916155 57459016384195220410374233)
            ·
              refine ⟨43094262288146415307780675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57459016384195220410374233 43094262288146415307780675)
              ·
                refine ⟨64641393432219622961671013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43094262288146415307780675 64641393432219622961671013)
                ·
                  refine ⟨12120261268541179305313315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64641393432219622961671013 12120261268541179305313315)
                  ·
                    refine ⟨18180391902811768957969973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12120261268541179305313315 18180391902811768957969973)
                    ·
                      refine ⟨1704411740888603339809685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18180391902811768957969973 1704411740888603339809685)
                      ·
                        rfl

theorem cell23_3319330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_3319330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319330 prefixEnd_3319330 := by exact prefixLift 3319330
  have htrace : WordTrace (prefixWord ++ tailWord_3319330) baseStart_3319330 baseEnd_3319330 := by
    simpa [prefixWord, tailWord_3319330, baseEnd_3319330] using wordTrace_append hprefix tailTrace_3319330
  have hstable : (prefixWord ++ tailWord_3319330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319330).length < 2 ^ (prefixWord ++ tailWord_3319330).sum := by decide
  have hdescent : baseEnd_3319330 < baseStart_3319330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319367 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 7]
def baseStart_3319367 : Nat := 118140960795 + 3319367 * 2 ^ 59
def prefixEnd_3319367 : Nat := 4983230072969 + 3 ^ 40 * 3319367 * 2
def baseEnd_3319367 : Nat := 189381193296979966116335

theorem tailTrace_3319367 : CollatzResearch.WordTrace tailWord_3319367 prefixEnd_3319367 189381193296979966116335 := by
  unfold tailWord_3319367
  simp only [CollatzResearch.WordTrace]
  refine ⟨121067260565507736595276355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80711507043671824396850903 121067260565507736595276355)
  ·
    refine ⟨181600890848261604892914533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121067260565507736595276355 181600890848261604892914533)
    ·
      refine ⟨34050167034049050917421475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181600890848261604892914533 34050167034049050917421475)
      ·
        refine ⟨51075250551073576376132213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34050167034049050917421475 51075250551073576376132213)
        ·
          refine ⟨4788304739163147785262395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51075250551073576376132213 4788304739163147785262395)
          ·
            refine ⟨7182457108744721677893593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4788304739163147785262395 7182457108744721677893593)
            ·
              refine ⟨5386842831558541258420195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7182457108744721677893593 5386842831558541258420195)
              ·
                refine ⟨8080264247337811887630293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5386842831558541258420195 8080264247337811887630293)
                ·
                  refine ⟨189381193296979966116335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8080264247337811887630293 189381193296979966116335)
                  ·
                    rfl

theorem cell23_3319367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 7].length) (baseStart_3319367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319367 prefixEnd_3319367 := by exact prefixLift 3319367
  have htrace : WordTrace (prefixWord ++ tailWord_3319367) baseStart_3319367 baseEnd_3319367 := by
    simpa [prefixWord, tailWord_3319367, baseEnd_3319367] using wordTrace_append hprefix tailTrace_3319367
  have hstable : (prefixWord ++ tailWord_3319367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319367).length < 2 ^ (prefixWord ++ tailWord_3319367).sum := by decide
  have hdescent : baseEnd_3319367 < baseStart_3319367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319378 : List Nat := [3, 2, 2, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_3319378 : Nat := 118140960795 + 3319378 * 2 ^ 59
def prefixEnd_3319378 : Nat := 4983230072969 + 3 ^ 40 * 3319378 * 2
def baseEnd_3319378 : Nat := 1704436387960019152009465

theorem tailTrace_3319378 : CollatzResearch.WordTrace tailWord_3319378 prefixEnd_3319378 1704436387960019152009465 := by
  unfold tailWord_3319378
  simp only [CollatzResearch.WordTrace]
  refine ⟨30266915442116971368481697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80711774512311923649284525 30266915442116971368481697)
  ·
    refine ⟨22700186581587728526361273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30266915442116971368481697 22700186581587728526361273)
    ·
      refine ⟨17025139936190796394770955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22700186581587728526361273 17025139936190796394770955)
      ·
        refine ⟨25537709904286194592156433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17025139936190796394770955 25537709904286194592156433)
        ·
          refine ⟨19153282428214645944117325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25537709904286194592156433 19153282428214645944117325)
          ·
            refine ⟨7182480910580492229043997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19153282428214645944117325 7182480910580492229043997)
            ·
              refine ⟨2693430341467684585891499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7182480910580492229043997 2693430341467684585891499)
              ·
                refine ⟨4040145512201526878837249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2693430341467684585891499 4040145512201526878837249)
                ·
                  refine ⟨3030109134151145159127937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4040145512201526878837249 3030109134151145159127937)
                  ·
                    refine ⟨2272581850613358869345953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3030109134151145159127937 2272581850613358869345953)
                    ·
                      refine ⟨1704436387960019152009465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2272581850613358869345953 1704436387960019152009465)
                      ·
                        rfl

theorem cell23_3319378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_3319378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319378 prefixEnd_3319378 := by exact prefixLift 3319378
  have htrace : WordTrace (prefixWord ++ tailWord_3319378) baseStart_3319378 baseEnd_3319378 := by
    simpa [prefixWord, tailWord_3319378, baseEnd_3319378] using wordTrace_append hprefix tailTrace_3319378
  have hstable : (prefixWord ++ tailWord_3319378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319378).length < 2 ^ (prefixWord ++ tailWord_3319378).sum := by decide
  have hdescent : baseEnd_3319378 < baseStart_3319378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319380 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_3319380 : Nat := 118140960795 + 3319380 * 2 ^ 59
def prefixEnd_3319380 : Nat := 4983230072969 + 3 ^ 40 * 3319380 * 2
def baseEnd_3319380 : Nat := 568145804973776048061485

theorem tailTrace_3319380 : CollatzResearch.WordTrace tailWord_3319380 prefixEnd_3319380 568145804973776048061485 := by
  unfold tailWord_3319380
  simp only [CollatzResearch.WordTrace]
  refine ⟨60533867357230319907749797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80711823142973759876999729 60533867357230319907749797)
  ·
    refine ⟨11350100129480684982703087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60533867357230319907749797 11350100129480684982703087)
    ·
      refine ⟨17025150194221027474054631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11350100129480684982703087 17025150194221027474054631)
      ·
        refine ⟨25537725291331541211081947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17025150194221027474054631 25537725291331541211081947)
        ·
          refine ⟨38306587936997311816622921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25537725291331541211081947 38306587936997311816622921)
          ·
            refine ⟨28729940952747983862467191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38306587936997311816622921 28729940952747983862467191)
            ·
              refine ⟨43094911429121975793700787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28729940952747983862467191 43094911429121975793700787)
              ·
                refine ⟨64642367143682963690551181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43094911429121975793700787 64642367143682963690551181)
                ·
                  refine ⟨24240887678881111383956693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64642367143682963690551181 24240887678881111383956693)
                  ·
                    refine ⟨568145804973776048061485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24240887678881111383956693 568145804973776048061485)
                    ·
                      rfl

theorem cell23_3319380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_3319380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319380 prefixEnd_3319380 := by exact prefixLift 3319380
  have htrace : WordTrace (prefixWord ++ tailWord_3319380) baseStart_3319380 baseEnd_3319380 := by
    simpa [prefixWord, tailWord_3319380, baseEnd_3319380] using wordTrace_append hprefix tailTrace_3319380
  have hstable : (prefixWord ++ tailWord_3319380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319380).length < 2 ^ (prefixWord ++ tailWord_3319380).sum := by decide
  have hdescent : baseEnd_3319380 < baseStart_3319380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319414 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_3319414 : Nat := 118140960795 + 3319414 * 2 ^ 59
def prefixEnd_3319414 : Nat := 4983230072969 + 3 ^ 40 * 3319414 * 2
def baseEnd_3319414 : Nat := 568151624421193670386433

theorem tailTrace_3319414 : CollatzResearch.WordTrace tailWord_3319414 prefixEnd_3319414 568151624421193670386433 := by
  unfold tailWord_3319414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7566810924771091476389831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80712649864224975748158197 7566810924771091476389831)
  ·
    refine ⟨11350216387156637214584747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7566810924771091476389831 11350216387156637214584747)
    ·
      refine ⟨17025324580734955821877121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11350216387156637214584747 17025324580734955821877121)
      ·
        refine ⟨12768993435551216866407841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17025324580734955821877121 12768993435551216866407841)
        ·
          refine ⟨9576745076663412649805881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12768993435551216866407841 9576745076663412649805881)
          ·
            refine ⟨7182558807497559487354411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9576745076663412649805881 7182558807497559487354411)
            ·
              refine ⟨10773838211246339231031617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7182558807497559487354411 10773838211246339231031617)
              ·
                refine ⟨8080378658434754423273713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10773838211246339231031617 8080378658434754423273713)
                ·
                  refine ⟨6060283993826065817455285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8080378658434754423273713 6060283993826065817455285)
                  ·
                    refine ⟨568151624421193670386433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6060283993826065817455285 568151624421193670386433)
                    ·
                      rfl

theorem cell23_3319414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_3319414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319414 prefixEnd_3319414 := by exact prefixLift 3319414
  have htrace : WordTrace (prefixWord ++ tailWord_3319414) baseStart_3319414 baseEnd_3319414 := by
    simpa [prefixWord, tailWord_3319414, baseEnd_3319414] using wordTrace_append hprefix tailTrace_3319414
  have hstable : (prefixWord ++ tailWord_3319414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319414).length < 2 ^ (prefixWord ++ tailWord_3319414).sum := by decide
  have hdescent : baseEnd_3319414 < baseStart_3319414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319417 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 2, 1, 4]
def baseStart_3319417 : Nat := 118140960795 + 3319417 * 2 ^ 59
def prefixEnd_3319417 : Nat := 4983230072969 + 3 ^ 40 * 3319417 * 2
def baseEnd_3319417 : Nat := 1704456413705544499421785

theorem tailTrace_3319417 : CollatzResearch.WordTrace tailWord_3319417 prefixEnd_3319417 1704456413705544499421785 := by
  unfold tailWord_3319417
  simp only [CollatzResearch.WordTrace]
  refine ⟨121069084215326595134596505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80712722810217730089731003 121069084215326595134596505)
  ·
    refine ⟨90801813161494946350947379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121069084215326595134596505 90801813161494946350947379)
    ·
      refine ⟨136202719742242419526421069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90801813161494946350947379 136202719742242419526421069)
      ·
        refine ⟨51076019903340907322407901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136202719742242419526421069 51076019903340907322407901)
        ·
          refine ⟨19153507463752840245902963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51076019903340907322407901 19153507463752840245902963)
          ·
            refine ⟨28730261195629260368854445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19153507463752840245902963 28730261195629260368854445)
            ·
              refine ⟨10773847948360972638320417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28730261195629260368854445 10773847948360972638320417)
              ·
                refine ⟨8080385961270729478740313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10773847948360972638320417 8080385961270729478740313)
                ·
                  refine ⟨6060289470953047109055235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8080385961270729478740313 6060289470953047109055235)
                  ·
                    refine ⟨9090434206429570663582853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6060289470953047109055235 9090434206429570663582853)
                    ·
                      refine ⟨1704456413705544499421785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9090434206429570663582853 1704456413705544499421785)
                      ·
                        rfl

theorem cell23_3319417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_3319417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319417 prefixEnd_3319417 := by exact prefixLift 3319417
  have htrace : WordTrace (prefixWord ++ tailWord_3319417) baseStart_3319417 baseEnd_3319417 := by
    simpa [prefixWord, tailWord_3319417, baseEnd_3319417] using wordTrace_append hprefix tailTrace_3319417
  have hstable : (prefixWord ++ tailWord_3319417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319417).length < 2 ^ (prefixWord ++ tailWord_3319417).sum := by decide
  have hdescent : baseEnd_3319417 < baseStart_3319417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319480 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_3319480 : Nat := 118140960795 + 3319480 * 2 ^ 59
def prefixEnd_3319480 : Nat := 4983230072969 + 3 ^ 40 * 3319480 * 2
def baseEnd_3319480 : Nat := 1704488762986777752933995

theorem tailTrace_3319480 : CollatzResearch.WordTrace tailWord_3319480 prefixEnd_3319480 1704488762986777752933995 := by
  unfold tailWord_3319480
  simp only [CollatzResearch.WordTrace]
  refine ⟨60535691007049178447069947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80714254676065571262759929 60535691007049178447069947)
  ·
    refine ⟨90803536510573767670604921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60535691007049178447069947 90803536510573767670604921)
    ·
      refine ⟨68102652382930325752953691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90803536510573767670604921 68102652382930325752953691)
      ·
        refine ⟨102153978574395488629430537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68102652382930325752953691 102153978574395488629430537)
        ·
          refine ⟨76615483930796616472072903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102153978574395488629430537 76615483930796616472072903)
          ·
            refine ⟨114923225896194924708109355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76615483930796616472072903 114923225896194924708109355)
            ·
              refine ⟨172384838844292387062164033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114923225896194924708109355 172384838844292387062164033)
              ·
                refine ⟨129288629133219290296623025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172384838844292387062164033 129288629133219290296623025)
                ·
                  refine ⟨96966471849914467722467269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129288629133219290296623025 96966471849914467722467269)
                  ·
                    refine ⟨18181213471858962697962613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96966471849914467722467269 18181213471858962697962613)
                    ·
                      refine ⟨1704488762986777752933995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18181213471858962697962613 1704488762986777752933995)
                      ·
                        rfl

theorem cell23_3319480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_3319480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319480 prefixEnd_3319480 := by exact prefixLift 3319480
  have htrace : WordTrace (prefixWord ++ tailWord_3319480) baseStart_3319480 baseEnd_3319480 := by
    simpa [prefixWord, tailWord_3319480, baseEnd_3319480] using wordTrace_append hprefix tailTrace_3319480
  have hstable : (prefixWord ++ tailWord_3319480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319480).length < 2 ^ (prefixWord ++ tailWord_3319480).sum := by decide
  have hdescent : baseEnd_3319480 < baseStart_3319480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319524 : List Nat := [2, 3, 1, 1, 1, 3, 3, 3, 1, 1, 4]
def baseStart_3319524 : Nat := 118140960795 + 3319524 * 2 ^ 59
def prefixEnd_3319524 : Nat := 4983230072969 + 3 ^ 40 * 3319524 * 2
def baseEnd_3319524 : Nat := 1704511356135575580783793

theorem tailTrace_3319524 : CollatzResearch.WordTrace tailWord_3319524 prefixEnd_3319524 1704511356135575580783793 := by
  unfold tailWord_3319524
  simp only [CollatzResearch.WordTrace]
  refine ⟨60536493412969476204370813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80715324550625968272494417 60536493412969476204370813)
  ·
    refine ⟨22701185029863553576639055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60536493412969476204370813 22701185029863553576639055)
    ·
      refine ⟨34051777544795330364958583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22701185029863553576639055 34051777544795330364958583)
      ·
        refine ⟨51077666317192995547437875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34051777544795330364958583 51077666317192995547437875)
        ·
          refine ⟨76616499475789493321156813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51077666317192995547437875 76616499475789493321156813)
          ·
            refine ⟨28731187303421059995433805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76616499475789493321156813 28731187303421059995433805)
            ·
              refine ⟨10774195238782897498287677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28731187303421059995433805 10774195238782897498287677)
              ·
                refine ⟨4040323214543586561857879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10774195238782897498287677 4040323214543586561857879)
                ·
                  refine ⟨6060484821815379842786819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4040323214543586561857879 6060484821815379842786819)
                  ·
                    refine ⟨9090727232723069764180229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6060484821815379842786819 9090727232723069764180229)
                    ·
                      refine ⟨1704511356135575580783793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9090727232723069764180229 1704511356135575580783793)
                      ·
                        rfl

theorem cell23_3319524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_3319524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319524 prefixEnd_3319524 := by exact prefixLift 3319524
  have htrace : WordTrace (prefixWord ++ tailWord_3319524) baseStart_3319524 baseEnd_3319524 := by
    simpa [prefixWord, tailWord_3319524, baseEnd_3319524] using wordTrace_append hprefix tailTrace_3319524
  have hstable : (prefixWord ++ tailWord_3319524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319524).length < 2 ^ (prefixWord ++ tailWord_3319524).sum := by decide
  have hdescent : baseEnd_3319524 < baseStart_3319524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319534 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_3319534 : Nat := 118140960795 + 3319534 * 2 ^ 59
def prefixEnd_3319534 : Nat := 4983230072969 + 3 ^ 40 * 3319534 * 2
def baseEnd_3319534 : Nat := 568172163647373513886249

theorem tailTrace_3319534 : CollatzResearch.WordTrace tailWord_3319534 prefixEnd_3319534 568172163647373513886249 := by
  unfold tailWord_3319534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15134168944487840514575707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80715567703935149411070437 15134168944487840514575707)
  ·
    refine ⟨22701253416731760771863561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15134168944487840514575707 22701253416731760771863561)
    ·
      refine ⟨17025940062548820578897671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22701253416731760771863561 17025940062548820578897671)
      ·
        refine ⟨25538910093823230868346507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17025940062548820578897671 25538910093823230868346507)
        ·
          refine ⟨38308365140734846302519761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25538910093823230868346507 38308365140734846302519761)
          ·
            refine ⟨28731273855551134726889821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38308365140734846302519761 28731273855551134726889821)
            ·
              refine ⟨10774227695831675522583683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28731273855551134726889821 10774227695831675522583683)
              ·
                refine ⟨16161341543747513283875525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10774227695831675522583683 16161341543747513283875525)
                ·
                  refine ⟨3030251539452658740726661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16161341543747513283875525 3030251539452658740726661)
                  ·
                    refine ⟨568172163647373513886249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3030251539452658740726661 568172163647373513886249)
                    ·
                      rfl

theorem cell23_3319534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_3319534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319534 prefixEnd_3319534 := by exact prefixLift 3319534
  have htrace : WordTrace (prefixWord ++ tailWord_3319534) baseStart_3319534 baseEnd_3319534 := by
    simpa [prefixWord, tailWord_3319534, baseEnd_3319534] using wordTrace_append hprefix tailTrace_3319534
  have hstable : (prefixWord ++ tailWord_3319534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319534).length < 2 ^ (prefixWord ++ tailWord_3319534).sum := by decide
  have hdescent : baseEnd_3319534 < baseStart_3319534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319554 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3319554 : Nat := 118140960795 + 3319554 * 2 ^ 59
def prefixEnd_3319554 : Nat := 4983230072969 + 3 ^ 40 * 3319554 * 2
def baseEnd_3319554 : Nat := 1704526760555210463408655

theorem tailTrace_3319554 : CollatzResearch.WordTrace tailWord_3319554 prefixEnd_3319554 1704526760555210463408655 := by
  unfold tailWord_3319554
  simp only [CollatzResearch.WordTrace]
  refine ⟨30268520253957566883083429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80716054010553511688222477 30268520253957566883083429)
  ·
    refine ⟨5675347547617043790578143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30268520253957566883083429 5675347547617043790578143)
    ·
      refine ⟨8513021321425565685867215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5675347547617043790578143 8513021321425565685867215)
      ·
        refine ⟨12769531982138348528800823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8513021321425565685867215 12769531982138348528800823)
        ·
          refine ⟨19154297973207522793201235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12769531982138348528800823 19154297973207522793201235)
          ·
            refine ⟨28731446959811284189801853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19154297973207522793201235 28731446959811284189801853)
            ·
              refine ⟨10774292609929231571175695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28731446959811284189801853 10774292609929231571175695)
              ·
                refine ⟨16161438914893847356763543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10774292609929231571175695 16161438914893847356763543)
                ·
                  refine ⟨24242158372340771035145315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16161438914893847356763543 24242158372340771035145315)
                  ·
                    refine ⟨36363237558511156552717973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24242158372340771035145315 36363237558511156552717973)
                    ·
                      refine ⟨1704526760555210463408655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36363237558511156552717973 1704526760555210463408655)
                      ·
                        rfl

theorem cell23_3319554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3319554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319554 prefixEnd_3319554 := by exact prefixLift 3319554
  have htrace : WordTrace (prefixWord ++ tailWord_3319554) baseStart_3319554 baseEnd_3319554 := by
    simpa [prefixWord, tailWord_3319554, baseEnd_3319554] using wordTrace_append hprefix tailTrace_3319554
  have hstable : (prefixWord ++ tailWord_3319554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319554).length < 2 ^ (prefixWord ++ tailWord_3319554).sum := by decide
  have hdescent : baseEnd_3319554 < baseStart_3319554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319575 : List Nat := [1, 1, 3, 4, 2, 1, 3, 3, 1, 2, 2]
def baseStart_3319575 : Nat := 118140960795 + 3319575 * 2 ^ 59
def prefixEnd_3319575 : Nat := 4983230072969 + 3 ^ 40 * 3319575 * 2
def baseEnd_3319575 : Nat := 1704537543648954881246059

theorem tailTrace_3319575 : CollatzResearch.WordTrace tailWord_3319575 prefixEnd_3319575 1704537543648954881246059 := by
  unfold tailWord_3319575
  simp only [CollatzResearch.WordTrace]
  refine ⟨121074846948754188118848179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80716564632502792079232119 121074846948754188118848179)
  ·
    refine ⟨181612270423131282178272269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121074846948754188118848179 181612270423131282178272269)
    ·
      refine ⟨68104601408674230816852101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181612270423131282178272269 68104601408674230816852101)
      ·
        refine ⟨12769612764126418278159769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68104601408674230816852101 12769612764126418278159769)
        ·
          refine ⟨9577209573094813708619827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12769612764126418278159769 9577209573094813708619827)
          ·
            refine ⟨14365814359642220562929741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9577209573094813708619827 14365814359642220562929741)
            ·
              refine ⟨5387180384865832711098653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14365814359642220562929741 5387180384865832711098653)
              ·
                refine ⟨2020192644324687266661995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5387180384865832711098653 2020192644324687266661995)
                ·
                  refine ⟨3030288966487030899992993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020192644324687266661995 3030288966487030899992993)
                  ·
                    refine ⟨2272716724865273174994745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3030288966487030899992993 2272716724865273174994745)
                    ·
                      refine ⟨1704537543648954881246059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2272716724865273174994745 1704537543648954881246059)
                      ·
                        rfl

theorem cell23_3319575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_3319575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319575 prefixEnd_3319575 := by exact prefixLift 3319575
  have htrace : WordTrace (prefixWord ++ tailWord_3319575) baseStart_3319575 baseEnd_3319575 := by
    simpa [prefixWord, tailWord_3319575, baseEnd_3319575] using wordTrace_append hprefix tailTrace_3319575
  have hstable : (prefixWord ++ tailWord_3319575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319575).length < 2 ^ (prefixWord ++ tailWord_3319575).sum := by decide
  have hdescent : baseEnd_3319575 < baseStart_3319575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319592 : List Nat := [2, 1, 5, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_3319592 : Nat := 118140960795 + 3319592 * 2 ^ 59
def prefixEnd_3319592 : Nat := 4983230072969 + 3 ^ 40 * 3319592 * 2
def baseEnd_3319592 : Nat := 1704546272820081314733481

theorem tailTrace_3319592 : CollatzResearch.WordTrace tailWord_3319592 prefixEnd_3319592 1704546272820081314733481 := by
  unfold tailWord_3319592
  simp only [CollatzResearch.WordTrace]
  refine ⟨60537733494846300011108515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80716977993128400014811353 60537733494846300011108515)
  ·
    refine ⟨90806600242269450016662773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60537733494846300011108515 90806600242269450016662773)
    ·
      refine ⟨8513118772712760939062135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90806600242269450016662773 8513118772712760939062135)
      ·
        refine ⟨12769678159069141408593203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8513118772712760939062135 12769678159069141408593203)
        ·
          refine ⟨19154517238603712112889805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12769678159069141408593203 19154517238603712112889805)
          ·
            refine ⟨7182943964476392042333677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19154517238603712112889805 7182943964476392042333677)
            ·
              refine ⟨2693603986678647015875129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7182943964476392042333677 2693603986678647015875129)
              ·
                refine ⟨2020202990008985261906347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2693603986678647015875129 2020202990008985261906347)
                ·
                  refine ⟨3030304485013477892859521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020202990008985261906347 3030304485013477892859521)
                  ·
                    refine ⟨2272728363760108419644641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3030304485013477892859521 2272728363760108419644641)
                    ·
                      refine ⟨1704546272820081314733481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2272728363760108419644641 1704546272820081314733481)
                      ·
                        rfl

theorem cell23_3319592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_3319592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319592 prefixEnd_3319592 := by exact prefixLift 3319592
  have htrace : WordTrace (prefixWord ++ tailWord_3319592) baseStart_3319592 baseEnd_3319592 := by
    simpa [prefixWord, tailWord_3319592, baseEnd_3319592] using wordTrace_append hprefix tailTrace_3319592
  have hstable : (prefixWord ++ tailWord_3319592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319592).length < 2 ^ (prefixWord ++ tailWord_3319592).sum := by decide
  have hdescent : baseEnd_3319592 < baseStart_3319592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319608 : List Nat := [2, 1, 2, 1, 3, 3, 4, 1, 2, 1, 3]
def baseStart_3319608 : Nat := 118140960795 + 3319608 * 2 ^ 59
def prefixEnd_3319608 : Nat := 4983230072969 + 3 ^ 40 * 3319608 * 2
def baseEnd_3319608 : Nat := 1704554488510553252133407

theorem tailTrace_3319608 : CollatzResearch.WordTrace tailWord_3319608 prefixEnd_3319608 1704554488510553252133407 := by
  unfold tailWord_3319608
  simp only [CollatzResearch.WordTrace]
  refine ⟨60538025278817317377399739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80717367038423089836532985 60538025278817317377399739)
  ·
    refine ⟨90807037918225976066099609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60538025278817317377399739 90807037918225976066099609)
    ·
      refine ⟨68105278438669482049574707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90807037918225976066099609 68105278438669482049574707)
      ·
        refine ⟨102157917658004223074362061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68105278438669482049574707 102157917658004223074362061)
        ·
          refine ⟨38309219121751583652885773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102157917658004223074362061 38309219121751583652885773)
          ·
            refine ⟨14365957170656843869832165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38309219121751583652885773 14365957170656843869832165)
            ·
              refine ⟨2693616969498158225593531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14365957170656843869832165 2693616969498158225593531)
              ·
                refine ⟨4040425454247237338390297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2693616969498158225593531 4040425454247237338390297)
                ·
                  refine ⟨3030319090685428003792723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4040425454247237338390297 3030319090685428003792723)
                  ·
                    refine ⟨4545478636028142005689085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3030319090685428003792723 4545478636028142005689085)
                    ·
                      refine ⟨1704554488510553252133407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4545478636028142005689085 1704554488510553252133407)
                      ·
                        rfl

theorem cell23_3319608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 2, 1, 3].length) (baseStart_3319608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319608 prefixEnd_3319608 := by exact prefixLift 3319608
  have htrace : WordTrace (prefixWord ++ tailWord_3319608) baseStart_3319608 baseEnd_3319608 := by
    simpa [prefixWord, tailWord_3319608, baseEnd_3319608] using wordTrace_append hprefix tailTrace_3319608
  have hstable : (prefixWord ++ tailWord_3319608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319608).length < 2 ^ (prefixWord ++ tailWord_3319608).sum := by decide
  have hdescent : baseEnd_3319608 < baseStart_3319608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319634 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_3319634 : Nat := 118140960795 + 3319634 * 2 ^ 59
def prefixEnd_3319634 : Nat := 4983230072969 + 3 ^ 40 * 3319634 * 2
def baseEnd_3319634 : Nat := 1704567839007570150408287

theorem tailTrace_3319634 : CollatzResearch.WordTrace tailWord_3319634 prefixEnd_3319634 1704567839007570150408287 := by
  unfold tailWord_3319634
  simp only [CollatzResearch.WordTrace]
  refine ⟨30269249713885110298811489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80717999237026960796830637 30269249713885110298811489)
  ·
    refine ⟨22701937285413832724108617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30269249713885110298811489 22701937285413832724108617)
    ·
      refine ⟨17026452964060374543081463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22701937285413832724108617 17026452964060374543081463)
      ·
        refine ⟨25539679446090561814622195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17026452964060374543081463 25539679446090561814622195)
        ·
          refine ⟨38309519169135842721933293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25539679446090561814622195 38309519169135842721933293)
          ·
            refine ⟨14366069688425941020724985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38309519169135842721933293 14366069688425941020724985)
            ·
              refine ⟨10774552266319455765543739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14366069688425941020724985 10774552266319455765543739)
              ·
                refine ⟨16161828399479183648315609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10774552266319455765543739 16161828399479183648315609)
                ·
                  refine ⟨12121371299609387736236707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16161828399479183648315609 12121371299609387736236707)
                  ·
                    refine ⟨18182056949414081604355061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12121371299609387736236707 18182056949414081604355061)
                    ·
                      refine ⟨1704567839007570150408287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18182056949414081604355061 1704567839007570150408287)
                      ·
                        rfl

theorem cell23_3319634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_3319634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319634 prefixEnd_3319634 := by exact prefixLift 3319634
  have htrace : WordTrace (prefixWord ++ tailWord_3319634) baseStart_3319634 baseEnd_3319634 := by
    simpa [prefixWord, tailWord_3319634, baseEnd_3319634] using wordTrace_append hprefix tailTrace_3319634
  have hstable : (prefixWord ++ tailWord_3319634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319634).length < 2 ^ (prefixWord ++ tailWord_3319634).sum := by decide
  have hdescent : baseEnd_3319634 < baseStart_3319634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319648 : List Nat := [2, 1, 1, 3, 3, 2, 1, 4, 2, 2, 2]
def baseStart_3319648 : Nat := 118140960795 + 3319648 * 2 ^ 59
def prefixEnd_3319648 : Nat := 4983230072969 + 3 ^ 40 * 3319648 * 2
def baseEnd_3319648 : Nat := 1704575027736733095633223

theorem tailTrace_3319648 : CollatzResearch.WordTrace tailWord_3319648 prefixEnd_3319648 1704575027736733095633223 := by
  unfold tailWord_3319648
  simp only [CollatzResearch.WordTrace]
  refine ⟨60538754738744860793127799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80718339651659814390837065 60538754738744860793127799)
  ·
    refine ⟨90808132108117291189691699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60538754738744860793127799 90808132108117291189691699)
    ·
      refine ⟨136212198162175936784537549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90808132108117291189691699 136212198162175936784537549)
      ·
        refine ⟨51079574310815976294201581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136212198162175936784537549 51079574310815976294201581)
        ·
          refine ⟨19154840366555991110325593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51079574310815976294201581 19154840366555991110325593)
          ·
            refine ⟨14366130274916993332744195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19154840366555991110325593 14366130274916993332744195)
            ·
              refine ⟨21549195412375489999116293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14366130274916993332744195 21549195412375489999116293)
              ·
                refine ⟨4040474139820404374834305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21549195412375489999116293 4040474139820404374834305)
                ·
                  refine ⟨3030355604865303281125729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4040474139820404374834305 3030355604865303281125729)
                  ·
                    refine ⟨2272766703648977460844297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3030355604865303281125729 2272766703648977460844297)
                    ·
                      refine ⟨1704575027736733095633223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2272766703648977460844297 1704575027736733095633223)
                      ·
                        rfl

theorem cell23_3319648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_3319648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319648 prefixEnd_3319648 := by exact prefixLift 3319648
  have htrace : WordTrace (prefixWord ++ tailWord_3319648) baseStart_3319648 baseEnd_3319648 := by
    simpa [prefixWord, tailWord_3319648, baseEnd_3319648] using wordTrace_append hprefix tailTrace_3319648
  have hstable : (prefixWord ++ tailWord_3319648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319648).length < 2 ^ (prefixWord ++ tailWord_3319648).sum := by decide
  have hdescent : baseEnd_3319648 < baseStart_3319648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319667 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 1, 7]
def baseStart_3319667 : Nat := 118140960795 + 3319667 * 2 ^ 59
def prefixEnd_3319667 : Nat := 4983230072969 + 3 ^ 40 * 3319667 * 2
def baseEnd_3319667 : Nat := 568194927956389507098545

theorem tailTrace_3319667 : CollatzResearch.WordTrace tailWord_3319667 prefixEnd_3319667 568194927956389507098545 := by
  unfold tailWord_3319667
  simp only [CollatzResearch.WordTrace]
  refine ⟨121078202464420887831197255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80718801642947258554131503 121078202464420887831197255)
  ·
    refine ⟨181617303696631331746795883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121078202464420887831197255 181617303696631331746795883)
    ·
      refine ⟨272425955544946997620193825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181617303696631331746795883 272425955544946997620193825)
      ·
        refine ⟨204319466658710248215145369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272425955544946997620193825 204319466658710248215145369)
        ·
          refine ⟨153239599994032686161359027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204319466658710248215145369 153239599994032686161359027)
          ·
            refine ⟨229859399991049029242038541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153239599994032686161359027 229859399991049029242038541)
            ·
              refine ⟨86197274996643385965764453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229859399991049029242038541 86197274996643385965764453)
              ·
                refine ⟨16161989061870634868580835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86197274996643385965764453 16161989061870634868580835)
                ·
                  refine ⟨24242983592805952302871253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16161989061870634868580835 24242983592805952302871253)
                  ·
                    refine ⟨568194927956389507098545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24242983592805952302871253 568194927956389507098545)
                    ·
                      rfl

theorem cell23_3319667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 7].length) (baseStart_3319667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319667 prefixEnd_3319667 := by exact prefixLift 3319667
  have htrace : WordTrace (prefixWord ++ tailWord_3319667) baseStart_3319667 baseEnd_3319667 := by
    simpa [prefixWord, tailWord_3319667, baseEnd_3319667] using wordTrace_append hprefix tailTrace_3319667
  have hstable : (prefixWord ++ tailWord_3319667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319667).length < 2 ^ (prefixWord ++ tailWord_3319667).sum := by decide
  have hdescent : baseEnd_3319667 < baseStart_3319667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319688 : List Nat := [2, 1, 3, 3, 3, 1, 2, 3, 5]
def baseStart_3319688 : Nat := 118140960795 + 3319688 * 2 ^ 59
def prefixEnd_3319688 : Nat := 4983230072969 + 3 ^ 40 * 3319688 * 2
def baseEnd_3319688 : Nat := 189399507440323659903671

theorem tailTrace_3319688 : CollatzResearch.WordTrace tailWord_3319688 prefixEnd_3319688 189399507440323659903671 := by
  unfold tailWord_3319688
  simp only [CollatzResearch.WordTrace]
  refine ⟨60539484198672404208855859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80719312264896538945141145 60539484198672404208855859)
  ·
    refine ⟨90809226298008606313283789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60539484198672404208855859 90809226298008606313283789)
    ·
      refine ⟨34053459861753227367481421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90809226298008606313283789 34053459861753227367481421)
      ·
        refine ⟨12770047448157460262805533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34053459861753227367481421 12770047448157460262805533)
        ·
          refine ⟨4788767793059047598552075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12770047448157460262805533 4788767793059047598552075)
          ·
            refine ⟨7183151689588571397828113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4788767793059047598552075 7183151689588571397828113)
            ·
              refine ⟨5387363767191428548371085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7183151689588571397828113 5387363767191428548371085)
              ·
                refine ⟨2020261412696785705639157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5387363767191428548371085 2020261412696785705639157)
                ·
                  refine ⟨189399507440323659903671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2020261412696785705639157 189399507440323659903671)
                  ·
                    rfl

theorem cell23_3319688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 5].length) (baseStart_3319688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319688 prefixEnd_3319688 := by exact prefixLift 3319688
  have htrace : WordTrace (prefixWord ++ tailWord_3319688) baseStart_3319688 baseEnd_3319688 := by
    simpa [prefixWord, tailWord_3319688, baseEnd_3319688] using wordTrace_append hprefix tailTrace_3319688
  have hstable : (prefixWord ++ tailWord_3319688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319688).length < 2 ^ (prefixWord ++ tailWord_3319688).sum := by decide
  have hdescent : baseEnd_3319688 < baseStart_3319688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319741 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_3319741 : Nat := 118140960795 + 3319741 * 2 ^ 59
def prefixEnd_3319741 : Nat := 4983230072969 + 3 ^ 40 * 3319741 * 2
def baseEnd_3319741 : Nat := 1704622781437601231770295

theorem tailTrace_3319741 : CollatzResearch.WordTrace tailWord_3319741 prefixEnd_3319741 1704622781437601231770295 := by
  unfold tailWord_3319741
  simp only [CollatzResearch.WordTrace]
  refine ⟨121080901466152798469391077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80720600977435198979594051 121080901466152798469391077)
  ·
    refine ⟨22702669024903649713010827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121080901466152798469391077 22702669024903649713010827)
    ·
      refine ⟨34054003537355474569516241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22702669024903649713010827 34054003537355474569516241)
      ·
        refine ⟨25540502653016605927137181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34054003537355474569516241 25540502653016605927137181)
        ·
          refine ⟨9577688494881227222676443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25540502653016605927137181 9577688494881227222676443)
          ·
            refine ⟨14366532742321840834014665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9577688494881227222676443 14366532742321840834014665)
            ·
              refine ⟨10774899556741380625510999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14366532742321840834014665 10774899556741380625510999)
              ·
                refine ⟨16162349335112070938266499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10774899556741380625510999 16162349335112070938266499)
                ·
                  refine ⟨24243524002668106407399749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16162349335112070938266499 24243524002668106407399749)
                  ·
                    refine ⟨4545660750500269951387453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24243524002668106407399749 4545660750500269951387453)
                    ·
                      refine ⟨1704622781437601231770295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4545660750500269951387453 1704622781437601231770295)
                      ·
                        rfl

theorem cell23_3319741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_3319741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319741 prefixEnd_3319741 := by exact prefixLift 3319741
  have htrace : WordTrace (prefixWord ++ tailWord_3319741) baseStart_3319741 baseEnd_3319741 := by
    simpa [prefixWord, tailWord_3319741, baseEnd_3319741] using wordTrace_append hprefix tailTrace_3319741
  have hstable : (prefixWord ++ tailWord_3319741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319741).length < 2 ^ (prefixWord ++ tailWord_3319741).sum := by decide
  have hdescent : baseEnd_3319741 < baseStart_3319741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319811 : List Nat := [1, 1, 1, 3, 2, 1, 1, 7, 1, 1, 4]
def baseStart_3319811 : Nat := 118140960795 + 3319811 * 2 ^ 59
def prefixEnd_3319811 : Nat := 4983230072969 + 3 ^ 40 * 3319811 * 2
def baseEnd_3319811 : Nat := 1704658725083415957894973

theorem tailTrace_3319811 : CollatzResearch.WordTrace tailWord_3319811 prefixEnd_3319811 1704658725083415957894973 := by
  unfold tailWord_3319811
  simp only [CollatzResearch.WordTrace]
  refine ⟨121083454575899200424439287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80722303050599466949626191 121083454575899200424439287)
  ·
    refine ⟨181625181863848800636658931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121083454575899200424439287 181625181863848800636658931)
    ·
      refine ⟨272437772795773200954988397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181625181863848800636658931 272437772795773200954988397)
      ·
        refine ⟨102164164798414950358120649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272437772795773200954988397 102164164798414950358120649)
        ·
          refine ⟨76623123598811212768590487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102164164798414950358120649 76623123598811212768590487)
          ·
            refine ⟨114934685398216819152885731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76623123598811212768590487 114934685398216819152885731)
            ·
              refine ⟨172402028097325228729328597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114934685398216819152885731 172402028097325228729328597)
              ·
                refine ⟨4040672533531060048343639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 172402028097325228729328597 4040672533531060048343639)
                ·
                  refine ⟨6061008800296590072515459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4040672533531060048343639 6061008800296590072515459)
                  ·
                    refine ⟨9091513200444885108773189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6061008800296590072515459 9091513200444885108773189)
                    ·
                      refine ⟨1704658725083415957894973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9091513200444885108773189 1704658725083415957894973)
                      ·
                        rfl

theorem cell23_3319811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_3319811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319811 prefixEnd_3319811 := by exact prefixLift 3319811
  have htrace : WordTrace (prefixWord ++ tailWord_3319811) baseStart_3319811 baseEnd_3319811 := by
    simpa [prefixWord, tailWord_3319811, baseEnd_3319811] using wordTrace_append hprefix tailTrace_3319811
  have hstable : (prefixWord ++ tailWord_3319811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319811).length < 2 ^ (prefixWord ++ tailWord_3319811).sum := by decide
  have hdescent : baseEnd_3319811 < baseStart_3319811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319845 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 3, 2, 2]
def baseStart_3319845 : Nat := 118140960795 + 3319845 * 2 ^ 59
def prefixEnd_3319845 : Nat := 4983230072969 + 3 ^ 40 * 3319845 * 2
def baseEnd_3319845 : Nat := 1704676183425668824869817

theorem tailTrace_3319845 : CollatzResearch.WordTrace tailWord_3319845 prefixEnd_3319845 1704676183425668824869817 := by
  unfold tailWord_3319845
  simp only [CollatzResearch.WordTrace]
  refine ⟨121084694657776024231176989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80723129771850682820784659 121084694657776024231176989)
  ·
    refine ⟨45406760496666009086691371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121084694657776024231176989 45406760496666009086691371)
    ·
      refine ⟨68110140744999013630037057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45406760496666009086691371 68110140744999013630037057)
      ·
        refine ⟨51082605558749260222527793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68110140744999013630037057 51082605558749260222527793)
        ·
          refine ⟨38311954169061945166895845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51082605558749260222527793 38311954169061945166895845)
          ·
            refine ⟨7183491406699114718792971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38311954169061945166895845 7183491406699114718792971)
            ·
              refine ⟨10775237110048672078189457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7183491406699114718792971 10775237110048672078189457)
              ·
                refine ⟨8081427832536504058642093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10775237110048672078189457 8081427832536504058642093)
                ·
                  refine ⟨3030535437201189021990785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8081427832536504058642093 3030535437201189021990785)
                  ·
                    refine ⟨2272901577900891766493089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3030535437201189021990785 2272901577900891766493089)
                    ·
                      refine ⟨1704676183425668824869817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2272901577900891766493089 1704676183425668824869817)
                      ·
                        rfl

theorem cell23_3319845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_3319845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319845 prefixEnd_3319845 := by exact prefixLift 3319845
  have htrace : WordTrace (prefixWord ++ tailWord_3319845) baseStart_3319845 baseEnd_3319845 := by
    simpa [prefixWord, tailWord_3319845, baseEnd_3319845] using wordTrace_append hprefix tailTrace_3319845
  have hstable : (prefixWord ++ tailWord_3319845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319845).length < 2 ^ (prefixWord ++ tailWord_3319845).sum := by decide
  have hdescent : baseEnd_3319845 < baseStart_3319845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319865 : List Nat := [1, 2, 1, 5, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3319865 : Nat := 118140960795 + 3319865 * 2 ^ 59
def prefixEnd_3319865 : Nat := 4983230072969 + 3 ^ 40 * 3319865 * 2
def baseEnd_3319865 : Nat := 1704686453038758746619725

theorem tailTrace_3319865 : CollatzResearch.WordTrace tailWord_3319865 prefixEnd_3319865 1704686453038758746619725 := by
  unfold tailWord_3319865
  simp only [CollatzResearch.WordTrace]
  refine ⟨121085424117703567646905049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80723616078469045097936699 121085424117703567646905049)
  ·
    refine ⟨90814068088277675735178787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121085424117703567646905049 90814068088277675735178787)
    ·
      refine ⟨136221102132416513602768181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90814068088277675735178787 136221102132416513602768181)
      ·
        refine ⟨12770728324914048150259517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136221102132416513602768181 12770728324914048150259517)
        ·
          refine ⟨4789023121842768056347319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12770728324914048150259517 4789023121842768056347319)
          ·
            refine ⟨7183534682764152084520979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789023121842768056347319 7183534682764152084520979)
            ·
              refine ⟨10775302024146228126781469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7183534682764152084520979 10775302024146228126781469)
              ·
                refine ⟨4040738259054835547543051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10775302024146228126781469 4040738259054835547543051)
                ·
                  refine ⟨6061107388582253321314577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4040738259054835547543051 6061107388582253321314577)
                  ·
                    refine ⟨4545830541436689990985933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6061107388582253321314577 4545830541436689990985933)
                    ·
                      refine ⟨1704686453038758746619725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4545830541436689990985933 1704686453038758746619725)
                      ·
                        rfl

theorem cell23_3319865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3319865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319865 prefixEnd_3319865 := by exact prefixLift 3319865
  have htrace : WordTrace (prefixWord ++ tailWord_3319865) baseStart_3319865 baseEnd_3319865 := by
    simpa [prefixWord, tailWord_3319865, baseEnd_3319865] using wordTrace_append hprefix tailTrace_3319865
  have hstable : (prefixWord ++ tailWord_3319865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319865).length < 2 ^ (prefixWord ++ tailWord_3319865).sum := by decide
  have hdescent : baseEnd_3319865 < baseStart_3319865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319921 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_3319921 : Nat := 118140960795 + 3319921 * 2 ^ 59
def prefixEnd_3319921 : Nat := 4983230072969 + 3 ^ 40 * 3319921 * 2
def baseEnd_3319921 : Nat := 1704715207955410527519467

theorem tailTrace_3319921 : CollatzResearch.WordTrace tailWord_3319921 prefixEnd_3319921 1704715207955410527519467 := by
  unfold tailWord_3319921
  simp only [CollatzResearch.WordTrace]
  refine ⟨121087466605500689210943617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80724977737000459473962411 121087466605500689210943617)
  ·
    refine ⟨90815599954125516908207713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121087466605500689210943617 90815599954125516908207713)
    ·
      refine ⟨68111699965594137681155785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90815599954125516908207713 68111699965594137681155785)
      ·
        refine ⟨51083774974195603260866839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68111699965594137681155785 51083774974195603260866839)
        ·
          refine ⟨76625662461293404891300259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51083774974195603260866839 76625662461293404891300259)
          ·
            refine ⟨114938493691940107336950389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76625662461293404891300259 114938493691940107336950389)
            ·
              refine ⟨10775483783619385062839099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114938493691940107336950389 10775483783619385062839099)
              ·
                refine ⟨16163225675429077594258649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10775483783619385062839099 16163225675429077594258649)
                ·
                  refine ⟨12122419256571808195693987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16163225675429077594258649 12122419256571808195693987)
                  ·
                    refine ⟨18183628884857712293540981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12122419256571808195693987 18183628884857712293540981)
                    ·
                      refine ⟨1704715207955410527519467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18183628884857712293540981 1704715207955410527519467)
                      ·
                        rfl

theorem cell23_3319921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_3319921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319921 prefixEnd_3319921 := by exact prefixLift 3319921
  have htrace : WordTrace (prefixWord ++ tailWord_3319921) baseStart_3319921 baseEnd_3319921 := by
    simpa [prefixWord, tailWord_3319921, baseEnd_3319921] using wordTrace_append hprefix tailTrace_3319921
  have hstable : (prefixWord ++ tailWord_3319921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319921).length < 2 ^ (prefixWord ++ tailWord_3319921).sum := by decide
  have hdescent : baseEnd_3319921 < baseStart_3319921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3319956 : List Nat := [2, 4, 2, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_3319956 : Nat := 118140960795 + 3319956 * 2 ^ 59
def prefixEnd_3319956 : Nat := 4983230072969 + 3 ^ 40 * 3319956 * 2
def baseEnd_3319956 : Nat := 1704733179778317890581807

theorem tailTrace_3319956 : CollatzResearch.WordTrace tailWord_3319956 prefixEnd_3319956 1704733179778317890581807 := by
  unfold tailWord_3319956
  simp only [CollatzResearch.WordTrace]
  refine ⟨60544371580186945094233861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80725828773582593458978481 60544371580186945094233861)
  ·
    refine ⟨11352069671285052205168849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60544371580186945094233861 11352069671285052205168849)
    ·
      refine ⟨8514052253463789153876637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11352069671285052205168849 8514052253463789153876637)
      ·
        refine ⟨3192769595048920932703739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8514052253463789153876637 3192769595048920932703739)
        ·
          refine ⟨4789154392573381399055609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3192769595048920932703739 4789154392573381399055609)
          ·
            refine ⟨3591865794430036049291707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4789154392573381399055609 3591865794430036049291707)
            ·
              refine ⟨5387798691645054073937561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3591865794430036049291707 5387798691645054073937561)
              ·
                refine ⟨4040849018733790555453171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5387798691645054073937561 4040849018733790555453171)
                ·
                  refine ⟨6061273528100685833179757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4040849018733790555453171 6061273528100685833179757)
                  ·
                    refine ⟨2272977573037757187442409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6061273528100685833179757 2272977573037757187442409)
                    ·
                      refine ⟨1704733179778317890581807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2272977573037757187442409 1704733179778317890581807)
                      ·
                        rfl

theorem cell23_3319956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_3319956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3319956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3319956 prefixEnd_3319956 := by exact prefixLift 3319956
  have htrace : WordTrace (prefixWord ++ tailWord_3319956) baseStart_3319956 baseEnd_3319956 := by
    simpa [prefixWord, tailWord_3319956, baseEnd_3319956] using wordTrace_append hprefix tailTrace_3319956
  have hstable : (prefixWord ++ tailWord_3319956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3319956).length < 2 ^ (prefixWord ++ tailWord_3319956).sum := by decide
  have hdescent : baseEnd_3319956 < baseStart_3319956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3319956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320002 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3320002 : Nat := 118140960795 + 3320002 * 2 ^ 59
def prefixEnd_3320002 : Nat := 4983230072969 + 3 ^ 40 * 3320002 * 2
def baseEnd_3320002 : Nat := 1704756799888424710606595

theorem tailTrace_3320002 : CollatzResearch.WordTrace tailWord_3320002 prefixEnd_3320002 1704756799888424710606595 := by
  unfold tailWord_3320002
  simp only [CollatzResearch.WordTrace]
  refine ⟨30272605229551810011160565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80726947278804826696428173 30272605229551810011160565)
  ·
    refine ⟨2838056740270482188546303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30272605229551810011160565 2838056740270482188546303)
    ·
      refine ⟨4257085110405723282819455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2838056740270482188546303 4257085110405723282819455)
      ·
        refine ⟨6385627665608584924229183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4257085110405723282819455 6385627665608584924229183)
        ·
          refine ⟨9578441498412877386343775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6385627665608584924229183 9578441498412877386343775)
          ·
            refine ⟨14367662247619316079515663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9578441498412877386343775 14367662247619316079515663)
            ·
              refine ⟨21551493371428974119273495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14367662247619316079515663 21551493371428974119273495)
              ·
                refine ⟨32327240057143461178910243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21551493371428974119273495 32327240057143461178910243)
                ·
                  refine ⟨48490860085715191768365365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32327240057143461178910243 48490860085715191768365365)
                  ·
                    refine ⟨4546018133035799228284253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48490860085715191768365365 4546018133035799228284253)
                    ·
                      refine ⟨1704756799888424710606595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4546018133035799228284253 1704756799888424710606595)
                      ·
                        rfl

theorem cell23_3320002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3320002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320002 prefixEnd_3320002 := by exact prefixLift 3320002
  have htrace : WordTrace (prefixWord ++ tailWord_3320002) baseStart_3320002 baseEnd_3320002 := by
    simpa [prefixWord, tailWord_3320002, baseEnd_3320002] using wordTrace_append hprefix tailTrace_3320002
  have hstable : (prefixWord ++ tailWord_3320002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320002).length < 2 ^ (prefixWord ++ tailWord_3320002).sum := by decide
  have hdescent : baseEnd_3320002 < baseStart_3320002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320022 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_3320022 : Nat := 118140960795 + 3320022 * 2 ^ 59
def prefixEnd_3320022 : Nat := 4983230072969 + 3 ^ 40 * 3320022 * 2
def baseEnd_3320022 : Nat := 568255689833838210785501

theorem tailTrace_3320022 : CollatzResearch.WordTrace tailWord_3320022 prefixEnd_3320022 568255689833838210785501 := by
  unfold tailWord_3320022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7568196898633423966273145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80727433585423188973580213 7568196898633423966273145)
  ·
    refine ⟨5676147673975067974704859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7568196898633423966273145 5676147673975067974704859)
    ·
      refine ⟨8514221510962601962057289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5676147673975067974704859 8514221510962601962057289)
      ·
        refine ⟨6385666133221951471542967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8514221510962601962057289 6385666133221951471542967)
        ·
          refine ⟨9578499199832927207314451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6385666133221951471542967 9578499199832927207314451)
          ·
            refine ⟨14367748799749390810971677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9578499199832927207314451 14367748799749390810971677)
            ·
              refine ⟨5387905799906021554114379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14367748799749390810971677 5387905799906021554114379)
              ·
                refine ⟨8081858699859032331171569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5387905799906021554114379 8081858699859032331171569)
                ·
                  refine ⟨6061394024894274248378677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8081858699859032331171569 6061394024894274248378677)
                  ·
                    refine ⟨568255689833838210785501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6061394024894274248378677 568255689833838210785501)
                    ·
                      rfl

theorem cell23_3320022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_3320022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320022 prefixEnd_3320022 := by exact prefixLift 3320022
  have htrace : WordTrace (prefixWord ++ tailWord_3320022) baseStart_3320022 baseEnd_3320022 := by
    simpa [prefixWord, tailWord_3320022, baseEnd_3320022] using wordTrace_append hprefix tailTrace_3320022
  have hstable : (prefixWord ++ tailWord_3320022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320022).length < 2 ^ (prefixWord ++ tailWord_3320022).sum := by decide
  have hdescent : baseEnd_3320022 < baseStart_3320022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320031 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 8]
def baseStart_3320031 : Nat := 118140960795 + 3320031 * 2 ^ 59
def prefixEnd_3320031 : Nat := 4983230072969 + 3 ^ 40 * 3320031 * 2
def baseEnd_3320031 : Nat := 189419076758600566349329

theorem tailTrace_3320031 : CollatzResearch.WordTrace tailWord_3320031 prefixEnd_3320031 189419076758600566349329 := by
  unfold tailWord_3320031
  simp only [CollatzResearch.WordTrace]
  refine ⟨121091478635102177997447947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80727652423401451998298631 121091478635102177997447947)
  ·
    refine ⟨181637217952653266996171921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121091478635102177997447947 181637217952653266996171921)
    ·
      refine ⟨136227913464489950247128941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181637217952653266996171921 136227913464489950247128941)
      ·
        refine ⟨51085467549183731342673353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136227913464489950247128941 51085467549183731342673353)
        ·
          refine ⟨38314100661887798507005015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51085467549183731342673353 38314100661887798507005015)
          ·
            refine ⟨57471150992831697760507523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38314100661887798507005015 57471150992831697760507523)
            ·
              refine ⟨86206726489247546640761285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57471150992831697760507523 86206726489247546640761285)
              ·
                refine ⟨16163761216733914995142741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86206726489247546640761285 16163761216733914995142741)
                ·
                  refine ⟨189419076758600566349329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16163761216733914995142741 189419076758600566349329)
                  ·
                    rfl

theorem cell23_3320031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 8].length) (baseStart_3320031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320031 prefixEnd_3320031 := by exact prefixLift 3320031
  have htrace : WordTrace (prefixWord ++ tailWord_3320031) baseStart_3320031 baseEnd_3320031 := by
    simpa [prefixWord, tailWord_3320031, baseEnd_3320031] using wordTrace_append hprefix tailTrace_3320031
  have hstable : (prefixWord ++ tailWord_3320031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320031).length < 2 ^ (prefixWord ++ tailWord_3320031).sum := by decide
  have hdescent : baseEnd_3320031 < baseStart_3320031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320051 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 8]
def baseStart_3320051 : Nat := 118140960795 + 3320051 * 2 ^ 59
def prefixEnd_3320051 : Nat := 4983230072969 + 3 ^ 40 * 3320051 * 2
def baseEnd_3320051 : Nat := 1704781960440495018893869

theorem tailTrace_3320051 : CollatzResearch.WordTrace tailWord_3320051 prefixEnd_3320051 1704781960440495018893869 := by
  unfold tailWord_3320051
  simp only [CollatzResearch.WordTrace]
  refine ⟨121092208095029721413176007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80728138730019814275450671 121092208095029721413176007)
  ·
    refine ⟨181638312142544582119764011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121092208095029721413176007 181638312142544582119764011)
    ·
      refine ⟨272457468213816873179646017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181638312142544582119764011 272457468213816873179646017)
      ·
        refine ⟨204343101160362654884734513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272457468213816873179646017 204343101160362654884734513)
        ·
          refine ⟨153257325870271991163550885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204343101160362654884734513 153257325870271991163550885)
          ·
            refine ⟨28735748600675998343165791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153257325870271991163550885 28735748600675998343165791)
            ·
              refine ⟨43103622901013997514748687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28735748600675998343165791 43103622901013997514748687)
              ·
                refine ⟨64655434351520996272123031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43103622901013997514748687 64655434351520996272123031)
                ·
                  refine ⟨96983151527281494408184547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64655434351520996272123031 96983151527281494408184547)
                  ·
                    refine ⟨145474727290922241612276821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96983151527281494408184547 145474727290922241612276821)
                    ·
                      refine ⟨1704781960440495018893869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 145474727290922241612276821 1704781960440495018893869)
                      ·
                        rfl

theorem cell23_3320051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_3320051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320051 prefixEnd_3320051 := by exact prefixLift 3320051
  have htrace : WordTrace (prefixWord ++ tailWord_3320051) baseStart_3320051 baseEnd_3320051 := by
    simpa [prefixWord, tailWord_3320051, baseEnd_3320051] using wordTrace_append hprefix tailTrace_3320051
  have hstable : (prefixWord ++ tailWord_3320051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320051).length < 2 ^ (prefixWord ++ tailWord_3320051).sum := by decide
  have hdescent : baseEnd_3320051 < baseStart_3320051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320065 : List Nat := [1, 2, 4, 1, 1, 2, 5, 1, 6]
def baseStart_3320065 : Nat := 118140960795 + 3320065 * 2 ^ 59
def prefixEnd_3320065 : Nat := 4983230072969 + 3 ^ 40 * 3320065 * 2
def baseEnd_3320065 : Nat := 189421016574406440457645

theorem tailTrace_3320065 : CollatzResearch.WordTrace tailWord_3320065 prefixEnd_3320065 189421016574406440457645 := by
  unfold tailWord_3320065
  simp only [CollatzResearch.WordTrace]
  refine ⟨121092718716979001804185649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80728479144652667869457099 121092718716979001804185649)
  ·
    refine ⟨90819539037734251353139237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121092718716979001804185649 90819539037734251353139237)
    ·
      refine ⟨17028663569575172128713607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90819539037734251353139237 17028663569575172128713607)
      ·
        refine ⟨25542995354362758193070411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17028663569575172128713607 25542995354362758193070411)
        ·
          refine ⟨38314493031544137289605617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25542995354362758193070411 38314493031544137289605617)
          ·
            refine ⟨28735869773658102967204213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38314493031544137289605617 28735869773658102967204213)
            ·
              refine ⟨2693987791280447153175395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28735869773658102967204213 2693987791280447153175395)
              ·
                refine ⟨4040981686920670729763093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2693987791280447153175395 4040981686920670729763093)
                ·
                  refine ⟨189421016574406440457645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4040981686920670729763093 189421016574406440457645)
                  ·
                    rfl

theorem cell23_3320065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 6].length) (baseStart_3320065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320065 prefixEnd_3320065 := by exact prefixLift 3320065
  have htrace : WordTrace (prefixWord ++ tailWord_3320065) baseStart_3320065 baseEnd_3320065 := by
    simpa [prefixWord, tailWord_3320065, baseEnd_3320065] using wordTrace_append hprefix tailTrace_3320065
  have hstable : (prefixWord ++ tailWord_3320065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320065).length < 2 ^ (prefixWord ++ tailWord_3320065).sum := by decide
  have hdescent : baseEnd_3320065 < baseStart_3320065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320075 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 3, 1, 3]
def baseStart_3320075 : Nat := 118140960795 + 3320075 * 2 ^ 59
def prefixEnd_3320075 : Nat := 4983230072969 + 3 ^ 40 * 3320075 * 2
def baseEnd_3320075 : Nat := 1704794283976202924993759

theorem tailTrace_3320075 : CollatzResearch.WordTrace tailWord_3320075 prefixEnd_3320075 1704794283976202924993759 := by
  unfold tailWord_3320075
  simp only [CollatzResearch.WordTrace]
  refine ⟨121093083446942773512049679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80728722297961849008033119 121093083446942773512049679)
  ·
    refine ⟨181639625170414160268074519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121093083446942773512049679 181639625170414160268074519)
    ·
      refine ⟨272459437755621240402111779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181639625170414160268074519 272459437755621240402111779)
      ·
        refine ⟨408689156633431860603167669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272459437755621240402111779 408689156633431860603167669)
        ·
          refine ⟨38314608434384236931546969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 408689156633431860603167669 38314608434384236931546969)
          ·
            refine ⟨28735956325788177698660227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38314608434384236931546969 28735956325788177698660227)
            ·
              refine ⟨43103934488682266547990341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28735956325788177698660227 43103934488682266547990341)
              ·
                refine ⟨8081987716627924977748189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43103934488682266547990341 8081987716627924977748189)
                ·
                  refine ⟨3030745393735471866655571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8081987716627924977748189 3030745393735471866655571)
                  ·
                    refine ⟨4546118090603207799983357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3030745393735471866655571 4546118090603207799983357)
                    ·
                      refine ⟨1704794283976202924993759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4546118090603207799983357 1704794283976202924993759)
                      ·
                        rfl

theorem cell23_3320075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 1, 3].length) (baseStart_3320075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320075 prefixEnd_3320075 := by exact prefixLift 3320075
  have htrace : WordTrace (prefixWord ++ tailWord_3320075) baseStart_3320075 baseEnd_3320075 := by
    simpa [prefixWord, tailWord_3320075, baseEnd_3320075] using wordTrace_append hprefix tailTrace_3320075
  have hstable : (prefixWord ++ tailWord_3320075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320075).length < 2 ^ (prefixWord ++ tailWord_3320075).sum := by decide
  have hdescent : baseEnd_3320075 < baseStart_3320075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320085 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 1, 5, 2]
def baseStart_3320085 : Nat := 118140960795 + 3320085 * 2 ^ 59
def prefixEnd_3320085 : Nat := 4983230072969 + 3 ^ 40 * 3320085 * 2
def baseEnd_3320085 : Nat := 1704799418782747885868713

theorem tailTrace_3320085 : CollatzResearch.WordTrace tailWord_3320085 prefixEnd_3320085 1704799418782747885868713 := by
  unfold tailWord_3320085
  simp only [CollatzResearch.WordTrace]
  refine ⟨121093448176906545219913709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80728965451271030146609139 121093448176906545219913709)
  ·
    refine ⟨45410043066339954457467641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121093448176906545219913709 45410043066339954457467641)
    ·
      refine ⟨34057532299754965843100731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45410043066339954457467641 34057532299754965843100731)
      ·
        refine ⟨51086298449632448764651097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34057532299754965843100731 51086298449632448764651097)
        ·
          refine ⟨38314723837224336573488323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51086298449632448764651097 38314723837224336573488323)
          ·
            refine ⟨57472085755836504860232485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38314723837224336573488323 57472085755836504860232485)
            ·
              refine ⟨10776016079219344661293591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57472085755836504860232485 10776016079219344661293591)
              ·
                refine ⟨16164024118829016991940387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10776016079219344661293591 16164024118829016991940387)
                ·
                  refine ⟨24246036178243525487910581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16164024118829016991940387 24246036178243525487910581)
                  ·
                    refine ⟨2273065891710330514491617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24246036178243525487910581 2273065891710330514491617)
                    ·
                      refine ⟨1704799418782747885868713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2273065891710330514491617 1704799418782747885868713)
                      ·
                        rfl

theorem cell23_3320085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_3320085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320085 prefixEnd_3320085 := by exact prefixLift 3320085
  have htrace : WordTrace (prefixWord ++ tailWord_3320085) baseStart_3320085 baseEnd_3320085 := by
    simpa [prefixWord, tailWord_3320085, baseEnd_3320085] using wordTrace_append hprefix tailTrace_3320085
  have hstable : (prefixWord ++ tailWord_3320085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320085).length < 2 ^ (prefixWord ++ tailWord_3320085).sum := by decide
  have hdescent : baseEnd_3320085 < baseStart_3320085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320095 : List Nat := [1, 1, 2, 4, 3, 1, 2, 3, 1, 5]
def baseStart_3320095 : Nat := 118140960795 + 3320095 * 2 ^ 59
def prefixEnd_3320095 : Nat := 4983230072969 + 3 ^ 40 * 3320095 * 2
def baseEnd_3320095 : Nat := 568268184529764282247889

theorem tailTrace_3320095 : CollatzResearch.WordTrace tailWord_3320095 prefixEnd_3320095 568268184529764282247889 := by
  unfold tailWord_3320095
  simp only [CollatzResearch.WordTrace]
  refine ⟨121093812906870316927777739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80729208604580211285185159 121093812906870316927777739)
  ·
    refine ⟨181640719360305475391666609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121093812906870316927777739 181640719360305475391666609)
    ·
      refine ⟨136230539520229106543749957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181640719360305475391666609 136230539520229106543749957)
      ·
        refine ⟨25543226160042957476953117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136230539520229106543749957 25543226160042957476953117)
        ·
          refine ⟨9578709810016109053857419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25543226160042957476953117 9578709810016109053857419)
          ·
            refine ⟨14368064715024163580786129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9578709810016109053857419 14368064715024163580786129)
            ·
              refine ⟨10776048536268122685589597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14368064715024163580786129 10776048536268122685589597)
              ·
                refine ⟨4041018201100546007096099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10776048536268122685589597 4041018201100546007096099)
                ·
                  refine ⟨6061527301650819010644149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041018201100546007096099 6061527301650819010644149)
                  ·
                    refine ⟨568268184529764282247889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6061527301650819010644149 568268184529764282247889)
                    ·
                      rfl

theorem cell23_3320095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 5].length) (baseStart_3320095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320095 prefixEnd_3320095 := by exact prefixLift 3320095
  have htrace : WordTrace (prefixWord ++ tailWord_3320095) baseStart_3320095 baseEnd_3320095 := by
    simpa [prefixWord, tailWord_3320095, baseEnd_3320095] using wordTrace_append hprefix tailTrace_3320095
  have hstable : (prefixWord ++ tailWord_3320095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320095).length < 2 ^ (prefixWord ++ tailWord_3320095).sum := by decide
  have hdescent : baseEnd_3320095 < baseStart_3320095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320103 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3320103 : Nat := 118140960795 + 3320103 * 2 ^ 59
def prefixEnd_3320103 : Nat := 4983230072969 + 3 ^ 40 * 3320103 * 2
def baseEnd_3320103 : Nat := 568269553811509605147877

theorem tailTrace_3320103 : CollatzResearch.WordTrace tailWord_3320103 prefixEnd_3320103 568269553811509605147877 := by
  unfold tailWord_3320103
  simp only [CollatzResearch.WordTrace]
  refine ⟨121094104690841334294068963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80729403127227556196045975 121094104690841334294068963)
  ·
    refine ⟨181641157036262001441103445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121094104690841334294068963 181641157036262001441103445)
    ·
      refine ⟨2128607309018695329387931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 181641157036262001441103445 2128607309018695329387931)
      ·
        refine ⟨3192910963528042994081897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2128607309018695329387931 3192910963528042994081897)
        ·
          refine ⟨2394683222646032245561423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3192910963528042994081897 2394683222646032245561423)
          ·
            refine ⟨3592024833969048368342135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394683222646032245561423 3592024833969048368342135)
            ·
              refine ⟨5388037250953572552513203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592024833969048368342135 5388037250953572552513203)
              ·
                refine ⟨8082055876430358828769805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5388037250953572552513203 8082055876430358828769805)
                ·
                  refine ⟨3030770953661384560788677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8082055876430358828769805 3030770953661384560788677)
                  ·
                    refine ⟨568269553811509605147877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3030770953661384560788677 568269553811509605147877)
                    ·
                      rfl

theorem cell23_3320103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3320103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320103 prefixEnd_3320103 := by exact prefixLift 3320103
  have htrace : WordTrace (prefixWord ++ tailWord_3320103) baseStart_3320103 baseEnd_3320103 := by
    simpa [prefixWord, tailWord_3320103, baseEnd_3320103] using wordTrace_append hprefix tailTrace_3320103
  have hstable : (prefixWord ++ tailWord_3320103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320103).length < 2 ^ (prefixWord ++ tailWord_3320103).sum := by decide
  have hdescent : baseEnd_3320103 < baseStart_3320103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320129 : List Nat := [1, 2, 5, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3320129 : Nat := 118140960795 + 3320129 * 2 ^ 59
def prefixEnd_3320129 : Nat := 4983230072969 + 3 ^ 40 * 3320129 * 2
def baseEnd_3320129 : Nat := 568274003977181904572837

theorem tailTrace_3320129 : CollatzResearch.WordTrace tailWord_3320129 prefixEnd_3320129 568274003977181904572837 := by
  unfold tailWord_3320129
  simp only [CollatzResearch.WordTrace]
  refine ⟨121095052988747140734515441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80730035325831427156343627 121095052988747140734515441)
  ·
    refine ⟨90821289741560355550886581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121095052988747140734515441 90821289741560355550886581)
    ·
      refine ⟨8514495913271283332895617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90821289741560355550886581 8514495913271283332895617)
      ·
        refine ⟨6385871934953462499671713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8514495913271283332895617 6385871934953462499671713)
        ·
          refine ⟨4789403951215096874753785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6385871934953462499671713 4789403951215096874753785)
          ·
            refine ⟨3592052963411322656065339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4789403951215096874753785 3592052963411322656065339)
            ·
              refine ⟨5388079445116983984098009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592052963411322656065339 5388079445116983984098009)
              ·
                refine ⟨4041059583837737988073507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5388079445116983984098009 4041059583837737988073507)
                ·
                  refine ⟨6061589375756606982110261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041059583837737988073507 6061589375756606982110261)
                  ·
                    refine ⟨568274003977181904572837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6061589375756606982110261 568274003977181904572837)
                    ·
                      rfl

theorem cell23_3320129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3320129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320129 prefixEnd_3320129 := by exact prefixLift 3320129
  have htrace : WordTrace (prefixWord ++ tailWord_3320129) baseStart_3320129 baseEnd_3320129 := by
    simpa [prefixWord, tailWord_3320129, baseEnd_3320129] using wordTrace_append hprefix tailTrace_3320129
  have hstable : (prefixWord ++ tailWord_3320129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320129).length < 2 ^ (prefixWord ++ tailWord_3320129).sum := by decide
  have hdescent : baseEnd_3320129 < baseStart_3320129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320135 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_3320135 : Nat := 118140960795 + 3320135 * 2 ^ 59
def prefixEnd_3320135 : Nat := 4983230072969 + 3 ^ 40 * 3320135 * 2
def baseEnd_3320135 : Nat := 1704825092815472690243483

theorem tailTrace_3320135 : CollatzResearch.WordTrace tailWord_3320135 prefixEnd_3320135 1704825092815472690243483 := by
  unfold tailWord_3320135
  simp only [CollatzResearch.WordTrace]
  refine ⟨121095271826725403759233859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80730181217816935839489239 121095271826725403759233859)
  ·
    refine ⟨181642907740088105638850789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121095271826725403759233859 181642907740088105638850789)
    ·
      refine ⟨34058045201266519807284523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181642907740088105638850789 34058045201266519807284523)
      ·
        refine ⟨51087067801899779710926785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34058045201266519807284523 51087067801899779710926785)
        ·
          refine ⟨38315300851424834783195089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51087067801899779710926785 38315300851424834783195089)
          ·
            refine ⟨28736475638568626087396317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38315300851424834783195089 28736475638568626087396317)
            ·
              refine ⟨10776178364463234782773619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28736475638568626087396317 10776178364463234782773619)
              ·
                refine ⟨16164267546694852174160429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10776178364463234782773619 16164267546694852174160429)
                ·
                  refine ⟨6061600330010569565310161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16164267546694852174160429 6061600330010569565310161)
                  ·
                    refine ⟨4546200247507927173982621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6061600330010569565310161 4546200247507927173982621)
                    ·
                      refine ⟨1704825092815472690243483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4546200247507927173982621 1704825092815472690243483)
                      ·
                        rfl

theorem cell23_3320135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_3320135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320135 prefixEnd_3320135 := by exact prefixLift 3320135
  have htrace : WordTrace (prefixWord ++ tailWord_3320135) baseStart_3320135 baseEnd_3320135 := by
    simpa [prefixWord, tailWord_3320135, baseEnd_3320135] using wordTrace_append hprefix tailTrace_3320135
  have hstable : (prefixWord ++ tailWord_3320135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320135).length < 2 ^ (prefixWord ++ tailWord_3320135).sum := by decide
  have hdescent : baseEnd_3320135 < baseStart_3320135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320145 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 1, 2, 4]
def baseStart_3320145 : Nat := 118140960795 + 3320145 * 2 ^ 59
def prefixEnd_3320145 : Nat := 4983230072969 + 3 ^ 40 * 3320145 * 2
def baseEnd_3320145 : Nat := 1704830227622017651118437

theorem tailTrace_3320145 : CollatzResearch.WordTrace tailWord_3320145 prefixEnd_3320145 1704830227622017651118437 := by
  unfold tailWord_3320145
  simp only [CollatzResearch.WordTrace]
  refine ⟨121095636556689175467097889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80730424371126116978065259 121095636556689175467097889)
  ·
    refine ⟨90821727417516881600323417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121095636556689175467097889 90821727417516881600323417)
    ·
      refine ⟨68116295563137661200242563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90821727417516881600323417 68116295563137661200242563)
      ·
        refine ⟨102174443344706491800363845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68116295563137661200242563 102174443344706491800363845)
        ·
          refine ⟨19157708127132467212568221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102174443344706491800363845 19157708127132467212568221)
          ·
            refine ⟨7184140547674675204713083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19157708127132467212568221 7184140547674675204713083)
            ·
              refine ⟨10776210821512012807069625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7184140547674675204713083 10776210821512012807069625)
              ·
                refine ⟨8082158116134009605302219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10776210821512012807069625 8082158116134009605302219)
                ·
                  refine ⟨12123237174201014407953329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8082158116134009605302219 12123237174201014407953329)
                  ·
                    refine ⟨9092427880650760805964997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12123237174201014407953329 9092427880650760805964997)
                    ·
                      refine ⟨1704830227622017651118437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9092427880650760805964997 1704830227622017651118437)
                      ·
                        rfl

theorem cell23_3320145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_3320145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320145 prefixEnd_3320145 := by exact prefixLift 3320145
  have htrace : WordTrace (prefixWord ++ tailWord_3320145) baseStart_3320145 baseEnd_3320145 := by
    simpa [prefixWord, tailWord_3320145, baseEnd_3320145] using wordTrace_append hprefix tailTrace_3320145
  have hstable : (prefixWord ++ tailWord_3320145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320145).length < 2 ^ (prefixWord ++ tailWord_3320145).sum := by decide
  have hdescent : baseEnd_3320145 < baseStart_3320145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320149 : List Nat := [1, 3, 2, 2, 4, 1, 3, 1, 1, 1, 4]
def baseStart_3320149 : Nat := 118140960795 + 3320149 * 2 ^ 59
def prefixEnd_3320149 : Nat := 4983230072969 + 3 ^ 40 * 3320149 * 2
def baseEnd_3320149 : Nat := 1704832281544635635468419

theorem tailTrace_3320149 : CollatzResearch.WordTrace tailWord_3320149 prefixEnd_3320149 1704832281544635635468419 := by
  unfold tailWord_3320149
  simp only [CollatzResearch.WordTrace]
  refine ⟨121095782448674684150243501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80730521632449789433495667 121095782448674684150243501)
  ·
    refine ⟨45410918418253006556341313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121095782448674684150243501 45410918418253006556341313)
    ·
      refine ⟨34058188813689754917255985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45410918418253006556341313 34058188813689754917255985)
      ·
        refine ⟨25543641610267316187941989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34058188813689754917255985 25543641610267316187941989)
        ·
          refine ⟨4789432801925121785239123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25543641610267316187941989 4789432801925121785239123)
          ·
            refine ⟨7184149202887682677858685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789432801925121785239123 7184149202887682677858685)
            ·
              refine ⟨2694055951082881004197007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7184149202887682677858685 2694055951082881004197007)
              ·
                refine ⟨4041083926624321506295511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2694055951082881004197007 4041083926624321506295511)
                ·
                  refine ⟨6061625889936482259443267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041083926624321506295511 6061625889936482259443267)
                  ·
                    refine ⟨9092438834904723389164901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6061625889936482259443267 9092438834904723389164901)
                    ·
                      refine ⟨1704832281544635635468419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9092438834904723389164901 1704832281544635635468419)
                      ·
                        rfl

theorem cell23_3320149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_3320149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320149 prefixEnd_3320149 := by exact prefixLift 3320149
  have htrace : WordTrace (prefixWord ++ tailWord_3320149) baseStart_3320149 baseEnd_3320149 := by
    simpa [prefixWord, tailWord_3320149, baseEnd_3320149] using wordTrace_append hprefix tailTrace_3320149
  have hstable : (prefixWord ++ tailWord_3320149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320149).length < 2 ^ (prefixWord ++ tailWord_3320149).sum := by decide
  have hdescent : baseEnd_3320149 < baseStart_3320149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320172 : List Nat := [2, 2, 1, 1, 7, 1, 1, 8]
def baseStart_3320172 : Nat := 118140960795 + 3320172 * 2 ^ 59
def prefixEnd_3320172 : Nat := 4983230072969 + 3 ^ 40 * 3320172 * 2
def baseEnd_3320172 : Nat := 63142373762951446128919

theorem tailTrace_3320172 : CollatzResearch.WordTrace tailWord_3320172 prefixEnd_3320172 63142373762951446128919 := by
  unfold tailWord_3320172
  simp only [CollatzResearch.WordTrace]
  refine ⟨60548310663795679539165385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80731080885060906052220513 60548310663795679539165385)
  ·
    refine ⟨45411232997846759654374039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60548310663795679539165385 45411232997846759654374039)
    ·
      refine ⟨68116849496770139481561059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45411232997846759654374039 68116849496770139481561059)
      ·
        refine ⟨102175274245155209222341589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68116849496770139481561059 102175274245155209222341589)
        ·
          refine ⟨2394732990120825216148631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 102175274245155209222341589 2394732990120825216148631)
          ·
            refine ⟨3592099485181237824222947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394732990120825216148631 3592099485181237824222947)
            ·
              refine ⟨5388149227771856736334421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592099485181237824222947 5388149227771856736334421)
              ·
                refine ⟨63142373762951446128919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5388149227771856736334421 63142373762951446128919)
                ·
                  rfl

theorem cell23_3320172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 8].length) (baseStart_3320172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320172 prefixEnd_3320172 := by exact prefixLift 3320172
  have htrace : WordTrace (prefixWord ++ tailWord_3320172) baseStart_3320172 baseEnd_3320172 := by
    simpa [prefixWord, tailWord_3320172, baseEnd_3320172] using wordTrace_append hprefix tailTrace_3320172
  have hstable : (prefixWord ++ tailWord_3320172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320172).length < 2 ^ (prefixWord ++ tailWord_3320172).sum := by decide
  have hdescent : baseEnd_3320172 < baseStart_3320172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320216 : List Nat := [2, 1, 2, 5, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3320216 : Nat := 118140960795 + 3320216 * 2 ^ 59
def prefixEnd_3320216 : Nat := 4983230072969 + 3 ^ 40 * 3320216 * 2
def baseEnd_3320216 : Nat := 1704866684748486873330611

theorem tailTrace_3320216 : CollatzResearch.WordTrace tailWord_3320216 prefixEnd_3320216 1704866684748486873330611 := by
  unfold tailWord_3320216
  simp only [CollatzResearch.WordTrace]
  refine ⟨60549113069715977296466251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80732150759621303061955001 60549113069715977296466251)
  ·
    refine ⟨90823669604573965944699377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60549113069715977296466251 90823669604573965944699377)
    ·
      refine ⟨68117752203430474458524533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90823669604573965944699377 68117752203430474458524533)
      ·
        refine ⟨6386039269071606980486675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68117752203430474458524533 6386039269071606980486675)
        ·
          refine ⟨9579058903607410470730013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6386039269071606980486675 9579058903607410470730013)
          ·
            refine ⟨3592147088852778926523755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9579058903607410470730013 3592147088852778926523755)
            ·
              refine ⟨5388220633279168389785633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592147088852778926523755 5388220633279168389785633)
              ·
                refine ⟨4041165474959376292339225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5388220633279168389785633 4041165474959376292339225)
                ·
                  refine ⟨3030874106219532219254419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4041165474959376292339225 3030874106219532219254419)
                  ·
                    refine ⟨4546311159329298328881629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3030874106219532219254419 4546311159329298328881629)
                    ·
                      refine ⟨1704866684748486873330611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4546311159329298328881629 1704866684748486873330611)
                      ·
                        rfl

theorem cell23_3320216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3320216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320216 prefixEnd_3320216 := by exact prefixLift 3320216
  have htrace : WordTrace (prefixWord ++ tailWord_3320216) baseStart_3320216 baseEnd_3320216 := by
    simpa [prefixWord, tailWord_3320216, baseEnd_3320216] using wordTrace_append hprefix tailTrace_3320216
  have hstable : (prefixWord ++ tailWord_3320216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320216).length < 2 ^ (prefixWord ++ tailWord_3320216).sum := by decide
  have hdescent : baseEnd_3320216 < baseStart_3320216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320232 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 2, 6]
def baseStart_3320232 : Nat := 118140960795 + 3320232 * 2 ^ 59
def prefixEnd_3320232 : Nat := 4983230072969 + 3 ^ 40 * 3320232 * 2
def baseEnd_3320232 : Nat := 568291633479652936910179

theorem tailTrace_3320232 : CollatzResearch.WordTrace tailWord_3320232 prefixEnd_3320232 568291633479652936910179 := by
  unfold tailWord_3320232
  simp only [CollatzResearch.WordTrace]
  refine ⟨60549404853686994662757475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80732539804915992883676633 60549404853686994662757475)
  ·
    refine ⟨90824107280530491994136213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60549404853686994662757475 90824107280530491994136213)
    ·
      refine ⟨4257380028774866812225135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90824107280530491994136213 4257380028774866812225135)
      ·
        refine ⟨6386070043162300218337703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4257380028774866812225135 6386070043162300218337703)
        ·
          refine ⟨9579105064743450327506555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6386070043162300218337703 9579105064743450327506555)
          ·
            refine ⟨14368657597115175491259833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9579105064743450327506555 14368657597115175491259833)
            ·
              refine ⟨10776493197836381618444875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14368657597115175491259833 10776493197836381618444875)
              ·
                refine ⟨16164739796754572427667313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10776493197836381618444875 16164739796754572427667313)
                ·
                  refine ⟨12123554847565929320750485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16164739796754572427667313 12123554847565929320750485)
                  ·
                    refine ⟨568291633479652936910179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12123554847565929320750485 568291633479652936910179)
                    ·
                      rfl

theorem cell23_3320232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_3320232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320232 prefixEnd_3320232 := by exact prefixLift 3320232
  have htrace : WordTrace (prefixWord ++ tailWord_3320232) baseStart_3320232 baseEnd_3320232 := by
    simpa [prefixWord, tailWord_3320232, baseEnd_3320232] using wordTrace_append hprefix tailTrace_3320232
  have hstable : (prefixWord ++ tailWord_3320232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320232).length < 2 ^ (prefixWord ++ tailWord_3320232).sum := by decide
  have hdescent : baseEnd_3320232 < baseStart_3320232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320282 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2]
def baseStart_3320282 : Nat := 118140960795 + 3320282 * 2 ^ 59
def prefixEnd_3320282 : Nat := 4983230072969 + 3 ^ 40 * 3320282 * 2
def baseEnd_3320282 : Nat := 1704900574471683615105307

theorem tailTrace_3320282 : CollatzResearch.WordTrace tailWord_3320282 prefixEnd_3320282 1704900574471683615105307 := by
  unfold tailWord_3320282
  simp only [CollatzResearch.WordTrace]
  refine ⟨30275158339298211966208775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80733755571461898576556733 30275158339298211966208775)
  ·
    refine ⟨45412737508947317949313163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30275158339298211966208775 45412737508947317949313163)
    ·
      refine ⟨68119106263420976923969745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45412737508947317949313163 68119106263420976923969745)
      ·
        refine ⟨51089329697565732692977309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68119106263420976923969745 51089329697565732692977309)
        ·
          refine ⟨19158498636587149759866491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51089329697565732692977309 19158498636587149759866491)
          ·
            refine ⟨28737747954880724639799737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19158498636587149759866491 28737747954880724639799737)
            ·
              refine ⟨21553310966160543479849803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28737747954880724639799737 21553310966160543479849803)
              ·
                refine ⟨32329966449240815219774705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21553310966160543479849803 32329966449240815219774705)
                ·
                  refine ⟨24247474836930611414831029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32329966449240815219774705 24247474836930611414831029)
                  ·
                    refine ⟨2273200765962244820140409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24247474836930611414831029 2273200765962244820140409)
                    ·
                      refine ⟨1704900574471683615105307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2273200765962244820140409 1704900574471683615105307)
                      ·
                        rfl

theorem cell23_3320282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_3320282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320282 prefixEnd_3320282 := by exact prefixLift 3320282
  have htrace : WordTrace (prefixWord ++ tailWord_3320282) baseStart_3320282 baseEnd_3320282 := by
    simpa [prefixWord, tailWord_3320282, baseEnd_3320282] using wordTrace_append hprefix tailTrace_3320282
  have hstable : (prefixWord ++ tailWord_3320282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320282).length < 2 ^ (prefixWord ++ tailWord_3320282).sum := by decide
  have hdescent : baseEnd_3320282 < baseStart_3320282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320290 : List Nat := [3, 3, 3, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_3320290 : Nat := 118140960795 + 3320290 * 2 ^ 59
def prefixEnd_3320290 : Nat := 4983230072969 + 3 ^ 40 * 3320290 * 2
def baseEnd_3320290 : Nat := 1704904682316919583805271

theorem tailTrace_3320290 : CollatzResearch.WordTrace tailWord_3320290 prefixEnd_3320290 1704904682316919583805271 := by
  unfold tailWord_3320290
  simp only [CollatzResearch.WordTrace]
  refine ⟨30275231285290966307781581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80733950094109243487417549 30275231285290966307781581)
  ·
    refine ⟨11353211731984112365418093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30275231285290966307781581 11353211731984112365418093)
    ·
      refine ⟨4257454399494042137031785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11353211731984112365418093 4257454399494042137031785)
      ·
        refine ⟨3193090799620531602773839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4257454399494042137031785 3193090799620531602773839)
        ·
          refine ⟨4789636199430797404160759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193090799620531602773839 4789636199430797404160759)
          ·
            refine ⟨7184454299146196106241139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789636199430797404160759 7184454299146196106241139)
            ·
              refine ⟨10776681448719294159361709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7184454299146196106241139 10776681448719294159361709)
              ·
                refine ⟨4041255543269735309760641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10776681448719294159361709 4041255543269735309760641)
                ·
                  refine ⟨3030941657452301482320481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4041255543269735309760641 3030941657452301482320481)
                  ·
                    refine ⟨2273206243089226111740361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3030941657452301482320481 2273206243089226111740361)
                    ·
                      refine ⟨1704904682316919583805271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2273206243089226111740361 1704904682316919583805271)
                      ·
                        rfl

theorem cell23_3320290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_3320290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320290 prefixEnd_3320290 := by exact prefixLift 3320290
  have htrace : WordTrace (prefixWord ++ tailWord_3320290) baseStart_3320290 baseEnd_3320290 := by
    simpa [prefixWord, tailWord_3320290, baseEnd_3320290] using wordTrace_append hprefix tailTrace_3320290
  have hstable : (prefixWord ++ tailWord_3320290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320290).length < 2 ^ (prefixWord ++ tailWord_3320290).sum := by decide
  have hdescent : baseEnd_3320290 < baseStart_3320290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320312 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 2, 1, 4]
def baseStart_3320312 : Nat := 118140960795 + 3320312 * 2 ^ 59
def prefixEnd_3320312 : Nat := 4983230072969 + 3 ^ 40 * 3320312 * 2
def baseEnd_3320312 : Nat := 1704915978891318497730169

theorem tailTrace_3320312 : CollatzResearch.WordTrace tailWord_3320312 prefixEnd_3320312 1704915978891318497730169 := by
  unfold tailWord_3320312
  simp only [CollatzResearch.WordTrace]
  refine ⟨60550863773542081494213595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80734485031389441992284793 60550863773542081494213595)
  ·
    refine ⟨90826295660313122241320393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60550863773542081494213595 90826295660313122241320393)
    ·
      refine ⟨68119721745234841680990295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90826295660313122241320393 68119721745234841680990295)
      ·
        refine ⟨102179582617852262521485443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68119721745234841680990295 102179582617852262521485443)
        ·
          refine ⟨153269373926778393782228165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102179582617852262521485443 153269373926778393782228165)
          ·
            refine ⟨28738007611270948834167781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153269373926778393782228165 28738007611270948834167781)
            ·
              refine ⟨5388376427113302906406459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28738007611270948834167781 5388376427113302906406459)
              ·
                refine ⟨8082564640669954359609689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5388376427113302906406459 8082564640669954359609689)
                ·
                  refine ⟨6061923480502465769707267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8082564640669954359609689 6061923480502465769707267)
                  ·
                    refine ⟨9092885220753698654560901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6061923480502465769707267 9092885220753698654560901)
                    ·
                      refine ⟨1704915978891318497730169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9092885220753698654560901 1704915978891318497730169)
                      ·
                        rfl

theorem cell23_3320312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_3320312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320312 prefixEnd_3320312 := by exact prefixLift 3320312
  have htrace : WordTrace (prefixWord ++ tailWord_3320312) baseStart_3320312 baseEnd_3320312 := by
    simpa [prefixWord, tailWord_3320312, baseEnd_3320312] using wordTrace_append hprefix tailTrace_3320312
  have hstable : (prefixWord ++ tailWord_3320312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320312).length < 2 ^ (prefixWord ++ tailWord_3320312).sum := by decide
  have hdescent : baseEnd_3320312 < baseStart_3320312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320335 : List Nat := [1, 1, 2, 1, 1, 1, 2, 8, 6]
def baseStart_3320335 : Nat := 118140960795 + 3320335 * 2 ^ 59
def prefixEnd_3320335 : Nat := 4983230072969 + 3 ^ 40 * 3320335 * 2
def baseEnd_3320335 : Nat := 189436420994041323082507

theorem tailTrace_3320335 : CollatzResearch.WordTrace tailWord_3320335 prefixEnd_3320335 189436420994041323082507 := by
  unfold tailWord_3320335
  simp only [CollatzResearch.WordTrace]
  refine ⟨121102566426000837916514459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80735044284000558611009639 121102566426000837916514459)
  ·
    refine ⟨181653849639001256874771689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121102566426000837916514459 181653849639001256874771689)
    ·
      refine ⟨136240387229250942656078767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181653849639001256874771689 136240387229250942656078767)
      ·
        refine ⟨204360580843876413984118151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136240387229250942656078767 204360580843876413984118151)
        ·
          refine ⟨306540871265814620976177227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204360580843876413984118151 306540871265814620976177227)
          ·
            refine ⟨459811306898721931464265841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306540871265814620976177227 459811306898721931464265841)
            ·
              refine ⟨344858480174041448598199381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459811306898721931464265841 344858480174041448598199381)
              ·
                refine ⟨4041310314539548225760149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 344858480174041448598199381 4041310314539548225760149)
                ·
                  refine ⟨189436420994041323082507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4041310314539548225760149 189436420994041323082507)
                  ·
                    rfl

theorem cell23_3320335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 6].length) (baseStart_3320335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320335 prefixEnd_3320335 := by exact prefixLift 3320335
  have htrace : WordTrace (prefixWord ++ tailWord_3320335) baseStart_3320335 baseEnd_3320335 := by
    simpa [prefixWord, tailWord_3320335, baseEnd_3320335] using wordTrace_append hprefix tailTrace_3320335
  have hstable : (prefixWord ++ tailWord_3320335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320335).length < 2 ^ (prefixWord ++ tailWord_3320335).sum := by decide
  have hdescent : baseEnd_3320335 < baseStart_3320335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320339 : List Nat := [1, 1, 1, 2, 1, 5, 3, 4, 1, 4]
def baseStart_3320339 : Nat := 118140960795 + 3320339 * 2 ^ 59
def prefixEnd_3320339 : Nat := 4983230072969 + 3 ^ 40 * 3320339 * 2
def baseEnd_3320339 : Nat := 568309947622996630697515

theorem tailTrace_3320339 : CollatzResearch.WordTrace tailWord_3320339 prefixEnd_3320339 568309947622996630697515 := by
  unfold tailWord_3320339
  simp only [CollatzResearch.WordTrace]
  refine ⟨121102712317986346599660071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80735141545324231066440047 121102712317986346599660071)
  ·
    refine ⟨181654068476979519899490107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121102712317986346599660071 181654068476979519899490107)
    ·
      refine ⟨272481102715469279849235161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181654068476979519899490107 272481102715469279849235161)
      ·
        refine ⟨204360827036601959886926371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272481102715469279849235161 204360827036601959886926371)
        ·
          refine ⟨306541240554902939830389557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204360827036601959886926371 306541240554902939830389557)
          ·
            refine ⟨28738241302022150609099021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 306541240554902939830389557 28738241302022150609099021)
            ·
              refine ⟨10776840488258306478412133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28738241302022150609099021 10776840488258306478412133)
              ·
                refine ⟨2020657591548432464702275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10776840488258306478412133 2020657591548432464702275)
                ·
                  refine ⟨3030986387322648697053413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020657591548432464702275 3030986387322648697053413)
                  ·
                    refine ⟨568309947622996630697515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3030986387322648697053413 568309947622996630697515)
                    ·
                      rfl

theorem cell23_3320339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 1, 4].length) (baseStart_3320339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320339 prefixEnd_3320339 := by exact prefixLift 3320339
  have htrace : WordTrace (prefixWord ++ tailWord_3320339) baseStart_3320339 baseEnd_3320339 := by
    simpa [prefixWord, tailWord_3320339, baseEnd_3320339] using wordTrace_append hprefix tailTrace_3320339
  have hstable : (prefixWord ++ tailWord_3320339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320339).length < 2 ^ (prefixWord ++ tailWord_3320339).sum := by decide
  have hdescent : baseEnd_3320339 < baseStart_3320339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320356 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_3320356 : Nat := 118140960795 + 3320356 * 2 ^ 59
def prefixEnd_3320356 : Nat := 4983230072969 + 3 ^ 40 * 3320356 * 2
def baseEnd_3320356 : Nat := 568312857346705441859989

theorem tailTrace_3320356 : CollatzResearch.WordTrace tailWord_3320356 prefixEnd_3320356 568312857346705441859989 := by
  unfold tailWord_3320356
  simp only [CollatzResearch.WordTrace]
  refine ⟨60551666179462379251514461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80735554905949839002019281 60551666179462379251514461)
  ·
    refine ⟨22706874817298392219317923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60551666179462379251514461 22706874817298392219317923)
    ·
      refine ⟨34060312225947588328976885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22706874817298392219317923 34060312225947588328976885)
      ·
        refine ⟨3193154271182586405841583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34060312225947588328976885 3193154271182586405841583)
        ·
          refine ⟨4789731406773879608762375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193154271182586405841583 4789731406773879608762375)
          ·
            refine ⟨7184597110160819413143563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789731406773879608762375 7184597110160819413143563)
            ·
              refine ⟨10776895665241229119715345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7184597110160819413143563 10776895665241229119715345)
              ·
                refine ⟨8082671748930921839786509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10776895665241229119715345 8082671748930921839786509)
                ·
                  refine ⟨3031001905849095689919941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8082671748930921839786509 3031001905849095689919941)
                  ·
                    refine ⟨568312857346705441859989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3031001905849095689919941 568312857346705441859989)
                    ·
                      rfl

theorem cell23_3320356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_3320356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320356 prefixEnd_3320356 := by exact prefixLift 3320356
  have htrace : WordTrace (prefixWord ++ tailWord_3320356) baseStart_3320356 baseEnd_3320356 := by
    simpa [prefixWord, tailWord_3320356, baseEnd_3320356] using wordTrace_append hprefix tailTrace_3320356
  have hstable : (prefixWord ++ tailWord_3320356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320356).length < 2 ^ (prefixWord ++ tailWord_3320356).sum := by decide
  have hdescent : baseEnd_3320356 < baseStart_3320356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320395 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 3, 6]
def baseStart_3320395 : Nat := 118140960795 + 3320395 * 2 ^ 59
def prefixEnd_3320395 : Nat := 4983230072969 + 3 ^ 40 * 3320395 * 2
def baseEnd_3320395 : Nat := 568319532595213890997429

theorem tailTrace_3320395 : CollatzResearch.WordTrace tailWord_3320395 prefixEnd_3320395 568319532595213890997429 := by
  unfold tailWord_3320395
  simp only [CollatzResearch.WordTrace]
  refine ⟨121104754805783468163698639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80736503203855645442465759 121104754805783468163698639)
  ·
    refine ⟨181657132208675202245547959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121104754805783468163698639 181657132208675202245547959)
    ·
      refine ⟨272485698313012803368321939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181657132208675202245547959 272485698313012803368321939)
      ·
        refine ⟨408728547469519205052482909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272485698313012803368321939 408728547469519205052482909)
        ·
          refine ⟨153273205301069701894681091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 408728547469519205052482909 153273205301069701894681091)
          ·
            refine ⟨229909807951604552842021637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153273205301069701894681091 229909807951604552842021637)
            ·
              refine ⟨43108088990925853657879057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229909807951604552842021637 43108088990925853657879057)
              ·
                refine ⟨32331066743194390243409293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43108088990925853657879057 32331066743194390243409293)
                ·
                  refine ⟨12124150028697896341278485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32331066743194390243409293 12124150028697896341278485)
                  ·
                    refine ⟨568319532595213890997429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12124150028697896341278485 568319532595213890997429)
                    ·
                      rfl

theorem cell23_3320395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 6].length) (baseStart_3320395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320395 prefixEnd_3320395 := by exact prefixLift 3320395
  have htrace : WordTrace (prefixWord ++ tailWord_3320395) baseStart_3320395 baseEnd_3320395 := by
    simpa [prefixWord, tailWord_3320395, baseEnd_3320395] using wordTrace_append hprefix tailTrace_3320395
  have hstable : (prefixWord ++ tailWord_3320395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320395).length < 2 ^ (prefixWord ++ tailWord_3320395).sum := by decide
  have hdescent : baseEnd_3320395 < baseStart_3320395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320396 : List Nat := [2, 2, 1, 3, 1, 2, 1, 6, 1, 1, 3]
def baseStart_3320396 : Nat := 118140960795 + 3320396 * 2 ^ 59
def prefixEnd_3320396 : Nat := 4983230072969 + 3 ^ 40 * 3320396 * 2
def baseEnd_3320396 : Nat := 1704959111266296169079783

theorem tailTrace_3320396 : CollatzResearch.WordTrace tailWord_3320396 prefixEnd_3320396 1704959111266296169079783 := by
  unfold tailWord_3320396
  simp only [CollatzResearch.WordTrace]
  refine ⟨60552395639389922667242521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80736527519186563556323361 60552395639389922667242521)
  ·
    refine ⟨45414296729542442000431891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60552395639389922667242521 45414296729542442000431891)
    ·
      refine ⟨68121445094313663000647837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45414296729542442000431891 68121445094313663000647837)
      ·
        refine ⟨25545541910367623625242939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68121445094313663000647837 25545541910367623625242939)
        ·
          refine ⟨38318312865551435437864409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25545541910367623625242939 38318312865551435437864409)
          ·
            refine ⟨28738734649163576578398307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38318312865551435437864409 28738734649163576578398307)
            ·
              refine ⟨43108101973745364867597461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28738734649163576578398307 43108101973745364867597461)
              ·
                refine ⟨2020692280019313978168631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43108101973745364867597461 2020692280019313978168631)
                ·
                  refine ⟨3031038420028970967252947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020692280019313978168631 3031038420028970967252947)
                  ·
                    refine ⟨4546557630043456450879421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3031038420028970967252947 4546557630043456450879421)
                    ·
                      refine ⟨1704959111266296169079783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4546557630043456450879421 1704959111266296169079783)
                      ·
                        rfl

theorem cell23_3320396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_3320396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320396 prefixEnd_3320396 := by exact prefixLift 3320396
  have htrace : WordTrace (prefixWord ++ tailWord_3320396) baseStart_3320396 baseEnd_3320396 := by
    simpa [prefixWord, tailWord_3320396, baseEnd_3320396] using wordTrace_append hprefix tailTrace_3320396
  have hstable : (prefixWord ++ tailWord_3320396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320396).length < 2 ^ (prefixWord ++ tailWord_3320396).sum := by decide
  have hdescent : baseEnd_3320396 < baseStart_3320396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320419 : List Nat := [1, 1, 1, 5, 1, 2, 4, 2, 1, 1, 4]
def baseStart_3320419 : Nat := 118140960795 + 3320419 * 2 ^ 59
def prefixEnd_3320419 : Nat := 4983230072969 + 3 ^ 40 * 3320419 * 2
def baseEnd_3320419 : Nat := 1704970921321349579092177

theorem tailTrace_3320419 : CollatzResearch.WordTrace tailWord_3320419 prefixEnd_3320419 1704970921321349579092177 := by
  unfold tailWord_3320419
  simp only [CollatzResearch.WordTrace]
  refine ⟨121105630157696520262572311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80737086771797680175048207 121105630157696520262572311)
  ·
    refine ⟨181658445236544780393858467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121105630157696520262572311 181658445236544780393858467)
    ·
      refine ⟨272487667854817170590787701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181658445236544780393858467 272487667854817170590787701)
      ·
        refine ⟨25545718861389109742886347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272487667854817170590787701 25545718861389109742886347)
        ·
          refine ⟨38318578292083664614329521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25545718861389109742886347 38318578292083664614329521)
          ·
            refine ⟨28738933719062748460747141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38318578292083664614329521 28738933719062748460747141)
            ·
              refine ⟨5388550072324265336390089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28738933719062748460747141 5388550072324265336390089)
              ·
                refine ⟨4041412554243199002292567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5388550072324265336390089 4041412554243199002292567)
                ·
                  refine ⟨6062118831364798503438851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041412554243199002292567 6062118831364798503438851)
                  ·
                    refine ⟨9093178247047197755158277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6062118831364798503438851 9093178247047197755158277)
                    ·
                      refine ⟨1704970921321349579092177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9093178247047197755158277 1704970921321349579092177)
                      ·
                        rfl

theorem cell23_3320419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_3320419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320419 prefixEnd_3320419 := by exact prefixLift 3320419
  have htrace : WordTrace (prefixWord ++ tailWord_3320419) baseStart_3320419 baseEnd_3320419 := by
    simpa [prefixWord, tailWord_3320419, baseEnd_3320419] using wordTrace_append hprefix tailTrace_3320419
  have hstable : (prefixWord ++ tailWord_3320419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320419).length < 2 ^ (prefixWord ++ tailWord_3320419).sum := by decide
  have hdescent : baseEnd_3320419 < baseStart_3320419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320429 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_3320429 : Nat := 118140960795 + 3320429 * 2 ^ 59
def prefixEnd_3320429 : Nat := 4983230072969 + 3 ^ 40 * 3320429 * 2
def baseEnd_3320429 : Nat := 568325352042631513322377

theorem tailTrace_3320429 : CollatzResearch.WordTrace tailWord_3320429 prefixEnd_3320429 568325352042631513322377 := by
  unfold tailWord_3320429
  simp only [CollatzResearch.WordTrace]
  refine ⟨121105994887660291970436341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80737329925106861313624227 121105994887660291970436341)
  ·
    refine ⟨11353687020718152372228407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121105994887660291970436341 11353687020718152372228407)
    ·
      refine ⟨17030530531077228558342611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11353687020718152372228407 17030530531077228558342611)
      ·
        refine ⟨25545795796615842837513917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17030530531077228558342611 25545795796615842837513917)
        ·
          refine ⟨9579673423730941064067719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25545795796615842837513917 9579673423730941064067719)
          ·
            refine ⟨14369510135596411596101579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9579673423730941064067719 14369510135596411596101579)
            ·
              refine ⟨21554265203394617394152369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14369510135596411596101579 21554265203394617394152369)
              ·
                refine ⟨16165698902545963045614277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21554265203394617394152369 16165698902545963045614277)
                ·
                  refine ⟨3031068544227368071052677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16165698902545963045614277 3031068544227368071052677)
                  ·
                    refine ⟨568325352042631513322377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3031068544227368071052677 568325352042631513322377)
                    ·
                      rfl

theorem cell23_3320429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_3320429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320429 prefixEnd_3320429 := by exact prefixLift 3320429
  have htrace : WordTrace (prefixWord ++ tailWord_3320429) baseStart_3320429 baseEnd_3320429 := by
    simpa [prefixWord, tailWord_3320429, baseEnd_3320429] using wordTrace_append hprefix tailTrace_3320429
  have hstable : (prefixWord ++ tailWord_3320429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320429).length < 2 ^ (prefixWord ++ tailWord_3320429).sum := by decide
  have hdescent : baseEnd_3320429 < baseStart_3320429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320430 : List Nat := [4, 1, 2, 2, 2, 3, 1, 3, 1, 1, 3]
def baseStart_3320430 : Nat := 118140960795 + 3320430 * 2 ^ 59
def prefixEnd_3320430 : Nat := 4983230072969 + 3 ^ 40 * 3320430 * 2
def baseEnd_3320430 : Nat := 1704976569608549036054627

theorem tailTrace_3320430 : CollatzResearch.WordTrace tailWord_3320430 prefixEnd_3320430 1704976569608549036054627 := by
  unfold tailWord_3320430
  simp only [CollatzResearch.WordTrace]
  refine ⟨15138253920082083642652843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80737354240437779427481829 15138253920082083642652843)
  ·
    refine ⟨22707380880123125463979265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15138253920082083642652843 22707380880123125463979265)
    ·
      refine ⟨17030535660092344097984449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22707380880123125463979265 17030535660092344097984449)
      ·
        refine ⟨12772901745069258073488337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17030535660092344097984449 12772901745069258073488337)
        ·
          refine ⟨9579676308801943555116253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12772901745069258073488337 9579676308801943555116253)
          ·
            refine ⟨3592378615800728833168595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9579676308801943555116253 3592378615800728833168595)
            ·
              refine ⟨5388567923701093249752893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592378615800728833168595 5388567923701093249752893)
              ·
                refine ⟨2020712971387909968657335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5388567923701093249752893 2020712971387909968657335)
                ·
                  refine ⟨3031069457081864952986003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2020712971387909968657335 3031069457081864952986003)
                  ·
                    refine ⟨4546604185622797429479005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3031069457081864952986003 4546604185622797429479005)
                    ·
                      refine ⟨1704976569608549036054627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4546604185622797429479005 1704976569608549036054627)
                      ·
                        rfl

theorem cell23_3320430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_3320430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320430 prefixEnd_3320430 := by exact prefixLift 3320430
  have htrace : WordTrace (prefixWord ++ tailWord_3320430) baseStart_3320430 baseEnd_3320430 := by
    simpa [prefixWord, tailWord_3320430, baseEnd_3320430] using wordTrace_append hprefix tailTrace_3320430
  have hstable : (prefixWord ++ tailWord_3320430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320430).length < 2 ^ (prefixWord ++ tailWord_3320430).sum := by decide
  have hdescent : baseEnd_3320430 < baseStart_3320430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320439 : List Nat := [1, 1, 3, 1, 1, 3, 4, 3, 1, 2, 3]
def baseStart_3320439 : Nat := 118140960795 + 3320439 * 2 ^ 59
def prefixEnd_3320439 : Nat := 4983230072969 + 3 ^ 40 * 3320439 * 2
def baseEnd_3320439 : Nat := 1704981190934439500842085

theorem tailTrace_3320439 : CollatzResearch.WordTrace tailWord_3320439 prefixEnd_3320439 1704981190934439500842085 := by
  unfold tailWord_3320439
  simp only [CollatzResearch.WordTrace]
  refine ⟨121106359617624063678300371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80737573078416042452200247 121106359617624063678300371)
  ·
    refine ⟨181659539426436095517450557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121106359617624063678300371 181659539426436095517450557)
    ·
      refine ⟨68122327284913535819043959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181659539426436095517450557 68122327284913535819043959)
      ·
        refine ⟨102183490927370303728565939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68122327284913535819043959 102183490927370303728565939)
        ·
          refine ⟨153275236391055455592848909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102183490927370303728565939 153275236391055455592848909)
          ·
            refine ⟨57478213646645795847318341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153275236391055455592848909 57478213646645795847318341)
            ·
              refine ⟨10777165058746086721372189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57478213646645795847318341 10777165058746086721372189)
              ·
                refine ⟨4041436897029782520514571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10777165058746086721372189 4041436897029782520514571)
                ·
                  refine ⟨6062155345544673780771857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041436897029782520514571 6062155345544673780771857)
                  ·
                    refine ⟨4546616509158505335578893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6062155345544673780771857 4546616509158505335578893)
                    ·
                      refine ⟨1704981190934439500842085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4546616509158505335578893 1704981190934439500842085)
                      ·
                        rfl

theorem cell23_3320439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_3320439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320439 prefixEnd_3320439 := by exact prefixLift 3320439
  have htrace : WordTrace (prefixWord ++ tailWord_3320439) baseStart_3320439 baseEnd_3320439 := by
    simpa [prefixWord, tailWord_3320439, baseEnd_3320439] using wordTrace_append hprefix tailTrace_3320439
  have hstable : (prefixWord ++ tailWord_3320439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320439).length < 2 ^ (prefixWord ++ tailWord_3320439).sum := by decide
  have hdescent : baseEnd_3320439 < baseStart_3320439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320453 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 3, 2, 2]
def baseStart_3320453 : Nat := 118140960795 + 3320453 * 2 ^ 59
def prefixEnd_3320453 : Nat := 4983230072969 + 3 ^ 40 * 3320453 * 2
def baseEnd_3320453 : Nat := 1704988379663602446067021

theorem tailTrace_3320453 : CollatzResearch.WordTrace tailWord_3320453 prefixEnd_3320453 1704988379663602446067021 := by
  unfold tailWord_3320453
  simp only [CollatzResearch.WordTrace]
  refine ⟨121106870239573344069310013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80737913493048896046206675 121106870239573344069310013)
  ·
    refine ⟨45415076339840004025991255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121106870239573344069310013 45415076339840004025991255)
    ·
      refine ⟨68122614509760006038986883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45415076339840004025991255 68122614509760006038986883)
      ·
        refine ⟨102183921764640009058480325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68122614509760006038986883 102183921764640009058480325)
        ·
          refine ⟨19159485330870001698465061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102183921764640009058480325 19159485330870001698465061)
          ·
            refine ⟨3592403499538125318462199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19159485330870001698465061 3592403499538125318462199)
            ·
              refine ⟨5388605249307187977693299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592403499538125318462199 5388605249307187977693299)
              ·
                refine ⟨8082907873960781966539949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5388605249307187977693299 8082907873960781966539949)
                ·
                  refine ⟨3031090452735293237452481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8082907873960781966539949 3031090452735293237452481)
                  ·
                    refine ⟨2273317839551469928089361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3031090452735293237452481 2273317839551469928089361)
                    ·
                      refine ⟨1704988379663602446067021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2273317839551469928089361 1704988379663602446067021)
                      ·
                        rfl

theorem cell23_3320453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 2, 2].length) (baseStart_3320453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320453 prefixEnd_3320453 := by exact prefixLift 3320453
  have htrace : WordTrace (prefixWord ++ tailWord_3320453) baseStart_3320453 baseEnd_3320453 := by
    simpa [prefixWord, tailWord_3320453, baseEnd_3320453] using wordTrace_append hprefix tailTrace_3320453
  have hstable : (prefixWord ++ tailWord_3320453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320453).length < 2 ^ (prefixWord ++ tailWord_3320453).sum := by decide
  have hdescent : baseEnd_3320453 < baseStart_3320453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320462 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3320462 : Nat := 118140960795 + 3320462 * 2 ^ 59
def prefixEnd_3320462 : Nat := 4983230072969 + 3 ^ 40 * 3320462 * 2
def baseEnd_3320462 : Nat := 1704993000989492910854479

theorem tailTrace_3320462 : CollatzResearch.WordTrace tailWord_3320462 prefixEnd_3320462 1704993000989492910854479 := by
  unfold tailWord_3320462
  simp only [CollatzResearch.WordTrace]
  refine ⟨15138399812067592325798455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80738132331027159070925093 15138399812067592325798455)
  ·
    refine ⟨22707599718101388488697683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15138399812067592325798455 22707599718101388488697683)
    ·
      refine ⟨34061399577152082733046525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22707599718101388488697683 34061399577152082733046525)
      ·
        refine ⟨12773024841432031024892447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34061399577152082733046525 12773024841432031024892447)
        ·
          refine ⟨19159537262148046537338671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12773024841432031024892447 19159537262148046537338671)
          ·
            refine ⟨28739305893222069806008007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19159537262148046537338671 28739305893222069806008007)
            ·
              refine ⟨43108958839833104709012011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28739305893222069806008007 43108958839833104709012011)
              ·
                refine ⟨64663438259749657063518017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43108958839833104709012011 64663438259749657063518017)
                ·
                  refine ⟨48497578694812242797638513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64663438259749657063518017 48497578694812242797638513)
                  ·
                    refine ⟨36373184021109182098228885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48497578694812242797638513 36373184021109182098228885)
                    ·
                      refine ⟨1704993000989492910854479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36373184021109182098228885 1704993000989492910854479)
                      ·
                        rfl

theorem cell23_3320462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3320462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320462 prefixEnd_3320462 := by exact prefixLift 3320462
  have htrace : WordTrace (prefixWord ++ tailWord_3320462) baseStart_3320462 baseEnd_3320462 := by
    simpa [prefixWord, tailWord_3320462, baseEnd_3320462] using wordTrace_append hprefix tailTrace_3320462
  have hstable : (prefixWord ++ tailWord_3320462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320462).length < 2 ^ (prefixWord ++ tailWord_3320462).sum := by decide
  have hdescent : baseEnd_3320462 < baseStart_3320462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320490 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_3320490 : Nat := 118140960795 + 3320490 * 2 ^ 59
def prefixEnd_3320490 : Nat := 4983230072969 + 3 ^ 40 * 3320490 * 2
def baseEnd_3320490 : Nat := 1705007378447818801304351

theorem tailTrace_3320490 : CollatzResearch.WordTrace tailWord_3320490 prefixEnd_3320490 1705007378447818801304351 := by
  unfold tailWord_3320490
  simp only [CollatzResearch.WordTrace]
  refine ⟨30277054935109824847101731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80738813160292866258937949 30277054935109824847101731)
  ·
    refine ⟨45415582402664737270652597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30277054935109824847101731 45415582402664737270652597)
    ·
      refine ⟨4257710850249819119123681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45415582402664737270652597 4257710850249819119123681)
      ·
        refine ⟨3193283137687364339342761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4257710850249819119123681 3193283137687364339342761)
        ·
          refine ⟨2394962353265523254507071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3193283137687364339342761 2394962353265523254507071)
          ·
            refine ⟨3592443529898284881760607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394962353265523254507071 3592443529898284881760607)
            ·
              refine ⟨5388665294847427322640911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592443529898284881760607 5388665294847427322640911)
              ·
                refine ⟨8082997942271140983961367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5388665294847427322640911 8082997942271140983961367)
                ·
                  refine ⟨12124496913406711475942051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8082997942271140983961367 12124496913406711475942051)
                  ·
                    refine ⟨18186745370110067213913077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12124496913406711475942051 18186745370110067213913077)
                    ·
                      refine ⟨1705007378447818801304351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18186745370110067213913077 1705007378447818801304351)
                      ·
                        rfl

theorem cell23_3320490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_3320490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320490 prefixEnd_3320490 := by exact prefixLift 3320490
  have htrace : WordTrace (prefixWord ++ tailWord_3320490) baseStart_3320490 baseEnd_3320490 := by
    simpa [prefixWord, tailWord_3320490, baseEnd_3320490] using wordTrace_append hprefix tailTrace_3320490
  have hstable : (prefixWord ++ tailWord_3320490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320490).length < 2 ^ (prefixWord ++ tailWord_3320490).sum := by decide
  have hdescent : baseEnd_3320490 < baseStart_3320490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320503 : List Nat := [1, 1, 3, 1, 6, 1, 2, 2, 2, 1, 3]
def baseStart_3320503 : Nat := 118140960795 + 3320503 * 2 ^ 59
def prefixEnd_3320503 : Nat := 4983230072969 + 3 ^ 40 * 3320503 * 2
def baseEnd_3320503 : Nat := 1705014053696327250441791

theorem tailTrace_3320503 : CollatzResearch.WordTrace tailWord_3320503 prefixEnd_3320503 1705014053696327250441791 := by
  unfold tailWord_3320503
  simp only [CollatzResearch.WordTrace]
  refine ⟨121108693889392202608630163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80739129259594801739086775 121108693889392202608630163)
  ·
    refine ⟨181663040834088303912945245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121108693889392202608630163 181663040834088303912945245)
    ·
      refine ⟨68123640312783113967354467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181663040834088303912945245 68123640312783113967354467)
      ·
        refine ⟨102185460469174670951031701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68123640312783113967354467 102185460469174670951031701)
        ·
          refine ⟨4789943459492562700829611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102185460469174670951031701 4789943459492562700829611)
          ·
            refine ⟨7184915189238844051244417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789943459492562700829611 7184915189238844051244417)
            ·
              refine ⟨5388686391929133038433313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7184915189238844051244417 5388686391929133038433313)
              ·
                refine ⟨4041514793946849778824985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5388686391929133038433313 4041514793946849778824985)
                ·
                  refine ⟨3031136095460137334118739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4041514793946849778824985 3031136095460137334118739)
                  ·
                    refine ⟨4546704143190206001178109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3031136095460137334118739 4546704143190206001178109)
                    ·
                      refine ⟨1705014053696327250441791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4546704143190206001178109 1705014053696327250441791)
                      ·
                        rfl

theorem cell23_3320503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_3320503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320503 prefixEnd_3320503 := by exact prefixLift 3320503
  have htrace : WordTrace (prefixWord ++ tailWord_3320503) baseStart_3320503 baseEnd_3320503 := by
    simpa [prefixWord, tailWord_3320503, baseEnd_3320503] using wordTrace_append hprefix tailTrace_3320503
  have hstable : (prefixWord ++ tailWord_3320503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320503).length < 2 ^ (prefixWord ++ tailWord_3320503).sum := by decide
  have hdescent : baseEnd_3320503 < baseStart_3320503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320526 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2]
def baseStart_3320526 : Nat := 118140960795 + 3320526 * 2 ^ 59
def prefixEnd_3320526 : Nat := 4983230072969 + 3 ^ 40 * 3320526 * 2
def baseEnd_3320526 : Nat := 1705025863751380660454185

theorem tailTrace_3320526 : CollatzResearch.WordTrace tailWord_3320526 prefixEnd_3320526 1705025863751380660454185 := by
  unfold tailWord_3320526
  simp only [CollatzResearch.WordTrace]
  refine ⟨15138691596038609692089679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80739688512205918357811621 15138691596038609692089679)
  ·
    refine ⟨22708037394057914538134519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15138691596038609692089679 22708037394057914538134519)
    ·
      refine ⟨34062056091086871807201779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22708037394057914538134519 34062056091086871807201779)
      ·
        refine ⟨51093084136630307710802669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34062056091086871807201779 51093084136630307710802669)
        ·
          refine ⟨19159906551236365391551001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51093084136630307710802669 19159906551236365391551001)
          ·
            refine ⟨14369929913427274043663251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19159906551236365391551001 14369929913427274043663251)
            ·
              refine ⟨21554894870140911065494877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14369929913427274043663251 21554894870140911065494877)
              ·
                refine ⟨8083085576302841649560579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21554894870140911065494877 8083085576302841649560579)
                ·
                  refine ⟨12124628364454262474340869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8083085576302841649560579 12124628364454262474340869)
                  ·
                    refine ⟨2273367818335174213938913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12124628364454262474340869 2273367818335174213938913)
                    ·
                      refine ⟨1705025863751380660454185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2273367818335174213938913 1705025863751380660454185)
                      ·
                        rfl

theorem cell23_3320526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_3320526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320526 prefixEnd_3320526 := by exact prefixLift 3320526
  have htrace : WordTrace (prefixWord ++ tailWord_3320526) baseStart_3320526 baseEnd_3320526 := by
    simpa [prefixWord, tailWord_3320526, baseEnd_3320526] using wordTrace_append hprefix tailTrace_3320526
  have hstable : (prefixWord ++ tailWord_3320526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320526).length < 2 ^ (prefixWord ++ tailWord_3320526).sum := by decide
  have hdescent : baseEnd_3320526 < baseStart_3320526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320559 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 3]
def baseStart_3320559 : Nat := 118140960795 + 3320559 * 2 ^ 59
def prefixEnd_3320559 : Nat := 4983230072969 + 3 ^ 40 * 3320559 * 2
def baseEnd_3320559 : Nat := 1705042808612979031341533

theorem tailTrace_3320559 : CollatzResearch.WordTrace tailWord_3320559 prefixEnd_3320559 1705042808612979031341533 := by
  unfold tailWord_3320559
  simp only [CollatzResearch.WordTrace]
  refine ⟨121110736377189324172668731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80740490918126216115112487 121110736377189324172668731)
  ·
    refine ⟨181666104565783986259003097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121110736377189324172668731 181666104565783986259003097)
    ·
      refine ⟨136249578424337989694252323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181666104565783986259003097 136249578424337989694252323)
      ·
        refine ⟨204374367636506984541378485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136249578424337989694252323 204374367636506984541378485)
        ·
          refine ⟨19160096965922529800754233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204374367636506984541378485 19160096965922529800754233)
          ·
            refine ⟨14370072724441897350565675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19160096965922529800754233 14370072724441897350565675)
            ·
              refine ⟨21555109086662846025848513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14370072724441897350565675 21555109086662846025848513)
              ·
                refine ⟨16166331814997134519386385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21555109086662846025848513 16166331814997134519386385)
                ·
                  refine ⟨12124748861247850889539789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16166331814997134519386385 12124748861247850889539789)
                  ·
                    refine ⟨4546780822967944083577421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12124748861247850889539789 4546780822967944083577421)
                    ·
                      refine ⟨1705042808612979031341533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4546780822967944083577421 1705042808612979031341533)
                      ·
                        rfl

theorem cell23_3320559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 3].length) (baseStart_3320559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320559 prefixEnd_3320559 := by exact prefixLift 3320559
  have htrace : WordTrace (prefixWord ++ tailWord_3320559) baseStart_3320559 baseEnd_3320559 := by
    simpa [prefixWord, tailWord_3320559, baseEnd_3320559] using wordTrace_append hprefix tailTrace_3320559
  have hstable : (prefixWord ++ tailWord_3320559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320559).length < 2 ^ (prefixWord ++ tailWord_3320559).sum := by decide
  have hdescent : baseEnd_3320559 < baseStart_3320559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320566 : List Nat := [5, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_3320566 : Nat := 118140960795 + 3320566 * 2 ^ 59
def prefixEnd_3320566 : Nat := 4983230072969 + 3 ^ 40 * 3320566 * 2
def baseEnd_3320566 : Nat := 189449600330840055994889

theorem tailTrace_3320566 : CollatzResearch.WordTrace tailWord_3320566 prefixEnd_3320566 189449600330840055994889 := by
  unfold tailWord_3320566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7569436980510247773010847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80740661125442642912115701 7569436980510247773010847)
  ·
    refine ⟨11354155470765371659516271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7569436980510247773010847 11354155470765371659516271)
    ·
      refine ⟨17031233206148057489274407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11354155470765371659516271 17031233206148057489274407)
      ·
        refine ⟨25546849809222086233911611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17031233206148057489274407 25546849809222086233911611)
        ·
          refine ⟨38320274713833129350867417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25546849809222086233911611 38320274713833129350867417)
          ·
            refine ⟨28740206035374847013150563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38320274713833129350867417 28740206035374847013150563)
            ·
              refine ⟨43110309053062270519725845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28740206035374847013150563 43110309053062270519725845)
              ·
                refine ⟨2020795736862293930612149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43110309053062270519725845 2020795736862293930612149)
                ·
                  refine ⟨189449600330840055994889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2020795736862293930612149 189449600330840055994889)
                  ·
                    rfl

theorem cell23_3320566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_3320566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320566 prefixEnd_3320566 := by exact prefixLift 3320566
  have htrace : WordTrace (prefixWord ++ tailWord_3320566) baseStart_3320566 baseEnd_3320566 := by
    simpa [prefixWord, tailWord_3320566, baseEnd_3320566] using wordTrace_append hprefix tailTrace_3320566
  have hstable : (prefixWord ++ tailWord_3320566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320566).length < 2 ^ (prefixWord ++ tailWord_3320566).sum := by decide
  have hdescent : baseEnd_3320566 < baseStart_3320566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320569 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 1, 7, 2]
def baseStart_3320569 : Nat := 118140960795 + 3320569 * 2 ^ 59
def prefixEnd_3320569 : Nat := 4983230072969 + 3 ^ 40 * 3320569 * 2
def baseEnd_3320569 : Nat := 1705047943419523992216487

theorem tailTrace_3320569 : CollatzResearch.WordTrace tailWord_3320569 prefixEnd_3320569 1705047943419523992216487 := by
  unfold tailWord_3320569
  simp only [CollatzResearch.WordTrace]
  refine ⟨121111101107153095880532761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80740734071435397253688507 121111101107153095880532761)
  ·
    refine ⟨90833325830364821910399571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121111101107153095880532761 90833325830364821910399571)
    ·
      refine ⟨136249988745547232865599357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90833325830364821910399571 136249988745547232865599357)
      ·
        refine ⟨51093745779580212324599759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136249988745547232865599357 51093745779580212324599759)
        ·
          refine ⟨76640618669370318486899639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51093745779580212324599759 76640618669370318486899639)
          ·
            refine ⟨114960928004055477730349459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76640618669370318486899639 114960928004055477730349459)
            ·
              refine ⟨172441392006083216595524189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114960928004055477730349459 172441392006083216595524189)
              ·
                refine ⟨64665522002281206223321571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172441392006083216595524189 64665522002281206223321571)
                ·
                  refine ⟨96998283003421809334982357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64665522002281206223321571 96998283003421809334982357)
                  ·
                    refine ⟨2273397257892698656288649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 96998283003421809334982357 2273397257892698656288649)
                    ·
                      refine ⟨1705047943419523992216487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2273397257892698656288649 1705047943419523992216487)
                      ·
                        rfl

theorem cell23_3320569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_3320569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320569 prefixEnd_3320569 := by exact prefixLift 3320569
  have htrace : WordTrace (prefixWord ++ tailWord_3320569) baseStart_3320569 baseEnd_3320569 := by
    simpa [prefixWord, tailWord_3320569, baseEnd_3320569] using wordTrace_append hprefix tailTrace_3320569
  have hstable : (prefixWord ++ tailWord_3320569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320569).length < 2 ^ (prefixWord ++ tailWord_3320569).sum := by decide
  have hdescent : baseEnd_3320569 < baseStart_3320569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320616 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_3320616 : Nat := 118140960795 + 3320616 * 2 ^ 59
def prefixEnd_3320616 : Nat := 4983230072969 + 3 ^ 40 * 3320616 * 2
def baseEnd_3320616 : Nat := 1705072077010285308328771

theorem tailTrace_3320616 : CollatzResearch.WordTrace tailWord_3320616 prefixEnd_3320616 1705072077010285308328771 := by
  unfold tailWord_3320616
  simp only [CollatzResearch.WordTrace]
  refine ⟨60556407668991411453746851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80741876891988548604995801 60556407668991411453746851)
  ·
    refine ⟨90834611503487117180620277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60556407668991411453746851 90834611503487117180620277)
    ·
      refine ⟨8515744828451917235683151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90834611503487117180620277 8515744828451917235683151)
      ·
        refine ⟨12773617242677875853524727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8515744828451917235683151 12773617242677875853524727)
        ·
          refine ⟨19160425864016813780287091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12773617242677875853524727 19160425864016813780287091)
          ·
            refine ⟨28740638796025220670430637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19160425864016813780287091 28740638796025220670430637)
            ·
              refine ⟨10777739548509457751411489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28740638796025220670430637 10777739548509457751411489)
              ·
                refine ⟨8083304661382093313558617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10777739548509457751411489 8083304661382093313558617)
                ·
                  refine ⟨6062478496036569985168963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8083304661382093313558617 6062478496036569985168963)
                  ·
                    refine ⟨9093717744054854977753445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6062478496036569985168963 9093717744054854977753445)
                    ·
                      refine ⟨1705072077010285308328771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9093717744054854977753445 1705072077010285308328771)
                      ·
                        rfl

theorem cell23_3320616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_3320616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320616 prefixEnd_3320616 := by exact prefixLift 3320616
  have htrace : WordTrace (prefixWord ++ tailWord_3320616) baseStart_3320616 baseEnd_3320616 := by
    simpa [prefixWord, tailWord_3320616, baseEnd_3320616] using wordTrace_append hprefix tailTrace_3320616
  have hstable : (prefixWord ++ tailWord_3320616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320616).length < 2 ^ (prefixWord ++ tailWord_3320616).sum := by decide
  have hdescent : baseEnd_3320616 < baseStart_3320616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320619 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 3]
def baseStart_3320619 : Nat := 118140960795 + 3320619 * 2 ^ 59
def prefixEnd_3320619 : Nat := 4983230072969 + 3 ^ 40 * 3320619 * 2
def baseEnd_3320619 : Nat := 1705073617452248796591257

theorem tailTrace_3320619 : CollatzResearch.WordTrace tailWord_3320619 prefixEnd_3320619 1705073617452248796591257 := by
  unfold tailWord_3320619
  simp only [CollatzResearch.WordTrace]
  refine ⟨121112924756971954419852911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80741949837981302946568607 121112924756971954419852911)
  ·
    refine ⟨181669387135457931629779367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121112924756971954419852911 181669387135457931629779367)
    ·
      refine ⟨272504080703186897444669051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181669387135457931629779367 272504080703186897444669051)
      ·
        refine ⟨408756121054780346167003577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272504080703186897444669051 408756121054780346167003577)
        ·
          refine ⟨306567090791085259625252683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408756121054780346167003577 306567090791085259625252683)
          ·
            refine ⟨459850636186627889437879025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306567090791085259625252683 459850636186627889437879025)
            ·
              refine ⟨344887977139970917078409269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459850636186627889437879025 344887977139970917078409269)
              ·
                refine ⟨32333247856872273476100869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 344887977139970917078409269 32333247856872273476100869)
                ·
                  refine ⟨6062483973163551276768913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32333247856872273476100869 6062483973163551276768913)
                  ·
                    refine ⟨4546862979872663457576685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6062483973163551276768913 4546862979872663457576685)
                    ·
                      refine ⟨1705073617452248796591257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4546862979872663457576685 1705073617452248796591257)
                      ·
                        rfl

theorem cell23_3320619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 3].length) (baseStart_3320619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320619 prefixEnd_3320619 := by exact prefixLift 3320619
  have htrace : WordTrace (prefixWord ++ tailWord_3320619) baseStart_3320619 baseEnd_3320619 := by
    simpa [prefixWord, tailWord_3320619, baseEnd_3320619] using wordTrace_append hprefix tailTrace_3320619
  have hstable : (prefixWord ++ tailWord_3320619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320619).length < 2 ^ (prefixWord ++ tailWord_3320619).sum := by decide
  have hdescent : baseEnd_3320619 < baseStart_3320619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320699 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 1, 6]
def baseStart_3320699 : Nat := 118140960795 + 3320699 * 2 ^ 59
def prefixEnd_3320699 : Nat := 4983230072969 + 3 ^ 40 * 3320699 * 2
def baseEnd_3320699 : Nat := 568371565301536161196963

theorem tailTrace_3320699 : CollatzResearch.WordTrace tailWord_3320699 prefixEnd_3320699 568371565301536161196963 := by
  unfold tailWord_3320699
  simp only [CollatzResearch.WordTrace]
  refine ⟨121115842596682128082765151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80743895064454752055176767 121115842596682128082765151)
  ·
    refine ⟨181673763895023192124147727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121115842596682128082765151 181673763895023192124147727)
    ·
      refine ⟨272510645842534788186221591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181673763895023192124147727 272510645842534788186221591)
      ·
        refine ⟨408765968763802182279332387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272510645842534788186221591 408765968763802182279332387)
        ·
          refine ⟨613148953145703273418998581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408765968763802182279332387 613148953145703273418998581)
          ·
            refine ⟨57482714357409681883031117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 613148953145703273418998581 57482714357409681883031117)
            ·
              refine ⟨21556017884028630706136669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57482714357409681883031117 21556017884028630706136669)
              ·
                refine ⟨8083506706510736514801251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21556017884028630706136669 8083506706510736514801251)
                ·
                  refine ⟨12125260059766104772201877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8083506706510736514801251 12125260059766104772201877)
                  ·
                    refine ⟨568371565301536161196963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12125260059766104772201877 568371565301536161196963)
                    ·
                      rfl

theorem cell23_3320699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 6].length) (baseStart_3320699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320699 prefixEnd_3320699 := by exact prefixLift 3320699
  have htrace : WordTrace (prefixWord ++ tailWord_3320699) baseStart_3320699 baseEnd_3320699 := by
    simpa [prefixWord, tailWord_3320699, baseEnd_3320699] using wordTrace_append hprefix tailTrace_3320699
  have hstable : (prefixWord ++ tailWord_3320699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320699).length < 2 ^ (prefixWord ++ tailWord_3320699).sum := by decide
  have hdescent : baseEnd_3320699 < baseStart_3320699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320740 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 3, 2, 2]
def baseStart_3320740 : Nat := 118140960795 + 3320740 * 2 ^ 59
def prefixEnd_3320740 : Nat := 4983230072969 + 3 ^ 40 * 3320740 * 2
def baseEnd_3320740 : Nat := 1705135748611442823178201

theorem tailTrace_3320740 : CollatzResearch.WordTrace tailWord_3320740 prefixEnd_3320740 1705135748611442823178201 := by
  unfold tailWord_3320740
  simp only [CollatzResearch.WordTrace]
  refine ⟨60558668994766796042503837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80744891993022394723338449 60558668994766796042503837)
  ·
    refine ⟨22709500873037548515938939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60558668994766796042503837 22709500873037548515938939)
    ·
      refine ⟨34064251309556322773908409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22709500873037548515938939 34064251309556322773908409)
      ·
        refine ⟨25548188482167242080431307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34064251309556322773908409 25548188482167242080431307)
        ·
          refine ⟨38322282723250863120646961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25548188482167242080431307 38322282723250863120646961)
          ·
            refine ⟨28741712042438147340485221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38322282723250863120646961 28741712042438147340485221)
            ·
              refine ⟨5389071007957152626340979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28741712042438147340485221 5389071007957152626340979)
              ·
                refine ⟨8083606511935728939511469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5389071007957152626340979 8083606511935728939511469)
                ·
                  refine ⟨3031352441975898352316801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8083606511935728939511469 3031352441975898352316801)
                  ·
                    refine ⟨2273514331481923764237601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3031352441975898352316801 2273514331481923764237601)
                    ·
                      refine ⟨1705135748611442823178201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2273514331481923764237601 1705135748611442823178201)
                      ·
                        rfl

theorem cell23_3320740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_3320740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320740 prefixEnd_3320740 := by exact prefixLift 3320740
  have htrace : WordTrace (prefixWord ++ tailWord_3320740) baseStart_3320740 baseEnd_3320740 := by
    simpa [prefixWord, tailWord_3320740, baseEnd_3320740] using wordTrace_append hprefix tailTrace_3320740
  have hstable : (prefixWord ++ tailWord_3320740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320740).length < 2 ^ (prefixWord ++ tailWord_3320740).sum := by decide
  have hdescent : baseEnd_3320740 < baseStart_3320740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320743 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_3320743 : Nat := 118140960795 + 3320743 * 2 ^ 59
def prefixEnd_3320743 : Nat := 4983230072969 + 3 ^ 40 * 3320743 * 2
def baseEnd_3320743 : Nat := 1705137289053406311440687

theorem tailTrace_3320743 : CollatzResearch.WordTrace tailWord_3320743 prefixEnd_3320743 1705137289053406311440687 := by
  unfold tailWord_3320743
  simp only [CollatzResearch.WordTrace]
  refine ⟨121117447408522723597366883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80744964939015149064911255 121117447408522723597366883)
  ·
    refine ⟨181676171112784085396050325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121117447408522723597366883 181676171112784085396050325)
    ·
      refine ⟨8516070520911754002939859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 181676171112784085396050325 8516070520911754002939859)
      ·
        refine ⟨12774105781367631004409789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8516070520911754002939859 12774105781367631004409789)
        ·
          refine ⟨4790289668012861626653671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12774105781367631004409789 4790289668012861626653671)
          ·
            refine ⟨7185434502019292439980507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4790289668012861626653671 7185434502019292439980507)
            ·
              refine ⟨10778151753028938659970761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7185434502019292439980507 10778151753028938659970761)
              ·
                refine ⟨8083613814771703994978071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10778151753028938659970761 8083613814771703994978071)
                ·
                  refine ⟨12125420722157555992467107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8083613814771703994978071 12125420722157555992467107)
                  ·
                    refine ⟨18188131083236333988700661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12125420722157555992467107 18188131083236333988700661)
                    ·
                      refine ⟨1705137289053406311440687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18188131083236333988700661 1705137289053406311440687)
                      ·
                        rfl

theorem cell23_3320743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_3320743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320743 prefixEnd_3320743 := by exact prefixLift 3320743
  have htrace : WordTrace (prefixWord ++ tailWord_3320743) baseStart_3320743 baseEnd_3320743 := by
    simpa [prefixWord, tailWord_3320743, baseEnd_3320743] using wordTrace_append hprefix tailTrace_3320743
  have hstable : (prefixWord ++ tailWord_3320743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320743).length < 2 ^ (prefixWord ++ tailWord_3320743).sum := by decide
  have hdescent : baseEnd_3320743 < baseStart_3320743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320759 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 2, 7]
def baseStart_3320759 : Nat := 118140960795 + 3320759 * 2 ^ 59
def prefixEnd_3320759 : Nat := 4983230072969 + 3 ^ 40 * 3320759 * 2
def baseEnd_3320759 : Nat := 568381834914626082946871

theorem tailTrace_3320759 : CollatzResearch.WordTrace tailWord_3320759 prefixEnd_3320759 568381834914626082946871 := by
  unfold tailWord_3320759
  simp only [CollatzResearch.WordTrace]
  refine ⟨121118030976464758329949331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80745353984309838886632887 121118030976464758329949331)
  ·
    refine ⟨181677046464697137494923997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121118030976464758329949331 181677046464697137494923997)
    ·
      refine ⟨68128892424261426560596499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181677046464697137494923997 68128892424261426560596499)
      ·
        refine ⟨102193338636392139840894749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68128892424261426560596499 102193338636392139840894749)
        ·
          refine ⟨38322501988647052440335531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102193338636392139840894749 38322501988647052440335531)
          ·
            refine ⟨57483752982970578660503297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38322501988647052440335531 57483752982970578660503297)
            ·
              refine ⟨43112814737227933995377473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57483752982970578660503297 43112814737227933995377473)
              ·
                refine ⟨32334611052920950496533105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43112814737227933995377473 32334611052920950496533105)
                ·
                  refine ⟨24250958289690712872399829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32334611052920950496533105 24250958289690712872399829)
                  ·
                    refine ⟨568381834914626082946871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24250958289690712872399829 568381834914626082946871)
                    ·
                      rfl

theorem cell23_3320759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_3320759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320759 prefixEnd_3320759 := by exact prefixLift 3320759
  have htrace : WordTrace (prefixWord ++ tailWord_3320759) baseStart_3320759 baseEnd_3320759 := by
    simpa [prefixWord, tailWord_3320759, baseEnd_3320759] using wordTrace_append hprefix tailTrace_3320759
  have hstable : (prefixWord ++ tailWord_3320759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320759).length < 2 ^ (prefixWord ++ tailWord_3320759).sum := by decide
  have hdescent : baseEnd_3320759 < baseStart_3320759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320807 : List Nat := [1, 1, 5, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_3320807 : Nat := 118140960795 + 3320807 * 2 ^ 59
def prefixEnd_3320807 : Nat := 4983230072969 + 3 ^ 40 * 3320807 * 2
def baseEnd_3320807 : Nat := 1705170151815294061040393

theorem tailTrace_3320807 : CollatzResearch.WordTrace tailWord_3320807 prefixEnd_3320807 1705170151815294061040393 := by
  unfold tailWord_3320807
  simp only [CollatzResearch.WordTrace]
  refine ⟨121119781680290862527696675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80746521120193908351797783 121119781680290862527696675)
  ·
    refine ⟨181679672520436293791545013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121119781680290862527696675 181679672520436293791545013)
    ·
      refine ⟨17032469298790902542957345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181679672520436293791545013 17032469298790902542957345)
      ·
        refine ⟨12774351974093176907218009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17032469298790902542957345 12774351974093176907218009)
        ·
          refine ⟨9580763980569882680413507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12774351974093176907218009 9580763980569882680413507)
          ·
            refine ⟨14371145970854824020620261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9580763980569882680413507 14371145970854824020620261)
            ·
              refine ⟨2694589869535279503866299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14371145970854824020620261 2694589869535279503866299)
              ·
                refine ⟨4041884804302919255799449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2694589869535279503866299 4041884804302919255799449)
                ·
                  refine ⟨3031413603227189441849587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4041884804302919255799449 3031413603227189441849587)
                  ·
                    refine ⟨4547120404840784162774381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3031413603227189441849587 4547120404840784162774381)
                    ·
                      refine ⟨1705170151815294061040393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4547120404840784162774381 1705170151815294061040393)
                      ·
                        rfl

theorem cell23_3320807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_3320807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320807 prefixEnd_3320807 := by exact prefixLift 3320807
  have htrace : WordTrace (prefixWord ++ tailWord_3320807) baseStart_3320807 baseEnd_3320807 := by
    simpa [prefixWord, tailWord_3320807, baseEnd_3320807] using wordTrace_append hprefix tailTrace_3320807
  have hstable : (prefixWord ++ tailWord_3320807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320807).length < 2 ^ (prefixWord ++ tailWord_3320807).sum := by decide
  have hdescent : baseEnd_3320807 < baseStart_3320807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320809 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 6]
def baseStart_3320809 : Nat := 118140960795 + 3320809 * 2 ^ 59
def prefixEnd_3320809 : Nat := 4983230072969 + 3 ^ 40 * 3320809 * 2
def baseEnd_3320809 : Nat := 1705171178776603053215383

theorem tailTrace_3320809 : CollatzResearch.WordTrace tailWord_3320809 prefixEnd_3320809 1705171178776603053215383 := by
  unfold tailWord_3320809
  simp only [CollatzResearch.WordTrace]
  refine ⟨121119854626283616869269481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80746569750855744579512987 121119854626283616869269481)
  ·
    refine ⟨90839890969712712651952111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121119854626283616869269481 90839890969712712651952111)
    ·
      refine ⟨136259836454569068977928167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90839890969712712651952111 136259836454569068977928167)
      ·
        refine ⟨204389754681853603466892251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136259836454569068977928167 204389754681853603466892251)
        ·
          refine ⟨306584632022780405200338377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204389754681853603466892251 306584632022780405200338377)
          ·
            refine ⟨229938474017085303900253783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306584632022780405200338377 229938474017085303900253783)
            ·
              refine ⟨344907711025627955850380675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229938474017085303900253783 344907711025627955850380675)
              ·
                refine ⟨517361566538441933775571013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344907711025627955850380675 517361566538441933775571013)
                ·
                  refine ⟨97005293725957862582919565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 517361566538441933775571013 97005293725957862582919565)
                  ·
                    refine ⟨36376985147234198468594837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97005293725957862582919565 36376985147234198468594837)
                    ·
                      refine ⟨1705171178776603053215383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36376985147234198468594837 1705171178776603053215383)
                      ·
                        rfl

theorem cell23_3320809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_3320809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320809 prefixEnd_3320809 := by exact prefixLift 3320809
  have htrace : WordTrace (prefixWord ++ tailWord_3320809) baseStart_3320809 baseEnd_3320809 := by
    simpa [prefixWord, tailWord_3320809, baseEnd_3320809] using wordTrace_append hprefix tailTrace_3320809
  have hstable : (prefixWord ++ tailWord_3320809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320809).length < 2 ^ (prefixWord ++ tailWord_3320809).sum := by decide
  have hdescent : baseEnd_3320809 < baseStart_3320809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320817 : List Nat := [1, 2, 2, 2, 4, 3, 1, 2, 1, 3, 2]
def baseStart_3320817 : Nat := 118140960795 + 3320817 * 2 ^ 59
def prefixEnd_3320817 : Nat := 4983230072969 + 3 ^ 40 * 3320817 * 2
def baseEnd_3320817 : Nat := 1705175286621839021915347

theorem tailTrace_3320817 : CollatzResearch.WordTrace tailWord_3320817 prefixEnd_3320817 1705175286621839021915347 := by
  unfold tailWord_3320817
  simp only [CollatzResearch.WordTrace]
  refine ⟨121120146410254634235560705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80746764273503089490373803 121120146410254634235560705)
  ·
    refine ⟨90840109807690975676670529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121120146410254634235560705 90840109807690975676670529)
    ·
      refine ⟨68130082355768231757502897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90840109807690975676670529 68130082355768231757502897)
      ·
        refine ⟨51097561766826173818127173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68130082355768231757502897 51097561766826173818127173)
        ·
          refine ⟨9580792831279907590898845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51097561766826173818127173 9580792831279907590898845)
          ·
            refine ⟨3592797311729965346587067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9580792831279907590898845 3592797311729965346587067)
            ·
              refine ⟨5389195967594948019880601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592797311729965346587067 5389195967594948019880601)
              ·
                refine ⟨4041896975696211014910451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5389195967594948019880601 4041896975696211014910451)
                ·
                  refine ⟨6062845463544316522365677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041896975696211014910451 6062845463544316522365677)
                  ·
                    refine ⟨2273567048829118695887129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6062845463544316522365677 2273567048829118695887129)
                    ·
                      refine ⟨1705175286621839021915347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2273567048829118695887129 1705175286621839021915347)
                      ·
                        rfl

theorem cell23_3320817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_3320817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320817 prefixEnd_3320817 := by exact prefixLift 3320817
  have htrace : WordTrace (prefixWord ++ tailWord_3320817) baseStart_3320817 baseEnd_3320817 := by
    simpa [prefixWord, tailWord_3320817, baseEnd_3320817] using wordTrace_append hprefix tailTrace_3320817
  have hstable : (prefixWord ++ tailWord_3320817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320817).length < 2 ^ (prefixWord ++ tailWord_3320817).sum := by decide
  have hdescent : baseEnd_3320817 < baseStart_3320817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320863 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 3]
def baseStart_3320863 : Nat := 118140960795 + 3320863 * 2 ^ 59
def prefixEnd_3320863 : Nat := 4983230072969 + 3 ^ 40 * 3320863 * 2
def baseEnd_3320863 : Nat := 1705198906731945841940135

theorem tailTrace_3320863 : CollatzResearch.WordTrace tailWord_3320863 prefixEnd_3320863 1705198906731945841940135 := by
  unfold tailWord_3320863
  simp only [CollatzResearch.WordTrace]
  refine ⟨121121824168087984091735243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80747882778725322727823495 121121824168087984091735243)
  ·
    refine ⟨181682736252131976137602865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121121824168087984091735243 181682736252131976137602865)
    ·
      refine ⟨136262052189098982103202149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181682736252131976137602865 136262052189098982103202149)
      ·
        refine ⟨25549134785456059144350403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136262052189098982103202149 25549134785456059144350403)
        ·
          refine ⟨38323702178184088716525605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25549134785456059144350403 38323702178184088716525605)
          ·
            refine ⟨7185694158409516634348551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38323702178184088716525605 7185694158409516634348551)
            ·
              refine ⟨10778541237614274951522827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7185694158409516634348551 10778541237614274951522827)
              ·
                refine ⟨16167811856421412427284241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10778541237614274951522827 16167811856421412427284241)
                ·
                  refine ⟨12125858892316059320463181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16167811856421412427284241 12125858892316059320463181)
                  ·
                    refine ⟨4547197084618522245173693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12125858892316059320463181 4547197084618522245173693)
                    ·
                      refine ⟨1705198906731945841940135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4547197084618522245173693 1705198906731945841940135)
                      ·
                        rfl

theorem cell23_3320863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_3320863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320863 prefixEnd_3320863 := by exact prefixLift 3320863
  have htrace : WordTrace (prefixWord ++ tailWord_3320863) baseStart_3320863 baseEnd_3320863 := by
    simpa [prefixWord, tailWord_3320863, baseEnd_3320863] using wordTrace_append hprefix tailTrace_3320863
  have hstable : (prefixWord ++ tailWord_3320863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320863).length < 2 ^ (prefixWord ++ tailWord_3320863).sum := by decide
  have hdescent : baseEnd_3320863 < baseStart_3320863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320906 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_3320906 : Nat := 118140960795 + 3320906 * 2 ^ 59
def prefixEnd_3320906 : Nat := 4983230072969 + 3 ^ 40 * 3320906 * 2
def baseEnd_3320906 : Nat := 1705220986400089173702437

theorem tailTrace_3320906 : CollatzResearch.WordTrace tailWord_3320906 prefixEnd_3320906 1705220986400089173702437 := by
  unfold tailWord_3320906
  simp only [CollatzResearch.WordTrace]
  refine ⟨30280848126733050608887643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80748928337954801623700381 30280848126733050608887643)
  ·
    refine ⟨45421272190099575913331465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30280848126733050608887643 45421272190099575913331465)
    ·
      refine ⟨34065954142574681934998599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45421272190099575913331465 34065954142574681934998599)
      ·
        refine ⟨51098931213862022902497899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34065954142574681934998599 51098931213862022902497899)
        ·
          refine ⟨76648396820793034353746849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51098931213862022902497899 76648396820793034353746849)
          ·
            refine ⟨57486297615594775765310137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76648396820793034353746849 57486297615594775765310137)
            ·
              refine ⟨43114723211696081823982603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57486297615594775765310137 43114723211696081823982603)
              ·
                refine ⟨64672084817544122735973905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43114723211696081823982603 64672084817544122735973905)
                ·
                  refine ⟨48504063613158092051980429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64672084817544122735973905 48504063613158092051980429)
                  ·
                    refine ⟨18189023854934284519492661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48504063613158092051980429 18189023854934284519492661)
                    ·
                      refine ⟨1705220986400089173702437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18189023854934284519492661 1705220986400089173702437)
                      ·
                        rfl

theorem cell23_3320906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_3320906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320906 prefixEnd_3320906 := by exact prefixLift 3320906
  have htrace : WordTrace (prefixWord ++ tailWord_3320906) baseStart_3320906 baseEnd_3320906 := by
    simpa [prefixWord, tailWord_3320906, baseEnd_3320906] using wordTrace_append hprefix tailTrace_3320906
  have hstable : (prefixWord ++ tailWord_3320906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320906).length < 2 ^ (prefixWord ++ tailWord_3320906).sum := by decide
  have hdescent : baseEnd_3320906 < baseStart_3320906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320913 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 3, 4]
def baseStart_3320913 : Nat := 118140960795 + 3320913 * 2 ^ 59
def prefixEnd_3320913 : Nat := 4983230072969 + 3 ^ 40 * 3320913 * 2
def baseEnd_3320913 : Nat := 568408193588223548771635

theorem tailTrace_3320913 : CollatzResearch.WordTrace tailWord_3320913 prefixEnd_3320913 568408193588223548771635 := by
  unfold tailWord_3320913
  simp only [CollatzResearch.WordTrace]
  refine ⟨121123647817906842631055393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80749098545271228420703595 121123647817906842631055393)
  ·
    refine ⟨90842735863430131973291545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121123647817906842631055393 90842735863430131973291545)
    ·
      refine ⟨68132051897572598979968659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90842735863430131973291545 68132051897572598979968659)
      ·
        refine ⟨102198077846358898469952989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68132051897572598979968659 102198077846358898469952989)
        ·
          refine ⟨38324279192384586926232371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102198077846358898469952989 38324279192384586926232371)
          ·
            refine ⟨57486418788576880389348557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38324279192384586926232371 57486418788576880389348557)
            ·
              refine ⟨21557407045716330146005709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57486418788576880389348557 21557407045716330146005709)
              ·
                refine ⟨8084027642143623804752141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21557407045716330146005709 8084027642143623804752141)
                ·
                  refine ⟨3031510365803858926782053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8084027642143623804752141 3031510365803858926782053)
                  ·
                    refine ⟨568408193588223548771635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3031510365803858926782053 568408193588223548771635)
                    ·
                      rfl

theorem cell23_3320913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_3320913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320913 prefixEnd_3320913 := by exact prefixLift 3320913
  have htrace : WordTrace (prefixWord ++ tailWord_3320913) baseStart_3320913 baseEnd_3320913 := by
    simpa [prefixWord, tailWord_3320913, baseEnd_3320913] using wordTrace_append hprefix tailTrace_3320913
  have hstable : (prefixWord ++ tailWord_3320913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320913).length < 2 ^ (prefixWord ++ tailWord_3320913).sum := by decide
  have hdescent : baseEnd_3320913 < baseStart_3320913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320964 : List Nat := [2, 3, 2, 1, 2, 3, 3, 2, 1, 4]
def baseStart_3320964 : Nat := 118140960795 + 3320964 * 2 ^ 59
def prefixEnd_3320964 : Nat := 4983230072969 + 3 ^ 40 * 3320964 * 2
def baseEnd_3320964 : Nat := 568416922759349982259057

theorem tailTrace_3320964 : CollatzResearch.WordTrace tailWord_3320964 prefixEnd_3320964 568416922759349982259057 := by
  unfold tailWord_3320964
  simp only [CollatzResearch.WordTrace]
  refine ⟨60562753970361039170580973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80750338627148052227441297 60562753970361039170580973)
  ·
    refine ⟨22711032738885389688967865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60562753970361039170580973 22711032738885389688967865)
    ·
      refine ⟨17033274554164042266725899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22711032738885389688967865 17033274554164042266725899)
      ·
        refine ⟨25549911831246063400088849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17033274554164042266725899 25549911831246063400088849)
        ·
          refine ⟨19162433873434547550066637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25549911831246063400088849 19162433873434547550066637)
          ·
            refine ⟨7185912702537955331274989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19162433873434547550066637 7185912702537955331274989)
            ·
              refine ⟨2694717263451733249228121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7185912702537955331274989 2694717263451733249228121)
              ·
                refine ⟨2021037947588799936921091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694717263451733249228121 2021037947588799936921091)
                ·
                  refine ⟨3031556921383199905381637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021037947588799936921091 3031556921383199905381637)
                  ·
                    refine ⟨568416922759349982259057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3031556921383199905381637 568416922759349982259057)
                    ·
                      rfl

theorem cell23_3320964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_3320964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320964 prefixEnd_3320964 := by exact prefixLift 3320964
  have htrace : WordTrace (prefixWord ++ tailWord_3320964) baseStart_3320964 baseEnd_3320964 := by
    simpa [prefixWord, tailWord_3320964, baseEnd_3320964] using wordTrace_append hprefix tailTrace_3320964
  have hstable : (prefixWord ++ tailWord_3320964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320964).length < 2 ^ (prefixWord ++ tailWord_3320964).sum := by decide
  have hdescent : baseEnd_3320964 < baseStart_3320964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3320997 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 2, 3, 2]
def baseStart_3320997 : Nat := 118140960795 + 3320997 * 2 ^ 59
def prefixEnd_3320997 : Nat := 4983230072969 + 3 ^ 40 * 3320997 * 2
def baseEnd_3320997 : Nat := 1705267713139648317664519

theorem tailTrace_3320997 : CollatzResearch.WordTrace tailWord_3320997 prefixEnd_3320997 1705267713139648317664519 := by
  unfold tailWord_3320997
  simp only [CollatzResearch.WordTrace]
  refine ⟨121126711549602524977113245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80751141033068349984742163 121126711549602524977113245)
  ·
    refine ⟨45422516831100946866417467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121126711549602524977113245 45422516831100946866417467)
    ·
      refine ⟨68133775246651420299626201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45422516831100946866417467 68133775246651420299626201)
      ·
        refine ⟨51100331434988565224719651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68133775246651420299626201 51100331434988565224719651)
        ·
          refine ⟨76650497152482847837079477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51100331434988565224719651 76650497152482847837079477)
          ·
            refine ⟨7185984108045266984726201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76650497152482847837079477 7185984108045266984726201)
            ·
              refine ⟨5389488081033950238544651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7185984108045266984726201 5389488081033950238544651)
              ·
                refine ⟨8084232121550925357816977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5389488081033950238544651 8084232121550925357816977)
                ·
                  refine ⟨6063174091163194018362733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8084232121550925357816977 6063174091163194018362733)
                  ·
                    refine ⟨2273690284186197756886025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6063174091163194018362733 2273690284186197756886025)
                    ·
                      refine ⟨1705267713139648317664519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2273690284186197756886025 1705267713139648317664519)
                      ·
                        rfl

theorem cell23_3320997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_3320997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3320997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3320997 prefixEnd_3320997 := by exact prefixLift 3320997
  have htrace : WordTrace (prefixWord ++ tailWord_3320997) baseStart_3320997 baseEnd_3320997 := by
    simpa [prefixWord, tailWord_3320997, baseEnd_3320997] using wordTrace_append hprefix tailTrace_3320997
  have hstable : (prefixWord ++ tailWord_3320997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3320997).length < 2 ^ (prefixWord ++ tailWord_3320997).sum := by decide
  have hdescent : baseEnd_3320997 < baseStart_3320997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3320997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321043 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 3]
def baseStart_3321043 : Nat := 118140960795 + 3321043 * 2 ^ 59
def prefixEnd_3321043 : Nat := 4983230072969 + 3 ^ 40 * 3321043 * 2
def baseEnd_3321043 : Nat := 1705291333249755137689307

theorem tailTrace_3321043 : CollatzResearch.WordTrace tailWord_3321043 prefixEnd_3321043 1705291333249755137689307 := by
  unfold tailWord_3321043
  simp only [CollatzResearch.WordTrace]
  refine ⟨121128389307435874833287783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80752259538290583222191855 121128389307435874833287783)
  ·
    refine ⟨181692583961153812249931675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121128389307435874833287783 181692583961153812249931675)
    ·
      refine ⟨272538875941730718374897513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181692583961153812249931675 272538875941730718374897513)
      ·
        refine ⟨204404156956298038781173135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272538875941730718374897513 204404156956298038781173135)
        ·
          refine ⟨306606235434447058171759703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204404156956298038781173135 306606235434447058171759703)
          ·
            refine ⟨459909353151670587257639555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306606235434447058171759703 459909353151670587257639555)
            ·
              refine ⟨689864029727505880886459333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459909353151670587257639555 689864029727505880886459333)
              ·
                refine ⟨129349505573907352666211125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 689864029727505880886459333 129349505573907352666211125)
                ·
                  refine ⟨12126516147553814312457293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129349505573907352666211125 12126516147553814312457293)
                  ·
                    refine ⟨4547443555332680367171485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12126516147553814312457293 4547443555332680367171485)
                    ·
                      refine ⟨1705291333249755137689307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4547443555332680367171485 1705291333249755137689307)
                      ·
                        rfl

theorem cell23_3321043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 3].length) (baseStart_3321043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321043 prefixEnd_3321043 := by exact prefixLift 3321043
  have htrace : WordTrace (prefixWord ++ tailWord_3321043) baseStart_3321043 baseEnd_3321043 := by
    simpa [prefixWord, tailWord_3321043, baseEnd_3321043] using wordTrace_append hprefix tailTrace_3321043
  have hstable : (prefixWord ++ tailWord_3321043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321043).length < 2 ^ (prefixWord ++ tailWord_3321043).sum := by decide
  have hdescent : baseEnd_3321043 < baseStart_3321043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321060 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_3321060 : Nat := 118140960795 + 3321060 * 2 ^ 59
def prefixEnd_3321060 : Nat := 4983230072969 + 3 ^ 40 * 3321060 * 2
def baseEnd_3321060 : Nat := 1705300062420881571176729

theorem tailTrace_3321060 : CollatzResearch.WordTrace tailWord_3321060 prefixEnd_3321060 1705300062420881571176729 := by
  unfold tailWord_3321060
  simp only [CollatzResearch.WordTrace]
  refine ⟨60564504674187143368328317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80752672898916191157771089 60564504674187143368328317)
  ·
    refine ⟨22711689252820178763123119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60564504674187143368328317 22711689252820178763123119)
    ·
      refine ⟨34067533879230268144684679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22711689252820178763123119 34067533879230268144684679)
      ·
        refine ⟨51101300818845402217027019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34067533879230268144684679 51101300818845402217027019)
        ·
          refine ⟨76651951228268103325540529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51101300818845402217027019 76651951228268103325540529)
          ·
            refine ⟨57488963421201077494155397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76651951228268103325540529 57488963421201077494155397)
            ·
              refine ⟨10779180641475202030154137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57488963421201077494155397 10779180641475202030154137)
              ·
                refine ⟨8084385481106401522615603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10779180641475202030154137 8084385481106401522615603)
                ·
                  refine ⟨12126578221659602283923405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8084385481106401522615603 12126578221659602283923405)
                  ·
                    refine ⟨4547466833122350856471277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12126578221659602283923405 4547466833122350856471277)
                    ·
                      refine ⟨1705300062420881571176729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4547466833122350856471277 1705300062420881571176729)
                      ·
                        rfl

theorem cell23_3321060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_3321060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321060 prefixEnd_3321060 := by exact prefixLift 3321060
  have htrace : WordTrace (prefixWord ++ tailWord_3321060) baseStart_3321060 baseEnd_3321060 := by
    simpa [prefixWord, tailWord_3321060, baseEnd_3321060] using wordTrace_append hprefix tailTrace_3321060
  have hstable : (prefixWord ++ tailWord_3321060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321060).length < 2 ^ (prefixWord ++ tailWord_3321060).sum := by decide
  have hdescent : baseEnd_3321060 < baseStart_3321060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321061 : List Nat := [1, 3, 1, 4, 4, 1, 2, 1, 1, 1, 4]
def baseStart_3321061 : Nat := 118140960795 + 3321061 * 2 ^ 59
def prefixEnd_3321061 : Nat := 4983230072969 + 3 ^ 40 * 3321061 * 2
def baseEnd_3321061 : Nat := 1705300575901536067264225

theorem tailTrace_3321061 : CollatzResearch.WordTrace tailWord_3321061 prefixEnd_3321061 1705300575901536067264225 := by
  unfold tailWord_3321061
  simp only [CollatzResearch.WordTrace]
  refine ⟨121129045821370663907443037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80752697214247109271628691 121129045821370663907443037)
  ·
    refine ⟨45423392183013998965291139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121129045821370663907443037 45423392183013998965291139)
    ·
      refine ⟨68135088274520998447936709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45423392183013998965291139 68135088274520998447936709)
      ·
        refine ⟨12775329051472687208988133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68135088274520998447936709 12775329051472687208988133)
        ·
          refine ⟨2395374197151128851685275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12775329051472687208988133 2395374197151128851685275)
          ·
            refine ⟨3593061295726693277527913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395374197151128851685275 3593061295726693277527913)
            ·
              refine ⟨2694795971795019958145935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3593061295726693277527913 2694795971795019958145935)
              ·
                refine ⟨4042193957692529937218903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2694795971795019958145935 4042193957692529937218903)
                ·
                  refine ⟨6063290936538794905828355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4042193957692529937218903 6063290936538794905828355)
                  ·
                    refine ⟨9094936404808192358742533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6063290936538794905828355 9094936404808192358742533)
                    ·
                      refine ⟨1705300575901536067264225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9094936404808192358742533 1705300575901536067264225)
                      ·
                        rfl

theorem cell23_3321061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_3321061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321061 prefixEnd_3321061 := by exact prefixLift 3321061
  have htrace : WordTrace (prefixWord ++ tailWord_3321061) baseStart_3321061 baseEnd_3321061 := by
    simpa [prefixWord, tailWord_3321061, baseEnd_3321061] using wordTrace_append hprefix tailTrace_3321061
  have hstable : (prefixWord ++ tailWord_3321061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321061).length < 2 ^ (prefixWord ++ tailWord_3321061).sum := by decide
  have hdescent : baseEnd_3321061 < baseStart_3321061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321093 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 2, 6]
def baseStart_3321093 : Nat := 118140960795 + 3321093 * 2 ^ 59
def prefixEnd_3321093 : Nat := 4983230072969 + 3 ^ 40 * 3321093 * 2
def baseEnd_3321093 : Nat := 568439002427493314021359

theorem tailTrace_3321093 : CollatzResearch.WordTrace tailWord_3321093 prefixEnd_3321093 568439002427493314021359 := by
  unfold tailWord_3321093
  simp only [CollatzResearch.WordTrace]
  refine ⟨121130212957254733372607933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80753475304836488915071955 121130212957254733372607933)
  ·
    refine ⟨45423829858970525014727975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121130212957254733372607933 45423829858970525014727975)
    ·
      refine ⟨68135744788455787522091963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45423829858970525014727975 68135744788455787522091963)
      ·
        refine ⟨102203617182683681283137945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68135744788455787522091963 102203617182683681283137945)
        ·
          refine ⟨76652712887012760962353459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102203617182683681283137945 76652712887012760962353459)
          ·
            refine ⟨114979069330519141443530189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76652712887012760962353459 114979069330519141443530189)
            ·
              refine ⟨43117150998944678041323821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114979069330519141443530189 43117150998944678041323821)
              ·
                refine ⟨16168931624604254265496433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43117150998944678041323821 16168931624604254265496433)
                ·
                  refine ⟨12126698718453190699122325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16168931624604254265496433 12126698718453190699122325)
                  ·
                    refine ⟨568439002427493314021359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12126698718453190699122325 568439002427493314021359)
                    ·
                      rfl

theorem cell23_3321093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_3321093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321093 prefixEnd_3321093 := by exact prefixLift 3321093
  have htrace : WordTrace (prefixWord ++ tailWord_3321093) baseStart_3321093 baseEnd_3321093 := by
    simpa [prefixWord, tailWord_3321093, baseEnd_3321093] using wordTrace_append hprefix tailTrace_3321093
  have hstable : (prefixWord ++ tailWord_3321093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321093).length < 2 ^ (prefixWord ++ tailWord_3321093).sum := by decide
  have hdescent : baseEnd_3321093 < baseStart_3321093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321151 : List Nat := [1, 1, 2, 2, 4, 2, 4, 1, 2, 2, 2]
def baseStart_3321151 : Nat := 118140960795 + 3321151 * 2 ^ 59
def prefixEnd_3321151 : Nat := 4983230072969 + 3 ^ 40 * 3321151 * 2
def baseEnd_3321151 : Nat := 1705346789160440715138811

theorem tailTrace_3321151 : CollatzResearch.WordTrace tailWord_3321151 prefixEnd_3321151 1705346789160440715138811 := by
  unfold tailWord_3321151
  simp only [CollatzResearch.WordTrace]
  refine ⟨121132328391044609278219307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80754885594029739518812871 121132328391044609278219307)
  ·
    refine ⟨181698492586566913917328961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121132328391044609278219307 181698492586566913917328961)
    ·
      refine ⟨136273869439925185437996721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181698492586566913917328961 136273869439925185437996721)
      ·
        refine ⟨102205402079943889078497541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136273869439925185437996721 102205402079943889078497541)
        ·
          refine ⟨19163512889989479202218289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102205402079943889078497541 19163512889989479202218289)
          ·
            refine ⟨14372634667492109401663717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19163512889989479202218289 14372634667492109401663717)
            ·
              refine ⟨2694869000154770512811947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14372634667492109401663717 2694869000154770512811947)
              ·
                refine ⟨4042303500232155769217921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2694869000154770512811947 4042303500232155769217921)
                ·
                  refine ⟨3031727625174116826913441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4042303500232155769217921 3031727625174116826913441)
                  ·
                    refine ⟨2273795718880587620185081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3031727625174116826913441 2273795718880587620185081)
                    ·
                      refine ⟨1705346789160440715138811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2273795718880587620185081 1705346789160440715138811)
                      ·
                        rfl

theorem cell23_3321151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 2, 2, 2].length) (baseStart_3321151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321151 prefixEnd_3321151 := by exact prefixLift 3321151
  have htrace : WordTrace (prefixWord ++ tailWord_3321151) baseStart_3321151 baseEnd_3321151 := by
    simpa [prefixWord, tailWord_3321151, baseEnd_3321151] using wordTrace_append hprefix tailTrace_3321151
  have hstable : (prefixWord ++ tailWord_3321151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321151).length < 2 ^ (prefixWord ++ tailWord_3321151).sum := by decide
  have hdescent : baseEnd_3321151 < baseStart_3321151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321191 : List Nat := [1, 1, 5, 1, 4, 2, 2, 2, 5]
def baseStart_3321191 : Nat := 118140960795 + 3321191 * 2 ^ 59
def prefixEnd_3321191 : Nat := 4983230072969 + 3 ^ 40 * 3321191 * 2
def baseEnd_3321191 : Nat := 189485258709624506515403

theorem tailTrace_3321191 : CollatzResearch.WordTrace tailWord_3321191 prefixEnd_3321191 189485258709624506515403 := by
  unfold tailWord_3321191
  simp only [CollatzResearch.WordTrace]
  refine ⟨121133787310899696109675427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80755858207266464073116951 121133787310899696109675427)
  ·
    refine ⟨181700680966349544164513141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121133787310899696109675427 181700680966349544164513141)
    ·
      refine ⟨17034438840595269765423107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181700680966349544164513141 17034438840595269765423107)
      ·
        refine ⟨25551658260892904648134661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17034438840595269765423107 25551658260892904648134661)
        ·
          refine ⟨4790935923917419621525249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25551658260892904648134661 4790935923917419621525249)
          ·
            refine ⟨3593201942938064716143937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4790935923917419621525249 3593201942938064716143937)
            ·
              refine ⟨2694901457203548537107953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3593201942938064716143937 2694901457203548537107953)
              ·
                refine ⟨2021176092902661402830965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694901457203548537107953 2021176092902661402830965)
                ·
                  refine ⟨189485258709624506515403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2021176092902661402830965 189485258709624506515403)
                  ·
                    rfl

theorem cell23_3321191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 5].length) (baseStart_3321191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321191 prefixEnd_3321191 := by exact prefixLift 3321191
  have htrace : WordTrace (prefixWord ++ tailWord_3321191) baseStart_3321191 baseEnd_3321191 := by
    simpa [prefixWord, tailWord_3321191, baseEnd_3321191] using wordTrace_append hprefix tailTrace_3321191
  have hstable : (prefixWord ++ tailWord_3321191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321191).length < 2 ^ (prefixWord ++ tailWord_3321191).sum := by decide
  have hdescent : baseEnd_3321191 < baseStart_3321191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321207 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 2, 4, 2]
def baseStart_3321207 : Nat := 118140960795 + 3321207 * 2 ^ 59
def prefixEnd_3321207 : Nat := 4983230072969 + 3 ^ 40 * 3321207 * 2
def baseEnd_3321207 : Nat := 1705375544077092496038553

theorem tailTrace_3321207 : CollatzResearch.WordTrace tailWord_3321207 prefixEnd_3321207 1705375544077092496038553 := by
  unfold tailWord_3321207
  simp only [CollatzResearch.WordTrace]
  refine ⟨121134370878841730842257875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80756247252561153894838583 121134370878841730842257875)
  ·
    refine ⟨181701556318262596263386813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121134370878841730842257875 181701556318262596263386813)
    ·
      refine ⟨68138083619348473598770055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181701556318262596263386813 68138083619348473598770055)
      ·
        refine ⟨102207125429022710398155083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68138083619348473598770055 102207125429022710398155083)
        ·
          refine ⟨153310688143534065597232625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102207125429022710398155083 153310688143534065597232625)
          ·
            refine ⟨114983016107650549197924469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153310688143534065597232625 114983016107650549197924469)
            ·
              refine ⟨10779657760092238987305419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114983016107650549197924469 10779657760092238987305419)
              ·
                refine ⟨16169486640138358480958129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10779657760092238987305419 16169486640138358480958129)
                ·
                  refine ⟨12127114980103768860718597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16169486640138358480958129 12127114980103768860718597)
                  ·
                    refine ⟨2273834058769456661384737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12127114980103768860718597 2273834058769456661384737)
                    ·
                      refine ⟨1705375544077092496038553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2273834058769456661384737 1705375544077092496038553)
                      ·
                        rfl

theorem cell23_3321207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 4, 2].length) (baseStart_3321207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321207 prefixEnd_3321207 := by exact prefixLift 3321207
  have htrace : WordTrace (prefixWord ++ tailWord_3321207) baseStart_3321207 baseEnd_3321207 := by
    simpa [prefixWord, tailWord_3321207, baseEnd_3321207] using wordTrace_append hprefix tailTrace_3321207
  have hstable : (prefixWord ++ tailWord_3321207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321207).length < 2 ^ (prefixWord ++ tailWord_3321207).sum := by decide
  have hdescent : baseEnd_3321207 < baseStart_3321207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321210 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3]
def baseStart_3321210 : Nat := 118140960795 + 3321210 * 2 ^ 59
def prefixEnd_3321210 : Nat := 4983230072969 + 3 ^ 40 * 3321210 * 2
def baseEnd_3321210 : Nat := 1705377084519055984301039

theorem tailTrace_3321210 : CollatzResearch.WordTrace tailWord_3321210 prefixEnd_3321210 1705377084519055984301039 := by
  unfold tailWord_3321210
  simp only [CollatzResearch.WordTrace]
  refine ⟨30283620074457715588654271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80756320198553908236411389 30283620074457715588654271)
  ·
    refine ⟨45425430111686573382981407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30283620074457715588654271 45425430111686573382981407)
    ·
      refine ⟨68138145167529860074472111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45425430111686573382981407 68138145167529860074472111)
      ·
        refine ⟨102207217751294790111708167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68138145167529860074472111 102207217751294790111708167)
        ·
          refine ⟨153310826626942185167562251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102207217751294790111708167 153310826626942185167562251)
          ·
            refine ⟨229966239940413277751343377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153310826626942185167562251 229966239940413277751343377)
            ·
              refine ⟨172474679955309958313507533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229966239940413277751343377 172474679955309958313507533)
              ·
                refine ⟨64678004983241234367565325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172474679955309958313507533 64678004983241234367565325)
                ·
                  refine ⟨24254251868715462887836997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64678004983241234367565325 24254251868715462887836997)
                  ·
                    refine ⟨4547672225384149291469437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24254251868715462887836997 4547672225384149291469437)
                    ·
                      refine ⟨1705377084519055984301039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4547672225384149291469437 1705377084519055984301039)
                      ·
                        rfl

theorem cell23_3321210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_3321210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321210 prefixEnd_3321210 := by exact prefixLift 3321210
  have htrace : WordTrace (prefixWord ++ tailWord_3321210) baseStart_3321210 baseEnd_3321210 := by
    simpa [prefixWord, tailWord_3321210, baseEnd_3321210] using wordTrace_append hprefix tailTrace_3321210
  have hstable : (prefixWord ++ tailWord_3321210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321210).length < 2 ^ (prefixWord ++ tailWord_3321210).sum := by decide
  have hdescent : baseEnd_3321210 < baseStart_3321210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321224 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 2, 1, 4]
def baseStart_3321224 : Nat := 118140960795 + 3321224 * 2 ^ 59
def prefixEnd_3321224 : Nat := 4983230072969 + 3 ^ 40 * 3321224 * 2
def baseEnd_3321224 : Nat := 1705384273248218929525975

theorem tailTrace_3321224 : CollatzResearch.WordTrace tailWord_3321224 prefixEnd_3321224 1705384273248218929525975 := by
  unfold tailWord_3321224
  simp only [CollatzResearch.WordTrace]
  refine ⟨60567495459890071372813363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80756660613186761830417817 60567495459890071372813363)
  ·
    refine ⟨90851243189835107059220045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60567495459890071372813363 90851243189835107059220045)
    ·
      refine ⟨34069216196188165147207517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90851243189835107059220045 34069216196188165147207517)
      ·
        refine ⟨12775956073570561930202819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34069216196188165147207517 12775956073570561930202819)
        ·
          refine ⟨19163934110355842895304229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12775956073570561930202819 19163934110355842895304229)
          ·
            refine ⟨3593237645691720542869543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19163934110355842895304229 3593237645691720542869543)
            ·
              refine ⟨5389856468537580814304315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3593237645691720542869543 5389856468537580814304315)
              ·
                refine ⟨8084784702806371221456473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5389856468537580814304315 8084784702806371221456473)
                ·
                  refine ⟨6063588527104778416092355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8084784702806371221456473 6063588527104778416092355)
                  ·
                    refine ⟨9095382790657167624138533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6063588527104778416092355 9095382790657167624138533)
                    ·
                      refine ⟨1705384273248218929525975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9095382790657167624138533 1705384273248218929525975)
                      ·
                        rfl

theorem cell23_3321224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_3321224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321224 prefixEnd_3321224 := by exact prefixLift 3321224
  have htrace : WordTrace (prefixWord ++ tailWord_3321224) baseStart_3321224 baseEnd_3321224 := by
    simpa [prefixWord, tailWord_3321224, baseEnd_3321224] using wordTrace_append hprefix tailTrace_3321224
  have hstable : (prefixWord ++ tailWord_3321224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321224).length < 2 ^ (prefixWord ++ tailWord_3321224).sum := by decide
  have hdescent : baseEnd_3321224 < baseStart_3321224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321247 : List Nat := [1, 1, 2, 5, 1, 2, 3, 2, 6]
def baseStart_3321247 : Nat := 118140960795 + 3321247 * 2 ^ 59
def prefixEnd_3321247 : Nat := 4983230072969 + 3 ^ 40 * 3321247 * 2
def baseEnd_3321247 : Nat := 189488453700363593282041

theorem tailTrace_3321247 : CollatzResearch.WordTrace tailWord_3321247 prefixEnd_3321247 189488453700363593282041 := by
  unfold tailWord_3321247
  simp only [CollatzResearch.WordTrace]
  refine ⟨121135829798696817673713995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80757219865797878449142663 121135829798696817673713995)
  ·
    refine ⟨181703744698045226510570993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121135829798696817673713995 181703744698045226510570993)
    ·
      refine ⟨136277808523533919882928245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181703744698045226510570993 136277808523533919882928245)
      ·
        refine ⟨12776044549081304989024523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136277808523533919882928245 12776044549081304989024523)
        ·
          refine ⟨19164066823621957483536785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12776044549081304989024523 19164066823621957483536785)
          ·
            refine ⟨14373050117716468112652589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19164066823621957483536785 14373050117716468112652589)
            ·
              refine ⟨5389893794143675542244721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14373050117716468112652589 5389893794143675542244721)
              ·
                refine ⟨4042420345607756656683541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5389893794143675542244721 4042420345607756656683541)
                ·
                  refine ⟨189488453700363593282041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4042420345607756656683541 189488453700363593282041)
                  ·
                    rfl

theorem cell23_3321247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 6].length) (baseStart_3321247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321247 prefixEnd_3321247 := by exact prefixLift 3321247
  have htrace : WordTrace (prefixWord ++ tailWord_3321247) baseStart_3321247 baseEnd_3321247 := by
    simpa [prefixWord, tailWord_3321247, baseEnd_3321247] using wordTrace_append hprefix tailTrace_3321247
  have hstable : (prefixWord ++ tailWord_3321247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321247).length < 2 ^ (prefixWord ++ tailWord_3321247).sum := by decide
  have hdescent : baseEnd_3321247 < baseStart_3321247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321260 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 5, 5]
def baseStart_3321260 : Nat := 118140960795 + 3321260 * 2 ^ 59
def prefixEnd_3321260 : Nat := 4983230072969 + 3 ^ 40 * 3321260 * 2
def baseEnd_3321260 : Nat := 568467586183926929558603

theorem tailTrace_3321260 : CollatzResearch.WordTrace tailWord_3321260 prefixEnd_3321260 568467586183926929558603 := by
  unfold tailWord_3321260
  simp only [CollatzResearch.WordTrace]
  refine ⟨60568151973824860446968617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80757535965099813929291489 60568151973824860446968617)
  ·
    refine ⟨45426113980368645335226463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60568151973824860446968617 45426113980368645335226463)
    ·
      refine ⟨68139170970552968002839695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45426113980368645335226463 68139170970552968002839695)
      ·
        refine ⟨102208756455829452004259543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68139170970552968002839695 102208756455829452004259543)
        ·
          refine ⟨153313134683744178006389315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102208756455829452004259543 153313134683744178006389315)
          ·
            refine ⟨229969702025616267009583973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153313134683744178006389315 229969702025616267009583973)
            ·
              refine ⟨43119319129803050064296995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229969702025616267009583973 43119319129803050064296995)
              ·
                refine ⟨64678978694704575096445493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43119319129803050064296995 64678978694704575096445493)
                ·
                  refine ⟨6063654252628553915291765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64678978694704575096445493 6063654252628553915291765)
                  ·
                    refine ⟨568467586183926929558603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6063654252628553915291765 568467586183926929558603)
                    ·
                      rfl

theorem cell23_3321260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_3321260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321260 prefixEnd_3321260 := by exact prefixLift 3321260
  have htrace : WordTrace (prefixWord ++ tailWord_3321260) baseStart_3321260 baseEnd_3321260 := by
    simpa [prefixWord, tailWord_3321260, baseEnd_3321260] using wordTrace_append hprefix tailTrace_3321260
  have hstable : (prefixWord ++ tailWord_3321260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321260).length < 2 ^ (prefixWord ++ tailWord_3321260).sum := by decide
  have hdescent : baseEnd_3321260 < baseStart_3321260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321291 : List Nat := [1, 1, 1, 1, 3, 3, 5, 3, 1, 1, 3]
def baseStart_3321291 : Nat := 118140960795 + 3321291 * 2 ^ 59
def prefixEnd_3321291 : Nat := 4983230072969 + 3 ^ 40 * 3321291 * 2
def baseEnd_3321291 : Nat := 1705418676452070167388167

theorem tailTrace_3321291 : CollatzResearch.WordTrace tailWord_3321291 prefixEnd_3321291 1705418676452070167388167 := by
  unfold tailWord_3321291
  simp only [CollatzResearch.WordTrace]
  refine ⟨121137434610537413188315727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80758289740358275458877151 121137434610537413188315727)
  ·
    refine ⟨181706151915806119782473591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121137434610537413188315727 181706151915806119782473591)
    ·
      refine ⟨272559227873709179673710387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181706151915806119782473591 272559227873709179673710387)
      ·
        refine ⟨408838841810563769510565581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272559227873709179673710387 408838841810563769510565581)
        ·
          refine ⟨153314565678961413566462093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 408838841810563769510565581 153314565678961413566462093)
          ·
            refine ⟨57492962129610530087423285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153314565678961413566462093 57492962129610530087423285)
            ·
              refine ⟨5389965199650987195695933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57492962129610530087423285 5389965199650987195695933)
              ·
                refine ⟨2021236949869120198385975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5389965199650987195695933 2021236949869120198385975)
                ·
                  refine ⟨3031855424803680297578963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021236949869120198385975 3031855424803680297578963)
                  ·
                    refine ⟨4547783137205520446368445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3031855424803680297578963 4547783137205520446368445)
                    ·
                      refine ⟨1705418676452070167388167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4547783137205520446368445 1705418676452070167388167)
                      ·
                        rfl

theorem cell23_3321291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 1, 1, 3].length) (baseStart_3321291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321291 prefixEnd_3321291 := by exact prefixLift 3321291
  have htrace : WordTrace (prefixWord ++ tailWord_3321291) baseStart_3321291 baseEnd_3321291 := by
    simpa [prefixWord, tailWord_3321291, baseEnd_3321291] using wordTrace_append hprefix tailTrace_3321291
  have hstable : (prefixWord ++ tailWord_3321291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321291).length < 2 ^ (prefixWord ++ tailWord_3321291).sum := by decide
  have hdescent : baseEnd_3321291 < baseStart_3321291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321348 : List Nat := [2, 3, 2, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_3321348 : Nat := 118140960795 + 3321348 * 2 ^ 59
def prefixEnd_3321348 : Nat := 4983230072969 + 3 ^ 40 * 3321348 * 2
def baseEnd_3321348 : Nat := 1705447944849376444375405

theorem tailTrace_3321348 : CollatzResearch.WordTrace tailWord_3321348 prefixEnd_3321348 1705447944849376444375405 := by
  unfold tailWord_3321348
  simp only [CollatzResearch.WordTrace]
  refine ⟨60569756785665455961570349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80759675714220607948760465 60569756785665455961570349)
  ·
    refine ⟨22713658794624545985588881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60569756785665455961570349 22713658794624545985588881)
    ·
      refine ⟨17035244095968409489191661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22713658794624545985588881 17035244095968409489191661)
      ·
        refine ⟨6388216535988153558446873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17035244095968409489191661 6388216535988153558446873)
        ·
          refine ⟨4791162401991115168835155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6388216535988153558446873 4791162401991115168835155)
          ·
            refine ⟨7186743602986672753252733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4791162401991115168835155 7186743602986672753252733)
            ·
              refine ⟨2695028851120002282469775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7186743602986672753252733 2695028851120002282469775)
              ·
                refine ⟨4042543276680003423704663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695028851120002282469775 4042543276680003423704663)
                ·
                  refine ⟨6063814915020005135556995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4042543276680003423704663 6063814915020005135556995)
                  ·
                    refine ⟨9095722372530007703335493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6063814915020005135556995 9095722372530007703335493)
                    ·
                      refine ⟨1705447944849376444375405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9095722372530007703335493 1705447944849376444375405)
                      ·
                        rfl

theorem cell23_3321348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_3321348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321348 prefixEnd_3321348 := by exact prefixLift 3321348
  have htrace : WordTrace (prefixWord ++ tailWord_3321348) baseStart_3321348 baseEnd_3321348 := by
    simpa [prefixWord, tailWord_3321348, baseEnd_3321348] using wordTrace_append hprefix tailTrace_3321348
  have hstable : (prefixWord ++ tailWord_3321348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321348).length < 2 ^ (prefixWord ++ tailWord_3321348).sum := by decide
  have hdescent : baseEnd_3321348 < baseStart_3321348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321365 : List Nat := [1, 3, 2, 1, 3, 2, 4, 2, 1, 2, 2]
def baseStart_3321365 : Nat := 118140960795 + 3321365 * 2 ^ 59
def prefixEnd_3321365 : Nat := 4983230072969 + 3 ^ 40 * 3321365 * 2
def baseEnd_3321365 : Nat := 1705456674020502877862827

theorem tailTrace_3321365 : CollatzResearch.WordTrace tailWord_3321365 prefixEnd_3321365 1705456674020502877862827 := by
  unfold tailWord_3321365
  simp only [CollatzResearch.WordTrace]
  refine ⟨121140133612269323826509549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80760089074846215884339699 121140133612269323826509549)
  ·
    refine ⟨45427550104600996434941081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121140133612269323826509549 45427550104600996434941081)
    ·
      refine ⟨34070662578450747326205811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45427550104600996434941081 34070662578450747326205811)
      ·
        refine ⟨51105993867676120989308717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34070662578450747326205811 51105993867676120989308717)
        ·
          refine ⟨19164747700378545370990769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51105993867676120989308717 19164747700378545370990769)
          ·
            refine ⟨14373560775283909028243077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19164747700378545370990769 14373560775283909028243077)
            ·
              refine ⟨2695042645365732942795577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14373560775283909028243077 2695042645365732942795577)
              ·
                refine ⟨2021281984024299707096683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2695042645365732942795577 2021281984024299707096683)
                ·
                  refine ⟨3031922976036449560645025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021281984024299707096683 3031922976036449560645025)
                  ·
                    refine ⟨2273942232027337170483769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3031922976036449560645025 2273942232027337170483769)
                    ·
                      refine ⟨1705456674020502877862827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2273942232027337170483769 1705456674020502877862827)
                      ·
                        rfl

theorem cell23_3321365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_3321365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321365 prefixEnd_3321365 := by exact prefixLift 3321365
  have htrace : WordTrace (prefixWord ++ tailWord_3321365) baseStart_3321365 baseEnd_3321365 := by
    simpa [prefixWord, tailWord_3321365, baseEnd_3321365] using wordTrace_append hprefix tailTrace_3321365
  have hstable : (prefixWord ++ tailWord_3321365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321365).length < 2 ^ (prefixWord ++ tailWord_3321365).sum := by decide
  have hdescent : baseEnd_3321365 < baseStart_3321365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321415 : List Nat := [1, 1, 4, 1, 6, 1, 1, 2, 2, 1, 3]
def baseStart_3321415 : Nat := 118140960795 + 3321415 * 2 ^ 59
def prefixEnd_3321415 : Nat := 4983230072969 + 3 ^ 40 * 3321415 * 2
def baseEnd_3321415 : Nat := 1705482348053227682237597

theorem tailTrace_3321415 : CollatzResearch.WordTrace tailWord_3321415 prefixEnd_3321415 1705482348053227682237597 := by
  unfold tailWord_3321415
  simp only [CollatzResearch.WordTrace]
  refine ⟨121141957262088182365829699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80761304841392121577219799 121141957262088182365829699)
  ·
    refine ⟨181712935893132273548744549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121141957262088182365829699 181712935893132273548744549)
    ·
      refine ⟨34071175479962301290389603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181712935893132273548744549 34071175479962301290389603)
      ·
        refine ⟨51106763219943451935584405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34071175479962301290389603 51106763219943451935584405)
        ·
          refine ⟨2395629525934849309480519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51106763219943451935584405 2395629525934849309480519)
          ·
            refine ⟨3593444288902273964220779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395629525934849309480519 3593444288902273964220779)
            ·
              refine ⟨5390166433353410946331169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3593444288902273964220779 5390166433353410946331169)
              ·
                refine ⟨4042624825015058209748377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5390166433353410946331169 4042624825015058209748377)
                ·
                  refine ⟨3031968618761293657311283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4042624825015058209748377 3031968618761293657311283)
                  ·
                    refine ⟨4547952928141940485966925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3031968618761293657311283 4547952928141940485966925)
                    ·
                      refine ⟨1705482348053227682237597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4547952928141940485966925 1705482348053227682237597)
                      ·
                        rfl

theorem cell23_3321415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_3321415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321415 prefixEnd_3321415 := by exact prefixLift 3321415
  have htrace : WordTrace (prefixWord ++ tailWord_3321415) baseStart_3321415 baseEnd_3321415 := by
    simpa [prefixWord, tailWord_3321415, baseEnd_3321415] using wordTrace_append hprefix tailTrace_3321415
  have hstable : (prefixWord ++ tailWord_3321415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321415).length < 2 ^ (prefixWord ++ tailWord_3321415).sum := by decide
  have hdescent : baseEnd_3321415 < baseStart_3321415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321457 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 6, 5]
def baseStart_3321457 : Nat := 118140960795 + 3321457 * 2 ^ 59
def prefixEnd_3321457 : Nat := 4983230072969 + 3 ^ 40 * 3321457 * 2
def baseEnd_3321457 : Nat := 568501304746905505970801

theorem tailTrace_3321457 : CollatzResearch.WordTrace tailWord_3321457 prefixEnd_3321457 568501304746905505970801 := by
  unfold tailWord_3321457
  simp only [CollatzResearch.WordTrace]
  refine ⟨121143489127936023538858625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80762326085290682359239083 121143489127936023538858625)
  ·
    refine ⟨90857616845952017654143969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121143489127936023538858625 90857616845952017654143969)
    ·
      refine ⟨68143212634464013240607977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90857616845952017654143969 68143212634464013240607977)
      ·
        refine ⟨51107409475848009930455983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68143212634464013240607977 51107409475848009930455983)
        ·
          refine ⟨76661114213772014895683975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51107409475848009930455983 76661114213772014895683975)
          ·
            refine ⟨114991671320658022343525963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76661114213772014895683975 114991671320658022343525963)
            ·
              refine ⟨172487506980987033515288945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114991671320658022343525963 172487506980987033515288945)
              ·
                refine ⟨129365630235740275136466709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172487506980987033515288945 129365630235740275136466709)
                ·
                  refine ⟨6064013917300325397021877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129365630235740275136466709 6064013917300325397021877)
                  ·
                    refine ⟨568501304746905505970801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6064013917300325397021877 568501304746905505970801)
                    ·
                      rfl

theorem cell23_3321457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_3321457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321457 prefixEnd_3321457 := by exact prefixLift 3321457
  have htrace : WordTrace (prefixWord ++ tailWord_3321457) baseStart_3321457 baseEnd_3321457 := by
    simpa [prefixWord, tailWord_3321457, baseEnd_3321457] using wordTrace_append hprefix tailTrace_3321457
  have hstable : (prefixWord ++ tailWord_3321457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321457).length < 2 ^ (prefixWord ++ tailWord_3321457).sum := by decide
  have hdescent : baseEnd_3321457 < baseStart_3321457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321467 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 5]
def baseStart_3321467 : Nat := 118140960795 + 3321467 * 2 ^ 59
def prefixEnd_3321467 : Nat := 4983230072969 + 3 ^ 40 * 3321467 * 2
def baseEnd_3321467 : Nat := 1705509049047261478787357

theorem tailTrace_3321467 : CollatzResearch.WordTrace tailWord_3321467 prefixEnd_3321467 1705509049047261478787357 := by
  unfold tailWord_3321467
  simp only [CollatzResearch.WordTrace]
  refine ⟨121143853857899795246722655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80762569238599863497815103 121143853857899795246722655)
  ·
    refine ⟨181715780786849692870083983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121143853857899795246722655 181715780786849692870083983)
    ·
      refine ⟨272573671180274539305125975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181715780786849692870083983 272573671180274539305125975)
      ·
        refine ⟨408860506770411808957688963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272573671180274539305125975 408860506770411808957688963)
        ·
          refine ⟨613290760155617713436533445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408860506770411808957688963 613290760155617713436533445)
          ·
            refine ⟨114992017529178321269350021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 613290760155617713436533445 114992017529178321269350021)
            ·
              refine ⟨21561003286720935238003129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114992017529178321269350021 21561003286720935238003129)
              ·
                refine ⟨16170752465040701428502347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21561003286720935238003129 16170752465040701428502347)
                ·
                  refine ⟨24256128697561052142753521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16170752465040701428502347 24256128697561052142753521)
                  ·
                    refine ⟨18192096523170789107065141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24256128697561052142753521 18192096523170789107065141)
                    ·
                      refine ⟨1705509049047261478787357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18192096523170789107065141 1705509049047261478787357)
                      ·
                        rfl

theorem cell23_3321467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 5].length) (baseStart_3321467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321467 prefixEnd_3321467 := by exact prefixLift 3321467
  have htrace : WordTrace (prefixWord ++ tailWord_3321467) baseStart_3321467 baseEnd_3321467 := by
    simpa [prefixWord, tailWord_3321467, baseEnd_3321467] using wordTrace_append hprefix tailTrace_3321467
  have hstable : (prefixWord ++ tailWord_3321467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321467).length < 2 ^ (prefixWord ++ tailWord_3321467).sum := by decide
  have hdescent : baseEnd_3321467 < baseStart_3321467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321561 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 5, 1, 3]
def baseStart_3321561 : Nat := 118140960795 + 3321561 * 2 ^ 59
def prefixEnd_3321561 : Nat := 4983230072969 + 3 ^ 40 * 3321561 * 2
def baseEnd_3321561 : Nat := 1705557316228784111011925

theorem tailTrace_3321561 : CollatzResearch.WordTrace tailWord_3321561 prefixEnd_3321561 1705557316228784111011925 := by
  unfold tailWord_3321561
  simp only [CollatzResearch.WordTrace]
  refine ⟨121147282319559249300644537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80764854879706166200429691 121147282319559249300644537)
  ·
    refine ⟨90860461739669436975483403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121147282319559249300644537 90860461739669436975483403)
    ·
      refine ⟨136290692609504155463225105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90860461739669436975483403 136290692609504155463225105)
      ·
        refine ⟨102218019457128116597418829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136290692609504155463225105 102218019457128116597418829)
        ·
          refine ⟨38331757296423043724032061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102218019457128116597418829 38331757296423043724032061)
          ·
            refine ⟨14374408986158641396512023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38331757296423043724032061 14374408986158641396512023)
            ·
              refine ⟨21561613479237962094768035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14374408986158641396512023 21561613479237962094768035)
              ·
                refine ⟨32342420218856943142152053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21561613479237962094768035 32342420218856943142152053)
                ·
                  refine ⟨3032101895517838419576755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32342420218856943142152053 3032101895517838419576755)
                  ·
                    refine ⟨4548152843276757629365133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3032101895517838419576755 4548152843276757629365133)
                    ·
                      refine ⟨1705557316228784111011925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4548152843276757629365133 1705557316228784111011925)
                      ·
                        rfl

theorem cell23_3321561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_3321561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321561 prefixEnd_3321561 := by exact prefixLift 3321561
  have htrace : WordTrace (prefixWord ++ tailWord_3321561) baseStart_3321561 baseEnd_3321561 := by
    simpa [prefixWord, tailWord_3321561, baseEnd_3321561] using wordTrace_append hprefix tailTrace_3321561
  have hstable : (prefixWord ++ tailWord_3321561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321561).length < 2 ^ (prefixWord ++ tailWord_3321561).sum := by decide
  have hdescent : baseEnd_3321561 < baseStart_3321561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321584 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 4]
def baseStart_3321584 : Nat := 118140960795 + 3321584 * 2 ^ 59
def prefixEnd_3321584 : Nat := 4983230072969 + 3 ^ 40 * 3321584 * 2
def baseEnd_3321584 : Nat := 1705569126283837521024319

theorem tailTrace_3321584 : CollatzResearch.WordTrace tailWord_3321584 prefixEnd_3321584 1705569126283837521024319 := by
  unfold tailWord_3321584
  simp only [CollatzResearch.WordTrace]
  refine ⟨60574060599237962114365903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80765414132317282819154537 60574060599237962114365903)
  ·
    refine ⟨90861090898856943171548855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60574060599237962114365903 90861090898856943171548855)
    ·
      refine ⟨136291636348285414757323283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90861090898856943171548855 136291636348285414757323283)
      ·
        refine ⟨204437454522428122135984925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136291636348285414757323283 204437454522428122135984925)
        ·
          refine ⟨76664045445910545800994347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204437454522428122135984925 76664045445910545800994347)
          ·
            refine ⟨114996068168865818701491521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76664045445910545800994347 114996068168865818701491521)
            ·
              refine ⟨86247051126649364026118641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114996068168865818701491521 86247051126649364026118641)
              ·
                refine ⟨64685288344987023019588981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86247051126649364026118641 64685288344987023019588981)
                ·
                  refine ⟨6064245782342533408086467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64685288344987023019588981 6064245782342533408086467)
                  ·
                    refine ⟨9096368673513800112129701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6064245782342533408086467 9096368673513800112129701)
                    ·
                      refine ⟨1705569126283837521024319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9096368673513800112129701 1705569126283837521024319)
                      ·
                        rfl

theorem cell23_3321584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_3321584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321584 prefixEnd_3321584 := by exact prefixLift 3321584
  have htrace : WordTrace (prefixWord ++ tailWord_3321584) baseStart_3321584 baseEnd_3321584 := by
    simpa [prefixWord, tailWord_3321584, baseEnd_3321584] using wordTrace_append hprefix tailTrace_3321584
  have hstable : (prefixWord ++ tailWord_3321584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321584).length < 2 ^ (prefixWord ++ tailWord_3321584).sum := by decide
  have hdescent : baseEnd_3321584 < baseStart_3321584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321588 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3321588 : Nat := 118140960795 + 3321588 * 2 ^ 59
def prefixEnd_3321588 : Nat := 4983230072969 + 3 ^ 40 * 3321588 * 2
def baseEnd_3321588 : Nat := 1705571180206455505374301

theorem tailTrace_3321588 : CollatzResearch.WordTrace tailWord_3321588 prefixEnd_3321588 1705571180206455505374301 := by
  unfold tailWord_3321588
  simp only [CollatzResearch.WordTrace]
  refine ⟨60574133545230716455938709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80765511393640955274584945 60574133545230716455938709)
  ·
    refine ⟨2839412509932689833872127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60574133545230716455938709 2839412509932689833872127)
    ·
      refine ⟨4259118764899034750808191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2839412509932689833872127 4259118764899034750808191)
      ·
        refine ⟨6388678147348552126212287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4259118764899034750808191 6388678147348552126212287)
        ·
          refine ⟨9583017221022828189318431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6388678147348552126212287 9583017221022828189318431)
          ·
            refine ⟨14374525831534242283977647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9583017221022828189318431 14374525831534242283977647)
            ·
              refine ⟨21561788747301363425966471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14374525831534242283977647 21561788747301363425966471)
              ·
                refine ⟨32342683120952045138949707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21561788747301363425966471 32342683120952045138949707)
                ·
                  refine ⟨48514024681428067708424561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32342683120952045138949707 48514024681428067708424561)
                  ·
                    refine ⟨36385518511071050781318421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48514024681428067708424561 36385518511071050781318421)
                    ·
                      refine ⟨1705571180206455505374301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36385518511071050781318421 1705571180206455505374301)
                      ·
                        rfl

theorem cell23_3321588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3321588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321588 prefixEnd_3321588 := by exact prefixLift 3321588
  have htrace : WordTrace (prefixWord ++ tailWord_3321588) baseStart_3321588 baseEnd_3321588 := by
    simpa [prefixWord, tailWord_3321588, baseEnd_3321588] using wordTrace_append hprefix tailTrace_3321588
  have hstable : (prefixWord ++ tailWord_3321588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321588).length < 2 ^ (prefixWord ++ tailWord_3321588).sum := by decide
  have hdescent : baseEnd_3321588 < baseStart_3321588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321611 : List Nat := [1, 1, 1, 1, 5, 1, 2, 5, 2, 4]
def baseStart_3321611 : Nat := 118140960795 + 3321611 * 2 ^ 59
def prefixEnd_3321611 : Nat := 4983230072969 + 3 ^ 40 * 3321611 * 2
def baseEnd_3321611 : Nat := 568527663420502971795565

theorem tailTrace_3321611 : CollatzResearch.WordTrace tailWord_3321611 prefixEnd_3321611 568527663420502971795565 := by
  unfold tailWord_3321611
  simp only [CollatzResearch.WordTrace]
  refine ⟨121149105969378107839964687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80766070646252071893309791 121149105969378107839964687)
  ·
    refine ⟨181723658954067161759947031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121149105969378107839964687 181723658954067161759947031)
    ·
      refine ⟨272585488431100742639920547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181723658954067161759947031 272585488431100742639920547)
      ·
        refine ⟨408878232646651113959880821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272585488431100742639920547 408878232646651113959880821)
        ·
          refine ⟨38332334310623541933738827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 408878232646651113959880821 38332334310623541933738827)
          ·
            refine ⟨57498501465935312900608241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38332334310623541933738827 57498501465935312900608241)
            ·
              refine ⟨43123876099451484675456181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57498501465935312900608241 43123876099451484675456181)
              ·
                refine ⟨4042863384323576688324017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43123876099451484675456181 4042863384323576688324017)
                ·
                  refine ⟨3032147538242682516243013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4042863384323576688324017 3032147538242682516243013)
                  ·
                    refine ⟨568527663420502971795565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3032147538242682516243013 568527663420502971795565)
                    ·
                      rfl

theorem cell23_3321611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 4].length) (baseStart_3321611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321611 prefixEnd_3321611 := by exact prefixLift 3321611
  have htrace : WordTrace (prefixWord ++ tailWord_3321611) baseStart_3321611 baseEnd_3321611 := by
    simpa [prefixWord, tailWord_3321611, baseEnd_3321611] using wordTrace_append hprefix tailTrace_3321611
  have hstable : (prefixWord ++ tailWord_3321611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321611).length < 2 ^ (prefixWord ++ tailWord_3321611).sum := by decide
  have hdescent : baseEnd_3321611 < baseStart_3321611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321652 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_3321652 : Nat := 118140960795 + 3321652 * 2 ^ 59
def prefixEnd_3321652 : Nat := 4983230072969 + 3 ^ 40 * 3321652 * 2
def baseEnd_3321652 : Nat := 1705604042968343254974007

theorem tailTrace_3321652 : CollatzResearch.WordTrace tailWord_3321652 prefixEnd_3321652 1705604042968343254974007 := by
  unfold tailWord_3321652
  simp only [CollatzResearch.WordTrace]
  refine ⟨60575300681114785921103605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80767067574819714561471473 60575300681114785921103605)
  ·
    refine ⟨5678934438854511180103463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60575300681114785921103605 5678934438854511180103463)
    ·
      refine ⟨8518401658281766770155195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5678934438854511180103463 8518401658281766770155195)
      ·
        refine ⟨12777602487422650155232793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8518401658281766770155195 12777602487422650155232793)
        ·
          refine ⟨9583201865566987616424595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12777602487422650155232793 9583201865566987616424595)
          ·
            refine ⟨14374802798350481424636893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9583201865566987616424595 14374802798350481424636893)
            ·
              refine ⟨5390551049381430534238835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14374802798350481424636893 5390551049381430534238835)
              ·
                refine ⟨8085826574072145801358253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5390551049381430534238835 8085826574072145801358253)
                ·
                  refine ⟨3032184965277054675509345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8085826574072145801358253 3032184965277054675509345)
                  ·
                    refine ⟨2274138723957791006632009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3032184965277054675509345 2274138723957791006632009)
                    ·
                      refine ⟨1705604042968343254974007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2274138723957791006632009 1705604042968343254974007)
                      ·
                        rfl

theorem cell23_3321652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_3321652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321652 prefixEnd_3321652 := by exact prefixLift 3321652
  have htrace : WordTrace (prefixWord ++ tailWord_3321652) baseStart_3321652 baseEnd_3321652 := by
    simpa [prefixWord, tailWord_3321652, baseEnd_3321652] using wordTrace_append hprefix tailTrace_3321652
  have hstable : (prefixWord ++ tailWord_3321652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321652).length < 2 ^ (prefixWord ++ tailWord_3321652).sum := by decide
  have hdescent : baseEnd_3321652 < baseStart_3321652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321662 : List Nat := [4, 2, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_3321662 : Nat := 118140960795 + 3321662 * 2 ^ 59
def prefixEnd_3321662 : Nat := 4983230072969 + 3 ^ 40 * 3321662 * 2
def baseEnd_3321662 : Nat := 568536392591629405282987

theorem tailTrace_3321662 : CollatzResearch.WordTrace tailWord_3321662 prefixEnd_3321662 568536392591629405282987 := by
  unfold tailWord_3321662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15143870761524167943758905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80767310728128895700047493 15143870761524167943758905)
  ·
    refine ⟨11357903071143125957819179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15143870761524167943758905 11357903071143125957819179)
    ·
      refine ⟨17036854606714688936728769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11357903071143125957819179 17036854606714688936728769)
      ·
        refine ⟨12777640955036016702546577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17036854606714688936728769 12777640955036016702546577)
        ·
          refine ⟨9583230716277012526909933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12777640955036016702546577 9583230716277012526909933)
          ·
            refine ⟨3593711518603879697591225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9583230716277012526909933 3593711518603879697591225)
            ·
              refine ⟨2695283638952909773193419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3593711518603879697591225 2695283638952909773193419)
              ·
                refine ⟨4042925458429364659790129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695283638952909773193419 4042925458429364659790129)
                ·
                  refine ⟨3032194093822023494842597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4042925458429364659790129 3032194093822023494842597)
                  ·
                    refine ⟨568536392591629405282987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3032194093822023494842597 568536392591629405282987)
                    ·
                      rfl

theorem cell23_3321662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_3321662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321662 prefixEnd_3321662 := by exact prefixLift 3321662
  have htrace : WordTrace (prefixWord ++ tailWord_3321662) baseStart_3321662 baseEnd_3321662 := by
    simpa [prefixWord, tailWord_3321662, baseEnd_3321662] using wordTrace_append hprefix tailTrace_3321662
  have hstable : (prefixWord ++ tailWord_3321662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321662).length < 2 ^ (prefixWord ++ tailWord_3321662).sum := by decide
  have hdescent : baseEnd_3321662 < baseStart_3321662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321721 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 2, 2, 4]
def baseStart_3321721 : Nat := 118140960795 + 3321721 * 2 ^ 59
def prefixEnd_3321721 : Nat := 4983230072969 + 3 ^ 40 * 3321721 * 2
def baseEnd_3321721 : Nat := 1705639473133503485011189

theorem tailTrace_3321721 : CollatzResearch.WordTrace tailWord_3321721 prefixEnd_3321721 1705639473133503485011189 := by
  unfold tailWord_3321721
  simp only [CollatzResearch.WordTrace]
  refine ⟨121153117998979596626469017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80768745332653064417646011 121153117998979596626469017)
  ·
    refine ⟨90864838499234697469851763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121153117998979596626469017 90864838499234697469851763)
    ·
      refine ⟨136297257748852046204777645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90864838499234697469851763 136297257748852046204777645)
      ·
        refine ⟨51111471655819517326791617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136297257748852046204777645 51111471655819517326791617)
        ·
          refine ⟨38333603741864637995093713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51111471655819517326791617 38333603741864637995093713)
          ·
            refine ⟨28750202806398478496320285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38333603741864637995093713 28750202806398478496320285)
            ·
              refine ⟨10781326052399429436120107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28750202806398478496320285 10781326052399429436120107)
              ·
                refine ⟨16171989078599144154180161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10781326052399429436120107 16171989078599144154180161)
                ·
                  refine ⟨12128991808949358115635121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16171989078599144154180161 12128991808949358115635121)
                  ·
                    refine ⟨9096743856712018586726341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12128991808949358115635121 9096743856712018586726341)
                    ·
                      refine ⟨1705639473133503485011189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9096743856712018586726341 1705639473133503485011189)
                      ·
                        rfl

theorem cell23_3321721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_3321721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321721 prefixEnd_3321721 := by exact prefixLift 3321721
  have htrace : WordTrace (prefixWord ++ tailWord_3321721) baseStart_3321721 baseEnd_3321721 := by
    simpa [prefixWord, tailWord_3321721, baseEnd_3321721] using wordTrace_append hprefix tailTrace_3321721
  have hstable : (prefixWord ++ tailWord_3321721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321721).length < 2 ^ (prefixWord ++ tailWord_3321721).sum := by decide
  have hdescent : baseEnd_3321721 < baseStart_3321721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321731 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 7]
def baseStart_3321731 : Nat := 118140960795 + 3321731 * 2 ^ 59
def prefixEnd_3321731 : Nat := 4983230072969 + 3 ^ 40 * 3321731 * 2
def baseEnd_3321731 : Nat := 189516067548894271765127

theorem tailTrace_3321731 : CollatzResearch.WordTrace tailWord_3321731 prefixEnd_3321731 189516067548894271765127 := by
  unfold tailWord_3321731
  simp only [CollatzResearch.WordTrace]
  refine ⟨121153482728943368334333047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80768988485962245556222031 121153482728943368334333047)
  ·
    refine ⟨181730224093415052501499571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121153482728943368334333047 181730224093415052501499571)
    ·
      refine ⟨272595336140122578752249357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181730224093415052501499571 272595336140122578752249357)
      ·
        refine ⟨102223251052545967032093509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272595336140122578752249357 102223251052545967032093509)
        ·
          refine ⟨19166859572352368818517533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102223251052545967032093509 19166859572352368818517533)
          ·
            refine ⟨7187572339632138306944075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19166859572352368818517533 7187572339632138306944075)
            ·
              refine ⟨10781358509448207460416113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7187572339632138306944075 10781358509448207460416113)
              ·
                refine ⟨8086018882086155595312085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10781358509448207460416113 8086018882086155595312085)
                ·
                  refine ⟨189516067548894271765127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8086018882086155595312085 189516067548894271765127)
                  ·
                    rfl

theorem cell23_3321731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 7].length) (baseStart_3321731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321731 prefixEnd_3321731 := by exact prefixLift 3321731
  have htrace : WordTrace (prefixWord ++ tailWord_3321731) baseStart_3321731 baseEnd_3321731 := by
    simpa [prefixWord, tailWord_3321731, baseEnd_3321731] using wordTrace_append hprefix tailTrace_3321731
  have hstable : (prefixWord ++ tailWord_3321731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321731).length < 2 ^ (prefixWord ++ tailWord_3321731).sum := by decide
  have hdescent : baseEnd_3321731 < baseStart_3321731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321759 : List Nat := [1, 1, 2, 5, 3, 2, 1, 2, 2, 2, 2]
def baseStart_3321759 : Nat := 118140960795 + 3321759 * 2 ^ 59
def prefixEnd_3321759 : Nat := 4983230072969 + 3 ^ 40 * 3321759 * 2
def baseEnd_3321759 : Nat := 1705658985398374336336015

theorem tailTrace_3321759 : CollatzResearch.WordTrace tailWord_3321759 prefixEnd_3321759 1705658985398374336336015 := by
  unfold tailWord_3321759
  simp only [CollatzResearch.WordTrace]
  refine ⟨121154503972841929116352331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80769669315227952744234887 121154503972841929116352331)
  ·
    refine ⟨181731755959262893674528497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121154503972841929116352331 181731755959262893674528497)
    ·
      refine ⟨136298816969447170255896373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181731755959262893674528497 136298816969447170255896373)
      ·
        refine ⟨12778014090885672211490285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136298816969447170255896373 12778014090885672211490285)
        ·
          refine ⟨4791755284082127079308857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12778014090885672211490285 4791755284082127079308857)
          ·
            refine ⟨3593816463061595309481643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4791755284082127079308857 3593816463061595309481643)
            ·
              refine ⟨5390724694592392964222465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3593816463061595309481643 5390724694592392964222465)
              ·
                refine ⟨4043043520944294723166849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5390724694592392964222465 4043043520944294723166849)
                ·
                  refine ⟨3032282640708221042375137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4043043520944294723166849 3032282640708221042375137)
                  ·
                    refine ⟨2274211980531165781781353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3032282640708221042375137 2274211980531165781781353)
                    ·
                      refine ⟨1705658985398374336336015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2274211980531165781781353 1705658985398374336336015)
                      ·
                        rfl

theorem cell23_3321759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_3321759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321759 prefixEnd_3321759 := by exact prefixLift 3321759
  have htrace : WordTrace (prefixWord ++ tailWord_3321759) baseStart_3321759 baseEnd_3321759 := by
    simpa [prefixWord, tailWord_3321759, baseEnd_3321759] using wordTrace_append hprefix tailTrace_3321759
  have hstable : (prefixWord ++ tailWord_3321759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321759).length < 2 ^ (prefixWord ++ tailWord_3321759).sum := by decide
  have hdescent : baseEnd_3321759 < baseStart_3321759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321825 : List Nat := [1, 2, 3, 1, 2, 1, 2, 6, 1, 4]
def baseStart_3321825 : Nat := 118140960795 + 3321825 * 2 ^ 59
def prefixEnd_3321825 : Nat := 4983230072969 + 3 ^ 40 * 3321825 * 2
def baseEnd_3321825 : Nat := 568564291707190359370237

theorem tailTrace_3321825 : CollatzResearch.WordTrace tailWord_3321825 prefixEnd_3321825 568564291707190359370237 := by
  unfold tailWord_3321825
  simp only [CollatzResearch.WordTrace]
  refine ⟨121156911190602822388254929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80771274127068548258836619 121156911190602822388254929)
  ·
    refine ⟨90867683392952116791191197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121156911190602822388254929 90867683392952116791191197)
    ·
      refine ⟨34075381272357043796696699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90867683392952116791191197 34075381272357043796696699)
      ·
        refine ⟨51113071908535565695045049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34075381272357043796696699 51113071908535565695045049)
        ·
          refine ⟨38334803931401674271283787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51113071908535565695045049 38334803931401674271283787)
          ·
            refine ⟨57502205897102511406925681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38334803931401674271283787 57502205897102511406925681)
            ·
              refine ⟨43126654422826883555194261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57502205897102511406925681 43126654422826883555194261)
              ·
                refine ⟨2021561926070010166649731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43126654422826883555194261 2021561926070010166649731)
                ·
                  refine ⟨3032342889105015249974597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021561926070010166649731 3032342889105015249974597)
                  ·
                    refine ⟨568564291707190359370237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3032342889105015249974597 568564291707190359370237)
                    ·
                      rfl

theorem cell23_3321825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_3321825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321825 prefixEnd_3321825 := by exact prefixLift 3321825
  have htrace : WordTrace (prefixWord ++ tailWord_3321825) baseStart_3321825 baseEnd_3321825 := by
    simpa [prefixWord, tailWord_3321825, baseEnd_3321825] using wordTrace_append hprefix tailTrace_3321825
  have hstable : (prefixWord ++ tailWord_3321825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321825).length < 2 ^ (prefixWord ++ tailWord_3321825).sum := by decide
  have hdescent : baseEnd_3321825 < baseStart_3321825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321875 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 2, 3, 2]
def baseStart_3321875 : Nat := 118140960795 + 3321875 * 2 ^ 59
def prefixEnd_3321875 : Nat := 4983230072969 + 3 ^ 40 * 3321875 * 2
def baseEnd_3321875 : Nat := 1705718549154295882485481

theorem tailTrace_3321875 : CollatzResearch.WordTrace tailWord_3321875 prefixEnd_3321875 1705718549154295882485481 := by
  unfold tailWord_3321875
  simp only [CollatzResearch.WordTrace]
  refine ⟨121158734840421680927575079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80772489893614453951716719 121158734840421680927575079)
  ·
    refine ⟨181738102260632521391362619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121158734840421680927575079 181738102260632521391362619)
    ·
      refine ⟨272607153390948782087043929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181738102260632521391362619 272607153390948782087043929)
      ·
        refine ⟨204455365043211586565282947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272607153390948782087043929 204455365043211586565282947)
        ·
          refine ⟨306683047564817379847924421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204455365043211586565282947 306683047564817379847924421)
          ·
            refine ⟨57503071418403258721485829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 306683047564817379847924421 57503071418403258721485829)
            ·
              refine ⟨10781825890950611010278593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57503071418403258721485829 10781825890950611010278593)
              ·
                refine ⟨8086369418212958257708945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10781825890950611010278593 8086369418212958257708945)
                ·
                  refine ⟨6064777063659718693281709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8086369418212958257708945 6064777063659718693281709)
                  ·
                    refine ⟨2274291398872394509980641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6064777063659718693281709 2274291398872394509980641)
                    ·
                      refine ⟨1705718549154295882485481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2274291398872394509980641 1705718549154295882485481)
                      ·
                        rfl

theorem cell23_3321875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 3, 2].length) (baseStart_3321875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321875 prefixEnd_3321875 := by exact prefixLift 3321875
  have htrace : WordTrace (prefixWord ++ tailWord_3321875) baseStart_3321875 baseEnd_3321875 := by
    simpa [prefixWord, tailWord_3321875, baseEnd_3321875] using wordTrace_append hprefix tailTrace_3321875
  have hstable : (prefixWord ++ tailWord_3321875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321875).length < 2 ^ (prefixWord ++ tailWord_3321875).sum := by decide
  have hdescent : baseEnd_3321875 < baseStart_3321875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321876 : List Nat := [2, 4, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_3321876 : Nat := 118140960795 + 3321876 * 2 ^ 59
def prefixEnd_3321876 : Nat := 4983230072969 + 3 ^ 40 * 3321876 * 2
def baseEnd_3321876 : Nat := 568573020878316792857659

theorem tailTrace_3321876 : CollatzResearch.WordTrace tailWord_3321876 prefixEnd_3321876 568573020878316792857659 := by
  unfold tailWord_3321876
  simp only [CollatzResearch.WordTrace]
  refine ⟨60579385656709029049180741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80772514208945372065574321 60579385656709029049180741)
  ·
    refine ⟨11358634810632942946721389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60579385656709029049180741 11358634810632942946721389)
    ·
      refine ⟨4259488053987353605020521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11358634810632942946721389 4259488053987353605020521)
      ·
        refine ⟨3194616040490515203765391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4259488053987353605020521 3194616040490515203765391)
        ·
          refine ⟨4791924060735772805648087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3194616040490515203765391 4791924060735772805648087)
          ·
            refine ⟨7187886091103659208472131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4791924060735772805648087 7187886091103659208472131)
            ·
              refine ⟨10781829136655488812708197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7187886091103659208472131 10781829136655488812708197)
              ·
                refine ⟨2021592963122904152382787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10781829136655488812708197 2021592963122904152382787)
                ·
                  refine ⟨3032389444684356228574181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021592963122904152382787 3032389444684356228574181)
                  ·
                    refine ⟨568573020878316792857659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3032389444684356228574181 568573020878316792857659)
                    ·
                      rfl

theorem cell23_3321876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_3321876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321876 prefixEnd_3321876 := by exact prefixLift 3321876
  have htrace : WordTrace (prefixWord ++ tailWord_3321876) baseStart_3321876 baseEnd_3321876 := by
    simpa [prefixWord, tailWord_3321876, baseEnd_3321876] using wordTrace_append hprefix tailTrace_3321876
  have hstable : (prefixWord ++ tailWord_3321876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321876).length < 2 ^ (prefixWord ++ tailWord_3321876).sum := by decide
  have hdescent : baseEnd_3321876 < baseStart_3321876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321881 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 5, 6]
def baseStart_3321881 : Nat := 118140960795 + 3321881 * 2 ^ 59
def prefixEnd_3321881 : Nat := 4983230072969 + 3 ^ 40 * 3321881 * 2
def baseEnd_3321881 : Nat := 568573876679407619670151

theorem tailTrace_3321881 : CollatzResearch.WordTrace tailWord_3321881 prefixEnd_3321881 568573876679407619670151 := by
  unfold tailWord_3321881
  simp only [CollatzResearch.WordTrace]
  refine ⟨121158953678399943952293497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80772635785599962634862331 121158953678399943952293497)
  ·
    refine ⟨90869215258799957964220123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121158953678399943952293497 90869215258799957964220123)
    ·
      refine ⟨136303822888199936946330185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90869215258799957964220123 136303822888199936946330185)
      ·
        refine ⟨102227867166149952709747639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136303822888199936946330185 102227867166149952709747639)
        ·
          refine ⟨153341800749224929064621459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102227867166149952709747639 153341800749224929064621459)
          ·
            refine ⟨230012701123837393596932189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153341800749224929064621459 230012701123837393596932189)
            ·
              refine ⟨86254762921439022598849571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230012701123837393596932189 86254762921439022598849571)
              ·
                refine ⟨129382144382158533898274357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86254762921439022598849571 129382144382158533898274357)
                ·
                  refine ⟨12129576035827362552963221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129382144382158533898274357 12129576035827362552963221)
                  ·
                    refine ⟨568573876679407619670151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12129576035827362552963221 568573876679407619670151)
                    ·
                      rfl

theorem cell23_3321881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 6].length) (baseStart_3321881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321881 prefixEnd_3321881 := by exact prefixLift 3321881
  have htrace : WordTrace (prefixWord ++ tailWord_3321881) baseStart_3321881 baseEnd_3321881 := by
    simpa [prefixWord, tailWord_3321881, baseEnd_3321881] using wordTrace_append hprefix tailTrace_3321881
  have hstable : (prefixWord ++ tailWord_3321881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321881).length < 2 ^ (prefixWord ++ tailWord_3321881).sum := by decide
  have hdescent : baseEnd_3321881 < baseStart_3321881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321911 : List Nat := [1, 1, 3, 1, 2, 2, 2, 11]
def baseStart_3321911 : Nat := 118140960795 + 3321911 * 2 ^ 59
def prefixEnd_3321911 : Nat := 4983230072969 + 3 ^ 40 * 3321911 * 2
def baseEnd_3321911 : Nat := 63175445720661397838345

theorem tailTrace_3321911 : CollatzResearch.WordTrace tailWord_3321911 prefixEnd_3321911 63175445720661397838345 := by
  unfold tailWord_3321911
  simp only [CollatzResearch.WordTrace]
  refine ⟨121160047868291259075885587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80773365245527506050590391 121160047868291259075885587)
  ·
    refine ⟨181740071802436888613828381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121160047868291259075885587 181740071802436888613828381)
    ·
      refine ⟨68152526925913833230185643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181740071802436888613828381 68152526925913833230185643)
      ·
        refine ⟨102228790388870749845278465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68152526925913833230185643 102228790388870749845278465)
        ·
          refine ⟨76671592791653062383958849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102228790388870749845278465 76671592791653062383958849)
          ·
            refine ⟨57503694593739796787969137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76671592791653062383958849 57503694593739796787969137)
            ·
              refine ⟨43127770945304847590976853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57503694593739796787969137 43127770945304847590976853)
              ·
                refine ⟨63175445720661397838345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 43127770945304847590976853 63175445720661397838345)
                ·
                  rfl

theorem cell23_3321911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 11].length) (baseStart_3321911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321911 prefixEnd_3321911 := by exact prefixLift 3321911
  have htrace : WordTrace (prefixWord ++ tailWord_3321911) baseStart_3321911 baseEnd_3321911 := by
    simpa [prefixWord, tailWord_3321911, baseEnd_3321911] using wordTrace_append hprefix tailTrace_3321911
  have hstable : (prefixWord ++ tailWord_3321911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321911).length < 2 ^ (prefixWord ++ tailWord_3321911).sum := by decide
  have hdescent : baseEnd_3321911 < baseStart_3321911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321942 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3321942 : Nat := 118140960795 + 3321942 * 2 ^ 59
def prefixEnd_3321942 : Nat := 4983230072969 + 3 ^ 40 * 3321942 * 2
def baseEnd_3321942 : Nat := 1705752952358147120347673

theorem tailTrace_3321942 : CollatzResearch.WordTrace tailWord_3321942 prefixEnd_3321942 1705752952358147120347673 := by
  unfold tailWord_3321942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7572573658198684460641505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80774119020785967580176053 7572573658198684460641505)
  ·
    refine ⟨5679430243649013345481129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7572573658198684460641505 5679430243649013345481129)
    ·
      refine ⟨4259572682736760009110847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5679430243649013345481129 4259572682736760009110847)
      ·
        refine ⟨6389359024105140013666271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4259572682736760009110847 6389359024105140013666271)
        ·
          refine ⟨9584038536157710020499407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6389359024105140013666271 9584038536157710020499407)
          ·
            refine ⟨14376057804236565030749111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9584038536157710020499407 14376057804236565030749111)
            ·
              refine ⟨21564086706354847546123667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14376057804236565030749111 21564086706354847546123667)
              ·
                refine ⟨32346130059532271319185501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21564086706354847546123667 32346130059532271319185501)
                ·
                  refine ⟨12129798772324601744694563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32346130059532271319185501 12129798772324601744694563)
                  ·
                    refine ⟨18194698158486902617041845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12129798772324601744694563 18194698158486902617041845)
                    ·
                      refine ⟨1705752952358147120347673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18194698158486902617041845 1705752952358147120347673)
                      ·
                        rfl

theorem cell23_3321942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3321942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321942 prefixEnd_3321942 := by exact prefixLift 3321942
  have htrace : WordTrace (prefixWord ++ tailWord_3321942) baseStart_3321942 baseEnd_3321942 := by
    simpa [prefixWord, tailWord_3321942, baseEnd_3321942] using wordTrace_append hprefix tailTrace_3321942
  have hstable : (prefixWord ++ tailWord_3321942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321942).length < 2 ^ (prefixWord ++ tailWord_3321942).sum := by decide
  have hdescent : baseEnd_3321942 < baseStart_3321942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321955 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 3]
def baseStart_3321955 : Nat := 118140960795 + 3321955 * 2 ^ 59
def prefixEnd_3321955 : Nat := 4983230072969 + 3 ^ 40 * 3321955 * 2
def baseEnd_3321955 : Nat := 1705759627606655569485113

theorem tailTrace_3321955 : CollatzResearch.WordTrace tailWord_3321955 prefixEnd_3321955 1705759627606655569485113 := by
  unfold tailWord_3321955
  simp only [CollatzResearch.WordTrace]
  refine ⟨121161652680131854590487319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80774435120087903060324879 121161652680131854590487319)
  ·
    refine ⟨181742479020197781885730979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121161652680131854590487319 181742479020197781885730979)
    ·
      refine ⟨272613718530296672828596469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181742479020197781885730979 272613718530296672828596469)
      ·
        refine ⟨25557536112215313077680919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272613718530296672828596469 25557536112215313077680919)
        ·
          refine ⟨38336304168322969616521379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25557536112215313077680919 38336304168322969616521379)
          ·
            refine ⟨57504456252484454424782069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38336304168322969616521379 57504456252484454424782069)
            ·
              refine ⟨5391042773670417602323319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57504456252484454424782069 5391042773670417602323319)
              ·
                refine ⟨8086564160505626403484979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5391042773670417602323319 8086564160505626403484979)
                ·
                  refine ⟨12129846240758439605227469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8086564160505626403484979 12129846240758439605227469)
                  ·
                    refine ⟨4548692340284414851960301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12129846240758439605227469 4548692340284414851960301)
                    ·
                      refine ⟨1705759627606655569485113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4548692340284414851960301 1705759627606655569485113)
                      ·
                        rfl

theorem cell23_3321955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_3321955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321955 prefixEnd_3321955 := by exact prefixLift 3321955
  have htrace : WordTrace (prefixWord ++ tailWord_3321955) baseStart_3321955 baseEnd_3321955 := by
    simpa [prefixWord, tailWord_3321955, baseEnd_3321955] using wordTrace_append hprefix tailTrace_3321955
  have hstable : (prefixWord ++ tailWord_3321955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321955).length < 2 ^ (prefixWord ++ tailWord_3321955).sum := by decide
  have hdescent : baseEnd_3321955 < baseStart_3321955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
