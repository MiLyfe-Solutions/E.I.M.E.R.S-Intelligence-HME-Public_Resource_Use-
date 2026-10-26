import V185TrunkScan23Chunk1323

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7842296 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 1, 6]
def baseStart_7842296 : Nat := 118140960795 + 7842296 * 2 ^ 59
def prefixEnd_7842296 : Nat := 4983230072969 + 3 ^ 40 * 7842296 * 2
def baseEnd_7842296 : Nat := 1342289094277384738177981

theorem tailTrace_7842296 : CollatzResearch.WordTrace tailWord_7842296 prefixEnd_7842296 1342289094277384738177981 := by
  unfold tailWord_7842296
  simp only [CollatzResearch.WordTrace]
  refine ⟨143016016798354212185105371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190688022397805616246807161 143016016798354212185105371)
  ·
    refine ⟨214524025197531318277658057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143016016798354212185105371 214524025197531318277658057)
    ·
      refine ⟨160893018898148488708243543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214524025197531318277658057 160893018898148488708243543)
      ·
        refine ⟨241339528347222733062365315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160893018898148488708243543 241339528347222733062365315)
        ·
          refine ⟨362009292520834099593547973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241339528347222733062365315 362009292520834099593547973)
          ·
            refine ⟨67876742347656393673790245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 362009292520834099593547973 67876742347656393673790245)
            ·
              refine ⟨12726889190185573813835671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67876742347656393673790245 12726889190185573813835671)
              ·
                refine ⟨19090333785278360720753507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12726889190185573813835671 19090333785278360720753507)
                ·
                  refine ⟨28635500677917541081130261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19090333785278360720753507 28635500677917541081130261)
                  ·
                    refine ⟨1342289094277384738177981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28635500677917541081130261 1342289094277384738177981)
                    ·
                      rfl

theorem cell23_7842296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_7842296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842296 prefixEnd_7842296 := by exact prefixLift 7842296
  have htrace : WordTrace (prefixWord ++ tailWord_7842296) baseStart_7842296 baseEnd_7842296 := by
    simpa [prefixWord, tailWord_7842296, baseEnd_7842296] using wordTrace_append hprefix tailTrace_7842296
  have hstable : (prefixWord ++ tailWord_7842296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842296).length < 2 ^ (prefixWord ++ tailWord_7842296).sum := by decide
  have hdescent : baseEnd_7842296 < baseStart_7842296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842309 : List Nat := [1, 3, 1, 1, 2, 2, 2, 11]
def baseStart_7842309 : Nat := 118140960795 + 7842309 * 2 ^ 59
def prefixEnd_7842309 : Nat := 4983230072969 + 3 ^ 40 * 7842309 * 2
def baseEnd_7842309 : Nat := 149143479928913431987829

theorem tailTrace_7842309 : CollatzResearch.WordTrace tailWord_7842309 prefixEnd_7842309 149143479928913431987829 := by
  unfold tailWord_7842309
  simp only [CollatzResearch.WordTrace]
  refine ⟨286032507745661327590433981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190688338497107551726955987 286032507745661327590433981)
  ·
    refine ⟨107262190404622997846412743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286032507745661327590433981 107262190404622997846412743)
    ·
      refine ⟨160893285606934496769619115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107262190404622997846412743 160893285606934496769619115)
      ·
        refine ⟨241339928410401745154428673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160893285606934496769619115 241339928410401745154428673)
        ·
          refine ⟨181004946307801308865821505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241339928410401745154428673 181004946307801308865821505)
          ·
            refine ⟨135753709730850981649366129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181004946307801308865821505 135753709730850981649366129)
            ·
              refine ⟨101815282298138236237024597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135753709730850981649366129 101815282298138236237024597)
              ·
                refine ⟨149143479928913431987829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 101815282298138236237024597 149143479928913431987829)
                ·
                  rfl

theorem cell23_7842309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 11].length) (baseStart_7842309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842309 prefixEnd_7842309 := by exact prefixLift 7842309
  have htrace : WordTrace (prefixWord ++ tailWord_7842309) baseStart_7842309 baseEnd_7842309 := by
    simpa [prefixWord, tailWord_7842309, baseEnd_7842309] using wordTrace_append hprefix tailTrace_7842309
  have hstable : (prefixWord ++ tailWord_7842309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842309).length < 2 ^ (prefixWord ++ tailWord_7842309).sum := by decide
  have hdescent : baseEnd_7842309 < baseStart_7842309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842317 : List Nat := [1, 7, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_7842317 : Nat := 118140960795 + 7842317 * 2 ^ 59
def prefixEnd_7842317 : Nat := 4983230072969 + 3 ^ 40 * 7842317 * 2
def baseEnd_7842317 : Nat := 1342292688641966210790449

theorem tailTrace_7842317 : CollatzResearch.WordTrace tailWord_7842317 prefixEnd_7842317 1342292688641966210790449 := by
  unfold tailWord_7842317
  simp only [CollatzResearch.WordTrace]
  refine ⟨286032799529632344956725205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190688533019754896637816803 286032799529632344956725205)
  ·
    refine ⟨6703893738975758084923247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 286032799529632344956725205 6703893738975758084923247)
    ·
      refine ⟨10055840608463637127384871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6703893738975758084923247 10055840608463637127384871)
      ·
        refine ⟨15083760912695455691077307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10055840608463637127384871 15083760912695455691077307)
        ·
          refine ⟨22625641369043183536615961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15083760912695455691077307 22625641369043183536615961)
          ·
            refine ⟨16969231026782387652461971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22625641369043183536615961 16969231026782387652461971)
            ·
              refine ⟨25453846540173581478692957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16969231026782387652461971 25453846540173581478692957)
              ·
                refine ⟨9545192452565093054509859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25453846540173581478692957 9545192452565093054509859)
                ·
                  refine ⟨14317788678847639581764789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9545192452565093054509859 14317788678847639581764789)
                  ·
                    refine ⟨1342292688641966210790449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14317788678847639581764789 1342292688641966210790449)
                    ·
                      rfl

theorem cell23_7842317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_7842317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842317 prefixEnd_7842317 := by exact prefixLift 7842317
  have htrace : WordTrace (prefixWord ++ tailWord_7842317) baseStart_7842317 baseEnd_7842317 := by
    simpa [prefixWord, tailWord_7842317, baseEnd_7842317] using wordTrace_append hprefix tailTrace_7842317
  have hstable : (prefixWord ++ tailWord_7842317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842317).length < 2 ^ (prefixWord ++ tailWord_7842317).sum := by decide
  have hdescent : baseEnd_7842317 < baseStart_7842317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842323 : List Nat := [1, 1, 1, 2, 1, 5, 3, 3, 1, 2, 3]
def baseStart_7842323 : Nat := 118140960795 + 7842323 * 2 ^ 59
def prefixEnd_7842323 : Nat := 4983230072969 + 3 ^ 40 * 7842323 * 2
def baseEnd_7842323 : Nat := 4026881146809825608896319

theorem tailTrace_7842323 : CollatzResearch.WordTrace tailWord_7842323 prefixEnd_7842323 4026881146809825608896319 := by
  unfold tailWord_7842323
  simp only [CollatzResearch.WordTrace]
  refine ⟨286033018367610607981443623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190688678911740405320962415 286033018367610607981443623)
  ·
    refine ⟨429049527551415911972165435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286033018367610607981443623 429049527551415911972165435)
    ·
      refine ⟨643574291327123867958248153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429049527551415911972165435 643574291327123867958248153)
      ·
        refine ⟨482680718495342900968686115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643574291327123867958248153 482680718495342900968686115)
        ·
          refine ⟨724021077743014351453029173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482680718495342900968686115 724021077743014351453029173)
          ·
            refine ⟨67876976038407595448721485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 724021077743014351453029173 67876976038407595448721485)
            ·
              refine ⟨25453866014402848293270557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67876976038407595448721485 25453866014402848293270557)
              ·
                refine ⟨9545199755401068109976459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25453866014402848293270557 9545199755401068109976459)
                ·
                  refine ⟨14317799633101602164964689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9545199755401068109976459 14317799633101602164964689)
                  ·
                    refine ⟨10738349724826201623723517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14317799633101602164964689 10738349724826201623723517)
                    ·
                      refine ⟨4026881146809825608896319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10738349724826201623723517 4026881146809825608896319)
                      ·
                        rfl

theorem cell23_7842323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 2, 3].length) (baseStart_7842323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842323 prefixEnd_7842323 := by exact prefixLift 7842323
  have htrace : WordTrace (prefixWord ++ tailWord_7842323) baseStart_7842323 baseEnd_7842323 := by
    simpa [prefixWord, tailWord_7842323, baseEnd_7842323] using wordTrace_append hprefix tailTrace_7842323
  have hstable : (prefixWord ++ tailWord_7842323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842323).length < 2 ^ (prefixWord ++ tailWord_7842323).sum := by decide
  have hdescent : baseEnd_7842323 < baseStart_7842323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842337 : List Nat := [1, 2, 3, 2, 2, 1, 1, 6, 1, 2, 2]
def baseStart_7842337 : Nat := 118140960795 + 7842337 * 2 ^ 59
def prefixEnd_7842337 : Nat := 4983230072969 + 3 ^ 40 * 7842337 * 2
def baseEnd_7842337 : Nat := 4026888335538988554121255

theorem tailTrace_7842337 : CollatzResearch.WordTrace tailWord_7842337 prefixEnd_7842337 4026888335538988554121255 := by
  unfold tailWord_7842337
  simp only [CollatzResearch.WordTrace]
  refine ⟨286033528989559888372453265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190689019326373258914968843 286033528989559888372453265)
  ·
    refine ⟨214525146742169916279339949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286033528989559888372453265 214525146742169916279339949)
    ·
      refine ⟨80446930028313718604752481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214525146742169916279339949 80446930028313718604752481)
      ·
        refine ⟨60335197521235288953564361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80446930028313718604752481 60335197521235288953564361)
        ·
          refine ⟨45251398140926466715173271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60335197521235288953564361 45251398140926466715173271)
          ·
            refine ⟨67877097211389700072759907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45251398140926466715173271 67877097211389700072759907)
            ·
              refine ⟨101815645817084550109139861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67877097211389700072759907 101815645817084550109139861)
              ·
                refine ⟨4772608397675838286365931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101815645817084550109139861 4772608397675838286365931)
                ·
                  refine ⟨7158912596513757429548897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4772608397675838286365931 7158912596513757429548897)
                  ·
                    refine ⟨5369184447385318072161673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7158912596513757429548897 5369184447385318072161673)
                    ·
                      refine ⟨4026888335538988554121255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5369184447385318072161673 4026888335538988554121255)
                      ·
                        rfl

theorem cell23_7842337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_7842337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842337 prefixEnd_7842337 := by exact prefixLift 7842337
  have htrace : WordTrace (prefixWord ++ tailWord_7842337) baseStart_7842337 baseEnd_7842337 := by
    simpa [prefixWord, tailWord_7842337, baseEnd_7842337] using wordTrace_append hprefix tailTrace_7842337
  have hstable : (prefixWord ++ tailWord_7842337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842337).length < 2 ^ (prefixWord ++ tailWord_7842337).sum := by decide
  have hdescent : baseEnd_7842337 < baseStart_7842337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842340 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 1, 1, 5]
def baseStart_7842340 : Nat := 118140960795 + 7842340 * 2 ^ 59
def prefixEnd_7842340 : Nat := 4983230072969 + 3 ^ 40 * 7842340 * 2
def baseEnd_7842340 : Nat := 4026889875980952042383741

theorem tailTrace_7842340 : CollatzResearch.WordTrace tailWord_7842340 prefixEnd_7842340 4026889875980952042383741 := by
  unfold tailWord_7842340
  simp only [CollatzResearch.WordTrace]
  refine ⟨143016819204274509942406237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190689092272366013256541649 143016819204274509942406237)
  ·
    refine ⟨53631307201602941228402339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143016819204274509942406237 53631307201602941228402339)
    ·
      refine ⟨80446960802404411842603509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53631307201602941228402339 80446960802404411842603509)
      ·
        refine ⟨7541902575225413610244079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80446960802404411842603509 7541902575225413610244079)
        ·
          refine ⟨11312853862838120415366119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7541902575225413610244079 11312853862838120415366119)
          ·
            refine ⟨16969280794257180623049179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11312853862838120415366119 16969280794257180623049179)
            ·
              refine ⟨25453921191385770934573769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16969280794257180623049179 25453921191385770934573769)
              ·
                refine ⟨19090440893539328200930327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25453921191385770934573769 19090440893539328200930327)
                ·
                  refine ⟨28635661340308992301395491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19090440893539328200930327 28635661340308992301395491)
                  ·
                    refine ⟨42953492010463488452093237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28635661340308992301395491 42953492010463488452093237)
                    ·
                      refine ⟨4026889875980952042383741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42953492010463488452093237 4026889875980952042383741)
                      ·
                        rfl

theorem cell23_7842340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_7842340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842340 prefixEnd_7842340 := by exact prefixLift 7842340
  have htrace : WordTrace (prefixWord ++ tailWord_7842340) baseStart_7842340 baseEnd_7842340 := by
    simpa [prefixWord, tailWord_7842340, baseEnd_7842340] using wordTrace_append hprefix tailTrace_7842340
  have hstable : (prefixWord ++ tailWord_7842340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842340).length < 2 ^ (prefixWord ++ tailWord_7842340).sum := by decide
  have hdescent : baseEnd_7842340 < baseStart_7842340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842353 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 1, 3, 3]
def baseStart_7842353 : Nat := 118140960795 + 7842353 * 2 ^ 59
def prefixEnd_7842353 : Nat := 4983230072969 + 3 ^ 40 * 7842353 * 2
def baseEnd_7842353 : Nat := 4026896551229460491521181

theorem tailTrace_7842353 : CollatzResearch.WordTrace tailWord_7842353 prefixEnd_7842353 4026896551229460491521181 := by
  unfold tailWord_7842353
  simp only [CollatzResearch.WordTrace]
  refine ⟨286034112557501923105035713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190689408371667948736690475 286034112557501923105035713)
  ·
    refine ⟨214525584418126442328776785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286034112557501923105035713 214525584418126442328776785)
    ·
      refine ⟨160894188313594831746582589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214525584418126442328776785 160894188313594831746582589)
      ·
        refine ⟨60335320617598061904968471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160894188313594831746582589 60335320617598061904968471)
        ·
          refine ⟨90502980926397092857452707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60335320617598061904968471 90502980926397092857452707)
          ·
            refine ⟨135754471389595639286179061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90502980926397092857452707 135754471389595639286179061)
            ·
              refine ⟨12726981692774591183079287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135754471389595639286179061 12726981692774591183079287)
              ·
                refine ⟨19090472539161886774618931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12726981692774591183079287 19090472539161886774618931)
                ·
                  refine ⟨28635708808742830161928397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19090472539161886774618931 28635708808742830161928397)
                  ·
                    refine ⟨10738390803278561310723149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28635708808742830161928397 10738390803278561310723149)
                    ·
                      refine ⟨4026896551229460491521181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10738390803278561310723149 4026896551229460491521181)
                      ·
                        rfl

theorem cell23_7842353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_7842353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842353 prefixEnd_7842353 := by exact prefixLift 7842353
  have htrace : WordTrace (prefixWord ++ tailWord_7842353) baseStart_7842353 baseEnd_7842353 := by
    simpa [prefixWord, tailWord_7842353, baseEnd_7842353] using wordTrace_append hprefix tailTrace_7842353
  have hstable : (prefixWord ++ tailWord_7842353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842353).length < 2 ^ (prefixWord ++ tailWord_7842353).sum := by decide
  have hdescent : baseEnd_7842353 < baseStart_7842353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842380 : List Nat := [2, 2, 1, 3, 1, 2, 1, 5, 1, 3, 2]
def baseStart_7842380 : Nat := 118140960795 + 7842380 * 2 ^ 59
def prefixEnd_7842380 : Nat := 4983230072969 + 3 ^ 40 * 7842380 * 2
def baseEnd_7842380 : Nat := 4026910415207131885883557

theorem tailTrace_7842380 : CollatzResearch.WordTrace tailWord_7842380 prefixEnd_7842380 4026910415207131885883557 := by
  unfold tailWord_7842380
  simp only [CollatzResearch.WordTrace]
  refine ⟨143017548664202053358134297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190690064885602737810845729 143017548664202053358134297)
  ·
    refine ⟨107263161498151540018600723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143017548664202053358134297 107263161498151540018600723)
    ·
      refine ⟨160894742247227310027901085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107263161498151540018600723 160894742247227310027901085)
      ·
        refine ⟨60335528342710241260462907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160894742247227310027901085 60335528342710241260462907)
        ·
          refine ⟨90503292514065361890694361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60335528342710241260462907 90503292514065361890694361)
          ·
            refine ⟨67877469385549021418020771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90503292514065361890694361 67877469385549021418020771)
            ·
              refine ⟨101816204078323532127031157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67877469385549021418020771 101816204078323532127031157)
              ·
                refine ⟨9545269132342831136909171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101816204078323532127031157 9545269132342831136909171)
                ·
                  refine ⟨14317903698514246705363757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9545269132342831136909171 14317903698514246705363757)
                  ·
                    refine ⟨5369213886942842514511409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14317903698514246705363757 5369213886942842514511409)
                    ·
                      refine ⟨4026910415207131885883557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5369213886942842514511409 4026910415207131885883557)
                      ·
                        rfl

theorem cell23_7842380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_7842380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842380 prefixEnd_7842380 := by exact prefixLift 7842380
  have htrace : WordTrace (prefixWord ++ tailWord_7842380) baseStart_7842380 baseEnd_7842380 := by
    simpa [prefixWord, tailWord_7842380, baseEnd_7842380] using wordTrace_append hprefix tailTrace_7842380
  have hstable : (prefixWord ++ tailWord_7842380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842380).length < 2 ^ (prefixWord ++ tailWord_7842380).sum := by decide
  have hdescent : baseEnd_7842380 < baseStart_7842380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842398 : List Nat := [4, 4, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_7842398 : Nat := 118140960795 + 7842398 * 2 ^ 59
def prefixEnd_7842398 : Nat := 4983230072969 + 3 ^ 40 * 7842398 * 2
def baseEnd_7842398 : Nat := 1342306552619637605152825

theorem tailTrace_7842398 : CollatzResearch.WordTrace tailWord_7842398 prefixEnd_7842398 1342306552619637605152825 := by
  unfold tailWord_7842398
  simp only [CollatzResearch.WordTrace]
  refine ⟨35754469230292361973802981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190690502561559263860282565 35754469230292361973802981)
  ·
    refine ⟨6703962980679817870088059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35754469230292361973802981 6703962980679817870088059)
    ·
      refine ⟨10055944471019726805132089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6703962980679817870088059 10055944471019726805132089)
      ·
        refine ⟨7541958353264795103849067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10055944471019726805132089 7541958353264795103849067)
        ·
          refine ⟨11312937529897192655773601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7541958353264795103849067 11312937529897192655773601)
          ·
            refine ⟨8484703147422894491830201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11312937529897192655773601 8484703147422894491830201)
            ·
              refine ⟨6363527360567170868872651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8484703147422894491830201 6363527360567170868872651)
              ·
                refine ⟨9545291040850756303308977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6363527360567170868872651 9545291040850756303308977)
                ·
                  refine ⟨7158968280638067227481733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9545291040850756303308977 7158968280638067227481733)
                  ·
                    refine ⟨1342306552619637605152825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7158968280638067227481733 1342306552619637605152825)
                    ·
                      rfl

theorem cell23_7842398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_7842398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842398 prefixEnd_7842398 := by exact prefixLift 7842398
  have htrace : WordTrace (prefixWord ++ tailWord_7842398) baseStart_7842398 baseEnd_7842398 := by
    simpa [prefixWord, tailWord_7842398, baseEnd_7842398] using wordTrace_append hprefix tailTrace_7842398
  have hstable : (prefixWord ++ tailWord_7842398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842398).length < 2 ^ (prefixWord ++ tailWord_7842398).sum := by decide
  have hdescent : baseEnd_7842398 < baseStart_7842398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842410 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_7842410 : Nat := 118140960795 + 7842410 * 2 ^ 59
def prefixEnd_7842410 : Nat := 4983230072969 + 3 ^ 40 * 7842410 * 2
def baseEnd_7842410 : Nat := 4026925819626766768508419

theorem tailTrace_7842410 : CollatzResearch.WordTrace tailWord_7842410 prefixEnd_7842410 4026925819626766768508419 := by
  unfold tailWord_7842410
  simp only [CollatzResearch.WordTrace]
  refine ⟨71509047879573855459965171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190690794345530281226573789 71509047879573855459965171)
  ·
    refine ⟨107263571819360783189947757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71509047879573855459965171 107263571819360783189947757)
    ·
      refine ⟨40223839432260293696230409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107263571819360783189947757 40223839432260293696230409)
      ·
        refine ⟨30167879574195220272172807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40223839432260293696230409 30167879574195220272172807)
        ·
          refine ⟨45251819361292830408259211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30167879574195220272172807 45251819361292830408259211)
          ·
            refine ⟨67877729041939245612388817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45251819361292830408259211 67877729041939245612388817)
            ·
              refine ⟨50908296781454434209291613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67877729041939245612388817 50908296781454434209291613)
              ·
                refine ⟨19090611293045412828484355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50908296781454434209291613 19090611293045412828484355)
                ·
                  refine ⟨28635916939568119242726533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19090611293045412828484355 28635916939568119242726533)
                  ·
                    refine ⟨5369234426169022358011225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28635916939568119242726533 5369234426169022358011225)
                    ·
                      refine ⟨4026925819626766768508419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5369234426169022358011225 4026925819626766768508419)
                      ·
                        rfl

theorem cell23_7842410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_7842410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842410 prefixEnd_7842410 := by exact prefixLift 7842410
  have htrace : WordTrace (prefixWord ++ tailWord_7842410) baseStart_7842410 baseEnd_7842410 := by
    simpa [prefixWord, tailWord_7842410, baseEnd_7842410] using wordTrace_append hprefix tailTrace_7842410
  have hstable : (prefixWord ++ tailWord_7842410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842410).length < 2 ^ (prefixWord ++ tailWord_7842410).sum := by decide
  have hdescent : baseEnd_7842410 < baseStart_7842410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842413 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_7842413 : Nat := 118140960795 + 7842413 * 2 ^ 59
def prefixEnd_7842413 : Nat := 4983230072969 + 3 ^ 40 * 7842413 * 2
def baseEnd_7842413 : Nat := 4026927360068730256770905

theorem tailTrace_7842413 : CollatzResearch.WordTrace tailWord_7842413 prefixEnd_7842413 4026927360068730256770905 := by
  unfold tailWord_7842413
  simp only [CollatzResearch.WordTrace]
  refine ⟨286036300937284553352219893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190690867291523035568146595 286036300937284553352219893)
  ·
    refine ⟨26815903212870426876770615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286036300937284553352219893 26815903212870426876770615)
    ·
      refine ⟨40223854819305640315155923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26815903212870426876770615 40223854819305640315155923)
      ·
        refine ⟨60335782228958460472733885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40223854819305640315155923 60335782228958460472733885)
        ·
          refine ⟨22625918335859422677275207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60335782228958460472733885 22625918335859422677275207)
          ·
            refine ⟨33938877503789134015912811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22625918335859422677275207 33938877503789134015912811)
            ·
              refine ⟨50908316255683701023869217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33938877503789134015912811 50908316255683701023869217)
              ·
                refine ⟨38181237191762775767901913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50908316255683701023869217 38181237191762775767901913)
                ·
                  refine ⟨28635927893822081825926435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38181237191762775767901913 28635927893822081825926435)
                  ·
                    refine ⟨42953891840733122738889653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28635927893822081825926435 42953891840733122738889653)
                    ·
                      refine ⟨4026927360068730256770905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42953891840733122738889653 4026927360068730256770905)
                      ·
                        rfl

theorem cell23_7842413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_7842413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842413 prefixEnd_7842413 := by exact prefixLift 7842413
  have htrace : WordTrace (prefixWord ++ tailWord_7842413) baseStart_7842413 baseEnd_7842413 := by
    simpa [prefixWord, tailWord_7842413, baseEnd_7842413] using wordTrace_append hprefix tailTrace_7842413
  have hstable : (prefixWord ++ tailWord_7842413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842413).length < 2 ^ (prefixWord ++ tailWord_7842413).sum := by decide
  have hdescent : baseEnd_7842413 < baseStart_7842413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842414 : List Nat := [4, 1, 2, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_7842414 : Nat := 118140960795 + 7842414 * 2 ^ 59
def prefixEnd_7842414 : Nat := 4983230072969 + 3 ^ 40 * 7842414 * 2
def baseEnd_7842414 : Nat := 4026927873549384752858401

theorem tailTrace_7842414 : CollatzResearch.WordTrace tailWord_7842414 prefixEnd_7842414 4026927873549384752858401 := by
  unfold tailWord_7842414
  simp only [CollatzResearch.WordTrace]
  refine ⟨35754542176285116315375787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190690891606853953682004197 35754542176285116315375787)
  ·
    refine ⟨53631813264427674473063681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35754542176285116315375787 53631813264427674473063681)
    ·
      refine ⟨40223859948320755854797761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53631813264427674473063681 40223859948320755854797761)
      ·
        refine ⟨30167894961240566891098321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40223859948320755854797761 30167894961240566891098321)
        ·
          refine ⟨22625921220930425168323741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30167894961240566891098321 22625921220930425168323741)
          ·
            refine ⟨8484720457848909438121403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22625921220930425168323741 8484720457848909438121403)
            ·
              refine ⟨12727080686773364157182105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8484720457848909438121403 12727080686773364157182105)
              ·
                refine ⟨9545310515080023117886579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12727080686773364157182105 9545310515080023117886579)
                ·
                  refine ⟨14317965772620034676829869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9545310515080023117886579 14317965772620034676829869)
                  ·
                    refine ⟨5369237164732513003811201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14317965772620034676829869 5369237164732513003811201)
                    ·
                      refine ⟨4026927873549384752858401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5369237164732513003811201 4026927873549384752858401)
                      ·
                        rfl

theorem cell23_7842414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_7842414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842414 prefixEnd_7842414 := by exact prefixLift 7842414
  have htrace : WordTrace (prefixWord ++ tailWord_7842414) baseStart_7842414 baseEnd_7842414 := by
    simpa [prefixWord, tailWord_7842414, baseEnd_7842414] using wordTrace_append hprefix tailTrace_7842414
  have hstable : (prefixWord ++ tailWord_7842414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842414).length < 2 ^ (prefixWord ++ tailWord_7842414).sum := by decide
  have hdescent : baseEnd_7842414 < baseStart_7842414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842460 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_7842460 : Nat := 118140960795 + 7842460 * 2 ^ 59
def prefixEnd_7842460 : Nat := 4983230072969 + 3 ^ 40 * 7842460 * 2
def baseEnd_7842460 : Nat := 4026951493659491572883189

theorem tailTrace_7842460 : CollatzResearch.WordTrace tailWord_7842460 prefixEnd_7842460 4026951493659491572883189 := by
  unfold tailWord_7842460
  simp only [CollatzResearch.WordTrace]
  refine ⟨143019007584057140189590417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190692010112076186919453889 143019007584057140189590417)
  ·
    refine ⟨107264255688042855142192813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143019007584057140189590417 107264255688042855142192813)
    ·
      refine ⟨40224095883016070678322305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107264255688042855142192813 40224095883016070678322305)
      ·
        refine ⟨30168071912262053008741729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40224095883016070678322305 30168071912262053008741729)
        ·
          refine ⟨22626053934196539756556297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30168071912262053008741729 22626053934196539756556297)
          ·
            refine ⟨16969540450647404817417223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22626053934196539756556297 16969540450647404817417223)
            ·
              refine ⟨25454310675971107226125835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16969540450647404817417223 25454310675971107226125835)
              ·
                refine ⟨38181466013956660839188753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25454310675971107226125835 38181466013956660839188753)
                ·
                  refine ⟨28636099510467495629391565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38181466013956660839188753 28636099510467495629391565)
                  ·
                    refine ⟨10738537316425310861021837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28636099510467495629391565 10738537316425310861021837)
                    ·
                      refine ⟨4026951493659491572883189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10738537316425310861021837 4026951493659491572883189)
                      ·
                        rfl

theorem cell23_7842460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_7842460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842460 prefixEnd_7842460 := by exact prefixLift 7842460
  have htrace : WordTrace (prefixWord ++ tailWord_7842460) baseStart_7842460 baseEnd_7842460 := by
    simpa [prefixWord, tailWord_7842460, baseEnd_7842460] using wordTrace_append hprefix tailTrace_7842460
  have hstable : (prefixWord ++ tailWord_7842460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842460).length < 2 ^ (prefixWord ++ tailWord_7842460).sum := by decide
  have hdescent : baseEnd_7842460 < baseStart_7842460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842483 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 4]
def baseStart_7842483 : Nat := 118140960795 + 7842483 * 2 ^ 59
def prefixEnd_7842483 : Nat := 4983230072969 + 3 ^ 40 * 7842483 * 2
def baseEnd_7842483 : Nat := 4026963303714544982895583

theorem tailTrace_7842483 : CollatzResearch.WordTrace tailWord_7842483 prefixEnd_7842483 4026963303714544982895583 := by
  unfold tailWord_7842483
  simp only [CollatzResearch.WordTrace]
  refine ⟨286038854047030955307268103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190692569364687303538178735 286038854047030955307268103)
  ·
    refine ⟨429058281070546432960902155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286038854047030955307268103 429058281070546432960902155)
    ·
      refine ⟨643587421605819649441353233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429058281070546432960902155 643587421605819649441353233)
      ·
        refine ⟨482690566204364737081014925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643587421605819649441353233 482690566204364737081014925)
        ·
          refine ⟨181008962326636776405380597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482690566204364737081014925 181008962326636776405380597)
          ·
            refine ⟨16969590218122197788004431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181008962326636776405380597 16969590218122197788004431)
            ·
              refine ⟨25454385327183296682006647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16969590218122197788004431 25454385327183296682006647)
              ·
                refine ⟨38181577990774945023009971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25454385327183296682006647 38181577990774945023009971)
                ·
                  refine ⟨57272366986162417534514957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38181577990774945023009971 57272366986162417534514957)
                  ·
                    refine ⟨21477137619810906575443109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57272366986162417534514957 21477137619810906575443109)
                    ·
                      refine ⟨4026963303714544982895583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21477137619810906575443109 4026963303714544982895583)
                      ·
                        rfl

theorem cell23_7842483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_7842483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842483 prefixEnd_7842483 := by exact prefixLift 7842483
  have htrace : WordTrace (prefixWord ++ tailWord_7842483) baseStart_7842483 baseEnd_7842483 := by
    simpa [prefixWord, tailWord_7842483, baseEnd_7842483] using wordTrace_append hprefix tailTrace_7842483
  have hstable : (prefixWord ++ tailWord_7842483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842483).length < 2 ^ (prefixWord ++ tailWord_7842483).sum := by decide
  have hdescent : baseEnd_7842483 < baseStart_7842483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842510 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_7842510 : Nat := 118140960795 + 7842510 * 2 ^ 59
def prefixEnd_7842510 : Nat := 4983230072969 + 3 ^ 40 * 7842510 * 2
def baseEnd_7842510 : Nat := 1342325722564072125752653

theorem tailTrace_7842510 : CollatzResearch.WordTrace tailWord_7842510 prefixEnd_7842510 1342325722564072125752653 := by
  unfold tailWord_7842510
  simp only [CollatzResearch.WordTrace]
  refine ⟨35754979852241642364812623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190693225878622092612333989 35754979852241642364812623)
  ·
    refine ⟨53632469778362463547218935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35754979852241642364812623 53632469778362463547218935)
    ·
      refine ⟨80448704667543695320828403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53632469778362463547218935 80448704667543695320828403)
      ·
        refine ⟨120673057001315542981242605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80448704667543695320828403 120673057001315542981242605)
        ·
          refine ⟨45252396375493328617965977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120673057001315542981242605 45252396375493328617965977)
          ·
            refine ⟨33939297281619996463474483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45252396375493328617965977 33939297281619996463474483)
            ·
              refine ⟨50908945922429994695211725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33939297281619996463474483 50908945922429994695211725)
              ·
                refine ⟨19090854720911248010704397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50908945922429994695211725 19090854720911248010704397)
                ·
                  refine ⟨7159070520341718004014149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19090854720911248010704397 7159070520341718004014149)
                  ·
                    refine ⟨1342325722564072125752653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7159070520341718004014149 1342325722564072125752653)
                    ·
                      rfl

theorem cell23_7842510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_7842510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842510 prefixEnd_7842510 := by exact prefixLift 7842510
  have htrace : WordTrace (prefixWord ++ tailWord_7842510) baseStart_7842510 baseEnd_7842510 := by
    simpa [prefixWord, tailWord_7842510, baseEnd_7842510] using wordTrace_append hprefix tailTrace_7842510
  have hstable : (prefixWord ++ tailWord_7842510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842510).length < 2 ^ (prefixWord ++ tailWord_7842510).sum := by decide
  have hdescent : baseEnd_7842510 < baseStart_7842510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842594 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_7842594 : Nat := 118140960795 + 7842594 * 2 ^ 59
def prefixEnd_7842594 : Nat := 4983230072969 + 3 ^ 40 * 7842594 * 2
def baseEnd_7842594 : Nat := 4027020300067194048607573

theorem tailTrace_7842594 : CollatzResearch.WordTrace tailWord_7842594 prefixEnd_7842594 4027020300067194048607573 := by
  unfold tailWord_7842594
  simp only [CollatzResearch.WordTrace]
  refine ⟨71510725637407205316139709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190695268366419214176372557 71510725637407205316139709)
  ·
    refine ⟨26816522114027701993552391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71510725637407205316139709 26816522114027701993552391)
    ·
      refine ⟨40224783171041552990328587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26816522114027701993552391 40224783171041552990328587)
      ·
        refine ⟨60337174756562329485492881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40224783171041552990328587 60337174756562329485492881)
        ·
          refine ⟨45252881067421747114119661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60337174756562329485492881 45252881067421747114119661)
          ·
            refine ⟨16969830400283155167794873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45252881067421747114119661 16969830400283155167794873)
            ·
              refine ⟨12727372800212366375846155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16969830400283155167794873 12727372800212366375846155)
              ·
                refine ⟨19091059200318549563769233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12727372800212366375846155 19091059200318549563769233)
                ·
                  refine ⟨14318294400238912172826925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19091059200318549563769233 14318294400238912172826925)
                  ·
                    refine ⟨5369360400089592064810097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14318294400238912172826925 5369360400089592064810097)
                    ·
                      refine ⟨4027020300067194048607573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5369360400089592064810097 4027020300067194048607573)
                      ·
                        rfl

theorem cell23_7842594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_7842594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842594 prefixEnd_7842594 := by exact prefixLift 7842594
  have htrace : WordTrace (prefixWord ++ tailWord_7842594) baseStart_7842594 baseEnd_7842594 := by
    simpa [prefixWord, tailWord_7842594, baseEnd_7842594] using wordTrace_append hprefix tailTrace_7842594
  have hstable : (prefixWord ++ tailWord_7842594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842594).length < 2 ^ (prefixWord ++ tailWord_7842594).sum := by decide
  have hdescent : baseEnd_7842594 < baseStart_7842594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842600 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 1, 6]
def baseStart_7842600 : Nat := 118140960795 + 7842600 * 2 ^ 59
def prefixEnd_7842600 : Nat := 4983230072969 + 3 ^ 40 * 7842600 * 2
def baseEnd_7842600 : Nat := 1342341126983707008377515

theorem tailTrace_7842600 : CollatzResearch.WordTrace tailWord_7842600 prefixEnd_7842600 1342341126983707008377515 := by
  unfold tailWord_7842600
  simp only [CollatzResearch.WordTrace]
  refine ⟨143021560693803542144638627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190695414258404722859518169 143021560693803542144638627)
  ·
    refine ⟨214532341040705313216957941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143021560693803542144638627 214532341040705313216957941)
    ·
      refine ⟨20112406972566123114089807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214532341040705313216957941 20112406972566123114089807)
      ·
        refine ⟨30168610458849184671134711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20112406972566123114089807 30168610458849184671134711)
        ·
          refine ⟨45252915688273777006702067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30168610458849184671134711 45252915688273777006702067)
          ·
            refine ⟨67879373532410665510053101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45252915688273777006702067 67879373532410665510053101)
            ·
              refine ⟨25454765074653999566269913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67879373532410665510053101 25454765074653999566269913)
              ·
                refine ⟨19091073805990499674702435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25454765074653999566269913 19091073805990499674702435)
                ·
                  refine ⟨28636610708985749512053653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19091073805990499674702435 28636610708985749512053653)
                  ·
                    refine ⟨1342341126983707008377515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28636610708985749512053653 1342341126983707008377515)
                    ·
                      rfl

theorem cell23_7842600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_7842600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842600 prefixEnd_7842600 := by exact prefixLift 7842600
  have htrace : WordTrace (prefixWord ++ tailWord_7842600) baseStart_7842600 baseEnd_7842600 := by
    simpa [prefixWord, tailWord_7842600, baseEnd_7842600] using wordTrace_append hprefix tailTrace_7842600
  have hstable : (prefixWord ++ tailWord_7842600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842600).length < 2 ^ (prefixWord ++ tailWord_7842600).sum := by decide
  have hdescent : baseEnd_7842600 < baseStart_7842600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842603 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 4]
def baseStart_7842603 : Nat := 118140960795 + 7842603 * 2 ^ 59
def prefixEnd_7842603 : Nat := 4983230072969 + 3 ^ 40 * 7842603 * 2
def baseEnd_7842603 : Nat := 4027024921393084513395031

theorem tailTrace_7842603 : CollatzResearch.WordTrace tailWord_7842603 prefixEnd_7842603 4027024921393084513395031 := by
  unfold tailWord_7842603
  simp only [CollatzResearch.WordTrace]
  refine ⟨286043230806596215801636463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190695487204397477201090975 286043230806596215801636463)
  ·
    refine ⟨429064846209894323702454695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286043230806596215801636463 429064846209894323702454695)
    ·
      refine ⟨643597269314841485553682043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429064846209894323702454695 643597269314841485553682043)
      ·
        refine ⟨965395903972262228330523065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643597269314841485553682043 965395903972262228330523065)
        ·
          refine ⟨724046927979196671247892299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965395903972262228330523065 724046927979196671247892299)
          ·
            refine ⟨1086070391968795006871838449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724046927979196671247892299 1086070391968795006871838449)
            ·
              refine ⟨814552793976596255153878837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1086070391968795006871838449 814552793976596255153878837)
              ·
                refine ⟨76364324435305898920676141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 814552793976596255153878837 76364324435305898920676141)
                ·
                  refine ⟨28636621663239712095253553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76364324435305898920676141 28636621663239712095253553)
                  ·
                    refine ⟨21477466247429784071440165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28636621663239712095253553 21477466247429784071440165)
                    ·
                      refine ⟨4027024921393084513395031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21477466247429784071440165 4027024921393084513395031)
                      ·
                        rfl

theorem cell23_7842603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 4].length) (baseStart_7842603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842603 prefixEnd_7842603 := by exact prefixLift 7842603
  have htrace : WordTrace (prefixWord ++ tailWord_7842603) baseStart_7842603 baseEnd_7842603 := by
    simpa [prefixWord, tailWord_7842603, baseEnd_7842603] using wordTrace_append hprefix tailTrace_7842603
  have hstable : (prefixWord ++ tailWord_7842603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842603).length < 2 ^ (prefixWord ++ tailWord_7842603).sum := by decide
  have hdescent : baseEnd_7842603 < baseStart_7842603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842613 : List Nat := [1, 3, 3, 1, 3, 12]
def baseStart_7842613 : Nat := 118140960795 + 7842613 * 2 ^ 59
def prefixEnd_7842613 : Nat := 4983230072969 + 3 ^ 40 * 7842613 * 2
def baseEnd_7842613 : Nat := 16572140148969668618395

theorem tailTrace_7842613 : CollatzResearch.WordTrace tailWord_7842613 prefixEnd_7842613 16572140148969668618395 := by
  unfold tailWord_7842613
  simp only [CollatzResearch.WordTrace]
  refine ⟨286043595536559987509500493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190695730357706658339666995 286043595536559987509500493)
  ·
    refine ⟨107266348326209995316062685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286043595536559987509500493 107266348326209995316062685)
    ·
      refine ⟨40224880622328748243523507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107266348326209995316062685 40224880622328748243523507)
      ·
        refine ⟨60337320933493122365285261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40224880622328748243523507 60337320933493122365285261)
        ·
          refine ⟨22626495350059920886981973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60337320933493122365285261 22626495350059920886981973)
          ·
            refine ⟨16572140148969668618395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 22626495350059920886981973 16572140148969668618395)
            ·
              rfl

theorem cell23_7842613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 12].length) (baseStart_7842613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842613 prefixEnd_7842613 := by exact prefixLift 7842613
  have htrace : WordTrace (prefixWord ++ tailWord_7842613) baseStart_7842613 baseEnd_7842613 := by
    simpa [prefixWord, tailWord_7842613, baseEnd_7842613] using wordTrace_append hprefix tailTrace_7842613
  have hstable : (prefixWord ++ tailWord_7842613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842613).length < 2 ^ (prefixWord ++ tailWord_7842613).sum := by decide
  have hdescent : baseEnd_7842613 < baseStart_7842613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842618 : List Nat := [3, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3]
def baseStart_7842618 : Nat := 118140960795 + 7842618 * 2 ^ 59
def prefixEnd_7842618 : Nat := 4983230072969 + 3 ^ 40 * 7842618 * 2
def baseEnd_7842618 : Nat := 4027032623602901954707463

theorem tailTrace_7842618 : CollatzResearch.WordTrace tailWord_7842618 prefixEnd_7842618 4027032623602901954707463 := by
  unfold tailWord_7842618
  simp only [CollatzResearch.WordTrace]
  refine ⟨71510944475385468340858127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190695851934361248908955005 71510944475385468340858127)
  ·
    refine ⟨107266416713078202511287191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71510944475385468340858127 107266416713078202511287191)
    ·
      refine ⟨160899625069617303766930787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107266416713078202511287191 160899625069617303766930787)
      ·
        refine ⟨241349437604425955650396181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160899625069617303766930787 241349437604425955650396181)
        ·
          refine ⟨11313254887707466671112321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241349437604425955650396181 11313254887707466671112321)
          ·
            refine ⟨8484941165780600003334241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11313254887707466671112321 8484941165780600003334241)
            ·
              refine ⟨6363705874335450002500681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8484941165780600003334241 6363705874335450002500681)
              ·
                refine ⟨4772779405751587501875511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6363705874335450002500681 4772779405751587501875511)
                ·
                  refine ⟨7159169108627381252813267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4772779405751587501875511 7159169108627381252813267)
                  ·
                    refine ⟨10738753662941071879219901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7159169108627381252813267 10738753662941071879219901)
                    ·
                      refine ⟨4027032623602901954707463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10738753662941071879219901 4027032623602901954707463)
                      ·
                        rfl

theorem cell23_7842618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3].length) (baseStart_7842618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842618 prefixEnd_7842618 := by exact prefixLift 7842618
  have htrace : WordTrace (prefixWord ++ tailWord_7842618) baseStart_7842618 baseEnd_7842618 := by
    simpa [prefixWord, tailWord_7842618, baseEnd_7842618] using wordTrace_append hprefix tailTrace_7842618
  have hstable : (prefixWord ++ tailWord_7842618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842618).length < 2 ^ (prefixWord ++ tailWord_7842618).sum := by decide
  have hdescent : baseEnd_7842618 < baseStart_7842618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842640 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 3]
def baseStart_7842640 : Nat := 118140960795 + 7842640 * 2 ^ 59
def prefixEnd_7842640 : Nat := 4983230072969 + 3 ^ 40 * 7842640 * 2
def baseEnd_7842640 : Nat := 4027043920177300868632361

theorem tailTrace_7842640 : CollatzResearch.WordTrace tailWord_7842640 prefixEnd_7842640 4027043920177300868632361 := by
  unfold tailWord_7842640
  simp only [CollatzResearch.WordTrace]
  refine ⟨143022290153731085560366687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190696386871641447413822249 143022290153731085560366687)
  ·
    refine ⟨214533435230596628340550031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143022290153731085560366687 214533435230596628340550031)
    ·
      refine ⟨321800152845894942510825047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214533435230596628340550031 321800152845894942510825047)
      ·
        refine ⟨482700229268842413766237571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321800152845894942510825047 482700229268842413766237571)
        ·
          refine ⟨724050343903263620649356357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482700229268842413766237571 724050343903263620649356357)
          ·
            refine ⟨135759439481861928871754317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 724050343903263620649356357 135759439481861928871754317)
            ·
              refine ⟨50909789805698223326907869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135759439481861928871754317 50909789805698223326907869)
              ·
                refine ⟨19091171177136833747590451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50909789805698223326907869 19091171177136833747590451)
                ·
                  refine ⟨28636756765705250621385677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19091171177136833747590451 28636756765705250621385677)
                  ·
                    refine ⟨10738783787139468983019629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28636756765705250621385677 10738783787139468983019629)
                    ·
                      refine ⟨4027043920177300868632361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10738783787139468983019629 4027043920177300868632361)
                      ·
                        rfl

theorem cell23_7842640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 3].length) (baseStart_7842640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842640 prefixEnd_7842640 := by exact prefixLift 7842640
  have htrace : WordTrace (prefixWord ++ tailWord_7842640) baseStart_7842640 baseEnd_7842640 := by
    simpa [prefixWord, tailWord_7842640, baseEnd_7842640] using wordTrace_append hprefix tailTrace_7842640
  have hstable : (prefixWord ++ tailWord_7842640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842640).length < 2 ^ (prefixWord ++ tailWord_7842640).sum := by decide
  have hdescent : baseEnd_7842640 < baseStart_7842640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842658 : List Nat := [3, 3, 2, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_7842658 : Nat := 118140960795 + 7842658 * 2 ^ 59
def prefixEnd_7842658 : Nat := 4983230072969 + 3 ^ 40 * 7842658 * 2
def baseEnd_7842658 : Nat := 4027053162829081798207279

theorem tailTrace_7842658 : CollatzResearch.WordTrace tailWord_7842658 prefixEnd_7842658 4027053162829081798207279 := by
  unfold tailWord_7842658
  simp only [CollatzResearch.WordTrace]
  refine ⟨71511309205349240048722157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190696824547597973463259085 71511309205349240048722157)
  ·
    refine ⟨26816740952005965018270809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71511309205349240048722157 26816740952005965018270809)
    ·
      refine ⟨20112555714004473763703107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26816740952005965018270809 20112555714004473763703107)
      ·
        refine ⟨30168833571006710645554661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20112555714004473763703107 30168833571006710645554661)
        ·
          refine ⟨5656656294563758246041499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30168833571006710645554661 5656656294563758246041499)
          ·
            refine ⟨8484984441845637369062249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5656656294563758246041499 8484984441845637369062249)
            ·
              refine ⟨6363738331384228026796687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8484984441845637369062249 6363738331384228026796687)
              ·
                refine ⟨9545607497076342040195031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6363738331384228026796687 9545607497076342040195031)
                ·
                  refine ⟨14318411245614513060292547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9545607497076342040195031 14318411245614513060292547)
                  ·
                    refine ⟨21477616868421769590438821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14318411245614513060292547 21477616868421769590438821)
                    ·
                      refine ⟨4027053162829081798207279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21477616868421769590438821 4027053162829081798207279)
                      ·
                        rfl

theorem cell23_7842658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_7842658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842658 prefixEnd_7842658 := by exact prefixLift 7842658
  have htrace : WordTrace (prefixWord ++ tailWord_7842658) baseStart_7842658 baseEnd_7842658 := by
    simpa [prefixWord, tailWord_7842658, baseEnd_7842658] using wordTrace_append hprefix tailTrace_7842658
  have hstable : (prefixWord ++ tailWord_7842658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842658).length < 2 ^ (prefixWord ++ tailWord_7842658).sum := by decide
  have hdescent : baseEnd_7842658 < baseStart_7842658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842674 : List Nat := [3, 2, 1, 2, 1, 1, 5, 2, 2, 1, 3]
def baseStart_7842674 : Nat := 118140960795 + 7842674 * 2 ^ 59
def prefixEnd_7842674 : Nat := 4983230072969 + 3 ^ 40 * 7842674 * 2
def baseEnd_7842674 : Nat := 4027061378519553735607205

theorem tailTrace_7842674 : CollatzResearch.WordTrace tailWord_7842674 prefixEnd_7842674 4027061378519553735607205 := by
  unfold tailWord_7842674
  simp only [CollatzResearch.WordTrace]
  refine ⟨71511455097334748731867769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190697213592892663284980717 71511455097334748731867769)
  ·
    refine ⟨53633591323001061548900827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71511455097334748731867769 53633591323001061548900827)
    ·
      refine ⟨80450386984501592323351241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53633591323001061548900827 80450386984501592323351241)
      ·
        refine ⟨60337790238376194242513431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80450386984501592323351241 60337790238376194242513431)
        ·
          refine ⟨90506685357564291363770147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60337790238376194242513431 90506685357564291363770147)
          ·
            refine ⟨135760028036346437045655221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90506685357564291363770147 135760028036346437045655221)
            ·
              refine ⟨12727502628407478473030177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135760028036346437045655221 12727502628407478473030177)
              ·
                refine ⟨9545626971305608854772633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12727502628407478473030177 9545626971305608854772633)
                ·
                  refine ⟨7159220228479206641079475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9545626971305608854772633 7159220228479206641079475)
                  ·
                    refine ⟨10738830342718809961619213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7159220228479206641079475 10738830342718809961619213)
                    ·
                      refine ⟨4027061378519553735607205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10738830342718809961619213 4027061378519553735607205)
                      ·
                        rfl

theorem cell23_7842674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_7842674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842674 prefixEnd_7842674 := by exact prefixLift 7842674
  have htrace : WordTrace (prefixWord ++ tailWord_7842674) baseStart_7842674 baseEnd_7842674 := by
    simpa [prefixWord, tailWord_7842674, baseEnd_7842674] using wordTrace_append hprefix tailTrace_7842674
  have hstable : (prefixWord ++ tailWord_7842674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842674).length < 2 ^ (prefixWord ++ tailWord_7842674).sum := by decide
  have hdescent : baseEnd_7842674 < baseStart_7842674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842700 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 2, 4, 3]
def baseStart_7842700 : Nat := 118140960795 + 7842700 * 2 ^ 59
def prefixEnd_7842700 : Nat := 4983230072969 + 3 ^ 40 * 7842700 * 2
def baseEnd_7842700 : Nat := 4027074729016570633882085

theorem tailTrace_7842700 : CollatzResearch.WordTrace tailWord_7842700 prefixEnd_7842700 4027074729016570633882085 := by
  unfold tailWord_7842700
  simp only [CollatzResearch.WordTrace]
  refine ⟨143023384343622400683958777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190697845791496534245278369 143023384343622400683958777)
  ·
    refine ⟨107267538257716800512969083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143023384343622400683958777 107267538257716800512969083)
    ·
      refine ⟨160901307386575200769453625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107267538257716800512969083 160901307386575200769453625)
      ·
        refine ⟨120675980539931400577090219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160901307386575200769453625 120675980539931400577090219)
        ·
          refine ⟨181013970809897100865635329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120675980539931400577090219 181013970809897100865635329)
          ·
            refine ⟨135760478107422825649226497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181013970809897100865635329 135760478107422825649226497)
            ·
              refine ⟨101820358580567119236919873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135760478107422825649226497 101820358580567119236919873)
              ·
                refine ⟨76365268935425339427689905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101820358580567119236919873 76365268935425339427689905)
                ·
                  refine ⟨57273951701569004570767429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76365268935425339427689905 57273951701569004570767429)
                  ·
                    refine ⟨10738865944044188357018893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57273951701569004570767429 10738865944044188357018893)
                    ·
                      refine ⟨4027074729016570633882085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10738865944044188357018893 4027074729016570633882085)
                      ·
                        rfl

theorem cell23_7842700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_7842700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842700 prefixEnd_7842700 := by exact prefixLift 7842700
  have htrace : WordTrace (prefixWord ++ tailWord_7842700) baseStart_7842700 baseEnd_7842700 := by
    simpa [prefixWord, tailWord_7842700, baseEnd_7842700] using wordTrace_append hprefix tailTrace_7842700
  have hstable : (prefixWord ++ tailWord_7842700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842700).length < 2 ^ (prefixWord ++ tailWord_7842700).sum := by decide
  have hdescent : baseEnd_7842700 < baseStart_7842700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842765 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_7842765 : Nat := 118140960795 + 7842765 * 2 ^ 59
def prefixEnd_7842765 : Nat := 4983230072969 + 3 ^ 40 * 7842765 * 2
def baseEnd_7842765 : Nat := 4027108105259112879569287

theorem tailTrace_7842765 : CollatzResearch.WordTrace tailWord_7842765 prefixEnd_7842765 4027108105259112879569287 := by
  unfold tailWord_7842765
  simp only [CollatzResearch.WordTrace]
  refine ⟨286049139432009317469033749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190699426288006211646022499 286049139432009317469033749)
  ·
    refine ⟨13408553410875436756360957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 286049139432009317469033749 13408553410875436756360957)
    ·
      refine ⟨5028207529078288783635359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13408553410875436756360957 5028207529078288783635359)
      ·
        refine ⟨7542311293617433175453039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5028207529078288783635359 7542311293617433175453039)
        ·
          refine ⟨11313466940426149763179559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7542311293617433175453039 11313466940426149763179559)
          ·
            refine ⟨16970200410639224644769339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11313466940426149763179559 16970200410639224644769339)
            ·
              refine ⟨25455300615958836967154009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16970200410639224644769339 25455300615958836967154009)
              ·
                refine ⟨19091475461969127725365507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25455300615958836967154009 19091475461969127725365507)
                ·
                  refine ⟨28637213192953691588048261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19091475461969127725365507 28637213192953691588048261)
                  ·
                    refine ⟨5369477473678817172759049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28637213192953691588048261 5369477473678817172759049)
                    ·
                      refine ⟨4027108105259112879569287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5369477473678817172759049 4027108105259112879569287)
                      ·
                        rfl

theorem cell23_7842765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_7842765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842765 prefixEnd_7842765 := by exact prefixLift 7842765
  have htrace : WordTrace (prefixWord ++ tailWord_7842765) baseStart_7842765 baseEnd_7842765 := by
    simpa [prefixWord, tailWord_7842765, baseEnd_7842765] using wordTrace_append hprefix tailTrace_7842765
  have hstable : (prefixWord ++ tailWord_7842765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842765).length < 2 ^ (prefixWord ++ tailWord_7842765).sum := by decide
  have hdescent : baseEnd_7842765 < baseStart_7842765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842767 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 2, 5]
def baseStart_7842767 : Nat := 118140960795 + 7842767 * 2 ^ 59
def prefixEnd_7842767 : Nat := 4983230072969 + 3 ^ 40 * 7842767 * 2
def baseEnd_7842767 : Nat := 1342369710740140623914759

theorem tailTrace_7842767 : CollatzResearch.WordTrace tailWord_7842767 prefixEnd_7842767 1342369710740140623914759 := by
  unfold tailWord_7842767
  simp only [CollatzResearch.WordTrace]
  refine ⟨286049212378002071810606555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190699474918668047873737703 286049212378002071810606555)
  ·
    refine ⟨429073818567003107715909833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286049212378002071810606555 429073818567003107715909833)
    ·
      refine ⟨321805363925252330786932375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429073818567003107715909833 321805363925252330786932375)
      ·
        refine ⟨482708045887878496180398563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321805363925252330786932375 482708045887878496180398563)
        ·
          refine ⟨724062068831817744270597845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482708045887878496180398563 724062068831817744270597845)
          ·
            refine ⟨16970204738245728381342137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 724062068831817744270597845 16970204738245728381342137)
            ·
              refine ⟨12727653553684296286006603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16970204738245728381342137 12727653553684296286006603)
              ·
                refine ⟨19091480330526444429009905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12727653553684296286006603 19091480330526444429009905)
                ·
                  refine ⟨14318610247894833321757429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19091480330526444429009905 14318610247894833321757429)
                  ·
                    refine ⟨1342369710740140623914759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14318610247894833321757429 1342369710740140623914759)
                    ·
                      rfl

theorem cell23_7842767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 5].length) (baseStart_7842767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842767 prefixEnd_7842767 := by exact prefixLift 7842767
  have htrace : WordTrace (prefixWord ++ tailWord_7842767) baseStart_7842767 baseEnd_7842767 := by
    simpa [prefixWord, tailWord_7842767, baseEnd_7842767] using wordTrace_append hprefix tailTrace_7842767
  have hstable : (prefixWord ++ tailWord_7842767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842767).length < 2 ^ (prefixWord ++ tailWord_7842767).sum := by decide
  have hdescent : baseEnd_7842767 < baseStart_7842767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842787 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 4]
def baseStart_7842787 : Nat := 118140960795 + 7842787 * 2 ^ 59
def prefixEnd_7842787 : Nat := 4983230072969 + 3 ^ 40 * 7842787 * 2
def baseEnd_7842787 : Nat := 4027119401833511793494185

theorem tailTrace_7842787 : CollatzResearch.WordTrace tailWord_7842787 prefixEnd_7842787 4027119401833511793494185 := by
  unfold tailWord_7842787
  simp only [CollatzResearch.WordTrace]
  refine ⟨286049941837929615226334615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190699961225286410150889743 286049941837929615226334615)
  ·
    refine ⟨429074912756894422839501923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286049941837929615226334615 429074912756894422839501923)
    ·
      refine ⟨643612369135341634259252885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429074912756894422839501923 643612369135341634259252885)
      ·
        refine ⟨30169329803219139105902479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 643612369135341634259252885 30169329803219139105902479)
        ·
          refine ⟨45253994704828708658853719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30169329803219139105902479 45253994704828708658853719)
          ·
            refine ⟨67880992057243062988280579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45253994704828708658853719 67880992057243062988280579)
            ·
              refine ⟨101821488085864594482420869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67880992057243062988280579 101821488085864594482420869)
              ·
                refine ⟨19091529016099611465453913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101821488085864594482420869 19091529016099611465453913)
                ·
                  refine ⟨14318646762074708599090435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19091529016099611465453913 14318646762074708599090435)
                  ·
                    refine ⟨21477970143112062898635653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14318646762074708599090435 21477970143112062898635653)
                    ·
                      refine ⟨4027119401833511793494185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21477970143112062898635653 4027119401833511793494185)
                      ·
                        rfl

theorem cell23_7842787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_7842787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842787 prefixEnd_7842787 := by exact prefixLift 7842787
  have htrace : WordTrace (prefixWord ++ tailWord_7842787) baseStart_7842787 baseEnd_7842787 := by
    simpa [prefixWord, tailWord_7842787, baseEnd_7842787] using wordTrace_append hprefix tailTrace_7842787
  have hstable : (prefixWord ++ tailWord_7842787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842787).length < 2 ^ (prefixWord ++ tailWord_7842787).sum := by decide
  have hdescent : baseEnd_7842787 < baseStart_7842787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842800 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 4]
def baseStart_7842800 : Nat := 118140960795 + 7842800 * 2 ^ 59
def prefixEnd_7842800 : Nat := 4983230072969 + 3 ^ 40 * 7842800 * 2
def baseEnd_7842800 : Nat := 4027126077082020242631625

theorem tailTrace_7842800 : CollatzResearch.WordTrace tailWord_7842800 prefixEnd_7842800 4027126077082020242631625 := by
  unfold tailWord_7842800
  simp only [CollatzResearch.WordTrace]
  refine ⟨143025207993441259223278927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190700277324588345631038569 143025207993441259223278927)
  ·
    refine ⟨214537811990161888834918391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143025207993441259223278927 214537811990161888834918391)
    ·
      refine ⟨321806717985242833252377587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214537811990161888834918391 321806717985242833252377587)
      ·
        refine ⟨482710076977864249878566381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321806717985242833252377587 482710076977864249878566381)
        ·
          refine ⟨181016278866699093704462393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482710076977864249878566381 181016278866699093704462393)
          ·
            refine ⟨135762209150024320278346795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181016278866699093704462393 135762209150024320278346795)
            ·
              refine ⟨203643313725036480417520193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135762209150024320278346795 203643313725036480417520193)
              ·
                refine ⟨152732485293777360313140145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203643313725036480417520193 152732485293777360313140145)
                ·
                  refine ⟨114549363970333020234855109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152732485293777360313140145 114549363970333020234855109)
                  ·
                    refine ⟨21478005744437441294035333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114549363970333020234855109 21478005744437441294035333)
                    ·
                      refine ⟨4027126077082020242631625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21478005744437441294035333 4027126077082020242631625)
                      ·
                        rfl

theorem cell23_7842800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_7842800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842800 prefixEnd_7842800 := by exact prefixLift 7842800
  have htrace : WordTrace (prefixWord ++ tailWord_7842800) baseStart_7842800 baseEnd_7842800 := by
    simpa [prefixWord, tailWord_7842800, baseEnd_7842800] using wordTrace_append hprefix tailTrace_7842800
  have hstable : (prefixWord ++ tailWord_7842800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842800).length < 2 ^ (prefixWord ++ tailWord_7842800).sum := by decide
  have hdescent : baseEnd_7842800 < baseStart_7842800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842818 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_7842818 : Nat := 118140960795 + 7842818 * 2 ^ 59
def prefixEnd_7842818 : Nat := 4983230072969 + 3 ^ 40 * 7842818 * 2
def baseEnd_7842818 : Nat := 1342378439911267057402181

theorem tailTrace_7842818 : CollatzResearch.WordTrace tailWord_7842818 prefixEnd_7842818 1342378439911267057402181 := by
  unfold tailWord_7842818
  simp only [CollatzResearch.WordTrace]
  refine ⟨71512768125204326880178277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190700715000544871680475405 71512768125204326880178277)
  ·
    refine ⟨13408644023475811290033427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71512768125204326880178277 13408644023475811290033427)
    ·
      refine ⟨20112966035213716935050141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13408644023475811290033427 20112966035213716935050141)
      ·
        refine ⟨7542362263205143850643803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20112966035213716935050141 7542362263205143850643803)
        ·
          refine ⟨11313543394807715775965705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7542362263205143850643803 11313543394807715775965705)
          ·
            refine ⟨8485157546105786831974279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11313543394807715775965705 8485157546105786831974279)
            ·
              refine ⟨12727736319158680247961419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8485157546105786831974279 12727736319158680247961419)
              ·
                refine ⟨19091604478738020371942129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12727736319158680247961419 19091604478738020371942129)
                ·
                  refine ⟨14318703359053515278956597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19091604478738020371942129 14318703359053515278956597)
                  ·
                    refine ⟨1342378439911267057402181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14318703359053515278956597 1342378439911267057402181)
                    ·
                      rfl

theorem cell23_7842818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_7842818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842818 prefixEnd_7842818 := by exact prefixLift 7842818
  have htrace : WordTrace (prefixWord ++ tailWord_7842818) baseStart_7842818 baseEnd_7842818 := by
    simpa [prefixWord, tailWord_7842818, baseEnd_7842818] using wordTrace_append hprefix tailTrace_7842818
  have hstable : (prefixWord ++ tailWord_7842818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842818).length < 2 ^ (prefixWord ++ tailWord_7842818).sum := by decide
  have hdescent : baseEnd_7842818 < baseStart_7842818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842824 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_7842824 : Nat := 118140960795 + 7842824 * 2 ^ 59
def prefixEnd_7842824 : Nat := 4983230072969 + 3 ^ 40 * 7842824 * 2
def baseEnd_7842824 : Nat := 4027138400617728148731515

theorem tailTrace_7842824 : CollatzResearch.WordTrace tailWord_7842824 prefixEnd_7842824 4027138400617728148731515 := by
  unfold tailWord_7842824
  simp only [CollatzResearch.WordTrace]
  refine ⟨143025645669397785272715763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190700860892530380363621017 143025645669397785272715763)
  ·
    refine ⟨214538468504096677909073645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143025645669397785272715763 214538468504096677909073645)
    ·
      refine ⟨80451925689036254215902617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214538468504096677909073645 80451925689036254215902617)
      ·
        refine ⟨60338944266777190661926963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80451925689036254215902617 60338944266777190661926963)
        ·
          refine ⟨90508416400165785992890445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60338944266777190661926963 90508416400165785992890445)
          ·
            refine ⟨33940656150062169747333917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90508416400165785992890445 33940656150062169747333917)
            ·
              refine ⟨12727746056273313655250219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33940656150062169747333917 12727746056273313655250219)
              ·
                refine ⟨19091619084409970482875329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12727746056273313655250219 19091619084409970482875329)
                ·
                  refine ⟨14318714313307477862156497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19091619084409970482875329 14318714313307477862156497)
                  ·
                    refine ⟨10739035734980608396617373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14318714313307477862156497 10739035734980608396617373)
                    ·
                      refine ⟨4027138400617728148731515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10739035734980608396617373 4027138400617728148731515)
                      ·
                        rfl

theorem cell23_7842824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_7842824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842824 prefixEnd_7842824 := by exact prefixLift 7842824
  have htrace : WordTrace (prefixWord ++ tailWord_7842824) baseStart_7842824 baseEnd_7842824 := by
    simpa [prefixWord, tailWord_7842824, baseEnd_7842824] using wordTrace_append hprefix tailTrace_7842824
  have hstable : (prefixWord ++ tailWord_7842824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842824).length < 2 ^ (prefixWord ++ tailWord_7842824).sum := by decide
  have hdescent : baseEnd_7842824 < baseStart_7842824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842894 : List Nat := [4, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4]
def baseStart_7842894 : Nat := 118140960795 + 7842894 * 2 ^ 59
def prefixEnd_7842894 : Nat := 4983230072969 + 3 ^ 40 * 7842894 * 2
def baseEnd_7842894 : Nat := 4027174344263542874856193

theorem tailTrace_7842894 : CollatzResearch.WordTrace tailWord_7842894 prefixEnd_7842894 4027174344263542874856193 := by
  unfold tailWord_7842894
  simp only [CollatzResearch.WordTrace]
  refine ⟨35756730556067746562559967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190702562965694648333653157 35756730556067746562559967)
  ·
    refine ⟨53635095834101619843839951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35756730556067746562559967 53635095834101619843839951)
    ·
      refine ⟨80452643751152429765759927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53635095834101619843839951 80452643751152429765759927)
      ·
        refine ⟨120678965626728644648639891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80452643751152429765759927 120678965626728644648639891)
        ·
          refine ⟨181018448440092966972959837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120678965626728644648639891 181018448440092966972959837)
          ·
            refine ⟨67881918165034862614859939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181018448440092966972959837 67881918165034862614859939)
            ·
              refine ⟨101822877247552293922289909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67881918165034862614859939 101822877247552293922289909)
              ·
                refine ⟨9545894741958027555214679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101822877247552293922289909 9545894741958027555214679)
                ·
                  refine ⟨14318842112937041332822019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9545894741958027555214679 14318842112937041332822019)
                  ·
                    refine ⟨21478263169405561999233029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14318842112937041332822019 21478263169405561999233029)
                    ·
                      refine ⟨4027174344263542874856193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21478263169405561999233029 4027174344263542874856193)
                      ·
                        rfl

theorem cell23_7842894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_7842894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842894 prefixEnd_7842894 := by exact prefixLift 7842894
  have htrace : WordTrace (prefixWord ++ tailWord_7842894) baseStart_7842894 baseEnd_7842894 := by
    simpa [prefixWord, tailWord_7842894, baseEnd_7842894] using wordTrace_append hprefix tailTrace_7842894
  have hstable : (prefixWord ++ tailWord_7842894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842894).length < 2 ^ (prefixWord ++ tailWord_7842894).sum := by decide
  have hdescent : baseEnd_7842894 < baseStart_7842894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842897 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 1, 1, 5]
def baseStart_7842897 : Nat := 118140960795 + 7842897 * 2 ^ 59
def prefixEnd_7842897 : Nat := 4983230072969 + 3 ^ 40 * 7842897 * 2
def baseEnd_7842897 : Nat := 4027175884705506363118679

theorem tailTrace_7842897 : CollatzResearch.WordTrace tailWord_7842897 prefixEnd_7842897 4027175884705506363118679 := by
  unfold tailWord_7842897
  simp only [CollatzResearch.WordTrace]
  refine ⟨286053953867531104012838945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190702635911687402675225963 286053953867531104012838945)
  ·
    refine ⟨214540465400648328009629209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286053953867531104012838945 214540465400648328009629209)
    ·
      refine ⟨160905349050486246007221907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214540465400648328009629209 160905349050486246007221907)
      ·
        refine ⟨241358023575729369010832861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160905349050486246007221907 241358023575729369010832861)
        ·
          refine ⟨90509258840898513379062323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241358023575729369010832861 90509258840898513379062323)
          ·
            refine ⟨135763888261347770068593485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90509258840898513379062323 135763888261347770068593485)
            ·
              refine ⟨50911458098005413775722557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135763888261347770068593485 50911458098005413775722557)
              ·
                refine ⟨19091796786752030165895959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50911458098005413775722557 19091796786752030165895959)
                ·
                  refine ⟨28637695180128045248843939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19091796786752030165895959 28637695180128045248843939)
                  ·
                    refine ⟨42956542770192067873265909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28637695180128045248843939 42956542770192067873265909)
                    ·
                      refine ⟨4027175884705506363118679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42956542770192067873265909 4027175884705506363118679)
                      ·
                        rfl

theorem cell23_7842897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_7842897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842897 prefixEnd_7842897 := by exact prefixLift 7842897
  have htrace : WordTrace (prefixWord ++ tailWord_7842897) baseStart_7842897 baseEnd_7842897 := by
    simpa [prefixWord, tailWord_7842897, baseEnd_7842897] using wordTrace_append hprefix tailTrace_7842897
  have hstable : (prefixWord ++ tailWord_7842897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842897).length < 2 ^ (prefixWord ++ tailWord_7842897).sum := by decide
  have hdescent : baseEnd_7842897 < baseStart_7842897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842904 : List Nat := [2, 1, 2, 2, 1, 3, 2, 4, 2, 4]
def baseStart_7842904 : Nat := 118140960795 + 7842904 * 2 ^ 59
def prefixEnd_7842904 : Nat := 4983230072969 + 3 ^ 40 * 7842904 * 2
def baseEnd_7842904 : Nat := 1342393159690029278577049

theorem tailTrace_7842904 : CollatzResearch.WordTrace tailWord_7842904 prefixEnd_7842904 1342393159690029278577049 := by
  unfold tailWord_7842904
  simp only [CollatzResearch.WordTrace]
  refine ⟨143027104589252872104171883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190702806119003829472229177 143027104589252872104171883)
  ·
    refine ⟨214540656883879308156257825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143027104589252872104171883 214540656883879308156257825)
    ·
      refine ⟨160905492662909481117193369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214540656883879308156257825 160905492662909481117193369)
      ·
        refine ⟨120679119497182110837895027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160905492662909481117193369 120679119497182110837895027)
        ·
          refine ⟨181018679245773166256842541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120679119497182110837895027 181018679245773166256842541)
          ·
            refine ⟨67882004717164937346315953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181018679245773166256842541 67882004717164937346315953)
            ·
              refine ⟨50911503537873703009736965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67882004717164937346315953 50911503537873703009736965)
              ·
                refine ⟨9545906913351319314325681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50911503537873703009736965 9545906913351319314325681)
                ·
                  refine ⟨7159430185013489485744261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9545906913351319314325681 7159430185013489485744261)
                  ·
                    refine ⟨1342393159690029278577049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7159430185013489485744261 1342393159690029278577049)
                    ·
                      rfl

theorem cell23_7842904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_7842904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842904 prefixEnd_7842904 := by exact prefixLift 7842904
  have htrace : WordTrace (prefixWord ++ tailWord_7842904) baseStart_7842904 baseEnd_7842904 := by
    simpa [prefixWord, tailWord_7842904, baseEnd_7842904] using wordTrace_append hprefix tailTrace_7842904
  have hstable : (prefixWord ++ tailWord_7842904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842904).length < 2 ^ (prefixWord ++ tailWord_7842904).sum := by decide
  have hdescent : baseEnd_7842904 < baseStart_7842904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842917 : List Nat := [1, 3, 1, 3, 2, 1, 4, 8]
def baseStart_7842917 : Nat := 118140960795 + 7842917 * 2 ^ 59
def prefixEnd_7842917 : Nat := 4983230072969 + 3 ^ 40 * 7842917 * 2
def baseEnd_7842917 : Nat := 149155042752540603143281

theorem tailTrace_7842917 : CollatzResearch.WordTrace tailWord_7842917 prefixEnd_7842917 149155042752540603143281 := by
  unfold tailWord_7842917
  simp only [CollatzResearch.WordTrace]
  refine ⟨286054683327458647428567005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190703122218305764952378003 286054683327458647428567005)
  ·
    refine ⟨107270506247796992785712627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286054683327458647428567005 107270506247796992785712627)
    ·
      refine ⟨160905759371695489178568941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107270506247796992785712627 160905759371695489178568941)
      ·
        refine ⟨60339659764385808441963353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160905759371695489178568941 60339659764385808441963353)
        ·
          refine ⟨45254744823289356331472515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60339659764385808441963353 45254744823289356331472515)
          ·
            refine ⟨67882117234934034497208773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45254744823289356331472515 67882117234934034497208773)
            ·
              refine ⟨12727896981550131468226645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67882117234934034497208773 12727896981550131468226645)
              ·
                refine ⟨149155042752540603143281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12727896981550131468226645 149155042752540603143281)
                ·
                  rfl

theorem cell23_7842917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 8].length) (baseStart_7842917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842917 prefixEnd_7842917 := by exact prefixLift 7842917
  have htrace : WordTrace (prefixWord ++ tailWord_7842917) baseStart_7842917 baseEnd_7842917 := by
    simpa [prefixWord, tailWord_7842917, baseEnd_7842917] using wordTrace_append hprefix tailTrace_7842917
  have hstable : (prefixWord ++ tailWord_7842917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842917).length < 2 ^ (prefixWord ++ tailWord_7842917).sum := by decide
  have hdescent : baseEnd_7842917 < baseStart_7842917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842921 : List Nat := [1, 2, 1, 1, 1, 6, 4, 1, 2, 4]
def baseStart_7842921 : Nat := 118140960795 + 7842921 * 2 ^ 59
def prefixEnd_7842921 : Nat := 4983230072969 + 3 ^ 40 * 7842921 * 2
def baseEnd_7842921 : Nat := 1342396069413738089739523

theorem tailTrace_7842921 : CollatzResearch.WordTrace tailWord_7842921 prefixEnd_7842921 1342396069413738089739523 := by
  unfold tailWord_7842921
  simp only [CollatzResearch.WordTrace]
  refine ⟨286054829219444156111712617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190703219479629437407808411 286054829219444156111712617)
  ·
    refine ⟨214541121914583117083784463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286054829219444156111712617 214541121914583117083784463)
    ·
      refine ⟨321811682871874675625676695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214541121914583117083784463 321811682871874675625676695)
      ·
        refine ⟨482717524307812013438515043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321811682871874675625676695 482717524307812013438515043)
        ·
          refine ⟨724076286461718020157772565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482717524307812013438515043 724076286461718020157772565)
          ·
            refine ⟨33941075927893032194895589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 724076286461718020157772565 33941075927893032194895589)
            ·
              refine ⟨6363951736479943536542923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33941075927893032194895589 6363951736479943536542923)
              ·
                refine ⟨9545927604719915304814385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6363951736479943536542923 9545927604719915304814385)
                ·
                  refine ⟨7159445703539936478610789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9545927604719915304814385 7159445703539936478610789)
                  ·
                    refine ⟨1342396069413738089739523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7159445703539936478610789 1342396069413738089739523)
                    ·
                      rfl

theorem cell23_7842921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 2, 4].length) (baseStart_7842921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842921 prefixEnd_7842921 := by exact prefixLift 7842921
  have htrace : WordTrace (prefixWord ++ tailWord_7842921) baseStart_7842921 baseEnd_7842921 := by
    simpa [prefixWord, tailWord_7842921, baseEnd_7842921] using wordTrace_append hprefix tailTrace_7842921
  have hstable : (prefixWord ++ tailWord_7842921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842921).length < 2 ^ (prefixWord ++ tailWord_7842921).sum := by decide
  have hdescent : baseEnd_7842921 < baseStart_7842921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842942 : List Nat := [4, 2, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_7842942 : Nat := 118140960795 + 7842942 * 2 ^ 59
def prefixEnd_7842942 : Nat := 4983230072969 + 3 ^ 40 * 7842942 * 2
def baseEnd_7842942 : Nat := 1342399663778319562351991

theorem tailTrace_7842942 : CollatzResearch.WordTrace tailWord_7842942 prefixEnd_7842942 1342399663778319562351991 := by
  unfold tailWord_7842942
  simp only [CollatzResearch.WordTrace]
  refine ⟨35756949394046009587278385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190703730101578717798818053 35756949394046009587278385)
  ·
    refine ⟨26817712045534507190458789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35756949394046009587278385 26817712045534507190458789)
    ·
      refine ⟨5028321008537720098211023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26817712045534507190458789 5028321008537720098211023)
      ·
        refine ⟨7542481512806580147316535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5028321008537720098211023 7542481512806580147316535)
        ·
          refine ⟨11313722269209870220974803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7542481512806580147316535 11313722269209870220974803)
          ·
            refine ⟨16970583403814805331462205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11313722269209870220974803 16970583403814805331462205)
            ·
              refine ⟨6363968776430551999298327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16970583403814805331462205 6363968776430551999298327)
              ·
                refine ⟨9545953164645827998947491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6363968776430551999298327 9545953164645827998947491)
                ·
                  refine ⟨14318929746968741998421237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9545953164645827998947491 14318929746968741998421237)
                  ·
                    refine ⟨1342399663778319562351991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14318929746968741998421237 1342399663778319562351991)
                    ·
                      rfl

theorem cell23_7842942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_7842942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842942 prefixEnd_7842942 := by exact prefixLift 7842942
  have htrace : WordTrace (prefixWord ++ tailWord_7842942) baseStart_7842942 baseEnd_7842942 := by
    simpa [prefixWord, tailWord_7842942, baseEnd_7842942] using wordTrace_append hprefix tailTrace_7842942
  have hstable : (prefixWord ++ tailWord_7842942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842942).length < 2 ^ (prefixWord ++ tailWord_7842942).sum := by decide
  have hdescent : baseEnd_7842942 < baseStart_7842942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842944 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 6, 1, 3]
def baseStart_7842944 : Nat := 118140960795 + 7842944 * 2 ^ 59
def prefixEnd_7842944 : Nat := 4983230072969 + 3 ^ 40 * 7842944 * 2
def baseEnd_7842944 : Nat := 4027200018296267679230963

theorem tailTrace_7842944 : CollatzResearch.WordTrace tailWord_7842944 prefixEnd_7842944 4027200018296267679230963 := by
  unfold tailWord_7842944
  simp only [CollatzResearch.WordTrace]
  refine ⟨143027834049180415519899943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190703778732240554026533257 143027834049180415519899943)
  ·
    refine ⟨214541751073770623279849915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143027834049180415519899943 214541751073770623279849915)
    ·
      refine ⟨321812626610655934919774873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214541751073770623279849915 321812626610655934919774873)
      ·
        refine ⟨241359469957991951189831155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321812626610655934919774873 241359469957991951189831155)
        ·
          refine ⟨362039204936987926784746733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241359469957991951189831155 362039204936987926784746733)
          ·
            refine ⟨135764701851370472544280025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362039204936987926784746733 135764701851370472544280025)
            ·
              refine ⟨101823526388527854408210019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135764701851370472544280025 101823526388527854408210019)
              ·
                refine ⟨152735289582791781612315029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101823526388527854408210019 152735289582791781612315029)
                ·
                  refine ⟨7159466699193364763077267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152735289582791781612315029 7159466699193364763077267)
                  ·
                    refine ⟨10739200048790047144615901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7159466699193364763077267 10739200048790047144615901)
                    ·
                      refine ⟨4027200018296267679230963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10739200048790047144615901 4027200018296267679230963)
                      ·
                        rfl

theorem cell23_7842944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_7842944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842944 prefixEnd_7842944 := by exact prefixLift 7842944
  have htrace : WordTrace (prefixWord ++ tailWord_7842944) baseStart_7842944 baseEnd_7842944 := by
    simpa [prefixWord, tailWord_7842944, baseEnd_7842944] using wordTrace_append hprefix tailTrace_7842944
  have hstable : (prefixWord ++ tailWord_7842944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842944).length < 2 ^ (prefixWord ++ tailWord_7842944).sum := by decide
  have hdescent : baseEnd_7842944 < baseStart_7842944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842948 : List Nat := [2, 3, 2, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_7842948 : Nat := 118140960795 + 7842948 * 2 ^ 59
def prefixEnd_7842948 : Nat := 4983230072969 + 3 ^ 40 * 7842948 * 2
def baseEnd_7842948 : Nat := 4027202072218885663580945

theorem tailTrace_7842948 : CollatzResearch.WordTrace tailWord_7842948 prefixEnd_7842948 4027202072218885663580945 := by
  unfold tailWord_7842948
  simp only [CollatzResearch.WordTrace]
  refine ⟨143027906995173169861472749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190703875993564226481963665 143027906995173169861472749)
  ·
    refine ⟨53635465123189938698052281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143027906995173169861472749 53635465123189938698052281)
    ·
      refine ⟨40226598842392454023539211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53635465123189938698052281 40226598842392454023539211)
      ·
        refine ⟨60339898263588681035308817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40226598842392454023539211 60339898263588681035308817)
        ·
          refine ⟨45254923697691510776481613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60339898263588681035308817 45254923697691510776481613)
          ·
            refine ⟨16970596386634316541180605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45254923697691510776481613 16970596386634316541180605)
            ·
              refine ⟨6363973644987868702942727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16970596386634316541180605 6363973644987868702942727)
              ·
                refine ⟨9545960467481803054414091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6363973644987868702942727 9545960467481803054414091)
                ·
                  refine ⟨14318940701222704581621137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9545960467481803054414091 14318940701222704581621137)
                  ·
                    refine ⟨10739205525917028436215853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14318940701222704581621137 10739205525917028436215853)
                    ·
                      refine ⟨4027202072218885663580945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10739205525917028436215853 4027202072218885663580945)
                      ·
                        rfl

theorem cell23_7842948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_7842948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842948 prefixEnd_7842948 := by exact prefixLift 7842948
  have htrace : WordTrace (prefixWord ++ tailWord_7842948) baseStart_7842948 baseEnd_7842948 := by
    simpa [prefixWord, tailWord_7842948, baseEnd_7842948] using wordTrace_append hprefix tailTrace_7842948
  have hstable : (prefixWord ++ tailWord_7842948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842948).length < 2 ^ (prefixWord ++ tailWord_7842948).sum := by decide
  have hdescent : baseEnd_7842948 < baseStart_7842948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842962 : List Nat := [3, 2, 3, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_7842962 : Nat := 118140960795 + 7842962 * 2 ^ 59
def prefixEnd_7842962 : Nat := 4983230072969 + 3 ^ 40 * 7842962 * 2
def baseEnd_7842962 : Nat := 4027209260948048608805881

theorem tailTrace_7842962 : CollatzResearch.WordTrace tailWord_7842962 prefixEnd_7842962 4027209260948048608805881 := by
  unfold tailWord_7842962
  simp only [CollatzResearch.WordTrace]
  refine ⟨71514081153073905028488785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190704216408197080075970093 71514081153073905028488785)
  ·
    refine ⟨53635560864805428771366589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71514081153073905028488785 53635560864805428771366589)
    ·
      refine ⟨20113335324302035789262471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53635560864805428771366589 20113335324302035789262471)
      ·
        refine ⟨30170002986453053683893707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20113335324302035789262471 30170002986453053683893707)
        ·
          refine ⟨45255004479679580525840561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30170002986453053683893707 45255004479679580525840561)
          ·
            refine ⟨33941253359759685394380421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45255004479679580525840561 33941253359759685394380421)
            ·
              refine ⟨6363985004954941011446329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33941253359759685394380421 6363985004954941011446329)
              ·
                refine ⟨4772988753716205758584747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6363985004954941011446329 4772988753716205758584747)
                ·
                  refine ⟨7159483130574308637877121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4772988753716205758584747 7159483130574308637877121)
                  ·
                    refine ⟨5369612347930731478407841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7159483130574308637877121 5369612347930731478407841)
                    ·
                      refine ⟨4027209260948048608805881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5369612347930731478407841 4027209260948048608805881)
                      ·
                        rfl

theorem cell23_7842962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_7842962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842962 prefixEnd_7842962 := by exact prefixLift 7842962
  have htrace : WordTrace (prefixWord ++ tailWord_7842962) baseStart_7842962 baseEnd_7842962 := by
    simpa [prefixWord, tailWord_7842962, baseEnd_7842962] using wordTrace_append hprefix tailTrace_7842962
  have hstable : (prefixWord ++ tailWord_7842962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842962).length < 2 ^ (prefixWord ++ tailWord_7842962).sum := by decide
  have hdescent : baseEnd_7842962 < baseStart_7842962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842978 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_7842978 : Nat := 118140960795 + 7842978 * 2 ^ 59
def prefixEnd_7842978 : Nat := 4983230072969 + 3 ^ 40 * 7842978 * 2
def baseEnd_7842978 : Nat := 4027217476638520546205807

theorem tailTrace_7842978 : CollatzResearch.WordTrace tailWord_7842978 prefixEnd_7842978 4027217476638520546205807 := by
  unfold tailWord_7842978
  simp only [CollatzResearch.WordTrace]
  refine ⟨71514227045059413711634397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190704605453491769897691725 71514227045059413711634397)
  ·
    refine ⟨26817835141897280141862899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71514227045059413711634397 26817835141897280141862899)
    ·
      refine ⟨40226752712845920212794349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26817835141897280141862899 40226752712845920212794349)
      ·
        refine ⟨15085032267317220079797881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40226752712845920212794349 15085032267317220079797881)
        ·
          refine ⟨11313774200487915059848411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15085032267317220079797881 11313774200487915059848411)
          ·
            refine ⟨16970661300731872589772617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11313774200487915059848411 16970661300731872589772617)
            ·
              refine ⟨12727995975548904442329463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16970661300731872589772617 12727995975548904442329463)
              ·
                refine ⟨19091993963323356663494195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12727995975548904442329463 19091993963323356663494195)
                ·
                  refine ⟨28637990944985034995241293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19091993963323356663494195 28637990944985034995241293)
                  ·
                    refine ⟨10739246604369388123215485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28637990944985034995241293 10739246604369388123215485)
                    ·
                      refine ⟨4027217476638520546205807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10739246604369388123215485 4027217476638520546205807)
                      ·
                        rfl

theorem cell23_7842978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_7842978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842978 prefixEnd_7842978 := by exact prefixLift 7842978
  have htrace : WordTrace (prefixWord ++ tailWord_7842978) baseStart_7842978 baseEnd_7842978 := by
    simpa [prefixWord, tailWord_7842978, baseEnd_7842978] using wordTrace_append hprefix tailTrace_7842978
  have hstable : (prefixWord ++ tailWord_7842978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842978).length < 2 ^ (prefixWord ++ tailWord_7842978).sum := by decide
  have hdescent : baseEnd_7842978 < baseStart_7842978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843001 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 1, 4, 2]
def baseStart_7843001 : Nat := 118140960795 + 7843001 * 2 ^ 59
def prefixEnd_7843001 : Nat := 4983230072969 + 3 ^ 40 * 7843001 * 2
def baseEnd_7843001 : Nat := 4027229286693573956218201

theorem tailTrace_7843001 : CollatzResearch.WordTrace tailWord_7843001 prefixEnd_7843001 4027229286693573956218201 := by
  unfold tailWord_7843001
  simp only [CollatzResearch.WordTrace]
  refine ⟨286057747059154329774624857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190705164706102886516416571 286057747059154329774624857)
  ·
    refine ⟨214543310294365747330968643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286057747059154329774624857 214543310294365747330968643)
    ·
      refine ⟨321814965441548620996452965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214543310294365747330968643 321814965441548620996452965)
      ·
        refine ⟨60340306020290366436834931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321814965441548620996452965 60340306020290366436834931)
        ·
          refine ⟨90510459030435549655252397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60340306020290366436834931 90510459030435549655252397)
          ·
            refine ⟨33941422136413331120719649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90510459030435549655252397 33941422136413331120719649)
            ·
              refine ⟨25456066602309998340539737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33941422136413331120719649 25456066602309998340539737)
              ·
                refine ⟨19092049951732498755404803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25456066602309998340539737 19092049951732498755404803)
                ·
                  refine ⟨28638074927598748133107205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19092049951732498755404803 28638074927598748133107205)
                  ·
                    refine ⟨5369639048924765274957601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28638074927598748133107205 5369639048924765274957601)
                    ·
                      refine ⟨4027229286693573956218201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5369639048924765274957601 4027229286693573956218201)
                      ·
                        rfl

theorem cell23_7843001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_7843001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843001 prefixEnd_7843001 := by exact prefixLift 7843001
  have htrace : WordTrace (prefixWord ++ tailWord_7843001) baseStart_7843001 baseEnd_7843001 := by
    simpa [prefixWord, tailWord_7843001, baseEnd_7843001] using wordTrace_append hprefix tailTrace_7843001
  have hstable : (prefixWord ++ tailWord_7843001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843001).length < 2 ^ (prefixWord ++ tailWord_7843001).sum := by decide
  have hdescent : baseEnd_7843001 < baseStart_7843001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843012 : List Nat := [2, 3, 3, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_7843012 : Nat := 118140960795 + 7843012 * 2 ^ 59
def prefixEnd_7843012 : Nat := 4983230072969 + 3 ^ 40 * 7843012 * 2
def baseEnd_7843012 : Nat := 4027234934980773413180651

theorem tailTrace_7843012 : CollatzResearch.WordTrace tailWord_7843012 prefixEnd_7843012 4027234934980773413180651 := by
  unfold tailWord_7843012
  simp only [CollatzResearch.WordTrace]
  refine ⟨143029074131057239326637645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190705432174742985768850193 143029074131057239326637645)
  ·
    refine ⟨53635902799146464747489117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143029074131057239326637645 53635902799146464747489117)
    ·
      refine ⟨20113463549679924280308419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53635902799146464747489117 20113463549679924280308419)
      ·
        refine ⟨30170195324519886420462629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20113463549679924280308419 30170195324519886420462629)
        ·
          refine ⟨5656911623347478703836743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30170195324519886420462629 5656911623347478703836743)
          ·
            refine ⟨8485367435021218055755115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5656911623347478703836743 8485367435021218055755115)
            ·
              refine ⟨12728051152531827083632673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8485367435021218055755115 12728051152531827083632673)
              ·
                refine ⟨9546038364398870312724505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12728051152531827083632673 9546038364398870312724505)
                ·
                  refine ⟨7159528773299152734543379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9546038364398870312724505 7159528773299152734543379)
                  ·
                    refine ⟨10739293159948729101815069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7159528773299152734543379 10739293159948729101815069)
                    ·
                      refine ⟨4027234934980773413180651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10739293159948729101815069 4027234934980773413180651)
                      ·
                        rfl

theorem cell23_7843012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_7843012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843012 prefixEnd_7843012 := by exact prefixLift 7843012
  have htrace : WordTrace (prefixWord ++ tailWord_7843012) baseStart_7843012 baseEnd_7843012 := by
    simpa [prefixWord, tailWord_7843012, baseEnd_7843012] using wordTrace_append hprefix tailTrace_7843012
  have hstable : (prefixWord ++ tailWord_7843012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843012).length < 2 ^ (prefixWord ++ tailWord_7843012).sum := by decide
  have hdescent : baseEnd_7843012 < baseStart_7843012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843018 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 4, 2, 2]
def baseStart_7843018 : Nat := 118140960795 + 7843018 * 2 ^ 59
def prefixEnd_7843018 : Nat := 4983230072969 + 3 ^ 40 * 7843018 * 2
def baseEnd_7843018 : Nat := 4027238015864700389705623

theorem tailTrace_7843018 : CollatzResearch.WordTrace tailWord_7843018 prefixEnd_7843018 4027238015864700389705623 := by
  unfold tailWord_7843018
  simp only [CollatzResearch.WordTrace]
  refine ⟨71514591775023185419498427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190705578066728494451995805 71514591775023185419498427)
  ·
    refine ⟨107271887662534778129247641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71514591775023185419498427 107271887662534778129247641)
    ·
      refine ⟨80453915746901083596935731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107271887662534778129247641 80453915746901083596935731)
      ·
        refine ⟨120680873620351625395403597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80453915746901083596935731 120680873620351625395403597)
        ·
          refine ⟨45255327607631859523276349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120680873620351625395403597 45255327607631859523276349)
          ·
            refine ⟨16970747852861947321228631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45255327607631859523276349 16970747852861947321228631)
            ·
              refine ⟨25456121779292920981842947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16970747852861947321228631 25456121779292920981842947)
              ·
                refine ⟨38184182668939381472764421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25456121779292920981842947 38184182668939381472764421)
                ·
                  refine ⟨7159534250426134026143329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38184182668939381472764421 7159534250426134026143329)
                  ·
                    refine ⟨5369650687819600519607497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7159534250426134026143329 5369650687819600519607497)
                    ·
                      refine ⟨4027238015864700389705623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5369650687819600519607497 4027238015864700389705623)
                      ·
                        rfl

theorem cell23_7843018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_7843018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843018 prefixEnd_7843018 := by exact prefixLift 7843018
  have htrace : WordTrace (prefixWord ++ tailWord_7843018) baseStart_7843018 baseEnd_7843018 := by
    simpa [prefixWord, tailWord_7843018, baseEnd_7843018] using wordTrace_append hprefix tailTrace_7843018
  have hstable : (prefixWord ++ tailWord_7843018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843018).length < 2 ^ (prefixWord ++ tailWord_7843018).sum := by decide
  have hdescent : baseEnd_7843018 < baseStart_7843018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843054 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_7843054 : Nat := 118140960795 + 7843054 * 2 ^ 59
def prefixEnd_7843054 : Nat := 4983230072969 + 3 ^ 40 * 7843054 * 2
def baseEnd_7843054 : Nat := 1342418833722754082951819

theorem tailTrace_7843054 : CollatzResearch.WordTrace tailWord_7843054 prefixEnd_7843054 1342418833722754082951819 := by
  unfold tailWord_7843054
  simp only [CollatzResearch.WordTrace]
  refine ⟨35757460015995289978288027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190706453418641546550869477 35757460015995289978288027)
  ·
    refine ⟨53636190023992934967432041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35757460015995289978288027 53636190023992934967432041)
    ·
      refine ⟨40227142517994701225574031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53636190023992934967432041 40227142517994701225574031)
      ·
        refine ⟨60340713776992051838361047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40227142517994701225574031 60340713776992051838361047)
        ·
          refine ⟨90511070665488077757541571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60340713776992051838361047 90511070665488077757541571)
          ·
            refine ⟨135766605998232116636312357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90511070665488077757541571 135766605998232116636312357)
            ·
              refine ⟨25456238624668521869308567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135766605998232116636312357 25456238624668521869308567)
              ·
                refine ⟨38184357937002782803962851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25456238624668521869308567 38184357937002782803962851)
                ·
                  refine ⟨57276536905504174205944277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38184357937002782803962851 57276536905504174205944277)
                  ·
                    refine ⟨1342418833722754082951819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57276536905504174205944277 1342418833722754082951819)
                    ·
                      rfl

theorem cell23_7843054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_7843054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843054 prefixEnd_7843054 := by exact prefixLift 7843054
  have htrace : WordTrace (prefixWord ++ tailWord_7843054) baseStart_7843054 baseEnd_7843054 := by
    simpa [prefixWord, tailWord_7843054, baseEnd_7843054] using wordTrace_append hprefix tailTrace_7843054
  have hstable : (prefixWord ++ tailWord_7843054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843054).length < 2 ^ (prefixWord ++ tailWord_7843054).sum := by decide
  have hdescent : baseEnd_7843054 < baseStart_7843054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843135 : List Nat := [1, 1, 2, 2, 4, 2, 4, 2, 1, 4]
def baseStart_7843135 : Nat := 118140960795 + 7843135 * 2 ^ 59
def prefixEnd_7843135 : Nat := 4983230072969 + 3 ^ 40 * 7843135 * 2
def baseEnd_7843135 : Nat := 1342432697700425477314195

theorem tailTrace_7843135 : CollatzResearch.WordTrace tailWord_7843135 prefixEnd_7843135 1342432697700425477314195 := by
  unfold tailWord_7843135
  simp only [CollatzResearch.WordTrace]
  refine ⟨286062634440668870660002859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190708422960445913773335239 286062634440668870660002859)
  ·
    refine ⟨429093951661003305990004289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286062634440668870660002859 429093951661003305990004289)
    ·
      refine ⟨321820463745752479492503217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429093951661003305990004289 321820463745752479492503217)
      ·
        refine ⟨241365347809314359619377413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321820463745752479492503217 241365347809314359619377413)
        ·
          refine ⟨45256002714246442428633265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241365347809314359619377413 45256002714246442428633265)
          ·
            refine ⟨33942002035684831821474949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45256002714246442428633265 33942002035684831821474949)
            ·
              refine ⟨6364125381690905966526553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33942002035684831821474949 6364125381690905966526553)
              ·
                refine ⟨4773094036268179474894915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6364125381690905966526553 4773094036268179474894915)
                ·
                  refine ⟨7159641054402269212342373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4773094036268179474894915 7159641054402269212342373)
                  ·
                    refine ⟨1342432697700425477314195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7159641054402269212342373 1342432697700425477314195)
                    ·
                      rfl

theorem cell23_7843135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 1, 4].length) (baseStart_7843135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843135 prefixEnd_7843135 := by exact prefixLift 7843135
  have htrace : WordTrace (prefixWord ++ tailWord_7843135) baseStart_7843135 baseEnd_7843135 := by
    simpa [prefixWord, tailWord_7843135, baseEnd_7843135] using wordTrace_append hprefix tailTrace_7843135
  have hstable : (prefixWord ++ tailWord_7843135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843135).length < 2 ^ (prefixWord ++ tailWord_7843135).sum := by decide
  have hdescent : baseEnd_7843135 < baseStart_7843135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843141 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 7, 1, 3]
def baseStart_7843141 : Nat := 118140960795 + 7843141 * 2 ^ 59
def prefixEnd_7843141 : Nat := 4983230072969 + 3 ^ 40 * 7843141 * 2
def baseEnd_7843141 : Nat := 4027301173985203408467557

theorem tailTrace_7843141 : CollatzResearch.WordTrace tailWord_7843141 prefixEnd_7843141 4027301173985203408467557 := by
  unfold tailWord_7843141
  simp only [CollatzResearch.WordTrace]
  refine ⟨286062853278647133684721277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190708568852431422456480851 286062853278647133684721277)
  ·
    refine ⟨107273569979492675131770479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286062853278647133684721277 107273569979492675131770479)
    ·
      refine ⟨160910354969239012697655719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107273569979492675131770479 160910354969239012697655719)
      ·
        refine ⟨241365532453858519046483579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160910354969239012697655719 241365532453858519046483579)
        ·
          refine ⟨362048298680787778569725369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241365532453858519046483579 362048298680787778569725369)
          ·
            refine ⟨271536224010590833927294027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362048298680787778569725369 271536224010590833927294027)
            ·
              refine ⟨407304336015886250890941041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271536224010590833927294027 407304336015886250890941041)
              ·
                refine ⟨305478252011914688168205781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407304336015886250890941041 305478252011914688168205781)
                ·
                  refine ⟨7159646531529250503942323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 305478252011914688168205781 7159646531529250503942323)
                  ·
                    refine ⟨10739469797293875755913485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7159646531529250503942323 10739469797293875755913485)
                    ·
                      refine ⟨4027301173985203408467557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10739469797293875755913485 4027301173985203408467557)
                      ·
                        rfl

theorem cell23_7843141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_7843141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843141 prefixEnd_7843141 := by exact prefixLift 7843141
  have htrace : WordTrace (prefixWord ++ tailWord_7843141) baseStart_7843141 baseEnd_7843141 := by
    simpa [prefixWord, tailWord_7843141, baseEnd_7843141] using wordTrace_append hprefix tailTrace_7843141
  have hstable : (prefixWord ++ tailWord_7843141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843141).length < 2 ^ (prefixWord ++ tailWord_7843141).sum := by decide
  have hdescent : baseEnd_7843141 < baseStart_7843141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843154 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_7843154 : Nat := 118140960795 + 7843154 * 2 ^ 59
def prefixEnd_7843154 : Nat := 4983230072969 + 3 ^ 40 * 7843154 * 2
def baseEnd_7843154 : Nat := 4027307849233711857604997

theorem tailTrace_7843154 : CollatzResearch.WordTrace tailWord_7843154 prefixEnd_7843154 4027307849233711857604997 := by
  unfold tailWord_7843154
  simp only [CollatzResearch.WordTrace]
  refine ⟨71515831856900009226236129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190708884951733357936629677 71515831856900009226236129)
  ·
    refine ⟨53636873892675006919677097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71515831856900009226236129 53636873892675006919677097)
    ·
      refine ⟨40227655419506255189757823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53636873892675006919677097 40227655419506255189757823)
      ·
        refine ⟨60341483129259382784636735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40227655419506255189757823 60341483129259382784636735)
        ·
          refine ⟨90512224693889074176955103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60341483129259382784636735 90512224693889074176955103)
          ·
            refine ⟨135768337040833611265432655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90512224693889074176955103 135768337040833611265432655)
            ·
              refine ⟨203652505561250416898148983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135768337040833611265432655 203652505561250416898148983)
              ·
                refine ⟨305478758341875625347223475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203652505561250416898148983 305478758341875625347223475)
                ·
                  refine ⟨458218137512813438020835213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305478758341875625347223475 458218137512813438020835213)
                  ·
                    refine ⟨171831801567305039257813205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 458218137512813438020835213 171831801567305039257813205)
                    ·
                      refine ⟨4027307849233711857604997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171831801567305039257813205 4027307849233711857604997)
                      ·
                        rfl

theorem cell23_7843154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_7843154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843154 prefixEnd_7843154 := by exact prefixLift 7843154
  have htrace : WordTrace (prefixWord ++ tailWord_7843154) baseStart_7843154 baseEnd_7843154 := by
    simpa [prefixWord, tailWord_7843154, baseEnd_7843154] using wordTrace_append hprefix tailTrace_7843154
  have hstable : (prefixWord ++ tailWord_7843154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843154).length < 2 ^ (prefixWord ++ tailWord_7843154).sum := by decide
  have hdescent : baseEnd_7843154 < baseStart_7843154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843168 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 1, 5, 2]
def baseStart_7843168 : Nat := 118140960795 + 7843168 * 2 ^ 59
def prefixEnd_7843168 : Nat := 4983230072969 + 3 ^ 40 * 7843168 * 2
def baseEnd_7843168 : Nat := 4027315037962874802829933

theorem tailTrace_7843168 : CollatzResearch.WordTrace tailWord_7843168 prefixEnd_7843168 4027315037962874802829933 := by
  unfold tailWord_7843168
  simp only [CollatzResearch.WordTrace]
  refine ⟨143031919024774658647977079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190709225366366211530636105 143031919024774658647977079)
  ·
    refine ⟨214547878537161987971965619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143031919024774658647977079 214547878537161987971965619)
    ·
      refine ⟨321821817805742981957948429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214547878537161987971965619 321821817805742981957948429)
      ·
        refine ⟨120683181677153618234230661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321821817805742981957948429 120683181677153618234230661)
        ·
          refine ⟨22628096564466303418918249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120683181677153618234230661 22628096564466303418918249)
          ·
            refine ⟨16971072423349727564188687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22628096564466303418918249 16971072423349727564188687)
            ·
              refine ⟨25456608635024591346283031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16971072423349727564188687 25456608635024591346283031)
              ·
                refine ⟨38184912952536887019424547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25456608635024591346283031 38184912952536887019424547)
                ·
                  refine ⟨57277369428805330529136821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38184912952536887019424547 57277369428805330529136821)
                  ·
                    refine ⟨5369753383950499737106577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57277369428805330529136821 5369753383950499737106577)
                    ·
                      refine ⟨4027315037962874802829933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5369753383950499737106577 4027315037962874802829933)
                      ·
                        rfl

theorem cell23_7843168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_7843168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843168 prefixEnd_7843168 := by exact prefixLift 7843168
  have htrace : WordTrace (prefixWord ++ tailWord_7843168) baseStart_7843168 baseEnd_7843168 := by
    simpa [prefixWord, tailWord_7843168, baseEnd_7843168] using wordTrace_append hprefix tailTrace_7843168
  have hstable : (prefixWord ++ tailWord_7843168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843168).length < 2 ^ (prefixWord ++ tailWord_7843168).sum := by decide
  have hdescent : baseEnd_7843168 < baseStart_7843168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843182 : List Nat := [4, 1, 2, 4, 2, 1, 1, 2, 6]
def baseStart_7843182 : Nat := 118140960795 + 7843182 * 2 ^ 59
def prefixEnd_7843182 : Nat := 4983230072969 + 3 ^ 40 * 7843182 * 2
def baseEnd_7843182 : Nat := 447480247410226416450541

theorem tailTrace_7843182 : CollatzResearch.WordTrace tailWord_7843182 prefixEnd_7843182 447480247410226416450541 := by
  unfold tailWord_7843182
  simp only [CollatzResearch.WordTrace]
  refine ⟨35758043583937324710870475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190709565780999065124642533 35758043583937324710870475)
  ·
    refine ⟨53637065375905987066305713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35758043583937324710870475 53637065375905987066305713)
    ·
      refine ⟨40227799031929490299729285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53637065375905987066305713 40227799031929490299729285)
      ·
        refine ⟨7542712318486779431199241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40227799031929490299729285 7542712318486779431199241)
        ·
          refine ⟨5657034238865084573399431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7542712318486779431199241 5657034238865084573399431)
          ·
            refine ⟨8485551358297626860099147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5657034238865084573399431 8485551358297626860099147)
            ·
              refine ⟨12728327037446440290148721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8485551358297626860099147 12728327037446440290148721)
              ·
                refine ⟨9546245278084830217611541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12728327037446440290148721 9546245278084830217611541)
                ·
                  refine ⟨447480247410226416450541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9546245278084830217611541 447480247410226416450541)
                  ·
                    rfl

theorem cell23_7843182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_7843182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843182 prefixEnd_7843182 := by exact prefixLift 7843182
  have htrace : WordTrace (prefixWord ++ tailWord_7843182) baseStart_7843182 baseEnd_7843182 := by
    simpa [prefixWord, tailWord_7843182, baseEnd_7843182] using wordTrace_append hprefix tailTrace_7843182
  have hstable : (prefixWord ++ tailWord_7843182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843182).length < 2 ^ (prefixWord ++ tailWord_7843182).sum := by decide
  have hdescent : baseEnd_7843182 < baseStart_7843182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843191 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 4, 4]
def baseStart_7843191 : Nat := 118140960795 + 7843191 * 2 ^ 59
def prefixEnd_7843191 : Nat := 4983230072969 + 3 ^ 40 * 7843191 * 2
def baseEnd_7843191 : Nat := 1342442282672642737614109

theorem tailTrace_7843191 : CollatzResearch.WordTrace tailWord_7843191 prefixEnd_7843191 1342442282672642737614109 := by
  unfold tailWord_7843191
  simp only [CollatzResearch.WordTrace]
  refine ⟨286064676928465992224041427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190709784618977328149360951 286064676928465992224041427)
  ·
    refine ⟨429097015392698988336062141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286064676928465992224041427 429097015392698988336062141)
    ·
      refine ⟨160911380772262120626023303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429097015392698988336062141 160911380772262120626023303)
      ·
        refine ⟨241367071158393180939034955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160911380772262120626023303 241367071158393180939034955)
        ·
          refine ⟨362050606737589771408552433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241367071158393180939034955 362050606737589771408552433)
          ·
            refine ⟨271537955053192328556414325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362050606737589771408552433 271537955053192328556414325)
            ·
              refine ⟨25456683286236780802163843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271537955053192328556414325 25456683286236780802163843)
              ·
                refine ⟨38185024929355171203245765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25456683286236780802163843 38185024929355171203245765)
                ·
                  refine ⟨7159692174254094600608581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38185024929355171203245765 7159692174254094600608581)
                  ·
                    refine ⟨1342442282672642737614109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7159692174254094600608581 1342442282672642737614109)
                    ·
                      rfl

theorem cell23_7843191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_7843191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843191 prefixEnd_7843191 := by exact prefixLift 7843191
  have htrace : WordTrace (prefixWord ++ tailWord_7843191) baseStart_7843191 baseEnd_7843191 := by
    simpa [prefixWord, tailWord_7843191, baseEnd_7843191] using wordTrace_append hprefix tailTrace_7843191
  have hstable : (prefixWord ++ tailWord_7843191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843191).length < 2 ^ (prefixWord ++ tailWord_7843191).sum := by decide
  have hdescent : baseEnd_7843191 < baseStart_7843191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843194 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_7843194 : Nat := 118140960795 + 7843194 * 2 ^ 59
def prefixEnd_7843194 : Nat := 4983230072969 + 3 ^ 40 * 7843194 * 2
def baseEnd_7843194 : Nat := 4027328388459891701104813

theorem tailTrace_7843194 : CollatzResearch.WordTrace tailWord_7843194 prefixEnd_7843194 4027328388459891701104813 := by
  unfold tailWord_7843194
  simp only [CollatzResearch.WordTrace]
  refine ⟨71516196586863780934100159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190709857564970082490933757 71516196586863780934100159)
  ·
    refine ⟨107274294880295671401150239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71516196586863780934100159 107274294880295671401150239)
    ·
      refine ⟨160911442320443507101725359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107274294880295671401150239 160911442320443507101725359)
      ·
        refine ⟨241367163480665260652588039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160911442320443507101725359 241367163480665260652588039)
        ·
          refine ⟨362050745220997890978882059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241367163480665260652588039 362050745220997890978882059)
          ·
            refine ⟨543076117831496836468323089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362050745220997890978882059 543076117831496836468323089)
            ·
              refine ⟨407307088373622627351242317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543076117831496836468323089 407307088373622627351242317)
              ·
                refine ⟨152740158140108485256715869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407307088373622627351242317 152740158140108485256715869)
                ·
                  refine ⟨57277559302540681971268451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152740158140108485256715869 57277559302540681971268451)
                  ·
                    refine ⟨85916338953811022956902677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57277559302540681971268451 85916338953811022956902677)
                    ·
                      refine ⟨4027328388459891701104813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85916338953811022956902677 4027328388459891701104813)
                      ·
                        rfl

theorem cell23_7843194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_7843194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843194 prefixEnd_7843194 := by exact prefixLift 7843194
  have htrace : WordTrace (prefixWord ++ tailWord_7843194) baseStart_7843194 baseEnd_7843194 := by
    simpa [prefixWord, tailWord_7843194, baseEnd_7843194] using wordTrace_append hprefix tailTrace_7843194
  have hstable : (prefixWord ++ tailWord_7843194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843194).length < 2 ^ (prefixWord ++ tailWord_7843194).sum := by decide
  have hdescent : baseEnd_7843194 < baseStart_7843194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843208 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 1, 6]
def baseStart_7843208 : Nat := 118140960795 + 7843208 * 2 ^ 59
def prefixEnd_7843208 : Nat := 4983230072969 + 3 ^ 40 * 7843208 * 2
def baseEnd_7843208 : Nat := 1342445192396351548776583

theorem tailTrace_7843208 : CollatzResearch.WordTrace tailWord_7843208 prefixEnd_7843208 1342445192396351548776583 := by
  unfold tailWord_7843208
  simp only [CollatzResearch.WordTrace]
  refine ⟨143032648484702202063705139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190710197979602936084940185 143032648484702202063705139)
  ·
    refine ⟨214548972727053303095557709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143032648484702202063705139 214548972727053303095557709)
    ·
      refine ⟨80455864772644988660834141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214548972727053303095557709 80455864772644988660834141)
      ·
        refine ⟨30170949289741870747812803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80455864772644988660834141 30170949289741870747812803)
        ·
          refine ⟨45256423934612806121719205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30170949289741870747812803 45256423934612806121719205)
          ·
            refine ⟨8485579487739901147822351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45256423934612806121719205 8485579487739901147822351)
            ·
              refine ⟨12728369231609851721733527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8485579487739901147822351 12728369231609851721733527)
              ·
                refine ⟨19092553847414777582600291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12728369231609851721733527 19092553847414777582600291)
                ·
                  refine ⟨28638830771122166373900437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19092553847414777582600291 28638830771122166373900437)
                  ·
                    refine ⟨1342445192396351548776583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28638830771122166373900437 1342445192396351548776583)
                    ·
                      rfl

theorem cell23_7843208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_7843208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843208 prefixEnd_7843208 := by exact prefixLift 7843208
  have htrace : WordTrace (prefixWord ++ tailWord_7843208) baseStart_7843208 baseEnd_7843208 := by
    simpa [prefixWord, tailWord_7843208, baseEnd_7843208] using wordTrace_append hprefix tailTrace_7843208
  have hstable : (prefixWord ++ tailWord_7843208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843208).length < 2 ^ (prefixWord ++ tailWord_7843208).sum := by decide
  have hdescent : baseEnd_7843208 < baseStart_7843208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843221 : List Nat := [1, 3, 2, 1, 1, 2, 6, 7]
def baseStart_7843221 : Nat := 118140960795 + 7843221 * 2 ^ 59
def prefixEnd_7843221 : Nat := 4983230072969 + 3 ^ 40 * 7843221 * 2
def baseEnd_7843221 : Nat := 149160824164354188721007

theorem tailTrace_7843221 : CollatzResearch.WordTrace tailWord_7843221 prefixEnd_7843221 149160824164354188721007 := by
  unfold tailWord_7843221
  simp only [CollatzResearch.WordTrace]
  refine ⟨286065771118357307347633517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190710514078904871565089011 286065771118357307347633517)
  ·
    refine ⟨107274664169383990255362569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286065771118357307347633517 107274664169383990255362569)
    ·
      refine ⟨80455998127037992691521927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107274664169383990255362569 80455998127037992691521927)
      ·
        refine ⟨120683997190556989037282891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80455998127037992691521927 120683997190556989037282891)
        ·
          refine ⟨181025995785835483555924337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120683997190556989037282891 181025995785835483555924337)
          ·
            refine ⟨135769496839376612666943253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181025995785835483555924337 135769496839376612666943253)
            ·
              refine ⟨6364195164345778718762965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135769496839376612666943253 6364195164345778718762965)
              ·
                refine ⟨149160824164354188721007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6364195164345778718762965 149160824164354188721007)
                ·
                  rfl

theorem cell23_7843221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 7].length) (baseStart_7843221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843221 prefixEnd_7843221 := by exact prefixLift 7843221
  have htrace : WordTrace (prefixWord ++ tailWord_7843221) baseStart_7843221 baseEnd_7843221 := by
    simpa [prefixWord, tailWord_7843221, baseEnd_7843221] using wordTrace_append hprefix tailTrace_7843221
  have hstable : (prefixWord ++ tailWord_7843221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843221).length < 2 ^ (prefixWord ++ tailWord_7843221).sum := by decide
  have hdescent : baseEnd_7843221 < baseStart_7843221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843249 : List Nat := [1, 2, 2, 4, 1, 1, 5, 2, 1, 2, 2]
def baseStart_7843249 : Nat := 118140960795 + 7843249 * 2 ^ 59
def prefixEnd_7843249 : Nat := 4983230072969 + 3 ^ 40 * 7843249 * 2
def baseEnd_7843249 : Nat := 4027356629895888985917061

theorem tailTrace_7843249 : CollatzResearch.WordTrace tailWord_7843249 prefixEnd_7843249 4027356629895888985917061 := by
  unfold tailWord_7843249
  simp only [CollatzResearch.WordTrace]
  refine ⟨286066792362255868129652801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190711194908170578753101867 286066792362255868129652801)
  ·
    refine ⟨214550094271691901097239601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286066792362255868129652801 214550094271691901097239601)
    ·
      refine ⟨160912570703768925822929701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214550094271691901097239601 160912570703768925822929701)
      ·
        refine ⟨30171107006956673591799319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160912570703768925822929701 30171107006956673591799319)
        ·
          refine ⟨45256660510435010387698979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30171107006956673591799319 45256660510435010387698979)
          ·
            refine ⟨67884990765652515581548469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45256660510435010387698979 67884990765652515581548469)
            ·
              refine ⟨6364217884279923335770169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67884990765652515581548469 6364217884279923335770169)
              ·
                refine ⟨4773163413209942501827627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6364217884279923335770169 4773163413209942501827627)
                ·
                  refine ⟨7159745119814913752741441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4773163413209942501827627 7159745119814913752741441)
                  ·
                    refine ⟨5369808839861185314556081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7159745119814913752741441 5369808839861185314556081)
                    ·
                      refine ⟨4027356629895888985917061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5369808839861185314556081 4027356629895888985917061)
                      ·
                        rfl

theorem cell23_7843249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_7843249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843249 prefixEnd_7843249 := by exact prefixLift 7843249
  have htrace : WordTrace (prefixWord ++ tailWord_7843249) baseStart_7843249 baseEnd_7843249 := by
    simpa [prefixWord, tailWord_7843249, baseEnd_7843249] using wordTrace_append hprefix tailTrace_7843249
  have hstable : (prefixWord ++ tailWord_7843249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843249).length < 2 ^ (prefixWord ++ tailWord_7843249).sum := by decide
  have hdescent : baseEnd_7843249 < baseStart_7843249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843275 : List Nat := [1, 1, 1, 1, 3, 3, 5, 2, 1, 3, 2]
def baseStart_7843275 : Nat := 118140960795 + 7843275 * 2 ^ 59
def prefixEnd_7843275 : Nat := 4983230072969 + 3 ^ 40 * 7843275 * 2
def baseEnd_7843275 : Nat := 4027369980392905884191941

theorem tailTrace_7843275 : CollatzResearch.WordTrace tailWord_7843275 prefixEnd_7843275 4027369980392905884191941 := by
  unfold tailWord_7843275
  simp only [CollatzResearch.WordTrace]
  refine ⟨286067740660161674570099279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190711827106774449713399519 286067740660161674570099279)
  ·
    refine ⟨429101610990242511855148919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286067740660161674570099279 429101610990242511855148919)
    ·
      refine ⟨643652416485363767782723379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429101610990242511855148919 643652416485363767782723379)
      ·
        refine ⟨965478624728045651674085069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643652416485363767782723379 965478624728045651674085069)
        ·
          refine ⟨362054484273017119377781901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 965478624728045651674085069 362054484273017119377781901)
          ·
            refine ⟨135770431602381419766668213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362054484273017119377781901 135770431602381419766668213)
            ·
              refine ⟨12728477962723258103125145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135770431602381419766668213 12728477962723258103125145)
              ·
                refine ⟨9546358472042443577343859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12728477962723258103125145 9546358472042443577343859)
                ·
                  refine ⟨14319537708063665366015789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9546358472042443577343859 14319537708063665366015789)
                  ·
                    refine ⟨5369826640523874512255921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14319537708063665366015789 5369826640523874512255921)
                    ·
                      refine ⟨4027369980392905884191941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5369826640523874512255921 4027369980392905884191941)
                      ·
                        rfl

theorem cell23_7843275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 3, 2].length) (baseStart_7843275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843275 prefixEnd_7843275 := by exact prefixLift 7843275
  have htrace : WordTrace (prefixWord ++ tailWord_7843275) baseStart_7843275 baseEnd_7843275 := by
    simpa [prefixWord, tailWord_7843275, baseEnd_7843275] using wordTrace_append hprefix tailTrace_7843275
  have hstable : (prefixWord ++ tailWord_7843275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843275).length < 2 ^ (prefixWord ++ tailWord_7843275).sum := by decide
  have hdescent : baseEnd_7843275 < baseStart_7843275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843288 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 3, 4, 2]
def baseStart_7843288 : Nat := 118140960795 + 7843288 * 2 ^ 59
def prefixEnd_7843288 : Nat := 4983230072969 + 3 ^ 40 * 7843288 * 2
def baseEnd_7843288 : Nat := 4027376655641414333329381

theorem tailTrace_7843288 : CollatzResearch.WordTrace tailWord_7843288 prefixEnd_7843288 4027376655641414333329381 := by
  unfold tailWord_7843288
  simp only [CollatzResearch.WordTrace]
  refine ⟨143034107404557288895161259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190712143206076385193548345 143034107404557288895161259)
  ·
    refine ⟨214551161106835933342741889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143034107404557288895161259 214551161106835933342741889)
    ·
      refine ⟨160913370830126950007056417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214551161106835933342741889 160913370830126950007056417)
      ·
        refine ⟨120685028122595212505292313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160913370830126950007056417 120685028122595212505292313)
        ·
          refine ⟨90513771091946409378969235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120685028122595212505292313 90513771091946409378969235)
          ·
            refine ⟨135770656637919614068453853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90513771091946409378969235 135770656637919614068453853)
            ·
              refine ⟨50913996239219855275670195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135770656637919614068453853 50913996239219855275670195)
              ·
                refine ⟨76370994358829782913505293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50913996239219855275670195 76370994358829782913505293)
                ·
                  refine ⟨28639122884561168592564485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76370994358829782913505293 28639122884561168592564485)
                  ·
                    refine ⟨5369835540855219111105841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28639122884561168592564485 5369835540855219111105841)
                    ·
                      refine ⟨4027376655641414333329381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5369835540855219111105841 4027376655641414333329381)
                      ·
                        rfl

theorem cell23_7843288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_7843288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843288 prefixEnd_7843288 := by exact prefixLift 7843288
  have htrace : WordTrace (prefixWord ++ tailWord_7843288) baseStart_7843288 baseEnd_7843288 := by
    simpa [prefixWord, tailWord_7843288, baseEnd_7843288] using wordTrace_append hprefix tailTrace_7843288
  have hstable : (prefixWord ++ tailWord_7843288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843288).length < 2 ^ (prefixWord ++ tailWord_7843288).sum := by decide
  have hdescent : baseEnd_7843288 < baseStart_7843288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843318 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_7843318 : Nat := 118140960795 + 7843318 * 2 ^ 59
def prefixEnd_7843318 : Nat := 4983230072969 + 3 ^ 40 * 7843318 * 2
def baseEnd_7843318 : Nat := 4027392060061049215954243

theorem tailTrace_7843318 : CollatzResearch.WordTrace tailWord_7843318 prefixEnd_7843318 4027392060061049215954243 := by
  unfold tailWord_7843318
  simp only [CollatzResearch.WordTrace]
  refine ⟨17879331812437868307119663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190712872666003928609276405 17879331812437868307119663)
  ·
    refine ⟨26818997718656802460679495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17879331812437868307119663 26818997718656802460679495)
    ·
      refine ⟨40228496577985203691019243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26818997718656802460679495 40228496577985203691019243)
      ·
        refine ⟨60342744866977805536528865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40228496577985203691019243 60342744866977805536528865)
        ·
          refine ⟨45257058650233354152396649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60342744866977805536528865 45257058650233354152396649)
          ·
            refine ⟨33942793987675015614297487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45257058650233354152396649 33942793987675015614297487)
            ·
              refine ⟨50914190981512523421446231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33942793987675015614297487 50914190981512523421446231)
              ·
                refine ⟨76371286472268785132169347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50914190981512523421446231 76371286472268785132169347)
                ·
                  refine ⟨114556929708403177698254021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76371286472268785132169347 114556929708403177698254021)
                  ·
                    refine ⟨21479424320325595818422629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114556929708403177698254021 21479424320325595818422629)
                    ·
                      refine ⟨4027392060061049215954243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21479424320325595818422629 4027392060061049215954243)
                      ·
                        rfl

theorem cell23_7843318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_7843318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843318 prefixEnd_7843318 := by exact prefixLift 7843318
  have htrace : WordTrace (prefixWord ++ tailWord_7843318) baseStart_7843318 baseEnd_7843318 := by
    simpa [prefixWord, tailWord_7843318, baseEnd_7843318] using wordTrace_append hprefix tailTrace_7843318
  have hstable : (prefixWord ++ tailWord_7843318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843318).length < 2 ^ (prefixWord ++ tailWord_7843318).sum := by decide
  have hdescent : baseEnd_7843318 < baseStart_7843318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843415 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 3]
def baseStart_7843415 : Nat := 118140960795 + 7843415 * 2 ^ 59
def prefixEnd_7843415 : Nat := 4983230072969 + 3 ^ 40 * 7843415 * 2
def baseEnd_7843415 : Nat := 4027441867684535336441297

theorem tailTrace_7843415 : CollatzResearch.WordTrace tailWord_7843415 prefixEnd_7843415 4027441867684535336441297 := by
  unfold tailWord_7843415
  simp only [CollatzResearch.WordTrace]
  refine ⟨286072846879654478480195699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190715231253102985653463799 286072846879654478480195699)
  ·
    refine ⟨429109270319481717720293549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286072846879654478480195699 429109270319481717720293549)
    ·
      refine ⟨160915976369805644145110081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429109270319481717720293549 160915976369805644145110081)
      ·
        refine ⟨120686982277354233108832561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160915976369805644145110081 120686982277354233108832561)
        ·
          refine ⟨90515236708015674831624421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120686982277354233108832561 90515236708015674831624421)
          ·
            refine ⟨16971606882752939030929579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90515236708015674831624421 16971606882752939030929579)
            ·
              refine ⟨25457410324129408546394369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16971606882752939030929579 25457410324129408546394369)
              ·
                refine ⟨19093057743097056409795777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25457410324129408546394369 19093057743097056409795777)
                ·
                  refine ⟨14319793307322792307346833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19093057743097056409795777 14319793307322792307346833)
                  ·
                    refine ⟨10739844980492094230510125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14319793307322792307346833 10739844980492094230510125)
                    ·
                      refine ⟨4027441867684535336441297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10739844980492094230510125 4027441867684535336441297)
                      ·
                        rfl

theorem cell23_7843415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_7843415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843415 prefixEnd_7843415 := by exact prefixLift 7843415
  have htrace : WordTrace (prefixWord ++ tailWord_7843415) baseStart_7843415 baseEnd_7843415 := by
    simpa [prefixWord, tailWord_7843415, baseEnd_7843415] using wordTrace_append hprefix tailTrace_7843415
  have hstable : (prefixWord ++ tailWord_7843415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843415).length < 2 ^ (prefixWord ++ tailWord_7843415).sum := by decide
  have hdescent : baseEnd_7843415 < baseStart_7843415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843479 : List Nat := [1, 1, 3, 3, 2, 3, 1, 4, 1, 1, 3]
def baseStart_7843479 : Nat := 118140960795 + 7843479 * 2 ^ 59
def prefixEnd_7843479 : Nat := 4983230072969 + 3 ^ 40 * 7843479 * 2
def baseEnd_7843479 : Nat := 4027474730446423086041003

theorem tailTrace_7843479 : CollatzResearch.WordTrace tailWord_7843479 prefixEnd_7843479 4027474730446423086041003 := by
  unfold tailWord_7843479
  simp only [CollatzResearch.WordTrace]
  refine ⟨286075181151422617410525491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190716787434281744940350327 286075181151422617410525491)
  ·
    refine ⟨429112771727133926115788237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286075181151422617410525491 429112771727133926115788237)
    ·
      refine ⟨160917289397675222293420589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429112771727133926115788237 160917289397675222293420589)
      ·
        refine ⟨60343983524128208360032721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160917289397675222293420589 60343983524128208360032721)
        ·
          refine ⟨45257987643096156270024541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60343983524128208360032721 45257987643096156270024541)
          ·
            refine ⟨16971745366161058601259203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45257987643096156270024541 16971745366161058601259203)
            ·
              refine ⟨25457618049241587901888805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16971745366161058601259203 25457618049241587901888805)
              ·
                refine ⟨4773303384232797731604151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25457618049241587901888805 4773303384232797731604151)
                ·
                  refine ⟨7159955076349196597406227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4773303384232797731604151 7159955076349196597406227)
                  ·
                    refine ⟨10739932614523794896109341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7159955076349196597406227 10739932614523794896109341)
                    ·
                      refine ⟨4027474730446423086041003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10739932614523794896109341 4027474730446423086041003)
                      ·
                        rfl

theorem cell23_7843479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_7843479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843479 prefixEnd_7843479 := by exact prefixLift 7843479
  have htrace : WordTrace (prefixWord ++ tailWord_7843479) baseStart_7843479 baseEnd_7843479 := by
    simpa [prefixWord, tailWord_7843479, baseEnd_7843479] using wordTrace_append hprefix tailTrace_7843479
  have hstable : (prefixWord ++ tailWord_7843479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843479).length < 2 ^ (prefixWord ++ tailWord_7843479).sum := by decide
  have hdescent : baseEnd_7843479 < baseStart_7843479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843485 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_7843485 : Nat := 118140960795 + 7843485 * 2 ^ 59
def prefixEnd_7843485 : Nat := 4983230072969 + 3 ^ 40 * 7843485 * 2
def baseEnd_7843485 : Nat := 4027477811330350062565975

theorem tailTrace_7843485 : CollatzResearch.WordTrace tailWord_7843485 prefixEnd_7843485 4027477811330350062565975 := by
  unfold tailWord_7843485
  simp only [CollatzResearch.WordTrace]
  refine ⟨286075399989400880435243909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190716933326267253623495939 286075399989400880435243909)
  ·
    refine ⟨53639137498012665081608233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286075399989400880435243909 53639137498012665081608233)
    ·
      refine ⟨40229353123509498811206175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53639137498012665081608233 40229353123509498811206175)
      ·
        refine ⟨60344029685264248216809263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40229353123509498811206175 60344029685264248216809263)
        ·
          refine ⟨90516044527896372325213895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60344029685264248216809263 90516044527896372325213895)
          ·
            refine ⟨135774066791844558487820843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90516044527896372325213895 135774066791844558487820843)
            ·
              refine ⟨203661100187766837731731265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135774066791844558487820843 203661100187766837731731265)
              ·
                refine ⟨152745825140825128298798449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203661100187766837731731265 152745825140825128298798449)
                ·
                  refine ⟨114559368855618846224098837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152745825140825128298798449 114559368855618846224098837)
                  ·
                    refine ⟨5369970415107133416754633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114559368855618846224098837 5369970415107133416754633)
                    ·
                      refine ⟨4027477811330350062565975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5369970415107133416754633 4027477811330350062565975)
                      ·
                        rfl

theorem cell23_7843485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_7843485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843485 prefixEnd_7843485 := by exact prefixLift 7843485
  have htrace : WordTrace (prefixWord ++ tailWord_7843485) baseStart_7843485 baseEnd_7843485 := by
    simpa [prefixWord, tailWord_7843485, baseEnd_7843485] using wordTrace_append hprefix tailTrace_7843485
  have hstable : (prefixWord ++ tailWord_7843485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843485).length < 2 ^ (prefixWord ++ tailWord_7843485).sum := by decide
  have hdescent : baseEnd_7843485 < baseStart_7843485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843552 : List Nat := [2, 1, 1, 3, 1, 2, 2, 5, 2, 1, 3]
def baseStart_7843552 : Nat := 118140960795 + 7843552 * 2 ^ 59
def prefixEnd_7843552 : Nat := 4983230072969 + 3 ^ 40 * 7843552 * 2
def baseEnd_7843552 : Nat := 4027512214534201300428167

theorem tailTrace_7843552 : CollatzResearch.WordTrace tailWord_7843552 prefixEnd_7843552 4027512214534201300428167 := by
  unfold tailWord_7843552
  simp only [CollatzResearch.WordTrace]
  refine ⟨143038921840079075438966455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190718562453438767251955273 143038921840079075438966455)
  ·
    refine ⟨214558382760118613158449683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143038921840079075438966455 214558382760118613158449683)
    ·
      refine ⟨321837574140177919737674525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214558382760118613158449683 321837574140177919737674525)
      ·
        refine ⟨120689090302566719901627947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321837574140177919737674525 120689090302566719901627947)
        ·
          refine ⟨181033635453850079852441921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120689090302566719901627947 181033635453850079852441921)
          ·
            refine ⟨135775226590387559889331441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181033635453850079852441921 135775226590387559889331441)
            ·
              refine ⟨101831419942790669916998581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135775226590387559889331441 101831419942790669916998581)
              ·
                refine ⟨9546695619636625304718617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101831419942790669916998581 9546695619636625304718617)
                ·
                  refine ⟨7160021714727468978538963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9546695619636625304718617 7160021714727468978538963)
                  ·
                    refine ⟨10740032572091203467808445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7160021714727468978538963 10740032572091203467808445)
                    ·
                      refine ⟨4027512214534201300428167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10740032572091203467808445 4027512214534201300428167)
                      ·
                        rfl

theorem cell23_7843552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_7843552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843552 prefixEnd_7843552 := by exact prefixLift 7843552
  have htrace : WordTrace (prefixWord ++ tailWord_7843552) baseStart_7843552 baseEnd_7843552 := by
    simpa [prefixWord, tailWord_7843552, baseEnd_7843552] using wordTrace_append hprefix tailTrace_7843552
  have hstable : (prefixWord ++ tailWord_7843552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843552).length < 2 ^ (prefixWord ++ tailWord_7843552).sum := by decide
  have hdescent : baseEnd_7843552 < baseStart_7843552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843559 : List Nat := [1, 1, 5, 4, 1, 2, 2, 7]
def baseStart_7843559 : Nat := 118140960795 + 7843559 * 2 ^ 59
def prefixEnd_7843559 : Nat := 4983230072969 + 3 ^ 40 * 7843559 * 2
def baseEnd_7843559 : Nat := 149167252181436399001505

theorem tailTrace_7843559 : CollatzResearch.WordTrace tailWord_7843559 prefixEnd_7843559 149167252181436399001505 := by
  unfold tailWord_7843559
  simp only [CollatzResearch.WordTrace]
  refine ⟨286078098991132791073437731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190718732660755194048958487 286078098991132791073437731)
  ·
    refine ⟨429117148486699186610156597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286078098991132791073437731 429117148486699186610156597)
    ·
      refine ⟨40229732670628048744702181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 429117148486699186610156597 40229732670628048744702181)
      ·
        refine ⟨7543074875742759139631659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40229732670628048744702181 7543074875742759139631659)
        ·
          refine ⟨11314612313614138709447489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7543074875742759139631659 11314612313614138709447489)
          ·
            refine ⟨8485959235210604032085617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11314612313614138709447489 8485959235210604032085617)
            ·
              refine ⟨6364469426407953024064213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8485959235210604032085617 6364469426407953024064213)
              ·
                refine ⟨149167252181436399001505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6364469426407953024064213 149167252181436399001505)
                ·
                  rfl

theorem cell23_7843559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 7].length) (baseStart_7843559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843559 prefixEnd_7843559 := by exact prefixLift 7843559
  have htrace : WordTrace (prefixWord ++ tailWord_7843559) baseStart_7843559 baseEnd_7843559 := by
    simpa [prefixWord, tailWord_7843559, baseEnd_7843559] using wordTrace_append hprefix tailTrace_7843559
  have hstable : (prefixWord ++ tailWord_7843559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843559).length < 2 ^ (prefixWord ++ tailWord_7843559).sum := by decide
  have hdescent : baseEnd_7843559 < baseStart_7843559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843562 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_7843562 : Nat := 118140960795 + 7843562 * 2 ^ 59
def prefixEnd_7843562 : Nat := 4983230072969 + 3 ^ 40 * 7843562 * 2
def baseEnd_7843562 : Nat := 4027517349340746261303121

theorem tailTrace_7843562 : CollatzResearch.WordTrace tailWord_7843562 prefixEnd_7843562 4027517349340746261303121 := by
  unfold tailWord_7843562
  simp only [CollatzResearch.WordTrace]
  refine ⟨71519552102530480646449235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190718805606747948390531293 71519552102530480646449235)
  ·
    refine ⟨107279328153795720969673853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71519552102530480646449235 107279328153795720969673853)
    ·
      refine ⟨40229748057673395363627695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107279328153795720969673853 40229748057673395363627695)
      ·
        refine ⟨60344622086510093045441543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40229748057673395363627695 60344622086510093045441543)
        ·
          refine ⟨90516933129765139568162315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60344622086510093045441543 90516933129765139568162315)
          ·
            refine ⟨135775399694647709352243473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90516933129765139568162315 135775399694647709352243473)
            ·
              refine ⟨101831549770985782014182605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135775399694647709352243473 101831549770985782014182605)
              ·
                refine ⟨38186831164119668255318477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101831549770985782014182605 38186831164119668255318477)
                ·
                  refine ⟨14320061686544875595744429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38186831164119668255318477 14320061686544875595744429)
                  ·
                    refine ⟨5370023132454328348404161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14320061686544875595744429 5370023132454328348404161)
                    ·
                      refine ⟨4027517349340746261303121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5370023132454328348404161 4027517349340746261303121)
                      ·
                        rfl

theorem cell23_7843562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_7843562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843562 prefixEnd_7843562 := by exact prefixLift 7843562
  have htrace : WordTrace (prefixWord ++ tailWord_7843562) baseStart_7843562 baseEnd_7843562 := by
    simpa [prefixWord, tailWord_7843562, baseEnd_7843562] using wordTrace_append hprefix tailTrace_7843562
  have hstable : (prefixWord ++ tailWord_7843562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843562).length < 2 ^ (prefixWord ++ tailWord_7843562).sum := by decide
  have hdescent : baseEnd_7843562 < baseStart_7843562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843565 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_7843565 : Nat := 118140960795 + 7843565 * 2 ^ 59
def prefixEnd_7843565 : Nat := 4983230072969 + 3 ^ 40 * 7843565 * 2
def baseEnd_7843565 : Nat := 4027518889782709749565607

theorem tailTrace_7843565 : CollatzResearch.WordTrace tailWord_7843565 prefixEnd_7843565 4027518889782709749565607 := by
  unfold tailWord_7843565
  simp only [CollatzResearch.WordTrace]
  refine ⟨286078317829111054098156149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190718878552740702732104099 286078317829111054098156149)
  ·
    refine ⟨26819842296479161321702139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286078317829111054098156149 26819842296479161321702139)
    ·
      refine ⟨40229763444718741982553209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26819842296479161321702139 40229763444718741982553209)
      ·
        refine ⟨30172322583539056486914907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40229763444718741982553209 30172322583539056486914907)
        ·
          refine ⟨45258483875308584730372361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30172322583539056486914907 45258483875308584730372361)
          ·
            refine ⟨33943862906481438547779271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45258483875308584730372361 33943862906481438547779271)
            ·
              refine ⟨50915794359722157821668907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33943862906481438547779271 50915794359722157821668907)
              ·
                refine ⟨76373691539583236732503361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50915794359722157821668907 76373691539583236732503361)
                ·
                  refine ⟨57280268654687427549377521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76373691539583236732503361 57280268654687427549377521)
                  ·
                    refine ⟨42960201491015570662033141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57280268654687427549377521 42960201491015570662033141)
                    ·
                      refine ⟨4027518889782709749565607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42960201491015570662033141 4027518889782709749565607)
                      ·
                        rfl

theorem cell23_7843565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_7843565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843565 prefixEnd_7843565 := by exact prefixLift 7843565
  have htrace : WordTrace (prefixWord ++ tailWord_7843565) baseStart_7843565 baseEnd_7843565 := by
    simpa [prefixWord, tailWord_7843565, baseEnd_7843565] using wordTrace_append hprefix tailTrace_7843565
  have hstable : (prefixWord ++ tailWord_7843565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843565).length < 2 ^ (prefixWord ++ tailWord_7843565).sum := by decide
  have hdescent : baseEnd_7843565 < baseStart_7843565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843568 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 4, 6]
def baseStart_7843568 : Nat := 118140960795 + 7843568 * 2 ^ 59
def prefixEnd_7843568 : Nat := 4983230072969 + 3 ^ 40 * 7843568 * 2
def baseEnd_7843568 : Nat := 1342506810074891079276031

theorem tailTrace_7843568 : CollatzResearch.WordTrace tailWord_7843568 prefixEnd_7843568 1342506810074891079276031 := by
  unfold tailWord_7843568
  simp only [CollatzResearch.WordTrace]
  refine ⟨143039213624050092805257679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190718951498733457073676905 143039213624050092805257679)
  ·
    refine ⟨214558820436075139207886519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143039213624050092805257679 214558820436075139207886519)
    ·
      refine ⟨321838230654112708811829779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214558820436075139207886519 321838230654112708811829779)
      ·
        refine ⟨482757345981169063217744669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321838230654112708811829779 482757345981169063217744669)
        ·
          refine ⟨181034004742938398706654251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482757345981169063217744669 181034004742938398706654251)
          ·
            refine ⟨271551007114407598059981377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181034004742938398706654251 271551007114407598059981377)
            ·
              refine ⟨203663255335805698544986033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271551007114407598059981377 203663255335805698544986033)
              ·
                refine ⟨152747441501854273908739525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203663255335805698544986033 152747441501854273908739525)
                ·
                  refine ⟨28640145281597676357888661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152747441501854273908739525 28640145281597676357888661)
                  ·
                    refine ⟨1342506810074891079276031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28640145281597676357888661 1342506810074891079276031)
                    ·
                      rfl

theorem cell23_7843568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4, 6].length) (baseStart_7843568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843568 prefixEnd_7843568 := by exact prefixLift 7843568
  have htrace : WordTrace (prefixWord ++ tailWord_7843568) baseStart_7843568 baseEnd_7843568 := by
    simpa [prefixWord, tailWord_7843568, baseEnd_7843568] using wordTrace_append hprefix tailTrace_7843568
  have hstable : (prefixWord ++ tailWord_7843568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843568).length < 2 ^ (prefixWord ++ tailWord_7843568).sum := by decide
  have hdescent : baseEnd_7843568 < baseStart_7843568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843597 : List Nat := [1, 7, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_7843597 : Nat := 118140960795 + 7843597 * 2 ^ 59
def prefixEnd_7843597 : Nat := 4983230072969 + 3 ^ 40 * 7843597 * 2
def baseEnd_7843597 : Nat := 1342511773721217874788487

theorem tailTrace_7843597 : CollatzResearch.WordTrace tailWord_7843597 prefixEnd_7843597 1342511773721217874788487 := by
  unfold tailWord_7843597
  simp only [CollatzResearch.WordTrace]
  refine ⟨286079484964995123563321045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190719656643330082375547363 286079484964995123563321045)
  ·
    refine ⟨6704987928867073208515337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 286079484964995123563321045 6704987928867073208515337)
    ·
      refine ⟨5028740946650304906386503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6704987928867073208515337 5028740946650304906386503)
      ·
        refine ⟨7543111419975457359579755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5028740946650304906386503 7543111419975457359579755)
        ·
          refine ⟨11314667129963186039369633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7543111419975457359579755 11314667129963186039369633)
          ·
            refine ⟨8486000347472389529527225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11314667129963186039369633 8486000347472389529527225)
            ·
              refine ⟨6364500260604292147145419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8486000347472389529527225 6364500260604292147145419)
              ·
                refine ⟨9546750390906438220718129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6364500260604292147145419 9546750390906438220718129)
                ·
                  refine ⟨7160062793179828665538597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9546750390906438220718129 7160062793179828665538597)
                  ·
                    refine ⟨1342511773721217874788487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7160062793179828665538597 1342511773721217874788487)
                    ·
                      rfl

theorem cell23_7843597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_7843597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843597 prefixEnd_7843597 := by exact prefixLift 7843597
  have htrace : WordTrace (prefixWord ++ tailWord_7843597) baseStart_7843597 baseEnd_7843597 := by
    simpa [prefixWord, tailWord_7843597, baseEnd_7843597] using wordTrace_append hprefix tailTrace_7843597
  have hstable : (prefixWord ++ tailWord_7843597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843597).length < 2 ^ (prefixWord ++ tailWord_7843597).sum := by decide
  have hdescent : baseEnd_7843597 < baseStart_7843597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843655 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_7843655 : Nat := 118140960795 + 7843655 * 2 ^ 59
def prefixEnd_7843655 : Nat := 4983230072969 + 3 ^ 40 * 7843655 * 2
def baseEnd_7843655 : Nat := 4027565103041614397440193

theorem tailTrace_7843655 : CollatzResearch.WordTrace tailWord_7843655 prefixEnd_7843655 4027565103041614397440193 := by
  unfold tailWord_7843655
  simp only [CollatzResearch.WordTrace]
  refine ⟨286081600398784999468932419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190721066932523332979288279 286081600398784999468932419)
  ·
    refine ⟨429122400598177499203398629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286081600398784999468932419 429122400598177499203398629)
    ·
      refine ⟨80460450112158281100637243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429122400598177499203398629 80460450112158281100637243)
      ·
        refine ⟨120690675168237421650955865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80460450112158281100637243 120690675168237421650955865)
        ·
          refine ⟨90518006376178066238216899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120690675168237421650955865 90518006376178066238216899)
          ·
            refine ⟨135777009564267099357325349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90518006376178066238216899 135777009564267099357325349)
            ·
              refine ⟨25458189293300081129498503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135777009564267099357325349 25458189293300081129498503)
              ·
                refine ⟨38187283939950121694247755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25458189293300081129498503 38187283939950121694247755)
                ·
                  refine ⟨57280925909925182541371633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38187283939950121694247755 57280925909925182541371633)
                  ·
                    refine ⟨42960694432443886906028725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57280925909925182541371633 42960694432443886906028725)
                    ·
                      refine ⟨4027565103041614397440193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42960694432443886906028725 4027565103041614397440193)
                      ·
                        rfl

theorem cell23_7843655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_7843655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843655 prefixEnd_7843655 := by exact prefixLift 7843655
  have htrace : WordTrace (prefixWord ++ tailWord_7843655) baseStart_7843655 baseEnd_7843655 := by
    simpa [prefixWord, tailWord_7843655, baseEnd_7843655] using wordTrace_append hprefix tailTrace_7843655
  have hstable : (prefixWord ++ tailWord_7843655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843655).length < 2 ^ (prefixWord ++ tailWord_7843655).sum := by decide
  have hdescent : baseEnd_7843655 < baseStart_7843655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843705 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 8]
def baseStart_7843705 : Nat := 118140960795 + 7843705 * 2 ^ 59
def prefixEnd_7843705 : Nat := 4983230072969 + 3 ^ 40 * 7843705 * 2
def baseEnd_7843705 : Nat := 447510086341593244646107

theorem tailTrace_7843705 : CollatzResearch.WordTrace tailWord_7843705 prefixEnd_7843705 447510086341593244646107 := by
  unfold tailWord_7843705
  simp only [CollatzResearch.WordTrace]
  refine ⟨286083424048603858008252569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190722282699069238672168379 286083424048603858008252569)
  ·
    refine ⟨214562568036452893506189427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286083424048603858008252569 214562568036452893506189427)
    ·
      refine ⟨321843852054679340259284141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214562568036452893506189427 321843852054679340259284141)
      ·
        refine ⟨120691444520504752597231553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321843852054679340259284141 120691444520504752597231553)
        ·
          refine ⟨90518583390378564447923665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120691444520504752597231553 90518583390378564447923665)
          ·
            refine ⟨67888937542783923335942749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90518583390378564447923665 67888937542783923335942749)
            ·
              refine ⟨25458351578543971250978531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67888937542783923335942749 25458351578543971250978531)
              ·
                refine ⟨38187527367815956876467797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25458351578543971250978531 38187527367815956876467797)
                ·
                  refine ⟨447510086341593244646107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38187527367815956876467797 447510086341593244646107)
                  ·
                    rfl

theorem cell23_7843705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 8].length) (baseStart_7843705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843705 prefixEnd_7843705 := by exact prefixLift 7843705
  have htrace : WordTrace (prefixWord ++ tailWord_7843705) baseStart_7843705 baseEnd_7843705 := by
    simpa [prefixWord, tailWord_7843705, baseEnd_7843705] using wordTrace_append hprefix tailTrace_7843705
  have hstable : (prefixWord ++ tailWord_7843705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843705).length < 2 ^ (prefixWord ++ tailWord_7843705).sum := by decide
  have hdescent : baseEnd_7843705 < baseStart_7843705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843743 : List Nat := [1, 1, 2, 5, 3, 2, 1, 3, 1, 4]
def baseStart_7843743 : Nat := 118140960795 + 7843743 * 2 ^ 59
def prefixEnd_7843743 : Nat := 4983230072969 + 3 ^ 40 * 7843743 * 2
def baseEnd_7843743 : Nat := 1342536763113070017713263

theorem tailTrace_7843743 : CollatzResearch.WordTrace tailWord_7843743 prefixEnd_7843743 1342536763113070017713263 := by
  unfold tailWord_7843743
  simp only [CollatzResearch.WordTrace]
  refine ⟨286084810022466190498135883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190723206681644126998757255 286084810022466190498135883)
  ·
    refine ⟨429127215033699285747203825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286084810022466190498135883 429127215033699285747203825)
    ·
      refine ⟨321845411275274464310402869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429127215033699285747203825 321845411275274464310402869)
      ·
        refine ⟨30173007307056981029100269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 321845411275274464310402869 30173007307056981029100269)
        ·
          refine ⟨11314877740146367885912601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30173007307056981029100269 11314877740146367885912601)
          ·
            refine ⟨8486158305109775914434451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11314877740146367885912601 8486158305109775914434451)
            ·
              refine ⟨12729237457664663871651677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8486158305109775914434451 12729237457664663871651677)
              ·
                refine ⟨4773464046624248951869379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12729237457664663871651677 4773464046624248951869379)
                ·
                  refine ⟨7160196069936373427804069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4773464046624248951869379 7160196069936373427804069)
                  ·
                    refine ⟨1342536763113070017713263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7160196069936373427804069 1342536763113070017713263)
                    ·
                      rfl

theorem cell23_7843743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 1, 4].length) (baseStart_7843743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843743 prefixEnd_7843743 := by exact prefixLift 7843743
  have htrace : WordTrace (prefixWord ++ tailWord_7843743) baseStart_7843743 baseEnd_7843743 := by
    simpa [prefixWord, tailWord_7843743, baseEnd_7843743] using wordTrace_append hprefix tailTrace_7843743
  have hstable : (prefixWord ++ tailWord_7843743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843743).length < 2 ^ (prefixWord ++ tailWord_7843743).sum := by decide
  have hdescent : baseEnd_7843743 < baseStart_7843743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843759 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 2, 3, 2]
def baseStart_7843759 : Nat := 118140960795 + 7843759 * 2 ^ 59
def prefixEnd_7843759 : Nat := 4983230072969 + 3 ^ 40 * 7843759 * 2
def baseEnd_7843759 : Nat := 4027618505029681990539715

theorem tailTrace_7843759 : CollatzResearch.WordTrace tailWord_7843759 prefixEnd_7843759 4027618505029681990539715 := by
  unfold tailWord_7843759
  simp only [CollatzResearch.WordTrace]
  refine ⟨286085393590408225230718331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190723595726938816820478887 286085393590408225230718331)
  ·
    refine ⟨429128090385612337846077497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286085393590408225230718331 429128090385612337846077497)
    ·
      refine ⟨321846067789209253384558123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429128090385612337846077497 321846067789209253384558123)
      ·
        refine ⟨482769101683813880076837185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321846067789209253384558123 482769101683813880076837185)
        ·
          refine ⟨362076826262860410057627889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482769101683813880076837185 362076826262860410057627889)
          ·
            refine ⟨271557619697145307543220917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362076826262860410057627889 271557619697145307543220917)
            ·
              refine ⟨25458526846607372582176961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271557619697145307543220917 25458526846607372582176961)
              ·
                refine ⟨19093895134955529436632721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25458526846607372582176961 19093895134955529436632721)
                ·
                  refine ⟨14320421351216647077474541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19093895134955529436632721 14320421351216647077474541)
                  ·
                    refine ⟨5370158006706242654052953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14320421351216647077474541 5370158006706242654052953)
                    ·
                      refine ⟨4027618505029681990539715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5370158006706242654052953 4027618505029681990539715)
                      ·
                        rfl

theorem cell23_7843759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 3, 2].length) (baseStart_7843759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843759 prefixEnd_7843759 := by exact prefixLift 7843759
  have htrace : WordTrace (prefixWord ++ tailWord_7843759) baseStart_7843759 baseEnd_7843759 := by
    simpa [prefixWord, tailWord_7843759, baseEnd_7843759] using wordTrace_append hprefix tailTrace_7843759
  have hstable : (prefixWord ++ tailWord_7843759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843759).length < 2 ^ (prefixWord ++ tailWord_7843759).sum := by decide
  have hdescent : baseEnd_7843759 < baseStart_7843759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843809 : List Nat := [1, 2, 3, 1, 2, 1, 2, 5, 1, 2, 3]
def baseStart_7843809 : Nat := 118140960795 + 7843809 * 2 ^ 59
def prefixEnd_7843809 : Nat := 4983230072969 + 3 ^ 40 * 7843809 * 2
def baseEnd_7843809 : Nat := 4027644179062406794914485

theorem tailTrace_7843809 : CollatzResearch.WordTrace tailWord_7843809 prefixEnd_7843809 4027644179062406794914485 := by
  unfold tailWord_7843809
  simp only [CollatzResearch.WordTrace]
  refine ⟨286087217240227083770038481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190724811493484722513358987 286087217240227083770038481)
  ·
    refine ⟨214565412930170312827528861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286087217240227083770038481 214565412930170312827528861)
    ·
      refine ⟨80462029848813867310323323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214565412930170312827528861 80462029848813867310323323)
      ·
        refine ⟨120693044773220800965484985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80462029848813867310323323 120693044773220800965484985)
        ·
          refine ⟨90519783579915600724113739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120693044773220800965484985 90519783579915600724113739)
          ·
            refine ⟨135779675369873401086170609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90519783579915600724113739 135779675369873401086170609)
            ·
              refine ⟨101834756527405050814627957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135779675369873401086170609 101834756527405050814627957)
              ·
                refine ⟨9547008424444223513871371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101834756527405050814627957 9547008424444223513871371)
                ·
                  refine ⟨14320512636666335270807057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9547008424444223513871371 14320512636666335270807057)
                  ·
                    refine ⟨10740384477499751453105293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14320512636666335270807057 10740384477499751453105293)
                    ·
                      refine ⟨4027644179062406794914485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10740384477499751453105293 4027644179062406794914485)
                      ·
                        rfl

theorem cell23_7843809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_7843809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843809 prefixEnd_7843809 := by exact prefixLift 7843809
  have htrace : WordTrace (prefixWord ++ tailWord_7843809) baseStart_7843809 baseEnd_7843809 := by
    simpa [prefixWord, tailWord_7843809, baseEnd_7843809] using wordTrace_append hprefix tailTrace_7843809
  have hstable : (prefixWord ++ tailWord_7843809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843809).length < 2 ^ (prefixWord ++ tailWord_7843809).sum := by decide
  have hdescent : baseEnd_7843809 < baseStart_7843809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843823 : List Nat := [1, 1, 2, 1, 4, 2, 3, 4, 1, 2, 2]
def baseStart_7843823 : Nat := 118140960795 + 7843823 * 2 ^ 59
def prefixEnd_7843823 : Nat := 4983230072969 + 3 ^ 40 * 7843823 * 2
def baseEnd_7843823 : Nat := 4027651367791569740139421

theorem tailTrace_7843823 : CollatzResearch.WordTrace tailWord_7843823 prefixEnd_7843823 4027651367791569740139421 := by
  unfold tailWord_7843823
  simp only [CollatzResearch.WordTrace]
  refine ⟨286087727862176364161048123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190725151908117576107365415 286087727862176364161048123)
  ·
    refine ⟨429131591793264546241572185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286087727862176364161048123 429131591793264546241572185)
    ·
      refine ⟨321848693844948409681179139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429131591793264546241572185 321848693844948409681179139)
      ·
        refine ⟨482773040767422614521768709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321848693844948409681179139 482773040767422614521768709)
        ·
          refine ⟨90519945143891740222831633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 482773040767422614521768709 90519945143891740222831633)
          ·
            refine ⟨67889958857918805167123725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90519945143891740222831633 67889958857918805167123725)
            ·
              refine ⟨25458734571719551937671397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67889958857918805167123725 25458734571719551937671397)
              ·
                refine ⟨4773512732197415988313387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25458734571719551937671397 4773512732197415988313387)
                ·
                  refine ⟨7160269098296123982470081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4773512732197415988313387 7160269098296123982470081)
                  ·
                    refine ⟨5370201823722092986852561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7160269098296123982470081 5370201823722092986852561)
                    ·
                      refine ⟨4027651367791569740139421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5370201823722092986852561 4027651367791569740139421)
                      ·
                        rfl

theorem cell23_7843823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 1, 2, 2].length) (baseStart_7843823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843823 prefixEnd_7843823 := by exact prefixLift 7843823
  have htrace : WordTrace (prefixWord ++ tailWord_7843823) baseStart_7843823 baseEnd_7843823 := by
    simpa [prefixWord, tailWord_7843823, baseEnd_7843823] using wordTrace_append hprefix tailTrace_7843823
  have hstable : (prefixWord ++ tailWord_7843823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843823).length < 2 ^ (prefixWord ++ tailWord_7843823).sum := by decide
  have hdescent : baseEnd_7843823 < baseStart_7843823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843852 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_7843852 : Nat := 118140960795 + 7843852 * 2 ^ 59
def prefixEnd_7843852 : Nat := 4983230072969 + 3 ^ 40 * 7843852 * 2
def baseEnd_7843852 : Nat := 4027666258730550126676787

theorem tailTrace_7843852 : CollatzResearch.WordTrace tailWord_7843852 prefixEnd_7843852 4027666258730550126676787 := by
  unfold tailWord_7843852
  simp only [CollatzResearch.WordTrace]
  refine ⟨143044392789535651056926905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190725857052714201409235873 143044392789535651056926905)
  ·
    refine ⟨107283294592151738292695179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143044392789535651056926905 107283294592151738292695179)
    ·
      refine ⟨160924941888227607439042769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107283294592151738292695179 160924941888227607439042769)
      ·
        refine ⟨120693706416170705579282077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160924941888227607439042769 120693706416170705579282077)
        ·
          refine ⟨45260139906064014592230779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120693706416170705579282077 45260139906064014592230779)
          ·
            refine ⟨67890209859096021888346169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45260139906064014592230779 67890209859096021888346169)
            ·
              refine ⟨50917657394322016416259627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67890209859096021888346169 50917657394322016416259627)
              ·
                refine ⟨76376486091483024624389441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50917657394322016416259627 76376486091483024624389441)
                ·
                  refine ⟨57282364568612268468292081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76376486091483024624389441 57282364568612268468292081)
                  ·
                    refine ⟨42961773426459201351219061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57282364568612268468292081 42961773426459201351219061)
                    ·
                      refine ⟨4027666258730550126676787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42961773426459201351219061 4027666258730550126676787)
                      ·
                        rfl

theorem cell23_7843852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_7843852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843852 prefixEnd_7843852 := by exact prefixLift 7843852
  have htrace : WordTrace (prefixWord ++ tailWord_7843852) baseStart_7843852 baseEnd_7843852 := by
    simpa [prefixWord, tailWord_7843852, baseEnd_7843852] using wordTrace_append hprefix tailTrace_7843852
  have hstable : (prefixWord ++ tailWord_7843852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843852).length < 2 ^ (prefixWord ++ tailWord_7843852).sum := by decide
  have hdescent : baseEnd_7843852 < baseStart_7843852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843860 : List Nat := [2, 4, 3, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_7843860 : Nat := 118140960795 + 7843860 * 2 ^ 59
def prefixEnd_7843860 : Nat := 4983230072969 + 3 ^ 40 * 7843860 * 2
def baseEnd_7843860 : Nat := 4027670366575786095376751

theorem tailTrace_7843860 : CollatzResearch.WordTrace tailWord_7843860 prefixEnd_7843860 4027670366575786095376751 := by
  unfold tailWord_7843860
  simp only [CollatzResearch.WordTrace]
  refine ⟨143044538681521159740072517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190726051575361546320096689 143044538681521159740072517)
  ·
    refine ⟨26820851002785217451263597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143044538681521159740072517 26820851002785217451263597)
    ·
      refine ⟨10057819126044456544223849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26820851002785217451263597 10057819126044456544223849)
      ·
        refine ⟨7543364344533342408167887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10057819126044456544223849 7543364344533342408167887)
        ·
          refine ⟨11315046516800013612251831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7543364344533342408167887 11315046516800013612251831)
          ·
            refine ⟨16972569775200020418377747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11315046516800013612251831 16972569775200020418377747)
            ·
              refine ⟨25458854662800030627566621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16972569775200020418377747 25458854662800030627566621)
              ·
                refine ⟨9547070498550011485337483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25458854662800030627566621 9547070498550011485337483)
                ·
                  refine ⟨14320605747825017228006225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9547070498550011485337483 14320605747825017228006225)
                  ·
                    refine ⟨10740454310868762921004669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14320605747825017228006225 10740454310868762921004669)
                    ·
                      refine ⟨4027670366575786095376751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10740454310868762921004669 4027670366575786095376751)
                      ·
                        rfl

theorem cell23_7843860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_7843860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843860 prefixEnd_7843860 := by exact prefixLift 7843860
  have htrace : WordTrace (prefixWord ++ tailWord_7843860) baseStart_7843860 baseEnd_7843860 := by
    simpa [prefixWord, tailWord_7843860, baseEnd_7843860] using wordTrace_append hprefix tailTrace_7843860
  have hstable : (prefixWord ++ tailWord_7843860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843860).length < 2 ^ (prefixWord ++ tailWord_7843860).sum := by decide
  have hdescent : baseEnd_7843860 < baseStart_7843860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843949 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_7843949 : Nat := 118140960795 + 7843949 * 2 ^ 59
def prefixEnd_7843949 : Nat := 4983230072969 + 3 ^ 40 * 7843949 * 2
def baseEnd_7843949 : Nat := 1342572022118012082387947

theorem tailTrace_7843949 : CollatzResearch.WordTrace tailWord_7843949 prefixEnd_7843949 1342572022118012082387947 := by
  unfold tailWord_7843949
  simp only [CollatzResearch.WordTrace]
  refine ⟨286092323459719887680134901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190728215639813258453423267 286092323459719887680134901)
  ·
    refine ⟨26821155324348739470012647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286092323459719887680134901 26821155324348739470012647)
    ·
      refine ⟨40231732986523109205018971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26821155324348739470012647 40231732986523109205018971)
      ·
        refine ⟨60347599479784663807528457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40231732986523109205018971 60347599479784663807528457)
        ·
          refine ⟨45260699609838497855646343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60347599479784663807528457 45260699609838497855646343)
          ·
            refine ⟨67891049414757746783469515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45260699609838497855646343 67891049414757746783469515)
            ·
              refine ⟨101836574122136620175204273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67891049414757746783469515 101836574122136620175204273)
              ·
                refine ⟨76377430591602465131403205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101836574122136620175204273 76377430591602465131403205)
                ·
                  refine ⟨14320768235925462212138101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76377430591602465131403205 14320768235925462212138101)
                  ·
                    refine ⟨1342572022118012082387947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14320768235925462212138101 1342572022118012082387947)
                    ·
                      rfl

theorem cell23_7843949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_7843949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843949 prefixEnd_7843949 := by exact prefixLift 7843949
  have htrace : WordTrace (prefixWord ++ tailWord_7843949) baseStart_7843949 baseEnd_7843949 := by
    simpa [prefixWord, tailWord_7843949, baseEnd_7843949] using wordTrace_append hprefix tailTrace_7843949
  have hstable : (prefixWord ++ tailWord_7843949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843949).length < 2 ^ (prefixWord ++ tailWord_7843949).sum := by decide
  have hdescent : baseEnd_7843949 < baseStart_7843949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843986 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_7843986 : Nat := 118140960795 + 7843986 * 2 ^ 59
def prefixEnd_7843986 : Nat := 4983230072969 + 3 ^ 40 * 7843986 * 2
def baseEnd_7843986 : Nat := 4027735065138252602401171

theorem tailTrace_7843986 : CollatzResearch.WordTrace tailWord_7843986 prefixEnd_7843986 4027735065138252602401171 := by
  unfold tailWord_7843986
  simp only [CollatzResearch.WordTrace]
  refine ⟨71523418240146460749807953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190729115307057228666154541 71523418240146460749807953)
  ·
    refine ⟨53642563680109845562355965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71523418240146460749807953 53642563680109845562355965)
    ·
      refine ⟨20115961380041192085883487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53642563680109845562355965 20115961380041192085883487)
      ·
        refine ⟨30173942070061788128825231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20115961380041192085883487 30173942070061788128825231)
        ·
          refine ⟨45260913105092682193237847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30173942070061788128825231 45260913105092682193237847)
          ·
            refine ⟨67891369657639023289856771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45260913105092682193237847 67891369657639023289856771)
            ·
              refine ⟨101837054486458534934785157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67891369657639023289856771 101837054486458534934785157)
              ·
                refine ⟨19094447716210975300272217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101837054486458534934785157 19094447716210975300272217)
                ·
                  refine ⟨14320835787158231475204163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19094447716210975300272217 14320835787158231475204163)
                  ·
                    refine ⟨21481253680737347212806245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14320835787158231475204163 21481253680737347212806245)
                    ·
                      refine ⟨4027735065138252602401171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21481253680737347212806245 4027735065138252602401171)
                      ·
                        rfl

theorem cell23_7843986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_7843986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843986 prefixEnd_7843986 := by exact prefixLift 7843986
  have htrace : WordTrace (prefixWord ++ tailWord_7843986) baseStart_7843986 baseEnd_7843986 := by
    simpa [prefixWord, tailWord_7843986, baseEnd_7843986] using wordTrace_append hprefix tailTrace_7843986
  have hstable : (prefixWord ++ tailWord_7843986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843986).length < 2 ^ (prefixWord ++ tailWord_7843986).sum := by decide
  have hdescent : baseEnd_7843986 < baseStart_7843986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7843996 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 3, 4]
def baseStart_7843996 : Nat := 118140960795 + 7843996 * 2 ^ 59
def prefixEnd_7843996 : Nat := 4983230072969 + 3 ^ 40 * 7843996 * 2
def baseEnd_7843996 : Nat := 1342580066648265854425375

theorem tailTrace_7843996 : CollatzResearch.WordTrace tailWord_7843996 prefixEnd_7843996 1342580066648265854425375 := by
  unfold tailWord_7843996
  simp only [CollatzResearch.WordTrace]
  refine ⟨143047018845274807353547921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190729358460366409804730561 143047018845274807353547921)
  ·
    refine ⟨107285264133956105515160941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143047018845274807353547921 107285264133956105515160941)
    ·
      refine ⟨40231974050233539568185353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107285264133956105515160941 40231974050233539568185353)
      ·
        refine ⟨30173980537675154676139015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40231974050233539568185353 30173980537675154676139015)
        ·
          refine ⟨45260970806512732014208523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30173980537675154676139015 45260970806512732014208523)
          ·
            refine ⟨67891456209769098021312785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45260970806512732014208523 67891456209769098021312785)
            ·
              refine ⟨50918592157326823515984589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67891456209769098021312785 50918592157326823515984589)
              ·
                refine ⟨19094472058997558818494221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50918592157326823515984589 19094472058997558818494221)
                ·
                  refine ⟨7160427022124084556935333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19094472058997558818494221 7160427022124084556935333)
                  ·
                    refine ⟨1342580066648265854425375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7160427022124084556935333 1342580066648265854425375)
                    ·
                      rfl

theorem cell23_7843996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_7843996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7843996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7843996 prefixEnd_7843996 := by exact prefixLift 7843996
  have htrace : WordTrace (prefixWord ++ tailWord_7843996) baseStart_7843996 baseEnd_7843996 := by
    simpa [prefixWord, tailWord_7843996, baseEnd_7843996] using wordTrace_append hprefix tailTrace_7843996
  have hstable : (prefixWord ++ tailWord_7843996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7843996).length < 2 ^ (prefixWord ++ tailWord_7843996).sum := by decide
  have hdescent : baseEnd_7843996 < baseStart_7843996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7843996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844013 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_7844013 : Nat := 118140960795 + 7844013 * 2 ^ 59
def prefixEnd_7844013 : Nat := 4983230072969 + 3 ^ 40 * 7844013 * 2
def baseEnd_7844013 : Nat := 1342582976371974665587849

theorem tailTrace_7844013 : CollatzResearch.WordTrace tailWord_7844013 prefixEnd_7844013 1342582976371974665587849 := by
  unfold tailWord_7844013
  simp only [CollatzResearch.WordTrace]
  refine ⟨286094657731488026610464693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190729771820992017740309795 286094657731488026610464693)
  ·
    refine ⟨26821374162327002494731065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286094657731488026610464693 26821374162327002494731065)
    ·
      refine ⟨20116030621745251871048299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26821374162327002494731065 20116030621745251871048299)
      ·
        refine ⟨30174045932617877806572449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20116030621745251871048299 30174045932617877806572449)
        ·
          refine ⟨22630534449463408354929337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30174045932617877806572449 22630534449463408354929337)
          ·
            refine ⟨16972900837097556266197003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22630534449463408354929337 16972900837097556266197003)
            ·
              refine ⟨25459351255646334399295505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16972900837097556266197003 25459351255646334399295505)
              ·
                refine ⟨19094513441734750799471629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25459351255646334399295505 19094513441734750799471629)
                ·
                  refine ⟨7160442540650531549801861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19094513441734750799471629 7160442540650531549801861)
                  ·
                    refine ⟨1342582976371974665587849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7160442540650531549801861 1342582976371974665587849)
                    ·
                      rfl

theorem cell23_7844013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_7844013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844013 prefixEnd_7844013 := by exact prefixLift 7844013
  have htrace : WordTrace (prefixWord ++ tailWord_7844013) baseStart_7844013 baseEnd_7844013 := by
    simpa [prefixWord, tailWord_7844013, baseEnd_7844013] using wordTrace_append hprefix tailTrace_7844013
  have hstable : (prefixWord ++ tailWord_7844013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844013).length < 2 ^ (prefixWord ++ tailWord_7844013).sum := by decide
  have hdescent : baseEnd_7844013 < baseStart_7844013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844023 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 2, 2, 3]
def baseStart_7844023 : Nat := 118140960795 + 7844023 * 2 ^ 59
def prefixEnd_7844023 : Nat := 4983230072969 + 3 ^ 40 * 7844023 * 2
def baseEnd_7844023 : Nat := 4027754063922468957638501

theorem tailTrace_7844023 : CollatzResearch.WordTrace tailWord_7844023 prefixEnd_7844023 4027754063922468957638501 := by
  unfold tailWord_7844023
  simp only [CollatzResearch.WordTrace]
  refine ⟨286095022461451798318328723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190730014974301198878885815 286095022461451798318328723)
  ·
    refine ⟨429142533692177697477493085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286095022461451798318328723 429142533692177697477493085)
    ·
      refine ⟨160928450134566636554059907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429142533692177697477493085 160928450134566636554059907)
      ·
        refine ⟨241392675201849954831089861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160928450134566636554059907 241392675201849954831089861)
        ·
          refine ⟨45261126600346866530829349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241392675201849954831089861 45261126600346866530829349)
          ·
            refine ⟨8486461237565037474530503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45261126600346866530829349 8486461237565037474530503)
            ·
              refine ⟨12729691856347556211795755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8486461237565037474530503 12729691856347556211795755)
              ·
                refine ⟨19094537784521334317693633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12729691856347556211795755 19094537784521334317693633)
                ·
                  refine ⟨14320903338391000738270225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19094537784521334317693633 14320903338391000738270225)
                  ·
                    refine ⟨10740677503793250553702669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14320903338391000738270225 10740677503793250553702669)
                    ·
                      refine ⟨4027754063922468957638501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10740677503793250553702669 4027754063922468957638501)
                      ·
                        rfl

theorem cell23_7844023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_7844023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844023 prefixEnd_7844023 := by exact prefixLift 7844023
  have htrace : WordTrace (prefixWord ++ tailWord_7844023) baseStart_7844023 baseEnd_7844023 := by
    simpa [prefixWord, tailWord_7844023, baseEnd_7844023] using wordTrace_append hprefix tailTrace_7844023
  have hstable : (prefixWord ++ tailWord_7844023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844023).length < 2 ^ (prefixWord ++ tailWord_7844023).sum := by decide
  have hdescent : baseEnd_7844023 < baseStart_7844023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844076 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 2, 6, 2]
def baseStart_7844076 : Nat := 118140960795 + 7844076 * 2 ^ 59
def prefixEnd_7844076 : Nat := 4983230072969 + 3 ^ 40 * 7844076 * 2
def baseEnd_7844076 : Nat := 4027781278397157250275757

theorem tailTrace_7844076 : CollatzResearch.WordTrace tailWord_7844076 prefixEnd_7844076 4027781278397157250275757 := by
  unfold tailWord_7844076
  simp only [CollatzResearch.WordTrace]
  refine ⟨143048477765129894185004041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190731303686839858913338721 143048477765129894185004041)
  ·
    refine ⟨107286358323847420638753031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143048477765129894185004041 107286358323847420638753031)
    ·
      refine ⟨160929537485771130958129547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107286358323847420638753031 160929537485771130958129547)
      ·
        refine ⟨241394306228656696437194321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160929537485771130958129547 241394306228656696437194321)
        ·
          refine ⟨181045729671492522327895741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241394306228656696437194321 181045729671492522327895741)
          ·
            refine ⟨67892148626809695872960903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181045729671492522327895741 67892148626809695872960903)
            ·
              refine ⟨101838222940214543809441355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67892148626809695872960903 101838222940214543809441355)
              ·
                refine ⟨152757334410321815714162033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101838222940214543809441355 152757334410321815714162033)
                ·
                  refine ⟨114568000807741361785621525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152757334410321815714162033 114568000807741361785621525)
                  ·
                    refine ⟨5370375037862876333701009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114568000807741361785621525 5370375037862876333701009)
                    ·
                      refine ⟨4027781278397157250275757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5370375037862876333701009 4027781278397157250275757)
                      ·
                        rfl

theorem cell23_7844076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 6, 2].length) (baseStart_7844076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844076 prefixEnd_7844076 := by exact prefixLift 7844076
  have htrace : WordTrace (prefixWord ++ tailWord_7844076) baseStart_7844076 baseEnd_7844076 := by
    simpa [prefixWord, tailWord_7844076, baseEnd_7844076] using wordTrace_append hprefix tailTrace_7844076
  have hstable : (prefixWord ++ tailWord_7844076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844076).length < 2 ^ (prefixWord ++ tailWord_7844076).sum := by decide
  have hdescent : baseEnd_7844076 < baseStart_7844076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844086 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_7844086 : Nat := 118140960795 + 7844086 * 2 ^ 59
def prefixEnd_7844086 : Nat := 4983230072969 + 3 ^ 40 * 7844086 * 2
def baseEnd_7844086 : Nat := 1342595471067900737050237

theorem tailTrace_7844086 : CollatzResearch.WordTrace tailWord_7844086 prefixEnd_7844086 1342595471067900737050237 := by
  unfold tailWord_7844086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17881082516263972504867007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190731546840149040051914741 17881082516263972504867007)
  ·
    refine ⟨26821623774395958757300511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17881082516263972504867007 26821623774395958757300511)
    ·
      refine ⟨40232435661593938135950767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26821623774395958757300511 40232435661593938135950767)
      ·
        refine ⟨60348653492390907203926151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40232435661593938135950767 60348653492390907203926151)
        ·
          refine ⟨90522980238586360805889227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60348653492390907203926151 90522980238586360805889227)
          ·
            refine ⟨135784470357879541208833841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90522980238586360805889227 135784470357879541208833841)
            ·
              refine ⟨101838352768409655906625381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135784470357879541208833841 101838352768409655906625381)
              ·
                refine ⟨19094691144076810482492259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101838352768409655906625381 19094691144076810482492259)
                ·
                  refine ⟨28642036716115215723738389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19094691144076810482492259 28642036716115215723738389)
                  ·
                    refine ⟨1342595471067900737050237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28642036716115215723738389 1342595471067900737050237)
                    ·
                      rfl

theorem cell23_7844086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_7844086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844086 prefixEnd_7844086 := by exact prefixLift 7844086
  have htrace : WordTrace (prefixWord ++ tailWord_7844086) baseStart_7844086 baseEnd_7844086 := by
    simpa [prefixWord, tailWord_7844086, baseEnd_7844086] using wordTrace_append hprefix tailTrace_7844086
  have hstable : (prefixWord ++ tailWord_7844086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844086).length < 2 ^ (prefixWord ++ tailWord_7844086).sum := by decide
  have hdescent : baseEnd_7844086 < baseStart_7844086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844093 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 5, 2, 2]
def baseStart_7844093 : Nat := 118140960795 + 7844093 * 2 ^ 59
def prefixEnd_7844093 : Nat := 4983230072969 + 3 ^ 40 * 7844093 * 2
def baseEnd_7844093 : Nat := 4027790007568283683763179

theorem tailTrace_7844093 : CollatzResearch.WordTrace tailWord_7844093 prefixEnd_7844093 4027790007568283683763179 := by
  unfold tailWord_7844093
  simp only [CollatzResearch.WordTrace]
  refine ⟨286097575571198200273376933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190731717047465466848917955 286097575571198200273376933)
  ·
    refine ⟨53643295419599662551258175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286097575571198200273376933 53643295419599662551258175)
    ·
      refine ⟨80464943129399493826887263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53643295419599662551258175 80464943129399493826887263)
      ·
        refine ⟨120697414694099240740330895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80464943129399493826887263 120697414694099240740330895)
        ·
          refine ⟨181046122041148861110496343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120697414694099240740330895 181046122041148861110496343)
          ·
            refine ⟨271569183061723291665744515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181046122041148861110496343 271569183061723291665744515)
            ·
              refine ⟨407353774592584937498616773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271569183061723291665744515 407353774592584937498616773)
              ·
                refine ⟨76378832736109675780990645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407353774592584937498616773 76378832736109675780990645)
                ·
                  refine ⟨7160515569010282104467873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76378832736109675780990645 7160515569010282104467873)
                  ·
                    refine ⟨5370386676757711578350905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7160515569010282104467873 5370386676757711578350905)
                    ·
                      refine ⟨4027790007568283683763179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5370386676757711578350905 4027790007568283683763179)
                      ·
                        rfl

theorem cell23_7844093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_7844093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844093 prefixEnd_7844093 := by exact prefixLift 7844093
  have htrace : WordTrace (prefixWord ++ tailWord_7844093) baseStart_7844093 baseEnd_7844093 := by
    simpa [prefixWord, tailWord_7844093, baseEnd_7844093] using wordTrace_append hprefix tailTrace_7844093
  have hstable : (prefixWord ++ tailWord_7844093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844093).length < 2 ^ (prefixWord ++ tailWord_7844093).sum := by decide
  have hdescent : baseEnd_7844093 < baseStart_7844093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844130 : List Nat := [3, 3, 1, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_7844130 : Nat := 118140960795 + 7844130 * 2 ^ 59
def prefixEnd_7844130 : Nat := 4983230072969 + 3 ^ 40 * 7844130 * 2
def baseEnd_7844130 : Nat := 4027809006352500039000509

theorem tailTrace_7844130 : CollatzResearch.WordTrace tailWord_7844130 prefixEnd_7844130 4027809006352500039000509 := by
  unfold tailWord_7844130
  simp only [CollatzResearch.WordTrace]
  refine ⟨71524731268016038898118461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190732616714709437061649229 71524731268016038898118461)
  ·
    refine ⟨26821774225506014586794423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71524731268016038898118461 26821774225506014586794423)
    ·
      refine ⟨40232661338259021880191635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26821774225506014586794423 40232661338259021880191635)
      ·
        refine ⟨60348992007388532820287453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40232661338259021880191635 60348992007388532820287453)
        ·
          refine ⟨22630872002770699807607795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60348992007388532820287453 22630872002770699807607795)
          ·
            refine ⟨33946308004156049711411693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22630872002770699807607795 33946308004156049711411693)
            ·
              refine ⟨12729865501558518641779385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33946308004156049711411693 12729865501558518641779385)
              ·
                refine ⟨9547399126168888981334539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12729865501558518641779385 9547399126168888981334539)
                ·
                  refine ⟨14321098689253333472001809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9547399126168888981334539 14321098689253333472001809)
                  ·
                    refine ⟨10740824016940000104001357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14321098689253333472001809 10740824016940000104001357)
                    ·
                      refine ⟨4027809006352500039000509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10740824016940000104001357 4027809006352500039000509)
                      ·
                        rfl

theorem cell23_7844130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_7844130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844130 prefixEnd_7844130 := by exact prefixLift 7844130
  have htrace : WordTrace (prefixWord ++ tailWord_7844130) baseStart_7844130 baseEnd_7844130 := by
    simpa [prefixWord, tailWord_7844130, baseEnd_7844130] using wordTrace_append hprefix tailTrace_7844130
  have hstable : (prefixWord ++ tailWord_7844130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844130).length < 2 ^ (prefixWord ++ tailWord_7844130).sum := by decide
  have hdescent : baseEnd_7844130 < baseStart_7844130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844176 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 2, 6]
def baseStart_7844176 : Nat := 118140960795 + 7844176 * 2 ^ 59
def prefixEnd_7844176 : Nat := 4983230072969 + 3 ^ 40 * 7844176 * 2
def baseEnd_7844176 : Nat := 1342610875487535619675099

theorem tailTrace_7844176 : CollatzResearch.WordTrace tailWord_7844176 prefixEnd_7844176 1342610875487535619675099 := by
  unfold tailWord_7844176
  simp only [CollatzResearch.WordTrace]
  refine ⟨143050301414948752724324191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190733735219931670299098921 143050301414948752724324191)
  ·
    refine ⟨214575452122423129086486287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143050301414948752724324191 214575452122423129086486287)
    ·
      refine ⟨321863178183634693629729431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214575452122423129086486287 321863178183634693629729431)
      ·
        refine ⟨482794767275452040444594147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321863178183634693629729431 482794767275452040444594147)
        ·
          refine ⟨724192150913178060666891221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482794767275452040444594147 724192150913178060666891221)
          ·
            refine ⟨16973253537027610796880263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 724192150913178060666891221 16973253537027610796880263)
            ·
              refine ⟨25459880305541416195320395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16973253537027610796880263 25459880305541416195320395)
              ·
                refine ⟨38189820458312124292980593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25459880305541416195320395 38189820458312124292980593)
                ·
                  refine ⟨28642365343734093219735445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38189820458312124292980593 28642365343734093219735445)
                  ·
                    refine ⟨1342610875487535619675099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28642365343734093219735445 1342610875487535619675099)
                    ·
                      rfl

theorem cell23_7844176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 2, 6].length) (baseStart_7844176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844176 prefixEnd_7844176 := by exact prefixLift 7844176
  have htrace : WordTrace (prefixWord ++ tailWord_7844176) baseStart_7844176 baseEnd_7844176 := by
    simpa [prefixWord, tailWord_7844176, baseEnd_7844176] using wordTrace_append hprefix tailTrace_7844176
  have hstable : (prefixWord ++ tailWord_7844176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844176).length < 2 ^ (prefixWord ++ tailWord_7844176).sum := by decide
  have hdescent : baseEnd_7844176 < baseStart_7844176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844186 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3]
def baseStart_7844186 : Nat := 118140960795 + 7844186 * 2 ^ 59
def prefixEnd_7844186 : Nat := 4983230072969 + 3 ^ 40 * 7844186 * 2
def baseEnd_7844186 : Nat := 4027837761269151819900251

theorem tailTrace_7844186 : CollatzResearch.WordTrace tailWord_7844186 prefixEnd_7844186 4027837761269151819900251 := by
  unfold tailWord_7844186
  simp only [CollatzResearch.WordTrace]
  refine ⟨71525241889965319289128103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190733978373240851437674941 71525241889965319289128103)
  ·
    refine ⟨107287862834947978933692155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71525241889965319289128103 107287862834947978933692155)
    ·
      refine ⟨160931794252421968400538233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107287862834947978933692155 160931794252421968400538233)
      ·
        refine ⟨120698845689316476300403675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160931794252421968400538233 120698845689316476300403675)
        ·
          refine ⟨181048268533974714450605513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120698845689316476300403675 181048268533974714450605513)
          ·
            refine ⟨135786201400481035837954135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181048268533974714450605513 135786201400481035837954135)
            ·
              refine ⟨203679302100721553756931203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135786201400481035837954135 203679302100721553756931203)
              ·
                refine ⟨305518953151082330635396805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203679302100721553756931203 305518953151082330635396805)
                ·
                  refine ⟨57284803715827936994136901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305518953151082330635396805 57284803715827936994136901)
                  ·
                    refine ⟨10740900696717738186400669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57284803715827936994136901 10740900696717738186400669)
                    ·
                      refine ⟨4027837761269151819900251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10740900696717738186400669 4027837761269151819900251)
                      ·
                        rfl

theorem cell23_7844186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_7844186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844186 prefixEnd_7844186 := by exact prefixLift 7844186
  have htrace : WordTrace (prefixWord ++ tailWord_7844186) baseStart_7844186 baseEnd_7844186 := by
    simpa [prefixWord, tailWord_7844186, baseEnd_7844186] using wordTrace_append hprefix tailTrace_7844186
  have hstable : (prefixWord ++ tailWord_7844186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844186).length < 2 ^ (prefixWord ++ tailWord_7844186).sum := by decide
  have hdescent : baseEnd_7844186 < baseStart_7844186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844196 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_7844196 : Nat := 118140960795 + 7844196 * 2 ^ 59
def prefixEnd_7844196 : Nat := 4983230072969 + 3 ^ 40 * 7844196 * 2
def baseEnd_7844196 : Nat := 4027842896075696780775205

theorem tailTrace_7844196 : CollatzResearch.WordTrace tailWord_7844196 prefixEnd_7844196 4027842896075696780775205 := by
  unfold tailWord_7844196
  simp only [CollatzResearch.WordTrace]
  refine ⟨143050666144912524432188221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190734221526550032576250961 143050666144912524432188221)
  ·
    refine ⟨53643999804342196662070583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143050666144912524432188221 53643999804342196662070583)
    ·
      refine ⟨80465999706513294993105875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53643999804342196662070583 80465999706513294993105875)
      ·
        refine ⟨120698999559769942489658813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80465999706513294993105875 120698999559769942489658813)
        ·
          refine ⟨45262124834913728433622055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120698999559769942489658813 45262124834913728433622055)
          ·
            refine ⟨67893187252370592650433083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45262124834913728433622055 67893187252370592650433083)
            ·
              refine ⟨101839780878555888975649625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67893187252370592650433083 101839780878555888975649625)
              ·
                refine ⟨76379835658916916731737219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101839780878555888975649625 76379835658916916731737219)
                ·
                  refine ⟨114569753488375375097605829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76379835658916916731737219 114569753488375375097605829)
                  ·
                    refine ⟨21481828779070382830801093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114569753488375375097605829 21481828779070382830801093)
                    ·
                      refine ⟨4027842896075696780775205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21481828779070382830801093 4027842896075696780775205)
                      ·
                        rfl

theorem cell23_7844196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_7844196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844196 prefixEnd_7844196 := by exact prefixLift 7844196
  have htrace : WordTrace (prefixWord ++ tailWord_7844196) baseStart_7844196 baseEnd_7844196 := by
    simpa [prefixWord, tailWord_7844196, baseEnd_7844196] using wordTrace_append hprefix tailTrace_7844196
  have hstable : (prefixWord ++ tailWord_7844196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844196).length < 2 ^ (prefixWord ++ tailWord_7844196).sum := by decide
  have hdescent : baseEnd_7844196 < baseStart_7844196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844200 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_7844200 : Nat := 118140960795 + 7844200 * 2 ^ 59
def prefixEnd_7844200 : Nat := 4983230072969 + 3 ^ 40 * 7844200 * 2
def baseEnd_7844200 : Nat := 4027844949998314765125187

theorem tailTrace_7844200 : CollatzResearch.WordTrace tailWord_7844200 prefixEnd_7844200 4027844949998314765125187 := by
  unfold tailWord_7844200
  simp only [CollatzResearch.WordTrace]
  refine ⟨143050739090905278773761027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190734318787873705031681369 143050739090905278773761027)
  ·
    refine ⟨214576108636357918160641541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143050739090905278773761027 214576108636357918160641541)
    ·
      refine ⟨40233020369317109655120289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214576108636357918160641541 40233020369317109655120289)
      ·
        refine ⟨30174765276987832241340217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40233020369317109655120289 30174765276987832241340217)
        ·
          refine ⟨22631073957740874181005163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30174765276987832241340217 22631073957740874181005163)
          ·
            refine ⟨33946610936611311271507745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22631073957740874181005163 33946610936611311271507745)
            ·
              refine ⟨25459958202458483453630809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33946610936611311271507745 25459958202458483453630809)
              ·
                refine ⟨19094968651843862590223107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25459958202458483453630809 19094968651843862590223107)
                ·
                  refine ⟨28642452977765793885334661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19094968651843862590223107 28642452977765793885334661)
                  ·
                    refine ⟨5370459933331086353500249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28642452977765793885334661 5370459933331086353500249)
                    ·
                      refine ⟨4027844949998314765125187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5370459933331086353500249 4027844949998314765125187)
                      ·
                        rfl

theorem cell23_7844200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_7844200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844200 prefixEnd_7844200 := by exact prefixLift 7844200
  have htrace : WordTrace (prefixWord ++ tailWord_7844200) baseStart_7844200 baseEnd_7844200 := by
    simpa [prefixWord, tailWord_7844200, baseEnd_7844200] using wordTrace_append hprefix tailTrace_7844200
  have hstable : (prefixWord ++ tailWord_7844200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844200).length < 2 ^ (prefixWord ++ tailWord_7844200).sum := by decide
  have hdescent : baseEnd_7844200 < baseStart_7844200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844204 : List Nat := [2, 2, 1, 1, 6, 2, 2, 1, 1, 3, 2]
def baseStart_7844204 : Nat := 118140960795 + 7844204 * 2 ^ 59
def prefixEnd_7844204 : Nat := 4983230072969 + 3 ^ 40 * 7844204 * 2
def baseEnd_7844204 : Nat := 4027847003920932749475169

theorem tailTrace_7844204 : CollatzResearch.WordTrace tailWord_7844204 prefixEnd_7844204 4027847003920932749475169 := by
  unfold tailWord_7844204
  simp only [CollatzResearch.WordTrace]
  refine ⟨143050812036898033115333833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190734416049197377487111777 143050812036898033115333833)
  ·
    refine ⟨107288109027673524836500375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143050812036898033115333833 107288109027673524836500375)
    ·
      refine ⟨160932163541510287254750563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107288109027673524836500375 160932163541510287254750563)
      ·
        refine ⟨241398245312265430882125845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160932163541510287254750563 241398245312265430882125845)
        ·
          refine ⟨11315542749012442072599649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241398245312265430882125845 11315542749012442072599649)
          ·
            refine ⟨8486657061759331554449737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11315542749012442072599649 8486657061759331554449737)
            ·
              refine ⟨6364992796319498665837303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8486657061759331554449737 6364992796319498665837303)
              ·
                refine ⟨9547489194479247998755955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6364992796319498665837303 9547489194479247998755955)
                ·
                  refine ⟨14321233791718871998133933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9547489194479247998755955 14321233791718871998133933)
                  ·
                    refine ⟨5370462671894576999300225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14321233791718871998133933 5370462671894576999300225)
                    ·
                      refine ⟨4027847003920932749475169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5370462671894576999300225 4027847003920932749475169)
                      ·
                        rfl

theorem cell23_7844204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 3, 2].length) (baseStart_7844204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844204 prefixEnd_7844204 := by exact prefixLift 7844204
  have htrace : WordTrace (prefixWord ++ tailWord_7844204) baseStart_7844204 baseEnd_7844204 := by
    simpa [prefixWord, tailWord_7844204, baseEnd_7844204] using wordTrace_append hprefix tailTrace_7844204
  have hstable : (prefixWord ++ tailWord_7844204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844204).length < 2 ^ (prefixWord ++ tailWord_7844204).sum := by decide
  have hdescent : baseEnd_7844204 < baseStart_7844204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844213 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_7844213 : Nat := 118140960795 + 7844213 * 2 ^ 59
def prefixEnd_7844213 : Nat := 4983230072969 + 3 ^ 40 * 7844213 * 2
def baseEnd_7844213 : Nat := 4027851625246823214262627

theorem tailTrace_7844213 : CollatzResearch.WordTrace tailWord_7844213 prefixEnd_7844213 4027851625246823214262627 := by
  unfold tailWord_7844213
  simp only [CollatzResearch.WordTrace]
  refine ⟨286101952330763460767745293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190734634887175640511830195 286101952330763460767745293)
  ·
    refine ⟨107288232124036297787904485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286101952330763460767745293 107288232124036297787904485)
    ·
      refine ⟨20116543523256805835232091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107288232124036297787904485 20116543523256805835232091)
      ·
        refine ⟨30174815284885208752848137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20116543523256805835232091 30174815284885208752848137)
        ·
          refine ⟨22631111463663906564636103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30174815284885208752848137 22631111463663906564636103)
          ·
            refine ⟨33946667195495859846954155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22631111463663906564636103 33946667195495859846954155)
            ·
              refine ⟨50920000793243789770431233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33946667195495859846954155 50920000793243789770431233)
              ·
                refine ⟨38190000594932842327823425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50920000793243789770431233 38190000594932842327823425)
                ·
                  refine ⟨28642500446199631745867569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38190000594932842327823425 28642500446199631745867569)
                  ·
                    refine ⟨21481875334649723809400677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28642500446199631745867569 21481875334649723809400677)
                    ·
                      refine ⟨4027851625246823214262627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21481875334649723809400677 4027851625246823214262627)
                      ·
                        rfl

theorem cell23_7844213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_7844213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844213 prefixEnd_7844213 := by exact prefixLift 7844213
  have htrace : WordTrace (prefixWord ++ tailWord_7844213) baseStart_7844213 baseEnd_7844213 := by
    simpa [prefixWord, tailWord_7844213, baseEnd_7844213] using wordTrace_append hprefix tailTrace_7844213
  have hstable : (prefixWord ++ tailWord_7844213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844213).length < 2 ^ (prefixWord ++ tailWord_7844213).sum := by decide
  have hdescent : baseEnd_7844213 < baseStart_7844213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844233 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 2, 3, 3]
def baseStart_7844233 : Nat := 118140960795 + 7844233 * 2 ^ 59
def prefixEnd_7844233 : Nat := 4983230072969 + 3 ^ 40 * 7844233 * 2
def baseEnd_7844233 : Nat := 4027861894859913136012535

theorem tailTrace_7844233 : CollatzResearch.WordTrace tailWord_7844233 prefixEnd_7844233 4027861894859913136012535 := by
  unfold tailWord_7844233
  simp only [CollatzResearch.WordTrace]
  refine ⟨286102681790691004183473353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190735121193794002788982235 286102681790691004183473353)
  ·
    refine ⟨214577011343018253137605015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286102681790691004183473353 214577011343018253137605015)
    ·
      refine ⟨321865517014527379706407523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214577011343018253137605015 321865517014527379706407523)
      ·
        refine ⟨482798275521791069559611285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321865517014527379706407523 482798275521791069559611285)
        ·
          refine ⟨22631169165083956385606779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 482798275521791069559611285 22631169165083956385606779)
          ·
            refine ⟨33946753747625934578410169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22631169165083956385606779 33946753747625934578410169)
            ·
              refine ⟨25460065310719450933807627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33946753747625934578410169 25460065310719450933807627)
              ·
                refine ⟨38190097966079176400711441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25460065310719450933807627 38190097966079176400711441)
                ·
                  refine ⟨28642573474559382300533581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38190097966079176400711441 28642573474559382300533581)
                  ·
                    refine ⟨10740965052959768362700093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28642573474559382300533581 10740965052959768362700093)
                    ·
                      refine ⟨4027861894859913136012535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10740965052959768362700093 4027861894859913136012535)
                      ·
                        rfl

theorem cell23_7844233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 3, 3].length) (baseStart_7844233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844233 prefixEnd_7844233 := by exact prefixLift 7844233
  have htrace : WordTrace (prefixWord ++ tailWord_7844233) baseStart_7844233 baseEnd_7844233 := by
    simpa [prefixWord, tailWord_7844233, baseEnd_7844233] using wordTrace_append hprefix tailTrace_7844233
  have hstable : (prefixWord ++ tailWord_7844233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844233).length < 2 ^ (prefixWord ++ tailWord_7844233).sum := by decide
  have hdescent : baseEnd_7844233 < baseStart_7844233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844234 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 1, 4, 2]
def baseStart_7844234 : Nat := 118140960795 + 7844234 * 2 ^ 59
def prefixEnd_7844234 : Nat := 4983230072969 + 3 ^ 40 * 7844234 * 2
def baseEnd_7844234 : Nat := 4027862408340567632100031

theorem tailTrace_7844234 : CollatzResearch.WordTrace tailWord_7844234 prefixEnd_7844234 4027862408340567632100031 := by
  unfold tailWord_7844234
  simp only [CollatzResearch.WordTrace]
  refine ⟨71525679565921845338564939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190735145509124920902839837 71525679565921845338564939)
  ·
    refine ⟨107288519348882768007847409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71525679565921845338564939 107288519348882768007847409)
    ·
      refine ⟨80466389511662076005885557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107288519348882768007847409 80466389511662076005885557)
      ·
        refine ⟨7543724016718319625551771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80466389511662076005885557 7543724016718319625551771)
        ·
          refine ⟨11315586025077479438327657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7543724016718319625551771 11315586025077479438327657)
          ·
            refine ⟨8486689518808109578745743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11315586025077479438327657 8486689518808109578745743)
            ·
              refine ⟨12730034278212164368118615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8486689518808109578745743 12730034278212164368118615)
              ·
                refine ⟨19095051417318246552177923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12730034278212164368118615 19095051417318246552177923)
                ·
                  refine ⟨28642577125977369828266885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19095051417318246552177923 28642577125977369828266885)
                  ·
                    refine ⟨5370483211120756842800041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28642577125977369828266885 5370483211120756842800041)
                    ·
                      refine ⟨4027862408340567632100031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5370483211120756842800041 4027862408340567632100031)
                      ·
                        rfl

theorem cell23_7844234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_7844234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844234 prefixEnd_7844234 := by exact prefixLift 7844234
  have htrace : WordTrace (prefixWord ++ tailWord_7844234) baseStart_7844234 baseEnd_7844234 := by
    simpa [prefixWord, tailWord_7844234, baseEnd_7844234] using wordTrace_append hprefix tailTrace_7844234
  have hstable : (prefixWord ++ tailWord_7844234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844234).length < 2 ^ (prefixWord ++ tailWord_7844234).sum := by decide
  have hdescent : baseEnd_7844234 < baseStart_7844234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844236 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 1, 7]
def baseStart_7844236 : Nat := 118140960795 + 7844236 * 2 ^ 59
def prefixEnd_7844236 : Nat := 4983230072969 + 3 ^ 40 * 7844236 * 2
def baseEnd_7844236 : Nat := 1342621145100625541425007

theorem tailTrace_7844236 : CollatzResearch.WordTrace tailWord_7844236 prefixEnd_7844236 1342621145100625541425007 := by
  unfold tailWord_7844236
  simp only [CollatzResearch.WordTrace]
  refine ⟨143051395604840067847916281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190735194139786757130555041 143051395604840067847916281)
  ·
    refine ⟨107288546703630050885937211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143051395604840067847916281 107288546703630050885937211)
    ·
      refine ⟨160932820055445076328905817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107288546703630050885937211 160932820055445076328905817)
      ·
        refine ⟨120699615041583807246679363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160932820055445076328905817 120699615041583807246679363)
        ·
          refine ⟨181049422562375710870019045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120699615041583807246679363 181049422562375710870019045)
          ·
            refine ⟨33946766730445445788128571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181049422562375710870019045 33946766730445445788128571)
            ·
              refine ⟨50920150095668168682192857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33946766730445445788128571 50920150095668168682192857)
              ·
                refine ⟨38190112571751126511644643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50920150095668168682192857 38190112571751126511644643)
                ·
                  refine ⟨57285168857626689767466965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38190112571751126511644643 57285168857626689767466965)
                  ·
                    refine ⟨1342621145100625541425007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57285168857626689767466965 1342621145100625541425007)
                    ·
                      rfl

theorem cell23_7844236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_7844236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844236 prefixEnd_7844236 := by exact prefixLift 7844236
  have htrace : WordTrace (prefixWord ++ tailWord_7844236) baseStart_7844236 baseEnd_7844236 := by
    simpa [prefixWord, tailWord_7844236, baseEnd_7844236] using wordTrace_append hprefix tailTrace_7844236
  have hstable : (prefixWord ++ tailWord_7844236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844236).length < 2 ^ (prefixWord ++ tailWord_7844236).sum := by decide
  have hdescent : baseEnd_7844236 < baseStart_7844236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844273 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 4, 1, 4]
def baseStart_7844273 : Nat := 118140960795 + 7844273 * 2 ^ 59
def prefixEnd_7844273 : Nat := 4983230072969 + 3 ^ 40 * 7844273 * 2
def baseEnd_7844273 : Nat := 4027882434086092979512351

theorem tailTrace_7844273 : CollatzResearch.WordTrace tailWord_7844273 prefixEnd_7844273 4027882434086092979512351 := by
  unfold tailWord_7844273
  simp only [CollatzResearch.WordTrace]
  refine ⟨286104140710546091014929473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190736093807030727343286315 286104140710546091014929473)
  ·
    refine ⟨214578105532909568261197105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286104140710546091014929473 214578105532909568261197105)
    ·
      refine ⟨160933579149682176195897829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214578105532909568261197105 160933579149682176195897829)
      ·
        refine ⟨30175046090565408036730843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160933579149682176195897829 30175046090565408036730843)
        ·
          refine ⟨45262569135848112055096265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30175046090565408036730843 45262569135848112055096265)
          ·
            refine ⟨33946926851886084041322199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45262569135848112055096265 33946926851886084041322199)
            ·
              refine ⟨50920390277829126061983299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33946926851886084041322199 50920390277829126061983299)
              ·
                refine ⟨76380585416743689092974949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50920390277829126061983299 76380585416743689092974949)
                ·
                  refine ⟨14321359765639441704932803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76380585416743689092974949 14321359765639441704932803)
                  ·
                    refine ⟨21482039648459162557399205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14321359765639441704932803 21482039648459162557399205)
                    ·
                      refine ⟨4027882434086092979512351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21482039648459162557399205 4027882434086092979512351)
                      ·
                        rfl

theorem cell23_7844273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_7844273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844273 prefixEnd_7844273 := by exact prefixLift 7844273
  have htrace : WordTrace (prefixWord ++ tailWord_7844273) baseStart_7844273 baseEnd_7844273 := by
    simpa [prefixWord, tailWord_7844273, baseEnd_7844273] using wordTrace_append hprefix tailTrace_7844273
  have hstable : (prefixWord ++ tailWord_7844273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844273).length < 2 ^ (prefixWord ++ tailWord_7844273).sum := by decide
  have hdescent : baseEnd_7844273 < baseStart_7844273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844317 : List Nat := [1, 4, 3, 1, 1, 1, 2, 5, 1, 4]
def baseStart_7844317 : Nat := 118140960795 + 7844317 * 2 ^ 59
def prefixEnd_7844317 : Nat := 4983230072969 + 3 ^ 40 * 7844317 * 2
def baseEnd_7844317 : Nat := 1342635009078296935787383

theorem tailTrace_7844317 : CollatzResearch.WordTrace tailWord_7844317 prefixEnd_7844317 1342635009078296935787383 := by
  unfold tailWord_7844317
  simp only [CollatzResearch.WordTrace]
  refine ⟨286105745522386686529531205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190737163681591124353020803 286105745522386686529531205)
  ·
    refine ⟨53644827285447503724287101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286105745522386686529531205 53644827285447503724287101)
    ·
      refine ⟨20116810232042813896607663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53644827285447503724287101 20116810232042813896607663)
      ·
        refine ⟨30175215348064220844911495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20116810232042813896607663 30175215348064220844911495)
        ·
          refine ⟨45262823022096331267367243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30175215348064220844911495 45262823022096331267367243)
          ·
            refine ⟨67894234533144496901050865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45262823022096331267367243 67894234533144496901050865)
            ·
              refine ⟨50920675899858372675788149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67894234533144496901050865 50920675899858372675788149)
              ·
                refine ⟨4773813365611722438355139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50920675899858372675788149 4773813365611722438355139)
                ·
                  refine ⟨7160720048417583657532709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4773813365611722438355139 7160720048417583657532709)
                  ·
                    refine ⟨1342635009078296935787383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7160720048417583657532709 1342635009078296935787383)
                    ·
                      rfl

theorem cell23_7844317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_7844317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844317 prefixEnd_7844317 := by exact prefixLift 7844317
  have htrace : WordTrace (prefixWord ++ tailWord_7844317) baseStart_7844317 baseEnd_7844317 := by
    simpa [prefixWord, tailWord_7844317, baseEnd_7844317] using wordTrace_append hprefix tailTrace_7844317
  have hstable : (prefixWord ++ tailWord_7844317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844317).length < 2 ^ (prefixWord ++ tailWord_7844317).sum := by decide
  have hdescent : baseEnd_7844317 < baseStart_7844317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844330 : List Nat := [3, 1, 3, 1, 3, 2, 2, 2, 6]
def baseStart_7844330 : Nat := 118140960795 + 7844330 * 2 ^ 59
def prefixEnd_7844330 : Nat := 4983230072969 + 3 ^ 40 * 7844330 * 2
def baseEnd_7844330 : Nat := 447545744720377695166621

theorem tailTrace_7844330 : CollatzResearch.WordTrace tailWord_7844330 prefixEnd_7844330 447545744720377695166621 := by
  unfold tailWord_7844330
  simp only [CollatzResearch.WordTrace]
  refine ⟨71526554917834897437438611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190737479780893059833169629 71526554917834897437438611)
  ·
    refine ⟨107289832376752346156157917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71526554917834897437438611 107289832376752346156157917)
    ·
      refine ⟨40233687141282129808559219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107289832376752346156157917 40233687141282129808559219)
      ·
        refine ⟨60350530711923194712838829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40233687141282129808559219 60350530711923194712838829)
        ·
          refine ⟨22631449016971198017314561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60350530711923194712838829 22631449016971198017314561)
          ·
            refine ⟨16973586762728398512985921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22631449016971198017314561 16973586762728398512985921)
            ·
              refine ⟨12730190072046298884739441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16973586762728398512985921 12730190072046298884739441)
              ·
                refine ⟨9547642554034724163554581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12730190072046298884739441 9547642554034724163554581)
                ·
                  refine ⟨447545744720377695166621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9547642554034724163554581 447545744720377695166621)
                  ·
                    rfl

theorem cell23_7844330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 6].length) (baseStart_7844330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844330 prefixEnd_7844330 := by exact prefixLift 7844330
  have htrace : WordTrace (prefixWord ++ tailWord_7844330) baseStart_7844330 baseEnd_7844330 := by
    simpa [prefixWord, tailWord_7844330, baseEnd_7844330] using wordTrace_append hprefix tailTrace_7844330
  have hstable : (prefixWord ++ tailWord_7844330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844330).length < 2 ^ (prefixWord ++ tailWord_7844330).sum := by decide
  have hdescent : baseEnd_7844330 < baseStart_7844330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844334 : List Nat := [4, 1, 2, 1, 2, 2, 4, 2, 1, 4]
def baseStart_7844334 : Nat := 118140960795 + 7844334 * 2 ^ 59
def prefixEnd_7844334 : Nat := 4983230072969 + 3 ^ 40 * 7844334 * 2
def baseEnd_7844334 : Nat := 1342637918802005746949857

theorem tailTrace_7844334 : CollatzResearch.WordTrace tailWord_7844334 prefixEnd_7844334 1342637918802005746949857 := by
  unfold tailWord_7844334
  simp only [CollatzResearch.WordTrace]
  refine ⟨35763295695415637304112507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190737577042216732288600037 35763295695415637304112507)
  ·
    refine ⟨53644943543123455956168761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35763295695415637304112507 53644943543123455956168761)
    ·
      refine ⟨40233707657342591967126571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53644943543123455956168761 40233707657342591967126571)
      ·
        refine ⟨60350561486013887950689857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40233707657342591967126571 60350561486013887950689857)
        ·
          refine ⟨45262921114510415963017393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60350561486013887950689857 45262921114510415963017393)
          ·
            refine ⟨33947190835882811972263045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45262921114510415963017393 33947190835882811972263045)
            ·
              refine ⟨6365098281728027244799321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33947190835882811972263045 6365098281728027244799321)
              ·
                refine ⟨4773823711296020433599491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6365098281728027244799321 4773823711296020433599491)
                ·
                  refine ⟨7160735566944030650399237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4773823711296020433599491 7160735566944030650399237)
                  ·
                    refine ⟨1342637918802005746949857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7160735566944030650399237 1342637918802005746949857)
                    ·
                      rfl

theorem cell23_7844334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_7844334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844334 prefixEnd_7844334 := by exact prefixLift 7844334
  have htrace : WordTrace (prefixWord ++ tailWord_7844334) baseStart_7844334 baseEnd_7844334 := by
    simpa [prefixWord, tailWord_7844334, baseEnd_7844334] using wordTrace_append hprefix tailTrace_7844334
  have hstable : (prefixWord ++ tailWord_7844334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844334).length < 2 ^ (prefixWord ++ tailWord_7844334).sum := by decide
  have hdescent : baseEnd_7844334 < baseStart_7844334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844373 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 1, 6]
def baseStart_7844373 : Nat := 118140960795 + 7844373 * 2 ^ 59
def prefixEnd_7844373 : Nat := 4983230072969 + 3 ^ 40 * 7844373 * 2
def baseEnd_7844373 : Nat := 1342644594050514196087297

theorem tailTrace_7844373 : CollatzResearch.WordTrace tailWord_7844373 prefixEnd_7844373 1342644594050514196087297 := by
  unfold tailWord_7844373
  simp only [CollatzResearch.WordTrace]
  refine ⟨286107788010183808093569773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190738525340122538729046515 286107788010183808093569773)
  ·
    refine ⟨107290420503818928035088665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286107788010183808093569773 107290420503818928035088665)
    ·
      refine ⟨80467815377864196026316499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107290420503818928035088665 80467815377864196026316499)
      ·
        refine ⟨120701723066796294039474749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80467815377864196026316499 120701723066796294039474749)
        ·
          refine ⟨45263146150048610264803031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120701723066796294039474749 45263146150048610264803031)
          ·
            refine ⟨67894719225072915397204547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45263146150048610264803031 67894719225072915397204547)
            ·
              refine ⟨101842078837609373095806821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67894719225072915397204547 101842078837609373095806821)
              ·
                refine ⟨19095389782051757455463779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101842078837609373095806821 19095389782051757455463779)
                ·
                  refine ⟨28643084673077636183195669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19095389782051757455463779 28643084673077636183195669)
                  ·
                    refine ⟨1342644594050514196087297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28643084673077636183195669 1342644594050514196087297)
                    ·
                      rfl

theorem cell23_7844373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_7844373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844373 prefixEnd_7844373 := by exact prefixLift 7844373
  have htrace : WordTrace (prefixWord ++ tailWord_7844373) baseStart_7844373 baseEnd_7844373 := by
    simpa [prefixWord, tailWord_7844373, baseEnd_7844373] using wordTrace_append hprefix tailTrace_7844373
  have hstable : (prefixWord ++ tailWord_7844373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844373).length < 2 ^ (prefixWord ++ tailWord_7844373).sum := by decide
  have hdescent : baseEnd_7844373 < baseStart_7844373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844383 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 5]
def baseStart_7844383 : Nat := 118140960795 + 7844383 * 2 ^ 59
def prefixEnd_7844383 : Nat := 4983230072969 + 3 ^ 40 * 7844383 * 2
def baseEnd_7844383 : Nat := 4027938916958087549136845

theorem tailTrace_7844383 : CollatzResearch.WordTrace tailWord_7844383 prefixEnd_7844383 4027938916958087549136845 := by
  unfold tailWord_7844383
  simp only [CollatzResearch.WordTrace]
  refine ⟨286108152740147579801433803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190738768493431719867622535 286108152740147579801433803)
  ·
    refine ⟨429162229110221369702150705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286108152740147579801433803 429162229110221369702150705)
    ·
      refine ⟨321871671832666027276613029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429162229110221369702150705 321871671832666027276613029)
      ·
        refine ⟨60350938468624880114364943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321871671832666027276613029 60350938468624880114364943)
        ·
          refine ⟨90526407702937320171547415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60350938468624880114364943 90526407702937320171547415)
          ·
            refine ⟨135789611554405980257321123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90526407702937320171547415 135789611554405980257321123)
            ·
              refine ⟨203684417331608970385981685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135789611554405980257321123 203684417331608970385981685)
              ·
                refine ⟨19095414124838340973685783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203684417331608970385981685 19095414124838340973685783)
                ·
                  refine ⟨28643121187257511460528675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19095414124838340973685783 28643121187257511460528675)
                  ·
                    refine ⟨42964681780886267190793013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28643121187257511460528675 42964681780886267190793013)
                    ·
                      refine ⟨4027938916958087549136845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42964681780886267190793013 4027938916958087549136845)
                      ·
                        rfl

theorem cell23_7844383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_7844383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844383 prefixEnd_7844383 := by exact prefixLift 7844383
  have htrace : WordTrace (prefixWord ++ tailWord_7844383) baseStart_7844383 baseEnd_7844383 := by
    simpa [prefixWord, tailWord_7844383, baseEnd_7844383] using wordTrace_append hprefix tailTrace_7844383
  have hstable : (prefixWord ++ tailWord_7844383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844383).length < 2 ^ (prefixWord ++ tailWord_7844383).sum := by decide
  have hdescent : baseEnd_7844383 < baseStart_7844383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844391 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_7844391 : Nat := 118140960795 + 7844391 * 2 ^ 59
def prefixEnd_7844391 : Nat := 4983230072969 + 3 ^ 40 * 7844391 * 2
def baseEnd_7844391 : Nat := 4027943024803323517836809

theorem tailTrace_7844391 : CollatzResearch.WordTrace tailWord_7844391 prefixEnd_7844391 4027943024803323517836809 := by
  unfold tailWord_7844391
  simp only [CollatzResearch.WordTrace]
  refine ⟨286108444524118597167725027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190738963016079064778483351 286108444524118597167725027)
  ·
    refine ⟨429162666786177895751587541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286108444524118597167725027 429162666786177895751587541)
    ·
      refine ⟨10058500002801044431677833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 429162666786177895751587541 10058500002801044431677833)
      ·
        refine ⟨7543875002100783323758375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10058500002801044431677833 7543875002100783323758375)
        ·
          refine ⟨11315812503151174985637563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7543875002100783323758375 11315812503151174985637563)
          ·
            refine ⟨16973718754726762478456345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11315812503151174985637563 16973718754726762478456345)
            ·
              refine ⟨12730289066045071858842259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16973718754726762478456345 12730289066045071858842259)
              ·
                refine ⟨19095433599067607788263389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12730289066045071858842259 19095433599067607788263389)
                ·
                  refine ⟨7160787599650352920598771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19095433599067607788263389 7160787599650352920598771)
                  ·
                    refine ⟨10741181399475529380898157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7160787599650352920598771 10741181399475529380898157)
                    ·
                      refine ⟨4027943024803323517836809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10741181399475529380898157 4027943024803323517836809)
                      ·
                        rfl

theorem cell23_7844391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_7844391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844391 prefixEnd_7844391 := by exact prefixLift 7844391
  have htrace : WordTrace (prefixWord ++ tailWord_7844391) baseStart_7844391 baseEnd_7844391 := by
    simpa [prefixWord, tailWord_7844391, baseEnd_7844391] using wordTrace_append hprefix tailTrace_7844391
  have hstable : (prefixWord ++ tailWord_7844391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844391).length < 2 ^ (prefixWord ++ tailWord_7844391).sum := by decide
  have hdescent : baseEnd_7844391 < baseStart_7844391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844407 : List Nat := [1, 1, 3, 1, 2, 3, 5, 1, 2, 4]
def baseStart_7844407 : Nat := 118140960795 + 7844407 * 2 ^ 59
def prefixEnd_7844407 : Nat := 4983230072969 + 3 ^ 40 * 7844407 * 2
def baseEnd_7844407 : Nat := 1342650413497931818412245

theorem tailTrace_7844407 : CollatzResearch.WordTrace tailWord_7844407 prefixEnd_7844407 1342650413497931818412245 := by
  unfold tailWord_7844407
  simp only [CollatzResearch.WordTrace]
  refine ⟨286109028092060631900307475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190739352061373754600204983 286109028092060631900307475)
  ·
    refine ⟨429163542138090947850461213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286109028092060631900307475 429163542138090947850461213)
    ·
      refine ⟨160936328301784105443922955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429163542138090947850461213 160936328301784105443922955)
      ·
        refine ⟨241404492452676158165884433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160936328301784105443922955 241404492452676158165884433)
        ·
          refine ⟨181053369339507118624413325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241404492452676158165884433 181053369339507118624413325)
          ·
            refine ⟨67895013502315169484154997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181053369339507118624413325 67895013502315169484154997)
            ·
              refine ⟨6365157515842047139139531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67895013502315169484154997 6365157515842047139139531)
              ·
                refine ⟨9547736273763070708709297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6365157515842047139139531 9547736273763070708709297)
                ·
                  refine ⟨7160802205322303031531973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9547736273763070708709297 7160802205322303031531973)
                  ·
                    refine ⟨1342650413497931818412245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7160802205322303031531973 1342650413497931818412245)
                    ·
                      rfl

theorem cell23_7844407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_7844407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844407 prefixEnd_7844407 := by exact prefixLift 7844407
  have htrace : WordTrace (prefixWord ++ tailWord_7844407) baseStart_7844407 baseEnd_7844407 := by
    simpa [prefixWord, tailWord_7844407, baseEnd_7844407] using wordTrace_append hprefix tailTrace_7844407
  have hstable : (prefixWord ++ tailWord_7844407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844407).length < 2 ^ (prefixWord ++ tailWord_7844407).sum := by decide
  have hdescent : baseEnd_7844407 < baseStart_7844407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844410 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4]
def baseStart_7844410 : Nat := 118140960795 + 7844410 * 2 ^ 59
def prefixEnd_7844410 : Nat := 4983230072969 + 3 ^ 40 * 7844410 * 2
def baseEnd_7844410 : Nat := 4027952780935758943499221

theorem tailTrace_7844410 : CollatzResearch.WordTrace tailWord_7844410 prefixEnd_7844410 4027952780935758943499221 := by
  unfold tailWord_7844410
  simp only [CollatzResearch.WordTrace]
  refine ⟨71527284377762440853166671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190739425007366508941777789 71527284377762440853166671)
  ·
    refine ⟨107290926566643661279750007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71527284377762440853166671 107290926566643661279750007)
    ·
      refine ⟨160936389849965491919625011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107290926566643661279750007 160936389849965491919625011)
      ·
        refine ⟨241404584774948237879437517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160936389849965491919625011 241404584774948237879437517)
        ·
          refine ⟨90526719290605589204789069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241404584774948237879437517 90526719290605589204789069)
          ·
            refine ⟨33947519733977095951795901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90526719290605589204789069 33947519733977095951795901)
            ·
              refine ⟨12730319900241410981923463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33947519733977095951795901 12730319900241410981923463)
              ·
                refine ⟨19095479850362116472885195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12730319900241410981923463 19095479850362116472885195)
                ·
                  refine ⟨28643219775543174709327793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19095479850362116472885195 28643219775543174709327793)
                  ·
                    refine ⟨21482414831657381031995845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28643219775543174709327793 21482414831657381031995845)
                    ·
                      refine ⟨4027952780935758943499221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21482414831657381031995845 4027952780935758943499221)
                      ·
                        rfl

theorem cell23_7844410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_7844410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844410 prefixEnd_7844410 := by exact prefixLift 7844410
  have htrace : WordTrace (prefixWord ++ tailWord_7844410) baseStart_7844410 baseEnd_7844410 := by
    simpa [prefixWord, tailWord_7844410, baseEnd_7844410] using wordTrace_append hprefix tailTrace_7844410
  have hstable : (prefixWord ++ tailWord_7844410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844410).length < 2 ^ (prefixWord ++ tailWord_7844410).sum := by decide
  have hdescent : baseEnd_7844410 < baseStart_7844410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844417 : List Nat := [1, 2, 5, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_7844417 : Nat := 118140960795 + 7844417 * 2 ^ 59
def prefixEnd_7844417 : Nat := 4983230072969 + 3 ^ 40 * 7844417 * 2
def baseEnd_7844417 : Nat := 4027956375300340416111689

theorem tailTrace_7844417 : CollatzResearch.WordTrace tailWord_7844417 prefixEnd_7844417 4027956375300340416111689 := by
  unfold tailWord_7844417
  simp only [CollatzResearch.WordTrace]
  refine ⟨286109392822024403608171505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190739595214682935738781003 286109392822024403608171505)
  ·
    refine ⟨214582044616518302706128629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286109392822024403608171505 214582044616518302706128629)
    ·
      refine ⟨20117066682798590878699559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214582044616518302706128629 20117066682798590878699559)
      ·
        refine ⟨30175600024197886318049339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20117066682798590878699559 30175600024197886318049339)
        ·
          refine ⟨45263400036296829477074009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30175600024197886318049339 45263400036296829477074009)
          ·
            refine ⟨33947550027222622107805507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45263400036296829477074009 33947550027222622107805507)
            ·
              refine ⟨50921325040833933161708261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33947550027222622107805507 50921325040833933161708261)
              ·
                refine ⟨9547748445156362467820299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50921325040833933161708261 9547748445156362467820299)
                ·
                  refine ⟨14321622667734543701730449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9547748445156362467820299 14321622667734543701730449)
                  ·
                    refine ⟨10741217000800907776297837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14321622667734543701730449 10741217000800907776297837)
                    ·
                      refine ⟨4027956375300340416111689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10741217000800907776297837 4027956375300340416111689)
                      ·
                        rfl

theorem cell23_7844417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_7844417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844417 prefixEnd_7844417 := by exact prefixLift 7844417
  have htrace : WordTrace (prefixWord ++ tailWord_7844417) baseStart_7844417 baseEnd_7844417 := by
    simpa [prefixWord, tailWord_7844417, baseEnd_7844417] using wordTrace_append hprefix tailTrace_7844417
  have hstable : (prefixWord ++ tailWord_7844417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844417).length < 2 ^ (prefixWord ++ tailWord_7844417).sum := by decide
  have hdescent : baseEnd_7844417 < baseStart_7844417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844430 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_7844430 : Nat := 118140960795 + 7844430 * 2 ^ 59
def prefixEnd_7844430 : Nat := 4983230072969 + 3 ^ 40 * 7844430 * 2
def baseEnd_7844430 : Nat := 4027963050548848865249129

theorem tailTrace_7844430 : CollatzResearch.WordTrace tailWord_7844430 prefixEnd_7844430 4027963050548848865249129 := by
  unfold tailWord_7844430
  simp only [CollatzResearch.WordTrace]
  refine ⟨35763733371372163353549343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190739911313984871218929829 35763733371372163353549343)
  ·
    refine ⟨53645600057058245030324015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35763733371372163353549343 53645600057058245030324015)
    ·
      refine ⟨80468400085587367545486023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53645600057058245030324015 80468400085587367545486023)
      ·
        refine ⟨120702600128381051318229035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80468400085587367545486023 120702600128381051318229035)
        ·
          refine ⟨181053900192571576977343553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120702600128381051318229035 181053900192571576977343553)
          ·
            refine ⟨135790425144428682733007665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181053900192571576977343553 135790425144428682733007665)
            ·
              refine ⟨101842818858321512049755749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135790425144428682733007665 101842818858321512049755749)
              ·
                refine ⟨19095528535935283509329203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101842818858321512049755749 19095528535935283509329203)
                ·
                  refine ⟨28643292803902925263993805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19095528535935283509329203 28643292803902925263993805)
                  ·
                    refine ⟨10741234801463596973997677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28643292803902925263993805 10741234801463596973997677)
                    ·
                      refine ⟨4027963050548848865249129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10741234801463596973997677 4027963050548848865249129)
                      ·
                        rfl

theorem cell23_7844430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_7844430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844430 prefixEnd_7844430 := by exact prefixLift 7844430
  have htrace : WordTrace (prefixWord ++ tailWord_7844430) baseStart_7844430 baseEnd_7844430 := by
    simpa [prefixWord, tailWord_7844430, baseEnd_7844430] using wordTrace_append hprefix tailTrace_7844430
  have hstable : (prefixWord ++ tailWord_7844430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844430).length < 2 ^ (prefixWord ++ tailWord_7844430).sum := by decide
  have hdescent : baseEnd_7844430 < baseStart_7844430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844463 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 2, 6]
def baseStart_7844463 : Nat := 118140960795 + 7844463 * 2 ^ 59
def prefixEnd_7844463 : Nat := 4983230072969 + 3 ^ 40 * 7844463 * 2
def baseEnd_7844463 : Nat := 1342659998470149078712159

theorem tailTrace_7844463 : CollatzResearch.WordTrace tailWord_7844463 prefixEnd_7844463 1342659998470149078712159 := by
  unfold tailWord_7844463
  simp only [CollatzResearch.WordTrace]
  refine ⟨286111070579857753464346043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190740713719905168976230695 286111070579857753464346043)
  ·
    refine ⟨429166605869786630196519065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286111070579857753464346043 429166605869786630196519065)
    ·
      refine ⟨321874954402339972647389299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429166605869786630196519065 321874954402339972647389299)
      ·
        refine ⟨482812431603509958971083949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321874954402339972647389299 482812431603509958971083949)
        ·
          refine ⟨181054661851316234614156481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482812431603509958971083949 181054661851316234614156481)
          ·
            refine ⟨135790996388487175960617361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181054661851316234614156481 135790996388487175960617361)
            ·
              refine ⟨101843247291365381970463021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135790996388487175960617361 101843247291365381970463021)
              ·
                refine ⟨38191217734262018238923633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101843247291365381970463021 38191217734262018238923633)
                ·
                  refine ⟨28643413300696513679192725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38191217734262018238923633 28643413300696513679192725)
                  ·
                    refine ⟨1342659998470149078712159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28643413300696513679192725 1342659998470149078712159)
                    ·
                      rfl

theorem cell23_7844463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 6].length) (baseStart_7844463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844463 prefixEnd_7844463 := by exact prefixLift 7844463
  have htrace : WordTrace (prefixWord ++ tailWord_7844463) baseStart_7844463 baseEnd_7844463 := by
    simpa [prefixWord, tailWord_7844463, baseEnd_7844463] using wordTrace_append hprefix tailTrace_7844463
  have hstable : (prefixWord ++ tailWord_7844463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844463).length < 2 ^ (prefixWord ++ tailWord_7844463).sum := by decide
  have hdescent : baseEnd_7844463 < baseStart_7844463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844464 : List Nat := [2, 1, 1, 1, 7, 1, 1, 3, 2, 1, 3]
def baseStart_7844464 : Nat := 118140960795 + 7844464 * 2 ^ 59
def prefixEnd_7844464 : Nat := 4983230072969 + 3 ^ 40 * 7844464 * 2
def baseEnd_7844464 : Nat := 4027980508891101732223973

theorem tailTrace_7844464 : CollatzResearch.WordTrace tailWord_7844464 prefixEnd_7844464 4027980508891101732223973 := by
  unfold tailWord_7844464
  simp only [CollatzResearch.WordTrace]
  refine ⟨143055553526427065317566223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190740738035236087090088297 143055553526427065317566223)
  ·
    refine ⟨214583330289640597976349335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143055553526427065317566223 214583330289640597976349335)
    ·
      refine ⟨321874995434460896964524003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214583330289640597976349335 321874995434460896964524003)
      ·
        refine ⟨482812493151691345446786005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321874995434460896964524003 482812493151691345446786005)
        ·
          refine ⟨11315917808242765908909047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 482812493151691345446786005 11315917808242765908909047)
          ·
            refine ⟨16973876712364148863363571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11315917808242765908909047 16973876712364148863363571)
            ·
              refine ⟨25460815068546223295045357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16973876712364148863363571 25460815068546223295045357)
              ·
                refine ⟨9547805650704833735642009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25460815068546223295045357 9547805650704833735642009)
                ·
                  refine ⟨7160854238028625301731507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9547805650704833735642009 7160854238028625301731507)
                  ·
                    refine ⟨10741281357042937952597261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7160854238028625301731507 10741281357042937952597261)
                    ·
                      refine ⟨4027980508891101732223973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10741281357042937952597261 4027980508891101732223973)
                      ·
                        rfl

theorem cell23_7844464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 2, 1, 3].length) (baseStart_7844464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844464 prefixEnd_7844464 := by exact prefixLift 7844464
  have htrace : WordTrace (prefixWord ++ tailWord_7844464) baseStart_7844464 baseEnd_7844464 := by
    simpa [prefixWord, tailWord_7844464, baseEnd_7844464] using wordTrace_append hprefix tailTrace_7844464
  have hstable : (prefixWord ++ tailWord_7844464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844464).length < 2 ^ (prefixWord ++ tailWord_7844464).sum := by decide
  have hdescent : baseEnd_7844464 < baseStart_7844464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844487 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 1, 4, 2]
def baseStart_7844487 : Nat := 118140960795 + 7844487 * 2 ^ 59
def prefixEnd_7844487 : Nat := 4983230072969 + 3 ^ 40 * 7844487 * 2
def baseEnd_7844487 : Nat := 4027992318946155142236367

theorem tailTrace_7844487 : CollatzResearch.WordTrace tailWord_7844487 prefixEnd_7844487 4027992318946155142236367 := by
  unfold tailWord_7844487
  simp only [CollatzResearch.WordTrace]
  refine ⟨286111945931770805563219715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190741297287847203708813143 286111945931770805563219715)
  ·
    refine ⟨429167918897656208344829573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286111945931770805563219715 429167918897656208344829573)
    ·
      refine ⟨80468984793310539064655545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429167918897656208344829573 80468984793310539064655545)
      ·
        refine ⟨60351738594982904298491659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80468984793310539064655545 60351738594982904298491659)
        ·
          refine ⟨90527607892474356447737489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60351738594982904298491659 90527607892474356447737489)
          ·
            refine ⟨67895705919355767335803117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90527607892474356447737489 67895705919355767335803117)
            ·
              refine ⟨25460889719758412750926169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67895705919355767335803117 25460889719758412750926169)
              ·
                refine ⟨19095667289818809563194627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25460889719758412750926169 19095667289818809563194627)
                ·
                  refine ⟨28643500934728214344791941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19095667289818809563194627 28643500934728214344791941)
                  ·
                    refine ⟨5370656425261540189648489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28643500934728214344791941 5370656425261540189648489)
                    ·
                      refine ⟨4027992318946155142236367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5370656425261540189648489 4027992318946155142236367)
                      ·
                        rfl

theorem cell23_7844487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_7844487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844487 prefixEnd_7844487 := by exact prefixLift 7844487
  have htrace : WordTrace (prefixWord ++ tailWord_7844487) baseStart_7844487 baseEnd_7844487 := by
    simpa [prefixWord, tailWord_7844487, baseEnd_7844487] using wordTrace_append hprefix tailTrace_7844487
  have hstable : (prefixWord ++ tailWord_7844487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844487).length < 2 ^ (prefixWord ++ tailWord_7844487).sum := by decide
  have hdescent : baseEnd_7844487 < baseStart_7844487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844540 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 1, 7]
def baseStart_7844540 : Nat := 118140960795 + 7844540 * 2 ^ 59
def prefixEnd_7844540 : Nat := 4983230072969 + 3 ^ 40 * 7844540 * 2
def baseEnd_7844540 : Nat := 1342673177806947811624541

theorem tailTrace_7844540 : CollatzResearch.WordTrace tailWord_7844540 prefixEnd_7844540 1342673177806947811624541 := by
  unfold tailWord_7844540
  simp only [CollatzResearch.WordTrace]
  refine ⟨143056939500289397807449537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190742586000385863743266049 143056939500289397807449537)
  ·
    refine ⟨107292704625217048355587153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143056939500289397807449537 107292704625217048355587153)
    ·
      refine ⟨80469528468912786266690365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107292704625217048355587153 80469528468912786266690365)
      ·
        refine ⟨30176073175842294850008887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80469528468912786266690365 30176073175842294850008887)
        ·
          refine ⟨45264109763763442275013331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30176073175842294850008887 45264109763763442275013331)
          ·
            refine ⟨67896164645645163412519997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45264109763763442275013331 67896164645645163412519997)
            ·
              refine ⟨25461061742116936279694999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67896164645645163412519997 25461061742116936279694999)
              ·
                refine ⟨38191592613175404419542499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25461061742116936279694999 38191592613175404419542499)
                ·
                  refine ⟨57287388919763106629313749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38191592613175404419542499 57287388919763106629313749)
                  ·
                    refine ⟨1342673177806947811624541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57287388919763106629313749 1342673177806947811624541)
                    ·
                      rfl

theorem cell23_7844540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_7844540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844540 prefixEnd_7844540 := by exact prefixLift 7844540
  have htrace : WordTrace (prefixWord ++ tailWord_7844540) baseStart_7844540 baseEnd_7844540 := by
    simpa [prefixWord, tailWord_7844540, baseEnd_7844540] using wordTrace_append hprefix tailTrace_7844540
  have hstable : (prefixWord ++ tailWord_7844540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844540).length < 2 ^ (prefixWord ++ tailWord_7844540).sum := by decide
  have hdescent : baseEnd_7844540 < baseStart_7844540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844553 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 3, 10]
def baseStart_7844553 : Nat := 118140960795 + 7844553 * 2 ^ 59
def prefixEnd_7844553 : Nat := 4983230072969 + 3 ^ 40 * 7844553 * 2
def baseEnd_7844553 : Nat := 1342675402889783961337021

theorem tailTrace_7844553 : CollatzResearch.WordTrace tailWord_7844553 prefixEnd_7844553 1342675402889783961337021 := by
  unfold tailWord_7844553
  simp only [CollatzResearch.WordTrace]
  refine ⟨286114353149531698835122313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190742902099687799223414875 286114353149531698835122313)
  ·
    refine ⟨214585764862148774126341735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286114353149531698835122313 214585764862148774126341735)
    ·
      refine ⟨321878647293223161189512603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214585764862148774126341735 321878647293223161189512603)
      ·
        refine ⟨482817970939834741784268905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321878647293223161189512603 482817970939834741784268905)
        ·
          refine ⟨362113478204876056338201679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482817970939834741784268905 362113478204876056338201679)
          ·
            refine ⟨543170217307314084507302519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362113478204876056338201679 543170217307314084507302519)
            ·
              refine ⟨814755325960971126760953779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543170217307314084507302519 814755325960971126760953779)
              ·
                refine ⟨1222132988941456690141430669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814755325960971126760953779 1222132988941456690141430669)
                ·
                  refine ⟨458299870853046258803036501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1222132988941456690141430669 458299870853046258803036501)
                  ·
                    refine ⟨1342675402889783961337021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 458299870853046258803036501 1342675402889783961337021)
                    ·
                      rfl

theorem cell23_7844553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_7844553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844553 prefixEnd_7844553 := by exact prefixLift 7844553
  have htrace : WordTrace (prefixWord ++ tailWord_7844553) baseStart_7844553 baseEnd_7844553 := by
    simpa [prefixWord, tailWord_7844553, baseEnd_7844553] using wordTrace_append hprefix tailTrace_7844553
  have hstable : (prefixWord ++ tailWord_7844553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844553).length < 2 ^ (prefixWord ++ tailWord_7844553).sum := by decide
  have hdescent : baseEnd_7844553 < baseStart_7844553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844563 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 11]
def baseStart_7844563 : Nat := 118140960795 + 7844563 * 2 ^ 59
def prefixEnd_7844563 : Nat := 4983230072969 + 3 ^ 40 * 7844563 * 2
def baseEnd_7844563 : Nat := 4028031343475896844886017

theorem tailTrace_7844563 : CollatzResearch.WordTrace tailWord_7844563 prefixEnd_7844563 4028031343475896844886017 := by
  unfold tailWord_7844563
  simp only [CollatzResearch.WordTrace]
  refine ⟨286114717879495470542986343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190743145252996980361990895 286114717879495470542986343)
  ·
    refine ⟨429172076819243205814479515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286114717879495470542986343 429172076819243205814479515)
    ·
      refine ⟨643758115228864808721719273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429172076819243205814479515 643758115228864808721719273)
      ·
        refine ⟨482818586421648606541289455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643758115228864808721719273 482818586421648606541289455)
        ·
          refine ⟨724227879632472909811934183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482818586421648606541289455 724227879632472909811934183)
          ·
            refine ⟨1086341819448709364717901275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724227879632472909811934183 1086341819448709364717901275)
            ·
              refine ⟨1629512729173064047076851913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086341819448709364717901275 1629512729173064047076851913)
              ·
                refine ⟨1222134546879798035307638935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629512729173064047076851913 1222134546879798035307638935)
                ·
                  refine ⟨1833201820319697052961458403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1222134546879798035307638935 1833201820319697052961458403)
                  ·
                    refine ⟨2749802730479545579442187605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1833201820319697052961458403 2749802730479545579442187605)
                    ·
                      refine ⟨4028031343475896844886017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2749802730479545579442187605 4028031343475896844886017)
                      ·
                        rfl

theorem cell23_7844563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_7844563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844563 prefixEnd_7844563 := by exact prefixLift 7844563
  have htrace : WordTrace (prefixWord ++ tailWord_7844563) baseStart_7844563 baseEnd_7844563 := by
    simpa [prefixWord, tailWord_7844563, baseEnd_7844563] using wordTrace_append hprefix tailTrace_7844563
  have hstable : (prefixWord ++ tailWord_7844563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844563).length < 2 ^ (prefixWord ++ tailWord_7844563).sum := by decide
  have hdescent : baseEnd_7844563 < baseStart_7844563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844664 : List Nat := [2, 1, 2, 1, 3, 2, 5, 1, 1, 5]
def baseStart_7844664 : Nat := 118140960795 + 7844664 * 2 ^ 59
def prefixEnd_7844664 : Nat := 4983230072969 + 3 ^ 40 * 7844664 * 2
def baseEnd_7844664 : Nat := 1342694401674000316574351

theorem tailTrace_7844664 : CollatzResearch.WordTrace tailWord_7844664 prefixEnd_7844664 1342694401674000316574351 := by
  unfold tailWord_7844664
  simp only [CollatzResearch.WordTrace]
  refine ⟨143059200826064782396206523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190745601101419709861608697 143059200826064782396206523)
  ·
    refine ⟨214588801239097173594309785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143059200826064782396206523 214588801239097173594309785)
    ·
      refine ⟨160941600929322880195732339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214588801239097173594309785 160941600929322880195732339)
      ·
        refine ⟨241412401393984320293598509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160941600929322880195732339 241412401393984320293598509)
        ·
          refine ⟨90529650522744120110099441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241412401393984320293598509 90529650522744120110099441)
          ·
            refine ⟨67897237892058090082574581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90529650522744120110099441 67897237892058090082574581)
            ·
              refine ⟨6365366052380445945241367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67897237892058090082574581 6365366052380445945241367)
              ·
                refine ⟨9548049078570668917862051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6365366052380445945241367 9548049078570668917862051)
                ·
                  refine ⟨14322073617856003376793077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9548049078570668917862051 14322073617856003376793077)
                  ·
                    refine ⟨1342694401674000316574351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14322073617856003376793077 1342694401674000316574351)
                    ·
                      rfl

theorem cell23_7844664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_7844664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844664 prefixEnd_7844664 := by exact prefixLift 7844664
  have htrace : WordTrace (prefixWord ++ tailWord_7844664) baseStart_7844664 baseEnd_7844664 := by
    simpa [prefixWord, tailWord_7844664, baseEnd_7844664] using wordTrace_append hprefix tailTrace_7844664
  have hstable : (prefixWord ++ tailWord_7844664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844664).length < 2 ^ (prefixWord ++ tailWord_7844664).sum := by decide
  have hdescent : baseEnd_7844664 < baseStart_7844664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844697 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 1, 2, 4]
def baseStart_7844697 : Nat := 118140960795 + 7844697 * 2 ^ 59
def prefixEnd_7844697 : Nat := 4983230072969 + 3 ^ 40 * 7844697 * 2
def baseEnd_7844697 : Nat := 4028100149883599320610401

theorem tailTrace_7844697 : CollatzResearch.WordTrace tailWord_7844697 prefixEnd_7844697 4028100149883599320610401 := by
  unfold tailWord_7844697
  simp only [CollatzResearch.WordTrace]
  refine ⟨286119605261010011428364345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190746403507340007618909563 286119605261010011428364345)
  ·
    refine ⟨214589703945757508571273259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286119605261010011428364345 214589703945757508571273259)
    ·
      refine ⟨321884555918636262856909889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214589703945757508571273259 321884555918636262856909889)
      ·
        refine ⟨241413416938977197142682417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321884555918636262856909889 241413416938977197142682417)
        ·
          refine ⟨181060062704232897857011813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241413416938977197142682417 181060062704232897857011813)
          ·
            refine ⟨33948761757043668348189715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181060062704232897857011813 33948761757043668348189715)
            ·
              refine ⟨50923142635565502522284573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33948761757043668348189715 50923142635565502522284573)
              ·
                refine ⟨19096178488337063445856715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50923142635565502522284573 19096178488337063445856715)
                ·
                  refine ⟨28644267732505595168785073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19096178488337063445856715 28644267732505595168785073)
                  ·
                    refine ⟨21483200799379196376588805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28644267732505595168785073 21483200799379196376588805)
                    ·
                      refine ⟨4028100149883599320610401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21483200799379196376588805 4028100149883599320610401)
                      ·
                        rfl

theorem cell23_7844697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_7844697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844697 prefixEnd_7844697 := by exact prefixLift 7844697
  have htrace : WordTrace (prefixWord ++ tailWord_7844697) baseStart_7844697 baseEnd_7844697 := by
    simpa [prefixWord, tailWord_7844697, baseEnd_7844697] using wordTrace_append hprefix tailTrace_7844697
  have hstable : (prefixWord ++ tailWord_7844697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844697).length < 2 ^ (prefixWord ++ tailWord_7844697).sum := by decide
  have hdescent : baseEnd_7844697 < baseStart_7844697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844704 : List Nat := [2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 3]
def baseStart_7844704 : Nat := 118140960795 + 7844704 * 2 ^ 59
def prefixEnd_7844704 : Nat := 4983230072969 + 3 ^ 40 * 7844704 * 2
def baseEnd_7844704 : Nat := 4028103744248180793222869

theorem tailTrace_7844704 : CollatzResearch.WordTrace tailWord_7844704 prefixEnd_7844704 4028103744248180793222869 := by
  unfold tailWord_7844704
  simp only [CollatzResearch.WordTrace]
  refine ⟨143059930285992325811934583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190746573714656434415912777 143059930285992325811934583)
  ·
    refine ⟨214589895428988488717901875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143059930285992325811934583 214589895428988488717901875)
    ·
      refine ⟨321884843143482733076852813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214589895428988488717901875 321884843143482733076852813)
      ·
        refine ⟨120706816178806024903819805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321884843143482733076852813 120706816178806024903819805)
        ·
          refine ⟨45265056067052259338932427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120706816178806024903819805 45265056067052259338932427)
          ·
            refine ⟨67897584100578389008398641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45265056067052259338932427 67897584100578389008398641)
            ·
              refine ⟨50923188075433791756298981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67897584100578389008398641 50923188075433791756298981)
              ·
                refine ⟨9548097764143835954306059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50923188075433791756298981 9548097764143835954306059)
                ·
                  refine ⟨14322146646215753931459089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9548097764143835954306059 14322146646215753931459089)
                  ·
                    refine ⟨10741609984661815448594317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14322146646215753931459089 10741609984661815448594317)
                    ·
                      refine ⟨4028103744248180793222869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10741609984661815448594317 4028103744248180793222869)
                      ·
                        rfl

theorem cell23_7844704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_7844704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844704 prefixEnd_7844704 := by exact prefixLift 7844704
  have htrace : WordTrace (prefixWord ++ tailWord_7844704) baseStart_7844704 baseEnd_7844704 := by
    simpa [prefixWord, tailWord_7844704, baseEnd_7844704] using wordTrace_append hprefix tailTrace_7844704
  have hstable : (prefixWord ++ tailWord_7844704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844704).length < 2 ^ (prefixWord ++ tailWord_7844704).sum := by decide
  have hdescent : baseEnd_7844704 < baseStart_7844704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844721 : List Nat := [1, 2, 2, 2, 1, 4, 4, 1, 1, 2, 3]
def baseStart_7844721 : Nat := 118140960795 + 7844721 * 2 ^ 59
def prefixEnd_7844721 : Nat := 4983230072969 + 3 ^ 40 * 7844721 * 2
def baseEnd_7844721 : Nat := 4028112473419307226710291

theorem tailTrace_7844721 : CollatzResearch.WordTrace tailWord_7844721 prefixEnd_7844721 4028112473419307226710291 := by
  unfold tailWord_7844721
  simp only [CollatzResearch.WordTrace]
  refine ⟨286120480612923063527238017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190746987075282042351492011 286120480612923063527238017)
  ·
    refine ⟨214590360459692297645428513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286120480612923063527238017 214590360459692297645428513)
    ·
      refine ⟨160942770344769223234071385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214590360459692297645428513 160942770344769223234071385)
      ·
        refine ⟨120707077758576917425553539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160942770344769223234071385 120707077758576917425553539)
        ·
          refine ⟨181060616637865376138330309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120707077758576917425553539 181060616637865376138330309)
          ·
            refine ⟨33948865619599758025936933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181060616637865376138330309 33948865619599758025936933)
            ·
              refine ⟨6365412303674954629863175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33948865619599758025936933 6365412303674954629863175)
              ·
                refine ⟨9548118455512431944794763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6365412303674954629863175 9548118455512431944794763)
                ·
                  refine ⟨14322177683268647917192145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9548118455512431944794763 14322177683268647917192145)
                  ·
                    refine ⟨10741633262451485937894109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14322177683268647917192145 10741633262451485937894109)
                    ·
                      refine ⟨4028112473419307226710291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10741633262451485937894109 4028112473419307226710291)
                      ·
                        rfl

theorem cell23_7844721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_7844721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844721 prefixEnd_7844721 := by exact prefixLift 7844721
  have htrace : WordTrace (prefixWord ++ tailWord_7844721) baseStart_7844721 baseEnd_7844721 := by
    simpa [prefixWord, tailWord_7844721, baseEnd_7844721] using wordTrace_append hprefix tailTrace_7844721
  have hstable : (prefixWord ++ tailWord_7844721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844721).length < 2 ^ (prefixWord ++ tailWord_7844721).sum := by decide
  have hdescent : baseEnd_7844721 < baseStart_7844721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844738 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_7844738 : Nat := 118140960795 + 7844738 * 2 ^ 59
def prefixEnd_7844738 : Nat := 4983230072969 + 3 ^ 40 * 7844738 * 2
def baseEnd_7844738 : Nat := 4028121202590433660197713

theorem tailTrace_7844738 : CollatzResearch.WordTrace tailWord_7844738 prefixEnd_7844738 4028121202590433660197713 := by
  unfold tailWord_7844738
  simp only [CollatzResearch.WordTrace]
  refine ⟨71530275163465368857651717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190747400435907650287071245 71530275163465368857651717)
  ·
    refine ⟨13411926593149756660809697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71530275163465368857651717 13411926593149756660809697)
    ·
      refine ⟨10058944944862317495607273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13411926593149756660809697 10058944944862317495607273)
      ·
        refine ⟨7544208708646738121705455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10058944944862317495607273 7544208708646738121705455)
        ·
          refine ⟨11316313062970107182558183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7544208708646738121705455 11316313062970107182558183)
          ·
            refine ⟨16974469594455160773837275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11316313062970107182558183 16974469594455160773837275)
            ·
              refine ⟨25461704391682741160755913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16974469594455160773837275 25461704391682741160755913)
              ·
                refine ⟨19096278293762055870566935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25461704391682741160755913 19096278293762055870566935)
                ·
                  refine ⟨28644417440643083805850403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19096278293762055870566935 28644417440643083805850403)
                  ·
                    refine ⟨42966626160964625708775605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28644417440643083805850403 42966626160964625708775605)
                    ·
                      refine ⟨4028121202590433660197713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42966626160964625708775605 4028121202590433660197713)
                      ·
                        rfl

theorem cell23_7844738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_7844738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844738 prefixEnd_7844738 := by exact prefixLift 7844738
  have htrace : WordTrace (prefixWord ++ tailWord_7844738) baseStart_7844738 baseEnd_7844738 := by
    simpa [prefixWord, tailWord_7844738, baseEnd_7844738] using wordTrace_append hprefix tailTrace_7844738
  have hstable : (prefixWord ++ tailWord_7844738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844738).length < 2 ^ (prefixWord ++ tailWord_7844738).sum := by decide
  have hdescent : baseEnd_7844738 < baseStart_7844738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844758 : List Nat := [5, 3, 1, 1, 1, 1, 4, 7]
def baseStart_7844758 : Nat := 118140960795 + 7844758 * 2 ^ 59
def prefixEnd_7844758 : Nat := 4983230072969 + 3 ^ 40 * 7844758 * 2
def baseEnd_7844758 : Nat := 149190054526056428961023

theorem tailTrace_7844758 : CollatzResearch.WordTrace tailWord_7844758 prefixEnd_7844758 149190054526056428961023 := by
  unfold tailWord_7844758
  simp only [CollatzResearch.WordTrace]
  refine ⟨17882614382111813677895933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190747886742526012564223285 17882614382111813677895933)
  ·
    refine ⟨6705980393291930129210975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17882614382111813677895933 6705980393291930129210975)
    ·
      refine ⟨10058970589937895193816463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6705980393291930129210975 10058970589937895193816463)
      ·
        refine ⟨15088455884906842790724695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10058970589937895193816463 15088455884906842790724695)
        ·
          refine ⟨22632683827360264186087043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15088455884906842790724695 22632683827360264186087043)
          ·
            refine ⟨33949025741040396279130565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22632683827360264186087043 33949025741040396279130565)
            ·
              refine ⟨6365442326445074302336981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33949025741040396279130565 6365442326445074302336981)
              ·
                refine ⟨149190054526056428961023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6365442326445074302336981 149190054526056428961023)
                ·
                  rfl

theorem cell23_7844758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_7844758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844758 prefixEnd_7844758 := by exact prefixLift 7844758
  have htrace : WordTrace (prefixWord ++ tailWord_7844758) baseStart_7844758 baseEnd_7844758 := by
    simpa [prefixWord, tailWord_7844758, baseEnd_7844758] using wordTrace_append hprefix tailTrace_7844758
  have hstable : (prefixWord ++ tailWord_7844758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844758).length < 2 ^ (prefixWord ++ tailWord_7844758).sum := by decide
  have hdescent : baseEnd_7844758 < baseStart_7844758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844777 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 2, 1, 5]
def baseStart_7844777 : Nat := 118140960795 + 7844777 * 2 ^ 59
def prefixEnd_7844777 : Nat := 4983230072969 + 3 ^ 40 * 7844777 * 2
def baseEnd_7844777 : Nat := 4028141228335959007610033

theorem tailTrace_7844777 : CollatzResearch.WordTrace tailWord_7844777 prefixEnd_7844777 4028141228335959007610033 := by
  unfold tailWord_7844777
  simp only [CollatzResearch.WordTrace]
  refine ⟨286122523100720185091276585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190748348733813456727517723 286122523100720185091276585)
  ·
    refine ⟨214591892325540138818457439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286122523100720185091276585 214591892325540138818457439)
    ·
      refine ⟨321887838488310208227686159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214591892325540138818457439 321887838488310208227686159)
      ·
        refine ⟨482831757732465312341529239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321887838488310208227686159 482831757732465312341529239)
        ·
          refine ⟨724247636598697968512293859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482831757732465312341529239 724247636598697968512293859)
          ·
            refine ⟨1086371454898046952768440789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724247636598697968512293859 1086371454898046952768440789)
            ·
              refine ⟨25461830974172975455510331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1086371454898046952768440789 25461830974172975455510331)
              ·
                refine ⟨38192746461259463183265497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25461830974172975455510331 38192746461259463183265497)
                ·
                  refine ⟨28644559845944597387449123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38192746461259463183265497 28644559845944597387449123)
                  ·
                    refine ⟨42966839768916896081173685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28644559845944597387449123 42966839768916896081173685)
                    ·
                      refine ⟨4028141228335959007610033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42966839768916896081173685 4028141228335959007610033)
                      ·
                        rfl

theorem cell23_7844777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_7844777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844777 prefixEnd_7844777 := by exact prefixLift 7844777
  have htrace : WordTrace (prefixWord ++ tailWord_7844777) baseStart_7844777 baseEnd_7844777 := by
    simpa [prefixWord, tailWord_7844777, baseEnd_7844777] using wordTrace_append hprefix tailTrace_7844777
  have hstable : (prefixWord ++ tailWord_7844777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844777).length < 2 ^ (prefixWord ++ tailWord_7844777).sum := by decide
  have hdescent : baseEnd_7844777 < baseStart_7844777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844787 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 4]
def baseStart_7844787 : Nat := 118140960795 + 7844787 * 2 ^ 59
def prefixEnd_7844787 : Nat := 4983230072969 + 3 ^ 40 * 7844787 * 2
def baseEnd_7844787 : Nat := 4028146363142503968484987

theorem tailTrace_7844787 : CollatzResearch.WordTrace tailWord_7844787 prefixEnd_7844787 4028146363142503968484987 := by
  unfold tailWord_7844787
  simp only [CollatzResearch.WordTrace]
  refine ⟨286122887830683956799140615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190748591887122637866093743 286122887830683956799140615)
  ·
    refine ⟨429184331746025935198710923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286122887830683956799140615 429184331746025935198710923)
    ·
      refine ⟨643776497619038902798066385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429184331746025935198710923 643776497619038902798066385)
      ·
        refine ⟨482832373214279177098549789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643776497619038902798066385 482832373214279177098549789)
        ·
          refine ⟨181062139955354691411956171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482832373214279177098549789 181062139955354691411956171)
          ·
            refine ⟨271593209933032037117934257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181062139955354691411956171 271593209933032037117934257)
            ·
              refine ⟨203694907449774027838450693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271593209933032037117934257 203694907449774027838450693)
              ·
                refine ⟨38192795146832630219709505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203694907449774027838450693 38192795146832630219709505)
                ·
                  refine ⟨28644596360124472664782129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38192795146832630219709505 28644596360124472664782129)
                  ·
                    refine ⟨21483447270093354498586597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28644596360124472664782129 21483447270093354498586597)
                    ·
                      refine ⟨4028146363142503968484987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21483447270093354498586597 4028146363142503968484987)
                      ·
                        rfl

theorem cell23_7844787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_7844787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844787 prefixEnd_7844787 := by exact prefixLift 7844787
  have htrace : WordTrace (prefixWord ++ tailWord_7844787) baseStart_7844787 baseEnd_7844787 := by
    simpa [prefixWord, tailWord_7844787, baseEnd_7844787] using wordTrace_append hprefix tailTrace_7844787
  have hstable : (prefixWord ++ tailWord_7844787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844787).length < 2 ^ (prefixWord ++ tailWord_7844787).sum := by decide
  have hdescent : baseEnd_7844787 < baseStart_7844787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844791 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 4, 2, 2]
def baseStart_7844791 : Nat := 118140960795 + 7844791 * 2 ^ 59
def prefixEnd_7844791 : Nat := 4983230072969 + 3 ^ 40 * 7844791 * 2
def baseEnd_7844791 : Nat := 4028148417065121952834969

theorem tailTrace_7844791 : CollatzResearch.WordTrace tailWord_7844791 prefixEnd_7844791 4028148417065121952834969 := by
  unfold tailWord_7844791
  simp only [CollatzResearch.WordTrace]
  refine ⟨286123033722669465482286227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190748689148446310321524151 286123033722669465482286227)
  ·
    refine ⟨429184550584004198223429341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286123033722669465482286227 429184550584004198223429341)
    ·
      refine ⟨160944206469001574333786003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429184550584004198223429341 160944206469001574333786003)
      ·
        refine ⟨241416309703502361500679005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160944206469001574333786003 241416309703502361500679005)
        ·
          refine ⟨90531116138813385562754627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241416309703502361500679005 90531116138813385562754627)
          ·
            refine ⟨135796674208220078344131941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90531116138813385562754627 135796674208220078344131941)
            ·
              refine ⟨25461876414041264689524739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135796674208220078344131941 25461876414041264689524739)
              ·
                refine ⟨38192814621061897034287109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25461876414041264689524739 38192814621061897034287109)
                ·
                  refine ⟨7161152741449105693928833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38192814621061897034287109 7161152741449105693928833)
                  ·
                    refine ⟨5370864556086829270446625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7161152741449105693928833 5370864556086829270446625)
                    ·
                      refine ⟨4028148417065121952834969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5370864556086829270446625 4028148417065121952834969)
                      ·
                        rfl

theorem cell23_7844791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 2, 2].length) (baseStart_7844791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844791 prefixEnd_7844791 := by exact prefixLift 7844791
  have htrace : WordTrace (prefixWord ++ tailWord_7844791) baseStart_7844791 baseEnd_7844791 := by
    simpa [prefixWord, tailWord_7844791, baseEnd_7844791] using wordTrace_append hprefix tailTrace_7844791
  have hstable : (prefixWord ++ tailWord_7844791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844791).length < 2 ^ (prefixWord ++ tailWord_7844791).sum := by decide
  have hdescent : baseEnd_7844791 < baseStart_7844791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844806 : List Nat := [6, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_7844806 : Nat := 118140960795 + 7844806 * 2 ^ 59
def prefixEnd_7844806 : Nat := 4983230072969 + 3 ^ 40 * 7844806 * 2
def baseEnd_7844806 : Nat := 4028156119274939394147401

theorem tailTrace_7844806 : CollatzResearch.WordTrace tailWord_7844806 prefixEnd_7844806 4028156119274939394147401 := by
  unfold tailWord_7844806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8941361900550472595127571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190749053878410082029388181 8941361900550472595127571)
  ·
    refine ⟨13412042850825708892691357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8941361900550472595127571 13412042850825708892691357)
    ·
      refine ⟨5029516069059640834759259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13412042850825708892691357 5029516069059640834759259)
      ·
        refine ⟨7544274103589461252138889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5029516069059640834759259 7544274103589461252138889)
        ·
          refine ⟨5658205577692095939104167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7544274103589461252138889 5658205577692095939104167)
          ·
            refine ⟨8487308366538143908656251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5658205577692095939104167 8487308366538143908656251)
            ·
              refine ⟨12730962549807215862984377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8487308366538143908656251 12730962549807215862984377)
              ·
                refine ⟨9548221912355411897238283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12730962549807215862984377 9548221912355411897238283)
                ·
                  refine ⟨14322332868533117845857425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9548221912355411897238283 14322332868533117845857425)
                  ·
                    refine ⟨10741749651399838384393069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14322332868533117845857425 10741749651399838384393069)
                    ·
                      refine ⟨4028156119274939394147401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10741749651399838384393069 4028156119274939394147401)
                      ·
                        rfl

theorem cell23_7844806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_7844806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844806 prefixEnd_7844806 := by exact prefixLift 7844806
  have htrace : WordTrace (prefixWord ++ tailWord_7844806) baseStart_7844806 baseEnd_7844806 := by
    simpa [prefixWord, tailWord_7844806, baseEnd_7844806] using wordTrace_append hprefix tailTrace_7844806
  have hstable : (prefixWord ++ tailWord_7844806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844806).length < 2 ^ (prefixWord ++ tailWord_7844806).sum := by decide
  have hdescent : baseEnd_7844806 < baseStart_7844806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844882 : List Nat := [3, 2, 5, 1, 1, 1, 2, 3, 5]
def baseStart_7844882 : Nat := 118140960795 + 7844882 * 2 ^ 59
def prefixEnd_7844882 : Nat := 4983230072969 + 3 ^ 40 * 7844882 * 2
def baseEnd_7844882 : Nat := 447577238200520121866339

theorem tailTrace_7844882 : CollatzResearch.WordTrace tailWord_7844882 prefixEnd_7844882 447577238200520121866339 := by
  unfold tailWord_7844882
  simp only [CollatzResearch.WordTrace]
  refine ⟨71531588191334947005962225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190750901843559858682565933 71531588191334947005962225)
  ·
    refine ⟨53648691143501210254471669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71531588191334947005962225 53648691143501210254471669)
    ·
      refine ⟨5029564794703238461356719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53648691143501210254471669 5029564794703238461356719)
      ·
        refine ⟨7544347192054857692035079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5029564794703238461356719 7544347192054857692035079)
        ·
          refine ⟨11316520788082286538052619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7544347192054857692035079 11316520788082286538052619)
          ·
            refine ⟨16974781182123429807078929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11316520788082286538052619 16974781182123429807078929)
            ·
              refine ⟨12731085886592572355309197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16974781182123429807078929 12731085886592572355309197)
              ·
                refine ⟨4774157207472214633240949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12731085886592572355309197 4774157207472214633240949)
                ·
                  refine ⟨447577238200520121866339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4774157207472214633240949 447577238200520121866339)
                  ·
                    rfl

theorem cell23_7844882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_7844882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844882 prefixEnd_7844882 := by exact prefixLift 7844882
  have htrace : WordTrace (prefixWord ++ tailWord_7844882) baseStart_7844882 baseEnd_7844882 := by
    simpa [prefixWord, tailWord_7844882, baseEnd_7844882] using wordTrace_append hprefix tailTrace_7844882
  have hstable : (prefixWord ++ tailWord_7844882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844882).length < 2 ^ (prefixWord ++ tailWord_7844882).sum := by decide
  have hdescent : baseEnd_7844882 < baseStart_7844882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844907 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 8]
def baseStart_7844907 : Nat := 118140960795 + 7844907 * 2 ^ 59
def prefixEnd_7844907 : Nat := 4983230072969 + 3 ^ 40 * 7844907 * 2
def baseEnd_7844907 : Nat := 4028207980821043498984435

theorem tailTrace_7844907 : CollatzResearch.WordTrace tailWord_7844907 prefixEnd_7844907 4028207980821043498984435 := by
  unfold tailWord_7844907
  simp only [CollatzResearch.WordTrace]
  refine ⟨286127264590249217293508975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190751509726832811529005983 286127264590249217293508975)
  ·
    refine ⟨429190896885373825940263463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286127264590249217293508975 429190896885373825940263463)
    ·
      refine ⟨643786345328060738910395195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429190896885373825940263463 643786345328060738910395195)
      ·
        refine ⟨965679517992091108365592793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643786345328060738910395195 965679517992091108365592793)
        ·
          refine ⟨724259638494068331274194595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965679517992091108365592793 724259638494068331274194595)
          ·
            refine ⟨1086389457741102496911291893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724259638494068331274194595 1086389457741102496911291893)
            ·
              refine ⟨101849011663228359085433615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1086389457741102496911291893 101849011663228359085433615)
              ·
                refine ⟨152773517494842538628150423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101849011663228359085433615 152773517494842538628150423)
                ·
                  refine ⟨229160276242263807942225635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152773517494842538628150423 229160276242263807942225635)
                  ·
                    refine ⟨343740414363395711913338453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 229160276242263807942225635 343740414363395711913338453)
                    ·
                      refine ⟨4028207980821043498984435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 343740414363395711913338453 4028207980821043498984435)
                      ·
                        rfl

theorem cell23_7844907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 8].length) (baseStart_7844907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844907 prefixEnd_7844907 := by exact prefixLift 7844907
  have htrace : WordTrace (prefixWord ++ tailWord_7844907) baseStart_7844907 baseEnd_7844907 := by
    simpa [prefixWord, tailWord_7844907, baseEnd_7844907] using wordTrace_append hprefix tailTrace_7844907
  have hstable : (prefixWord ++ tailWord_7844907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844907).length < 2 ^ (prefixWord ++ tailWord_7844907).sum := by decide
  have hdescent : baseEnd_7844907 < baseStart_7844907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844931 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 3, 1, 3]
def baseStart_7844931 : Nat := 118140960795 + 7844931 * 2 ^ 59
def prefixEnd_7844931 : Nat := 4983230072969 + 3 ^ 40 * 7844931 * 2
def baseEnd_7844931 : Nat := 4028220304356751405084325

theorem tailTrace_7844931 : CollatzResearch.WordTrace tailWord_7844931 prefixEnd_7844931 4028220304356751405084325 := by
  unfold tailWord_7844931
  simp only [CollatzResearch.WordTrace]
  refine ⟨286128139942162269392382647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190752093294774846261588431 286128139942162269392382647)
  ·
    refine ⟨429192209913243404088573971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286128139942162269392382647 429192209913243404088573971)
    ·
      refine ⟨643788314869865106132860957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429192209913243404088573971 643788314869865106132860957)
      ·
        refine ⟨241420618076199414799822859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 643788314869865106132860957 241420618076199414799822859)
        ·
          refine ⟨362130927114299122199734289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241420618076199414799822859 362130927114299122199734289)
          ·
            refine ⟨271598195335724341649800717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362130927114299122199734289 271598195335724341649800717)
            ·
              refine ⟨101849323250896628118675269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271598195335724341649800717 101849323250896628118675269)
              ·
                refine ⟨19096748109543117772251613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101849323250896628118675269 19096748109543117772251613)
                ·
                  refine ⟨7161280541078669164594355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19096748109543117772251613 7161280541078669164594355)
                  ·
                    refine ⟨10741920811618003746891533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7161280541078669164594355 10741920811618003746891533)
                    ·
                      refine ⟨4028220304356751405084325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10741920811618003746891533 4028220304356751405084325)
                      ·
                        rfl

theorem cell23_7844931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_7844931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844931 prefixEnd_7844931 := by exact prefixLift 7844931
  have htrace : WordTrace (prefixWord ++ tailWord_7844931) baseStart_7844931 baseEnd_7844931 := by
    simpa [prefixWord, tailWord_7844931, baseEnd_7844931] using wordTrace_append hprefix tailTrace_7844931
  have hstable : (prefixWord ++ tailWord_7844931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844931).length < 2 ^ (prefixWord ++ tailWord_7844931).sum := by decide
  have hdescent : baseEnd_7844931 < baseStart_7844931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844984 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_7844984 : Nat := 118140960795 + 7844984 * 2 ^ 59
def prefixEnd_7844984 : Nat := 4983230072969 + 3 ^ 40 * 7844984 * 2
def baseEnd_7844984 : Nat := 4028247518831439697721581

theorem tailTrace_7844984 : CollatzResearch.WordTrace tailWord_7844984 prefixEnd_7844984 4028247518831439697721581 := by
  unfold tailWord_7844984
  simp only [CollatzResearch.WordTrace]
  refine ⟨143065036505485129722031003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190753382007313506296041337 143065036505485129722031003)
  ·
    refine ⟨214597554758227694583046505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143065036505485129722031003 214597554758227694583046505)
    ·
      refine ⟨160948166068670770937284879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214597554758227694583046505 160948166068670770937284879)
      ·
        refine ⟨241422249103006156405927319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160948166068670770937284879 241422249103006156405927319)
        ·
          refine ⟨362133373654509234608890979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241422249103006156405927319 362133373654509234608890979)
          ·
            refine ⟨543200060481763851913336469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362133373654509234608890979 543200060481763851913336469)
            ·
              refine ⟨25462502835082680558437647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 543200060481763851913336469 25462502835082680558437647)
              ·
                refine ⟨38193754252624020837656471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25462502835082680558437647 38193754252624020837656471)
                ·
                  refine ⟨57290631378936031256484707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38193754252624020837656471 57290631378936031256484707)
                  ·
                    refine ⟨85935947068404046884727061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57290631378936031256484707 85935947068404046884727061)
                    ·
                      refine ⟨4028247518831439697721581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85935947068404046884727061 4028247518831439697721581)
                      ·
                        rfl

theorem cell23_7844984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_7844984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844984 prefixEnd_7844984 := by exact prefixLift 7844984
  have htrace : WordTrace (prefixWord ++ tailWord_7844984) baseStart_7844984 baseEnd_7844984 := by
    simpa [prefixWord, tailWord_7844984, baseEnd_7844984] using wordTrace_append hprefix tailTrace_7844984
  have hstable : (prefixWord ++ tailWord_7844984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844984).length < 2 ^ (prefixWord ++ tailWord_7844984).sum := by decide
  have hdescent : baseEnd_7844984 < baseStart_7844984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844985 : List Nat := [1, 2, 1, 3, 6, 1, 1, 2, 1, 5]
def baseStart_7844985 : Nat := 118140960795 + 7844985 * 2 ^ 59
def prefixEnd_7844985 : Nat := 4983230072969 + 3 ^ 40 * 7844985 * 2
def baseEnd_7844985 : Nat := 1342749344104031397936359

theorem tailTrace_7844985 : CollatzResearch.WordTrace tailWord_7844985 prefixEnd_7844985 1342749344104031397936359 := by
  unfold tailWord_7844985
  simp only [CollatzResearch.WordTrace]
  refine ⟨286130109483966636614848409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190753406322644424409898939 286130109483966636614848409)
  ·
    refine ⟨214597582112974977461136307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286130109483966636614848409 214597582112974977461136307)
    ·
      refine ⟨321896373169462466191704461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214597582112974977461136307 321896373169462466191704461)
      ·
        refine ⟨120711139938548424821889173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321896373169462466191704461 120711139938548424821889173)
        ·
          refine ⟨5658334684619457413526055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120711139938548424821889173 5658334684619457413526055)
          ·
            refine ⟨8487502026929186120289083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5658334684619457413526055 8487502026929186120289083)
            ·
              refine ⟨12731253040393779180433625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8487502026929186120289083 12731253040393779180433625)
              ·
                refine ⟨9548439780295334385325219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12731253040393779180433625 9548439780295334385325219)
                ·
                  refine ⟨14322659670443001577987829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9548439780295334385325219 14322659670443001577987829)
                  ·
                    refine ⟨1342749344104031397936359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14322659670443001577987829 1342749344104031397936359)
                    ·
                      rfl

theorem cell23_7844985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 1, 5].length) (baseStart_7844985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844985 prefixEnd_7844985 := by exact prefixLift 7844985
  have htrace : WordTrace (prefixWord ++ tailWord_7844985) baseStart_7844985 baseEnd_7844985 := by
    simpa [prefixWord, tailWord_7844985, baseEnd_7844985] using wordTrace_append hprefix tailTrace_7844985
  have hstable : (prefixWord ++ tailWord_7844985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844985).length < 2 ^ (prefixWord ++ tailWord_7844985).sum := by decide
  have hdescent : baseEnd_7844985 < baseStart_7844985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7844988 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 5, 2, 2]
def baseStart_7844988 : Nat := 118140960795 + 7844988 * 2 ^ 59
def prefixEnd_7844988 : Nat := 4983230072969 + 3 ^ 40 * 7844988 * 2
def baseEnd_7844988 : Nat := 4028249572754057682071563

theorem tailTrace_7844988 : CollatzResearch.WordTrace tailWord_7844988 prefixEnd_7844988 4028249572754057682071563 := by
  unfold tailWord_7844988
  simp only [CollatzResearch.WordTrace]
  refine ⟨143065109451477884063603809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190753479268637178751471745 143065109451477884063603809)
  ·
    refine ⟨107298832088608413047702857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143065109451477884063603809 107298832088608413047702857)
    ·
      refine ⟨80474124066456309785777143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107298832088608413047702857 80474124066456309785777143)
      ·
        refine ⟨120711186099684464678665715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80474124066456309785777143 120711186099684464678665715)
        ·
          refine ⟨181066779149526697017998573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120711186099684464678665715 181066779149526697017998573)
          ·
            refine ⟨67900042181072511381749465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181066779149526697017998573 67900042181072511381749465)
            ·
              refine ⟨50925031635804383536312099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67900042181072511381749465 50925031635804383536312099)
              ·
                refine ⟨76387547453706575304468149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50925031635804383536312099 76387547453706575304468149)
                ·
                  refine ⟨7161332573784991434793889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76387547453706575304468149 7161332573784991434793889)
                  ·
                    refine ⟨5370999430338743576095417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7161332573784991434793889 5370999430338743576095417)
                    ·
                      refine ⟨4028249572754057682071563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5370999430338743576095417 4028249572754057682071563)
                      ·
                        rfl

theorem cell23_7844988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_7844988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7844988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7844988 prefixEnd_7844988 := by exact prefixLift 7844988
  have htrace : WordTrace (prefixWord ++ tailWord_7844988) baseStart_7844988 baseEnd_7844988 := by
    simpa [prefixWord, tailWord_7844988, baseEnd_7844988] using wordTrace_append hprefix tailTrace_7844988
  have hstable : (prefixWord ++ tailWord_7844988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7844988).length < 2 ^ (prefixWord ++ tailWord_7844988).sum := by decide
  have hdescent : baseEnd_7844988 < baseStart_7844988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7844988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845001 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 1, 2, 4]
def baseStart_7845001 : Nat := 118140960795 + 7845001 * 2 ^ 59
def prefixEnd_7845001 : Nat := 4983230072969 + 3 ^ 40 * 7845001 * 2
def baseEnd_7845001 : Nat := 4028256248002566131209003

theorem tailTrace_7845001 : CollatzResearch.WordTrace tailWord_7845001 prefixEnd_7845001 4028256248002566131209003 := by
  unfold tailWord_7845001
  simp only [CollatzResearch.WordTrace]
  refine ⟨286130693051908671347430857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190753795367939114231620571 286130693051908671347430857)
  ·
    refine ⟨214598019788931503510573143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286130693051908671347430857 214598019788931503510573143)
    ·
      refine ⟨321897029683397255265859715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214598019788931503510573143 321897029683397255265859715)
      ·
        refine ⟨482845544525095882898789573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321897029683397255265859715 482845544525095882898789573)
        ·
          refine ⟨90533539598455478043523045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 482845544525095882898789573 90533539598455478043523045)
          ·
            refine ⟨16975038674710402133160571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90533539598455478043523045 16975038674710402133160571)
            ·
              refine ⟨25462558012065603199740857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16975038674710402133160571 25462558012065603199740857)
              ·
                refine ⟨19096918509049202399805643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25462558012065603199740857 19096918509049202399805643)
                ·
                  refine ⟨28645377763573803599708465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19096918509049202399805643 28645377763573803599708465)
                  ·
                    refine ⟨21484033322680352699781349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28645377763573803599708465 21484033322680352699781349)
                    ·
                      refine ⟨4028256248002566131209003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21484033322680352699781349 4028256248002566131209003)
                      ·
                        rfl

theorem cell23_7845001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 2, 4].length) (baseStart_7845001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845001 prefixEnd_7845001 := by exact prefixLift 7845001
  have htrace : WordTrace (prefixWord ++ tailWord_7845001) baseStart_7845001 baseEnd_7845001 := by
    simpa [prefixWord, tailWord_7845001, baseEnd_7845001] using wordTrace_append hprefix tailTrace_7845001
  have hstable : (prefixWord ++ tailWord_7845001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845001).length < 2 ^ (prefixWord ++ tailWord_7845001).sum := by decide
  have hdescent : baseEnd_7845001 < baseStart_7845001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845021 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_7845021 : Nat := 118140960795 + 7845021 * 2 ^ 59
def prefixEnd_7845021 : Nat := 4983230072969 + 3 ^ 40 * 7845021 * 2
def baseEnd_7845021 : Nat := 4028266517615656052958911

theorem tailTrace_7845021 : CollatzResearch.WordTrace tailWord_7845021 prefixEnd_7845021 4028266517615656052958911 := by
  unfold tailWord_7845021
  simp only [CollatzResearch.WordTrace]
  refine ⟨286131422511836214763158917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190754281674557476508772611 286131422511836214763158917)
  ·
    refine ⟨53649641720969290268092297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286131422511836214763158917 53649641720969290268092297)
    ·
      refine ⟨40237231290726967701069223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53649641720969290268092297 40237231290726967701069223)
      ·
        refine ⟨60355846936090451551603835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40237231290726967701069223 60355846936090451551603835)
        ·
          refine ⟨90533770404135677327405753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60355846936090451551603835 90533770404135677327405753)
          ·
            refine ⟨67900327803101757995554315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90533770404135677327405753 67900327803101757995554315)
            ·
              refine ⟨101850491704652636993331473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67900327803101757995554315 101850491704652636993331473)
              ·
                refine ⟨76387868778489477744998605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101850491704652636993331473 76387868778489477744998605)
                ·
                  refine ⟨28645450791933554154374477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76387868778489477744998605 28645450791933554154374477)
                  ·
                    refine ⟨10742044046975082807890429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28645450791933554154374477 10742044046975082807890429)
                    ·
                      refine ⟨4028266517615656052958911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10742044046975082807890429 4028266517615656052958911)
                      ·
                        rfl

theorem cell23_7845021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_7845021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845021 prefixEnd_7845021 := by exact prefixLift 7845021
  have htrace : WordTrace (prefixWord ++ tailWord_7845021) baseStart_7845021 baseEnd_7845021 := by
    simpa [prefixWord, tailWord_7845021, baseEnd_7845021] using wordTrace_append hprefix tailTrace_7845021
  have hstable : (prefixWord ++ tailWord_7845021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845021).length < 2 ^ (prefixWord ++ tailWord_7845021).sum := by decide
  have hdescent : baseEnd_7845021 < baseStart_7845021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845024 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 1, 9]
def baseStart_7845024 : Nat := 118140960795 + 7845024 * 2 ^ 59
def prefixEnd_7845024 : Nat := 4983230072969 + 3 ^ 40 * 7845024 * 2
def baseEnd_7845024 : Nat := 1342756019352539847073799

theorem tailTrace_7845024 : CollatzResearch.WordTrace tailWord_7845024 prefixEnd_7845024 1342756019352539847073799 := by
  unfold tailWord_7845024
  simp only [CollatzResearch.WordTrace]
  refine ⟨143065765965412673137759063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190754354620550230850345417 143065765965412673137759063)
  ·
    refine ⟨214598648948119009706638595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143065765965412673137759063 214598648948119009706638595)
    ·
      refine ⟨321897973422178514559957893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214598648948119009706638595 321897973422178514559957893)
      ·
        refine ⟨60355870016658471479992105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321897973422178514559957893 60355870016658471479992105)
        ·
          refine ⟨45266902512493853609994079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60355870016658471479992105 45266902512493853609994079)
          ·
            refine ⟨67900353768740780414991119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45266902512493853609994079 67900353768740780414991119)
            ·
              refine ⟨101850530653111170622486679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67900353768740780414991119 101850530653111170622486679)
              ·
                refine ⟨152775795979666755933730019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101850530653111170622486679 152775795979666755933730019)
                ·
                  refine ⟨229163693969500133900595029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152775795979666755933730019 229163693969500133900595029)
                  ·
                    refine ⟨1342756019352539847073799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 229163693969500133900595029 1342756019352539847073799)
                    ·
                      rfl

theorem cell23_7845024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_7845024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845024 prefixEnd_7845024 := by exact prefixLift 7845024
  have htrace : WordTrace (prefixWord ++ tailWord_7845024) baseStart_7845024 baseEnd_7845024 := by
    simpa [prefixWord, tailWord_7845024, baseEnd_7845024] using wordTrace_append hprefix tailTrace_7845024
  have hstable : (prefixWord ++ tailWord_7845024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845024).length < 2 ^ (prefixWord ++ tailWord_7845024).sum := by decide
  have hdescent : baseEnd_7845024 < baseStart_7845024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845131 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 4, 5]
def baseStart_7845131 : Nat := 118140960795 + 7845131 * 2 ^ 59
def prefixEnd_7845131 : Nat := 4983230072969 + 3 ^ 40 * 7845131 * 2
def baseEnd_7845131 : Nat := 1342774333495883540861135

theorem tailTrace_7845131 : CollatzResearch.WordTrace tailWord_7845131 prefixEnd_7845131 1342774333495883540861135 := by
  unfold tailWord_7845131
  simp only [CollatzResearch.WordTrace]
  refine ⟨286135434541437703549663247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190756956360958469033108831 286135434541437703549663247)
  ·
    refine ⟨429203151812156555324494871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286135434541437703549663247 429203151812156555324494871)
    ·
      refine ⟨643804727718234832986742307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429203151812156555324494871 643804727718234832986742307)
      ·
        refine ⟨965707091577352249480113461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643804727718234832986742307 965707091577352249480113461)
        ·
          refine ⟨90535039835376773388760637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 965707091577352249480113461 90535039835376773388760637)
          ·
            refine ⟨33950639938266290020785239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90535039835376773388760637 33950639938266290020785239)
            ·
              refine ⟨50925959907399435031177859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33950639938266290020785239 50925959907399435031177859)
              ·
                refine ⟨76388939861099152546766789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50925959907399435031177859 76388939861099152546766789)
                ·
                  refine ⟨14322926223956091102518773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76388939861099152546766789 14322926223956091102518773)
                  ·
                    refine ⟨1342774333495883540861135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14322926223956091102518773 1342774333495883540861135)
                    ·
                      rfl

theorem cell23_7845131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 5].length) (baseStart_7845131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845131 prefixEnd_7845131 := by exact prefixLift 7845131
  have htrace : WordTrace (prefixWord ++ tailWord_7845131) baseStart_7845131 baseEnd_7845131 := by
    simpa [prefixWord, tailWord_7845131, baseEnd_7845131] using wordTrace_append hprefix tailTrace_7845131
  have hstable : (prefixWord ++ tailWord_7845131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845131).length < 2 ^ (prefixWord ++ tailWord_7845131).sum := by decide
  have hdescent : baseEnd_7845131 < baseStart_7845131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845165 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_7845165 : Nat := 118140960795 + 7845165 * 2 ^ 59
def prefixEnd_7845165 : Nat := 4983230072969 + 3 ^ 40 * 7845165 * 2
def baseEnd_7845165 : Nat := 1342780152943301163186083

theorem tailTrace_7845165 : CollatzResearch.WordTrace tailWord_7845165 prefixEnd_7845165 1342780152943301163186083 := by
  unfold tailWord_7845165
  simp only [CollatzResearch.WordTrace]
  refine ⟨286136674623314527356400949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190757783082209684904267299 286136674623314527356400949)
  ·
    refine ⟨26825313245935736939662589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286136674623314527356400949 26825313245935736939662589)
    ·
      refine ⟨10059492467225901352373471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26825313245935736939662589 10059492467225901352373471)
      ·
        refine ⟨15089238700838852028560207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10059492467225901352373471 15089238700838852028560207)
        ·
          refine ⟨22633858051258278042840311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15089238700838852028560207 22633858051258278042840311)
          ·
            refine ⟨33950787076887417064260467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22633858051258278042840311 33950787076887417064260467)
            ·
              refine ⟨50926180615331125596390701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33950787076887417064260467 50926180615331125596390701)
              ·
                refine ⟨19097317730749172098646513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50926180615331125596390701 19097317730749172098646513)
                ·
                  refine ⟨14322988298061879073984885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19097317730749172098646513 14322988298061879073984885)
                  ·
                    refine ⟨1342780152943301163186083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14322988298061879073984885 1342780152943301163186083)
                    ·
                      rfl

theorem cell23_7845165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_7845165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845165 prefixEnd_7845165 := by exact prefixLift 7845165
  have htrace : WordTrace (prefixWord ++ tailWord_7845165) baseStart_7845165 baseEnd_7845165 := by
    simpa [prefixWord, tailWord_7845165, baseEnd_7845165] using wordTrace_append hprefix tailTrace_7845165
  have hstable : (prefixWord ++ tailWord_7845165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845165).length < 2 ^ (prefixWord ++ tailWord_7845165).sum := by decide
  have hdescent : baseEnd_7845165 < baseStart_7845165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845168 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 4]
def baseStart_7845168 : Nat := 118140960795 + 7845168 * 2 ^ 59
def prefixEnd_7845168 : Nat := 4983230072969 + 3 ^ 40 * 7845168 * 2
def baseEnd_7845168 : Nat := 4028341999271866977820735

theorem tailTrace_7845168 : CollatzResearch.WordTrace tailWord_7845168 prefixEnd_7845168 4028341999271866977820735 := by
  unfold tailWord_7845168
  simp only [CollatzResearch.WordTrace]
  refine ⟨143068392021151829434380079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190757856028202439245840105 143068392021151829434380079)
  ·
    refine ⟨214602588031727744151570119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143068392021151829434380079 214602588031727744151570119)
    ·
      refine ⟨321903882047591616227355179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214602588031727744151570119 321903882047591616227355179)
      ·
        refine ⟨482855823071387424341032769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321903882047591616227355179 482855823071387424341032769)
        ·
          refine ⟨362141867303540568255774577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482855823071387424341032769 362141867303540568255774577)
          ·
            refine ⟨271606400477655426191830933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362141867303540568255774577 271606400477655426191830933)
            ·
              refine ⟨12731550022390098102742075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 271606400477655426191830933 12731550022390098102742075)
              ·
                refine ⟨19097325033585147154113113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12731550022390098102742075 19097325033585147154113113)
                ·
                  refine ⟨14322993775188860365584835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19097325033585147154113113 14322993775188860365584835)
                  ·
                    refine ⟨21484490662783290548377253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14322993775188860365584835 21484490662783290548377253)
                    ·
                      refine ⟨4028341999271866977820735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21484490662783290548377253 4028341999271866977820735)
                      ·
                        rfl

theorem cell23_7845168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 4].length) (baseStart_7845168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845168 prefixEnd_7845168 := by exact prefixLift 7845168
  have htrace : WordTrace (prefixWord ++ tailWord_7845168) baseStart_7845168 baseEnd_7845168 := by
    simpa [prefixWord, tailWord_7845168, baseEnd_7845168] using wordTrace_append hprefix tailTrace_7845168
  have hstable : (prefixWord ++ tailWord_7845168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845168).length < 2 ^ (prefixWord ++ tailWord_7845168).sum := by decide
  have hdescent : baseEnd_7845168 < baseStart_7845168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845185 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_7845185 : Nat := 118140960795 + 7845185 * 2 ^ 59
def prefixEnd_7845185 : Nat := 4983230072969 + 3 ^ 40 * 7845185 * 2
def baseEnd_7845185 : Nat := 4028350728442993411308157

theorem tailTrace_7845185 : CollatzResearch.WordTrace tailWord_7845185 prefixEnd_7845185 4028350728442993411308157 := by
  unfold tailWord_7845185
  simp only [CollatzResearch.WordTrace]
  refine ⟨286137404083242070772129009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190758269388828047181419339 286137404083242070772129009)
  ·
    refine ⟨214603053062431553079096757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286137404083242070772129009 214603053062431553079096757)
    ·
      refine ⟨20119036224602958101165321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214603053062431553079096757 20119036224602958101165321)
      ·
        refine ⟨15089277168452218575873991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20119036224602958101165321 15089277168452218575873991)
        ·
          refine ⟨22633915752678327863810987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15089277168452218575873991 22633915752678327863810987)
          ·
            refine ⟨33950873629017491795716481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22633915752678327863810987 33950873629017491795716481)
            ·
              refine ⟨25463155221763118846787361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33950873629017491795716481 25463155221763118846787361)
              ·
                refine ⟨19097366416322339135090521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25463155221763118846787361 19097366416322339135090521)
                ·
                  refine ⟨14323024812241754351317891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19097366416322339135090521 14323024812241754351317891)
                  ·
                    refine ⟨21484537218362631526976837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14323024812241754351317891 21484537218362631526976837)
                    ·
                      refine ⟨4028350728442993411308157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21484537218362631526976837 4028350728442993411308157)
                      ·
                        rfl

theorem cell23_7845185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_7845185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845185 prefixEnd_7845185 := by exact prefixLift 7845185
  have htrace : WordTrace (prefixWord ++ tailWord_7845185) baseStart_7845185 baseEnd_7845185 := by
    simpa [prefixWord, tailWord_7845185, baseEnd_7845185] using wordTrace_append hprefix tailTrace_7845185
  have hstable : (prefixWord ++ tailWord_7845185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845185).length < 2 ^ (prefixWord ++ tailWord_7845185).sum := by decide
  have hdescent : baseEnd_7845185 < baseStart_7845185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845245 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 4, 3, 2]
def baseStart_7845245 : Nat := 118140960795 + 7845245 * 2 ^ 59
def prefixEnd_7845245 : Nat := 4983230072969 + 3 ^ 40 * 7845245 * 2
def baseEnd_7845245 : Nat := 4028381537282263176557881

theorem tailTrace_7845245 : CollatzResearch.WordTrace tailWord_7845245 prefixEnd_7845245 4028381537282263176557881 := by
  unfold tailWord_7845245
  simp only [CollatzResearch.WordTrace]
  refine ⟨286139592463024701019313189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190759728308683134012875459 286139592463024701019313189)
  ·
    refine ⟨53651173586817131441121223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286139592463024701019313189 53651173586817131441121223)
    ·
      refine ⟨80476760380225697161681835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53651173586817131441121223 80476760380225697161681835)
      ·
        refine ⟨120715140570338545742522753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80476760380225697161681835 120715140570338545742522753)
        ·
          refine ⟨90536355427753909306892065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120715140570338545742522753 90536355427753909306892065)
          ·
            refine ⟨67902266570815431980169049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90536355427753909306892065 67902266570815431980169049)
            ·
              refine ⟨50926699928111573985126787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67902266570815431980169049 50926699928111573985126787)
              ·
                refine ⟨76390049892167360977690181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50926699928111573985126787 76390049892167360977690181)
                ·
                  refine ⟨14323134354781380183316909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76390049892167360977690181 14323134354781380183316909)
                  ·
                    refine ⟨5371175383043017568743841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14323134354781380183316909 5371175383043017568743841)
                    ·
                      refine ⟨4028381537282263176557881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5371175383043017568743841 4028381537282263176557881)
                      ·
                        rfl

theorem cell23_7845245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_7845245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845245 prefixEnd_7845245 := by exact prefixLift 7845245
  have htrace : WordTrace (prefixWord ++ tailWord_7845245) baseStart_7845245 baseEnd_7845245 := by
    simpa [prefixWord, tailWord_7845245, baseEnd_7845245] using wordTrace_append hprefix tailTrace_7845245
  have hstable : (prefixWord ++ tailWord_7845245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845245).length < 2 ^ (prefixWord ++ tailWord_7845245).sum := by decide
  have hdescent : baseEnd_7845245 < baseStart_7845245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845252 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_7845252 : Nat := 118140960795 + 7845252 * 2 ^ 59
def prefixEnd_7845252 : Nat := 4983230072969 + 3 ^ 40 * 7845252 * 2
def baseEnd_7845252 : Nat := 4028385131646844649170349

theorem tailTrace_7845252 : CollatzResearch.WordTrace tailWord_7845252 prefixEnd_7845252 4028385131646844649170349 := by
  unfold tailWord_7845252
  simp only [CollatzResearch.WordTrace]
  refine ⟨143069923886999670607409005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190759898515999560809878673 143069923886999670607409005)
  ·
    refine ⟨53651221457624876477778377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143069923886999670607409005 53651221457624876477778377)
    ·
      refine ⟨40238416093218657358333783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53651221457624876477778377 40238416093218657358333783)
      ·
        refine ⟨60357624139827986037500675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40238416093218657358333783 60357624139827986037500675)
        ·
          refine ⟨90536436209741979056251013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60357624139827986037500675 90536436209741979056251013)
          ·
            refine ⟨16975581789326621073047065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90536436209741979056251013 16975581789326621073047065)
            ·
              refine ⟨12731686341994965804785299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16975581789326621073047065 12731686341994965804785299)
              ·
                refine ⟨19097529512992448707177949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12731686341994965804785299 19097529512992448707177949)
                ·
                  refine ⟨7161573567372168265191731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19097529512992448707177949 7161573567372168265191731)
                  ·
                    refine ⟨10742360351058252397787597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7161573567372168265191731 10742360351058252397787597)
                    ·
                      refine ⟨4028385131646844649170349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10742360351058252397787597 4028385131646844649170349)
                      ·
                        rfl

theorem cell23_7845252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_7845252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845252 prefixEnd_7845252 := by exact prefixLift 7845252
  have htrace : WordTrace (prefixWord ++ tailWord_7845252) baseStart_7845252 baseEnd_7845252 := by
    simpa [prefixWord, tailWord_7845252, baseEnd_7845252] using wordTrace_append hprefix tailTrace_7845252
  have hstable : (prefixWord ++ tailWord_7845252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845252).length < 2 ^ (prefixWord ++ tailWord_7845252).sum := by decide
  have hdescent : baseEnd_7845252 < baseStart_7845252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845272 : List Nat := [2, 1, 2, 5, 2, 1, 2, 2, 1, 5]
def baseStart_7845272 : Nat := 118140960795 + 7845272 * 2 ^ 59
def prefixEnd_7845272 : Nat := 4983230072969 + 3 ^ 40 * 7845272 * 2
def baseEnd_7845272 : Nat := 1342798467086644856973419

theorem tailTrace_7845272 : CollatzResearch.WordTrace tailWord_7845272 prefixEnd_7845272 1342798467086644856973419 := by
  unfold tailWord_7845272
  simp only [CollatzResearch.WordTrace]
  refine ⟨143070288616963442315273035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190760384822617923087030713 143070288616963442315273035)
  ·
    refine ⟨214605432925445163472909553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143070288616963442315273035 214605432925445163472909553)
    ·
      refine ⟨160954074694083872604682165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214605432925445163472909553 160954074694083872604682165)
      ·
        refine ⟨15089444502570363056688953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160954074694083872604682165 15089444502570363056688953)
        ·
          refine ⟨11317083376927772292516715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15089444502570363056688953 11317083376927772292516715)
          ·
            refine ⟨16975625065391658438775073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11317083376927772292516715 16975625065391658438775073)
            ·
              refine ⟨12731718799043743829081305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16975625065391658438775073 12731718799043743829081305)
              ·
                refine ⟨9548789099282807871810979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12731718799043743829081305 9548789099282807871810979)
                ·
                  refine ⟨14323183648924211807716469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9548789099282807871810979 14323183648924211807716469)
                  ·
                    refine ⟨1342798467086644856973419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14323183648924211807716469 1342798467086644856973419)
                    ·
                      rfl

theorem cell23_7845272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_7845272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845272 prefixEnd_7845272 := by exact prefixLift 7845272
  have htrace : WordTrace (prefixWord ++ tailWord_7845272) baseStart_7845272 baseEnd_7845272 := by
    simpa [prefixWord, tailWord_7845272, baseEnd_7845272] using wordTrace_append hprefix tailTrace_7845272
  have hstable : (prefixWord ++ tailWord_7845272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845272).length < 2 ^ (prefixWord ++ tailWord_7845272).sum := by decide
  have hdescent : baseEnd_7845272 < baseStart_7845272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845291 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 7]
def baseStart_7845291 : Nat := 118140960795 + 7845291 * 2 ^ 59
def prefixEnd_7845291 : Nat := 4983230072969 + 3 ^ 40 * 7845291 * 2
def baseEnd_7845291 : Nat := 4028405157392369996582669

theorem tailTrace_7845291 : CollatzResearch.WordTrace tailWord_7845291 prefixEnd_7845291 4028405157392369996582669 := by
  unfold tailWord_7845291
  simp only [CollatzResearch.WordTrace]
  refine ⟨286141270220858050875487727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190760846813905367250325151 286141270220858050875487727)
  ·
    refine ⟨429211905331287076313231591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286141270220858050875487727 429211905331287076313231591)
    ·
      refine ⟨643817857996930614469847387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429211905331287076313231591 643817857996930614469847387)
      ·
        refine ⟨965726786995395921704771081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643817857996930614469847387 965726786995395921704771081)
        ·
          refine ⟨724295090246546941278578311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965726786995395921704771081 724295090246546941278578311)
          ·
            refine ⟨1086442635369820411917867467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724295090246546941278578311 1086442635369820411917867467)
            ·
              refine ⟨1629663953054730617876801201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086442635369820411917867467 1629663953054730617876801201)
              ·
                refine ⟨1222247964791047963407600901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629663953054730617876801201 1222247964791047963407600901)
                ·
                  refine ⟨229171493398321493138925169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1222247964791047963407600901 229171493398321493138925169)
                  ·
                    refine ⟨171878620048741119854193877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 229171493398321493138925169 171878620048741119854193877)
                    ·
                      refine ⟨4028405157392369996582669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171878620048741119854193877 4028405157392369996582669)
                      ·
                        rfl

theorem cell23_7845291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_7845291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845291 prefixEnd_7845291 := by exact prefixLift 7845291
  have htrace : WordTrace (prefixWord ++ tailWord_7845291) baseStart_7845291 baseEnd_7845291 := by
    simpa [prefixWord, tailWord_7845291, baseEnd_7845291] using wordTrace_append hprefix tailTrace_7845291
  have hstable : (prefixWord ++ tailWord_7845291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845291).length < 2 ^ (prefixWord ++ tailWord_7845291).sum := by decide
  have hdescent : baseEnd_7845291 < baseStart_7845291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845348 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_7845348 : Nat := 118140960795 + 7845348 * 2 ^ 59
def prefixEnd_7845348 : Nat := 4983230072969 + 3 ^ 40 * 7845348 * 2
def baseEnd_7845348 : Nat := 4028434425789676273569907

theorem tailTrace_7845348 : CollatzResearch.WordTrace tailWord_7845348 prefixEnd_7845348 4028434425789676273569907 := by
  unfold tailWord_7845348
  simp only [CollatzResearch.WordTrace]
  refine ⟨143071674590825774805156349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190762232787767699740208465 143071674590825774805156349)
  ·
    refine ⟨53651877971559665551933631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143071674590825774805156349 53651877971559665551933631)
    ·
      refine ⟨80477816957339498327900447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53651877971559665551933631 80477816957339498327900447)
      ·
        refine ⟨120716725436009247491850671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80477816957339498327900447 120716725436009247491850671)
        ·
          refine ⟨181075088154013871237776007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120716725436009247491850671 181075088154013871237776007)
          ·
            refine ⟨271612632231020806856664011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181075088154013871237776007 271612632231020806856664011)
            ·
              refine ⟨407418948346531210284996017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271612632231020806856664011 407418948346531210284996017)
              ·
                refine ⟨305564211259898407713747013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407418948346531210284996017 305564211259898407713747013)
                ·
                  refine ⟨57293289611230951446327565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305564211259898407713747013 57293289611230951446327565)
                  ·
                    refine ⟨21484983604211606792372837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57293289611230951446327565 21484983604211606792372837)
                    ·
                      refine ⟨4028434425789676273569907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21484983604211606792372837 4028434425789676273569907)
                      ·
                        rfl

theorem cell23_7845348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_7845348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845348 prefixEnd_7845348 := by exact prefixLift 7845348
  have htrace : WordTrace (prefixWord ++ tailWord_7845348) baseStart_7845348 baseEnd_7845348 := by
    simpa [prefixWord, tailWord_7845348, baseEnd_7845348] using wordTrace_append hprefix tailTrace_7845348
  have hstable : (prefixWord ++ tailWord_7845348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845348).length < 2 ^ (prefixWord ++ tailWord_7845348).sum := by decide
  have hdescent : baseEnd_7845348 < baseStart_7845348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845416 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_7845416 : Nat := 118140960795 + 7845416 * 2 ^ 59
def prefixEnd_7845416 : Nat := 4983230072969 + 3 ^ 40 * 7845416 * 2
def baseEnd_7845416 : Nat := 4028469342474182007519595

theorem tailTrace_7845416 : CollatzResearch.WordTrace tailWord_7845416 prefixEnd_7845416 4028469342474182007519595 := by
  unfold tailWord_7845416
  simp only [CollatzResearch.WordTrace]
  refine ⟨143072914672702598611894051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190763886230270131482525401 143072914672702598611894051)
  ·
    refine ⟨214609372009053897917841077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143072914672702598611894051 214609372009053897917841077)
    ·
      refine ⟨20119628625848802929797601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214609372009053897917841077 20119628625848802929797601)
      ·
        refine ⟨15089721469386602197348201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20119628625848802929797601 15089721469386602197348201)
        ·
          refine ⟨11317291102039951648011151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15089721469386602197348201 11317291102039951648011151)
          ·
            refine ⟨16975936653059927472016727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11317291102039951648011151 16975936653059927472016727)
            ·
              refine ⟨25463904979589891208025091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16975936653059927472016727 25463904979589891208025091)
              ·
                refine ⟨38195857469384836812037637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25463904979589891208025091 38195857469384836812037637)
                ·
                  refine ⟨7161723275509656902257057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38195857469384836812037637 7161723275509656902257057)
                  ·
                    refine ⟨5371292456632242676692793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7161723275509656902257057 5371292456632242676692793)
                    ·
                      refine ⟨4028469342474182007519595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5371292456632242676692793 4028469342474182007519595)
                      ·
                        rfl

theorem cell23_7845416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_7845416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845416 prefixEnd_7845416 := by exact prefixLift 7845416
  have htrace : WordTrace (prefixWord ++ tailWord_7845416) baseStart_7845416 baseEnd_7845416 := by
    simpa [prefixWord, tailWord_7845416, baseEnd_7845416] using wordTrace_append hprefix tailTrace_7845416
  have hstable : (prefixWord ++ tailWord_7845416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845416).length < 2 ^ (prefixWord ++ tailWord_7845416).sum := by decide
  have hdescent : baseEnd_7845416 < baseStart_7845416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845422 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 7]
def baseStart_7845422 : Nat := 118140960795 + 7845422 * 2 ^ 59
def prefixEnd_7845422 : Nat := 4983230072969 + 3 ^ 40 * 7845422 * 2
def baseEnd_7845422 : Nat := 447608047039789887116063

theorem tailTrace_7845422 : CollatzResearch.WordTrace tailWord_7845422 prefixEnd_7845422 447608047039789887116063 := by
  unfold tailWord_7845422
  simp only [CollatzResearch.WordTrace]
  refine ⟨35768256022922932531063315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190764032122255640165671013 35768256022922932531063315)
  ·
    refine ⟨53652384034384398796594973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35768256022922932531063315 53652384034384398796594973)
    ·
      refine ⟨20119644012894149548723115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53652384034384398796594973 20119644012894149548723115)
      ·
        refine ⟨30179466019341224323084673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20119644012894149548723115 30179466019341224323084673)
        ·
          refine ⟨22634599514505918242313505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30179466019341224323084673 22634599514505918242313505)
          ·
            refine ⟨16975949635879438681735129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22634599514505918242313505 16975949635879438681735129)
            ·
              refine ⟨12731962226909579011301347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16975949635879438681735129 12731962226909579011301347)
              ·
                refine ⟨19097943340364368516952021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12731962226909579011301347 19097943340364368516952021)
                ·
                  refine ⟨447608047039789887116063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19097943340364368516952021 447608047039789887116063)
                  ·
                    rfl

theorem cell23_7845422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_7845422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845422 prefixEnd_7845422 := by exact prefixLift 7845422
  have htrace : WordTrace (prefixWord ++ tailWord_7845422) baseStart_7845422 baseEnd_7845422 := by
    simpa [prefixWord, tailWord_7845422, baseEnd_7845422] using wordTrace_append hprefix tailTrace_7845422
  have hstable : (prefixWord ++ tailWord_7845422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845422).length < 2 ^ (prefixWord ++ tailWord_7845422).sum := by decide
  have hdescent : baseEnd_7845422 < baseStart_7845422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845455 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 4]
def baseStart_7845455 : Nat := 118140960795 + 7845455 * 2 ^ 59
def prefixEnd_7845455 : Nat := 4983230072969 + 3 ^ 40 * 7845455 * 2
def baseEnd_7845455 : Nat := 4028489368219707354931915

theorem tailTrace_7845455 : CollatzResearch.WordTrace tailWord_7845455 prefixEnd_7845455 4028489368219707354931915 := by
  unfold tailWord_7845455
  simp only [CollatzResearch.WordTrace]
  refine ⟨286147251792263906884457819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190764834528175937922971879 286147251792263906884457819)
  ·
    refine ⟨429220877688395860326686729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286147251792263906884457819 429220877688395860326686729)
    ·
      refine ⟨321915658266296895245015047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429220877688395860326686729 321915658266296895245015047)
      ·
        refine ⟨482873487399445342867522571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321915658266296895245015047 482873487399445342867522571)
        ·
          refine ⟨724310231099168014301283857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482873487399445342867522571 724310231099168014301283857)
          ·
            refine ⟨543232673324376010725962893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724310231099168014301283857 543232673324376010725962893)
            ·
              refine ⟨203712252496641004022236085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 543232673324376010725962893 203712252496641004022236085)
              ·
                refine ⟨19098023671560094127084633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203712252496641004022236085 19098023671560094127084633)
                ·
                  refine ⟨14323517753670070595313475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19098023671560094127084633 14323517753670070595313475)
                  ·
                    refine ⟨21485276630505105892970213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14323517753670070595313475 21485276630505105892970213)
                    ·
                      refine ⟨4028489368219707354931915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21485276630505105892970213 4028489368219707354931915)
                      ·
                        rfl

theorem cell23_7845455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_7845455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845455 prefixEnd_7845455 := by exact prefixLift 7845455
  have htrace : WordTrace (prefixWord ++ tailWord_7845455) baseStart_7845455 baseEnd_7845455 := by
    simpa [prefixWord, tailWord_7845455, baseEnd_7845455] using wordTrace_append hprefix tailTrace_7845455
  have hstable : (prefixWord ++ tailWord_7845455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845455).length < 2 ^ (prefixWord ++ tailWord_7845455).sum := by decide
  have hdescent : baseEnd_7845455 < baseStart_7845455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845465 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 5, 4]
def baseStart_7845465 : Nat := 118140960795 + 7845465 * 2 ^ 59
def prefixEnd_7845465 : Nat := 4983230072969 + 3 ^ 40 * 7845465 * 2
def baseEnd_7845465 : Nat := 1342831501008750771935623

theorem tailTrace_7845465 : CollatzResearch.WordTrace tailWord_7845465 prefixEnd_7845465 1342831501008750771935623 := by
  unfold tailWord_7845465
  simp only [CollatzResearch.WordTrace]
  refine ⟨286147616522227678592321849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190765077681485119061547899 286147616522227678592321849)
  ·
    refine ⟨214610712391670758944241387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286147616522227678592321849 214610712391670758944241387)
    ·
      refine ⟨321916068587506138416362081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214610712391670758944241387 321916068587506138416362081)
      ·
        refine ⟨241437051440629603812271561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321916068587506138416362081 241437051440629603812271561)
        ·
          refine ⟨181077788580472202859203671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241437051440629603812271561 181077788580472202859203671)
          ·
            refine ⟨271616682870708304288805507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181077788580472202859203671 271616682870708304288805507)
            ·
              refine ⟨407425024306062456433208261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271616682870708304288805507 407425024306062456433208261)
              ·
                refine ⟨76392192057386710581226549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407425024306062456433208261 76392192057386710581226549)
                ·
                  refine ⟨7161768005380004116989989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76392192057386710581226549 7161768005380004116989989)
                  ·
                    refine ⟨1342831501008750771935623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7161768005380004116989989 1342831501008750771935623)
                    ·
                      rfl

theorem cell23_7845465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 4].length) (baseStart_7845465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845465 prefixEnd_7845465 := by exact prefixLift 7845465
  have htrace : WordTrace (prefixWord ++ tailWord_7845465) baseStart_7845465 baseEnd_7845465 := by
    simpa [prefixWord, tailWord_7845465, baseEnd_7845465] using wordTrace_append hprefix tailTrace_7845465
  have hstable : (prefixWord ++ tailWord_7845465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845465).length < 2 ^ (prefixWord ++ tailWord_7845465).sum := by decide
  have hdescent : baseEnd_7845465 < baseStart_7845465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845549 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_7845549 : Nat := 118140960795 + 7845549 * 2 ^ 59
def prefixEnd_7845549 : Nat := 4983230072969 + 3 ^ 40 * 7845549 * 2
def baseEnd_7845549 : Nat := 4028537635401229987156483

theorem tailTrace_7845549 : CollatzResearch.WordTrace tailWord_7845549 prefixEnd_7845549 4028537635401229987156483 := by
  unfold tailWord_7845549
  simp only [CollatzResearch.WordTrace]
  refine ⟨286150680253923360938379701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190767120169282240625586467 286150680253923360938379701)
  ·
    refine ⟨26826626273805315087973097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286150680253923360938379701 26826626273805315087973097)
    ·
      refine ⟨20119969705353986315979823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26826626273805315087973097 20119969705353986315979823)
      ·
        refine ⟨30179954558030979473969735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20119969705353986315979823 30179954558030979473969735)
        ·
          refine ⟨45269931837046469210954603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30179954558030979473969735 45269931837046469210954603)
          ·
            refine ⟨67904897755569703816431905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45269931837046469210954603 67904897755569703816431905)
            ·
              refine ⟨50928673316677277862323929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67904897755569703816431905 50928673316677277862323929)
              ·
                refine ⟨38196504987507958396742947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50928673316677277862323929 38196504987507958396742947)
                ·
                  refine ⟨57294757481261937595114421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38196504987507958396742947 57294757481261937595114421)
                  ·
                    refine ⟨5371383513868306649541977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57294757481261937595114421 5371383513868306649541977)
                    ·
                      refine ⟨4028537635401229987156483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5371383513868306649541977 4028537635401229987156483)
                      ·
                        rfl

theorem cell23_7845549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_7845549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845549 prefixEnd_7845549 := by exact prefixLift 7845549
  have htrace : WordTrace (prefixWord ++ tailWord_7845549) baseStart_7845549 baseEnd_7845549 := by
    simpa [prefixWord, tailWord_7845549, baseEnd_7845549] using wordTrace_append hprefix tailTrace_7845549
  have hstable : (prefixWord ++ tailWord_7845549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845549).length < 2 ^ (prefixWord ++ tailWord_7845549).sum := by decide
  have hdescent : baseEnd_7845549 < baseStart_7845549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845562 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4]
def baseStart_7845562 : Nat := 118140960795 + 7845562 * 2 ^ 59
def prefixEnd_7845562 : Nat := 4983230072969 + 3 ^ 40 * 7845562 * 2
def baseEnd_7845562 : Nat := 4028544310649738436293923

theorem tailTrace_7845562 : CollatzResearch.WordTrace tailWord_7845562 prefixEnd_7845562 4028544310649738436293923 := by
  unfold tailWord_7845562
  simp only [CollatzResearch.WordTrace]
  refine ⟨71537788600719066039650735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190767436268584176105735293 71537788600719066039650735)
  ·
    refine ⟨107306682901078599059476103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71537788600719066039650735 107306682901078599059476103)
    ·
      refine ⟨160960024351617898589214155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107306682901078599059476103 160960024351617898589214155)
      ·
        refine ⟨241440036527426847883821233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160960024351617898589214155 241440036527426847883821233)
        ·
          refine ⟨181080027395570135912865925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241440036527426847883821233 181080027395570135912865925)
          ·
            refine ⟨33952505136669400483662361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181080027395570135912865925 33952505136669400483662361)
            ·
              refine ⟨25464378852502050362746771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33952505136669400483662361 25464378852502050362746771)
              ·
                refine ⟨38196568278753075544120157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25464378852502050362746771 38196568278753075544120157)
                ·
                  refine ⟨14323713104532403329045059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38196568278753075544120157 14323713104532403329045059)
                  ·
                    refine ⟨21485569656798604993567589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14323713104532403329045059 21485569656798604993567589)
                    ·
                      refine ⟨4028544310649738436293923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21485569656798604993567589 4028544310649738436293923)
                      ·
                        rfl

theorem cell23_7845562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_7845562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845562 prefixEnd_7845562 := by exact prefixLift 7845562
  have htrace : WordTrace (prefixWord ++ tailWord_7845562) baseStart_7845562 baseEnd_7845562 := by
    simpa [prefixWord, tailWord_7845562, baseEnd_7845562] using wordTrace_append hprefix tailTrace_7845562
  have hstable : (prefixWord ++ tailWord_7845562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845562).length < 2 ^ (prefixWord ++ tailWord_7845562).sum := by decide
  have hdescent : baseEnd_7845562 < baseStart_7845562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845566 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_7845566 : Nat := 118140960795 + 7845566 * 2 ^ 59
def prefixEnd_7845566 : Nat := 4983230072969 + 3 ^ 40 * 7845566 * 2
def baseEnd_7845566 : Nat := 4028546364572356420643905

theorem tailTrace_7845566 : CollatzResearch.WordTrace tailWord_7845566 prefixEnd_7845566 4028546364572356420643905 := by
  unfold tailWord_7845566
  simp only [CollatzResearch.WordTrace]
  refine ⟨35768912536857721605218569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190767533529907848561165701 35768912536857721605218569)
  ·
    refine ⟨26826684402643291203913927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35768912536857721605218569 26826684402643291203913927)
    ·
      refine ⟨40240026603964936805870891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26826684402643291203913927 40240026603964936805870891)
      ·
        refine ⟨60360039905947405208806337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40240026603964936805870891 60360039905947405208806337)
        ·
          refine ⟨45270029929460553906604753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60360039905947405208806337 45270029929460553906604753)
          ·
            refine ⟨33952522447095415429953565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45270029929460553906604753 33952522447095415429953565)
            ·
              refine ⟨12732195917660780786232587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33952522447095415429953565 12732195917660780786232587)
              ·
                refine ⟨19098293876491171179348881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12732195917660780786232587 19098293876491171179348881)
                ·
                  refine ⟨14323720407368378384511661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19098293876491171179348881 14323720407368378384511661)
                  ·
                    refine ⟨5371395152763141894191873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14323720407368378384511661 5371395152763141894191873)
                    ·
                      refine ⟨4028546364572356420643905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5371395152763141894191873 4028546364572356420643905)
                      ·
                        rfl

theorem cell23_7845566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_7845566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845566 prefixEnd_7845566 := by exact prefixLift 7845566
  have htrace : WordTrace (prefixWord ++ tailWord_7845566) baseStart_7845566 baseEnd_7845566 := by
    simpa [prefixWord, tailWord_7845566, baseEnd_7845566] using wordTrace_append hprefix tailTrace_7845566
  have hstable : (prefixWord ++ tailWord_7845566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845566).length < 2 ^ (prefixWord ++ tailWord_7845566).sum := by decide
  have hdescent : baseEnd_7845566 < baseStart_7845566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845572 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_7845572 : Nat := 118140960795 + 7845572 * 2 ^ 59
def prefixEnd_7845572 : Nat := 4983230072969 + 3 ^ 40 * 7845572 * 2
def baseEnd_7845572 : Nat := 1342849815152094465722959

theorem tailTrace_7845572 : CollatzResearch.WordTrace tailWord_7845572 prefixEnd_7845572 1342849815152094465722959 := by
  unfold tailWord_7845572
  simp only [CollatzResearch.WordTrace]
  refine ⟨143075759566420017933233485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190767679421893357244311313 143075759566420017933233485)
  ·
    refine ⟨53653409837407506724962557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143075759566420017933233485 53653409837407506724962557)
    ·
      refine ⟨20120028689027815021860959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53653409837407506724962557 20120028689027815021860959)
      ·
        refine ⟨30180043033541722532791439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20120028689027815021860959 30180043033541722532791439)
        ·
          refine ⟨45270064550312583799187159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30180043033541722532791439 45270064550312583799187159)
          ·
            refine ⟨67905096825468875698780739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45270064550312583799187159 67905096825468875698780739)
            ·
              refine ⟨101857645238203313548171109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67905096825468875698780739 101857645238203313548171109)
              ·
                refine ⟨19098308482163121290282083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101857645238203313548171109 19098308482163121290282083)
                ·
                  refine ⟨28647462723244681935423125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19098308482163121290282083 28647462723244681935423125)
                  ·
                    refine ⟨1342849815152094465722959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28647462723244681935423125 1342849815152094465722959)
                    ·
                      rfl

theorem cell23_7845572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_7845572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845572 prefixEnd_7845572 := by exact prefixLift 7845572
  have htrace : WordTrace (prefixWord ++ tailWord_7845572) baseStart_7845572 baseEnd_7845572 := by
    simpa [prefixWord, tailWord_7845572, baseEnd_7845572] using wordTrace_append hprefix tailTrace_7845572
  have hstable : (prefixWord ++ tailWord_7845572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845572).length < 2 ^ (prefixWord ++ tailWord_7845572).sum := by decide
  have hdescent : baseEnd_7845572 < baseStart_7845572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845582 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_7845582 : Nat := 118140960795 + 7845582 * 2 ^ 59
def prefixEnd_7845582 : Nat := 4983230072969 + 3 ^ 40 * 7845582 * 2
def baseEnd_7845582 : Nat := 4028554580262828358043831

theorem tailTrace_7845582 : CollatzResearch.WordTrace tailWord_7845582 prefixEnd_7845582 4028554580262828358043831 := by
  unfold tailWord_7845582
  simp only [CollatzResearch.WordTrace]
  refine ⟨35768985482850475946791375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190767922575202538382887333 35768985482850475946791375)
  ·
    refine ⟨53653478224275713920187063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35768985482850475946791375 53653478224275713920187063)
    ·
      refine ⟨80480217336413570880280595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53653478224275713920187063 80480217336413570880280595)
      ·
        refine ⟨120720326004620356320420893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80480217336413570880280595 120720326004620356320420893)
        ·
          refine ⟨45270122251732633620157835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120720326004620356320420893 45270122251732633620157835)
          ·
            refine ⟨67905183377598950430236753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45270122251732633620157835 67905183377598950430236753)
            ·
              refine ⟨50928887533199212822677565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67905183377598950430236753 50928887533199212822677565)
              ·
                refine ⟨19098332824949704808504087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50928887533199212822677565 19098332824949704808504087)
                ·
                  refine ⟨28647499237424557212756131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19098332824949704808504087 28647499237424557212756131)
                  ·
                    refine ⟨42971248856136835819134197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28647499237424557212756131 42971248856136835819134197)
                    ·
                      refine ⟨4028554580262828358043831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42971248856136835819134197 4028554580262828358043831)
                      ·
                        rfl

theorem cell23_7845582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_7845582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845582 prefixEnd_7845582 := by exact prefixLift 7845582
  have htrace : WordTrace (prefixWord ++ tailWord_7845582) baseStart_7845582 baseEnd_7845582 := by
    simpa [prefixWord, tailWord_7845582, baseEnd_7845582] using wordTrace_append hprefix tailTrace_7845582
  have hstable : (prefixWord ++ tailWord_7845582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845582).length < 2 ^ (prefixWord ++ tailWord_7845582).sum := by decide
  have hdescent : baseEnd_7845582 < baseStart_7845582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845585 : List Nat := [1, 2, 2, 1, 2, 5, 10]
def baseStart_7845585 : Nat := 118140960795 + 7845585 * 2 ^ 59
def prefixEnd_7845585 : Nat := 4983230072969 + 3 ^ 40 * 7845585 * 2
def baseEnd_7845585 : Nat := 49735260749441874645757

theorem tailTrace_7845585 : CollatzResearch.WordTrace tailWord_7845585 prefixEnd_7845585 49735260749441874645757 := by
  unfold tailWord_7845585
  simp only [CollatzResearch.WordTrace]
  refine ⟨286151993281792939086690209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190767995521195292724460139 286151993281792939086690209)
  ·
    refine ⟨214613994961344704315017657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286151993281792939086690209 214613994961344704315017657)
    ·
      refine ⟨160960496221008528236263243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214613994961344704315017657 160960496221008528236263243)
      ·
        refine ⟨241440744331512792354394865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160960496221008528236263243 241440744331512792354394865)
        ·
          refine ⟨181080558248634594265796149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241440744331512792354394865 181080558248634594265796149)
          ·
            refine ⟨16976302335809493212418389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181080558248634594265796149 16976302335809493212418389)
            ·
              refine ⟨49735260749441874645757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16976302335809493212418389 49735260749441874645757)
              ·
                rfl

theorem cell23_7845585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 10].length) (baseStart_7845585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845585 prefixEnd_7845585 := by exact prefixLift 7845585
  have htrace : WordTrace (prefixWord ++ tailWord_7845585) baseStart_7845585 baseEnd_7845585 := by
    simpa [prefixWord, tailWord_7845585, baseEnd_7845585] using wordTrace_append hprefix tailTrace_7845585
  have hstable : (prefixWord ++ tailWord_7845585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845585).length < 2 ^ (prefixWord ++ tailWord_7845585).sum := by decide
  have hdescent : baseEnd_7845585 < baseStart_7845585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845590 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_7845590 : Nat := 118140960795 + 7845590 * 2 ^ 59
def prefixEnd_7845590 : Nat := 4983230072969 + 3 ^ 40 * 7845590 * 2
def baseEnd_7845590 : Nat := 4028558688108064326743795

theorem tailTrace_7845590 : CollatzResearch.WordTrace tailWord_7845590 prefixEnd_7845590 4028558688108064326743795 := by
  unfold tailWord_7845590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17884510977923426558788889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190768117097849883293748149 17884510977923426558788889)
  ·
    refine ⟨13413383233442569919091667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17884510977923426558788889 13413383233442569919091667)
    ·
      refine ⟨20120074850163854878637501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13413383233442569919091667 20120074850163854878637501)
      ·
        refine ⟨7545028068811445579489063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20120074850163854878637501 7545028068811445579489063)
        ·
          refine ⟨11317542103217168369233595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7545028068811445579489063 11317542103217168369233595)
          ·
            refine ⟨16976313154825752553850393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11317542103217168369233595 16976313154825752553850393)
            ·
              refine ⟨12732234866119314415387795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16976313154825752553850393 12732234866119314415387795)
              ·
                refine ⟨19098352299178971623081693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12732234866119314415387795 19098352299178971623081693)
                ·
                  refine ⟨7161882112192114358655635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19098352299178971623081693 7161882112192114358655635)
                  ·
                    refine ⟨10742823168288171537983453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7161882112192114358655635 10742823168288171537983453)
                    ·
                      refine ⟨4028558688108064326743795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10742823168288171537983453 4028558688108064326743795)
                      ·
                        rfl

theorem cell23_7845590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_7845590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845590 prefixEnd_7845590 := by exact prefixLift 7845590
  have htrace : WordTrace (prefixWord ++ tailWord_7845590) baseStart_7845590 baseEnd_7845590 := by
    simpa [prefixWord, tailWord_7845590, baseEnd_7845590] using wordTrace_append hprefix tailTrace_7845590
  have hstable : (prefixWord ++ tailWord_7845590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845590).length < 2 ^ (prefixWord ++ tailWord_7845590).sum := by decide
  have hdescent : baseEnd_7845590 < baseStart_7845590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845722 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 1, 7]
def baseStart_7845722 : Nat := 118140960795 + 7845722 * 2 ^ 59
def prefixEnd_7845722 : Nat := 4983230072969 + 3 ^ 40 * 7845722 * 2
def baseEnd_7845722 : Nat := 1342875489184819270097729

theorem tailTrace_7845722 : CollatzResearch.WordTrace tailWord_7845722 prefixEnd_7845722 1342875489184819270097729 := by
  unfold tailWord_7845722
  simp only [CollatzResearch.WordTrace]
  refine ⟨71539247520574152871106855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190771326721531074322951613 71539247520574152871106855)
  ·
    refine ⟨107308871280861229306660283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71539247520574152871106855 107308871280861229306660283)
    ·
      refine ⟨160963306921291843959990425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107308871280861229306660283 160963306921291843959990425)
      ·
        refine ⟨120722480190968882969992819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160963306921291843959990425 120722480190968882969992819)
        ·
          refine ⟨181083720286453324454989229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120722480190968882969992819 181083720286453324454989229)
          ·
            refine ⟨67906395107419996670620961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181083720286453324454989229 67906395107419996670620961)
            ·
              refine ⟨50929796330564997502965721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67906395107419996670620961 50929796330564997502965721)
              ·
                refine ⟨38197347247923748127224291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50929796330564997502965721 38197347247923748127224291)
                ·
                  refine ⟨57296020871885622190836437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38197347247923748127224291 57296020871885622190836437)
                  ·
                    refine ⟨1342875489184819270097729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57296020871885622190836437 1342875489184819270097729)
                    ·
                      rfl

theorem cell23_7845722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_7845722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845722 prefixEnd_7845722 := by exact prefixLift 7845722
  have htrace : WordTrace (prefixWord ++ tailWord_7845722) baseStart_7845722 baseEnd_7845722 := by
    simpa [prefixWord, tailWord_7845722, baseEnd_7845722] using wordTrace_append hprefix tailTrace_7845722
  have hstable : (prefixWord ++ tailWord_7845722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845722).length < 2 ^ (prefixWord ++ tailWord_7845722).sum := by decide
  have hdescent : baseEnd_7845722 < baseStart_7845722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845729 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 2, 5, 2]
def baseStart_7845729 : Nat := 118140960795 + 7845729 * 2 ^ 59
def prefixEnd_7845729 : Nat := 4983230072969 + 3 ^ 40 * 7845729 * 2
def baseEnd_7845729 : Nat := 4028630061919039282905655

theorem tailTrace_7845729 : CollatzResearch.WordTrace tailWord_7845729 prefixEnd_7845729 4028630061919039282905655 := by
  unfold tailWord_7845729
  simp only [CollatzResearch.WordTrace]
  refine ⟨286157245393271251679932241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190771496928847501119954827 286157245393271251679932241)
  ·
    refine ⟨214617934044953438759949181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286157245393271251679932241 214617934044953438759949181)
    ·
      refine ⟨80481725266857539534980943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214617934044953438759949181 80481725266857539534980943)
      ·
        refine ⟨120722587900286309302471415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80481725266857539534980943 120722587900286309302471415)
        ·
          refine ⟨181083881850429463953707123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120722587900286309302471415 181083881850429463953707123)
          ·
            refine ⟨271625822775644195930560685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181083881850429463953707123 271625822775644195930560685)
            ·
              refine ⟨101859683540866573473960257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271625822775644195930560685 101859683540866573473960257)
              ·
                refine ⟨76394762655649930105470193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101859683540866573473960257 76394762655649930105470193)
                ·
                  refine ⟨57296071991737447579102645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76394762655649930105470193 57296071991737447579102645)
                  ·
                    refine ⟨5371506749225385710540873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57296071991737447579102645 5371506749225385710540873)
                    ·
                      refine ⟨4028630061919039282905655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5371506749225385710540873 4028630061919039282905655)
                      ·
                        rfl

theorem cell23_7845729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_7845729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845729 prefixEnd_7845729 := by exact prefixLift 7845729
  have htrace : WordTrace (prefixWord ++ tailWord_7845729) baseStart_7845729 baseEnd_7845729 := by
    simpa [prefixWord, tailWord_7845729, baseEnd_7845729] using wordTrace_append hprefix tailTrace_7845729
  have hstable : (prefixWord ++ tailWord_7845729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845729).length < 2 ^ (prefixWord ++ tailWord_7845729).sum := by decide
  have hdescent : baseEnd_7845729 < baseStart_7845729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845772 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_7845772 : Nat := 118140960795 + 7845772 * 2 ^ 59
def prefixEnd_7845772 : Nat := 4983230072969 + 3 ^ 40 * 7845772 * 2
def baseEnd_7845772 : Nat := 4028652141587182614667957

theorem tailTrace_7845772 : CollatzResearch.WordTrace tailWord_7845772 prefixEnd_7845772 4028652141587182614667957 := by
  unfold tailWord_7845772
  simp only [CollatzResearch.WordTrace]
  refine ⟨143079406866057735011873785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190772542488076980015831713 143079406866057735011873785)
  ·
    refine ⟨107309555149543301258905339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143079406866057735011873785 107309555149543301258905339)
    ·
      refine ⟨160964332724314951888358009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107309555149543301258905339 160964332724314951888358009)
      ·
        refine ⟨120723249543236213916268507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160964332724314951888358009 120723249543236213916268507)
        ·
          refine ⟨181084874314854320874402761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120723249543236213916268507 181084874314854320874402761)
          ·
            refine ⟨135813655736140740655802071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181084874314854320874402761 135813655736140740655802071)
            ·
              refine ⟨203720483604211110983703107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135813655736140740655802071 203720483604211110983703107)
              ·
                refine ⟨305580725406316666475554661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203720483604211110983703107 305580725406316666475554661)
                ·
                  refine ⟨57296386013684374964166499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305580725406316666475554661 57296386013684374964166499)
                  ·
                    refine ⟨85944579020526562446249749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57296386013684374964166499 85944579020526562446249749)
                    ·
                      refine ⟨4028652141587182614667957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85944579020526562446249749 4028652141587182614667957)
                      ·
                        rfl

theorem cell23_7845772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_7845772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845772 prefixEnd_7845772 := by exact prefixLift 7845772
  have htrace : WordTrace (prefixWord ++ tailWord_7845772) baseStart_7845772 baseEnd_7845772 := by
    simpa [prefixWord, tailWord_7845772, baseEnd_7845772] using wordTrace_append hprefix tailTrace_7845772
  have hstable : (prefixWord ++ tailWord_7845772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845772).length < 2 ^ (prefixWord ++ tailWord_7845772).sum := by decide
  have hdescent : baseEnd_7845772 < baseStart_7845772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845786 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 3, 4]
def baseStart_7845786 : Nat := 118140960795 + 7845786 * 2 ^ 59
def prefixEnd_7845786 : Nat := 4983230072969 + 3 ^ 40 * 7845786 * 2
def baseEnd_7845786 : Nat := 1342886443438781853297631

theorem tailTrace_7845786 : CollatzResearch.WordTrace tailWord_7845786 prefixEnd_7845786 1342886443438781853297631 := by
  unfold tailWord_7845786
  simp only [CollatzResearch.WordTrace]
  refine ⟨71539831088516187603689303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190772882902709833609838141 71539831088516187603689303)
  ·
    refine ⟨107309746632774281405533955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71539831088516187603689303 107309746632774281405533955)
    ·
      refine ⟨160964619949161422108300933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107309746632774281405533955 160964619949161422108300933)
      ·
        refine ⟨30180866240467766645306425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160964619949161422108300933 30180866240467766645306425)
        ·
          refine ⟨22635649680350824983979819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30180866240467766645306425 22635649680350824983979819)
          ·
            refine ⟨33953474520526237475969729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22635649680350824983979819 33953474520526237475969729)
            ·
              refine ⟨25465105890394678106977297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33953474520526237475969729 25465105890394678106977297)
              ·
                refine ⟨19098829417796008580232973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25465105890394678106977297 19098829417796008580232973)
                ·
                  refine ⟨7162061031673503217587365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19098829417796008580232973 7162061031673503217587365)
                  ·
                    refine ⟨1342886443438781853297631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7162061031673503217587365 1342886443438781853297631)
                    ·
                      rfl

theorem cell23_7845786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_7845786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845786 prefixEnd_7845786 := by exact prefixLift 7845786
  have htrace : WordTrace (prefixWord ++ tailWord_7845786) baseStart_7845786 baseEnd_7845786 := by
    simpa [prefixWord, tailWord_7845786, baseEnd_7845786] using wordTrace_append hprefix tailTrace_7845786
  have hstable : (prefixWord ++ tailWord_7845786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845786).length < 2 ^ (prefixWord ++ tailWord_7845786).sum := by decide
  have hdescent : baseEnd_7845786 < baseStart_7845786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845799 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 8]
def baseStart_7845799 : Nat := 118140960795 + 7845799 * 2 ^ 59
def prefixEnd_7845799 : Nat := 4983230072969 + 3 ^ 40 * 7845799 * 2
def baseEnd_7845799 : Nat := 447629556173872667670037

theorem tailTrace_7845799 : CollatzResearch.WordTrace tailWord_7845799 prefixEnd_7845799 447629556173872667670037 := by
  unfold tailWord_7845799
  simp only [CollatzResearch.WordTrace]
  refine ⟨286159798503017653634980451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190773199002011769089986967 286159798503017653634980451)
  ·
    refine ⟨429239697754526480452470677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286159798503017653634980451 429239697754526480452470677)
    ·
      refine ⟨20120610832243428771209563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 429239697754526480452470677 20120610832243428771209563)
      ·
        refine ⟨30180916248365143156814345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20120610832243428771209563 30180916248365143156814345)
        ·
          refine ⟨22635687186273857367610759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30180916248365143156814345 22635687186273857367610759)
          ·
            refine ⟨33953530779410786051416139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22635687186273857367610759 33953530779410786051416139)
            ·
              refine ⟨50930296169116179077124209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33953530779410786051416139 50930296169116179077124209)
              ·
                refine ⟨38197722126837134307843157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50930296169116179077124209 38197722126837134307843157)
                ·
                  refine ⟨447629556173872667670037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38197722126837134307843157 447629556173872667670037)
                  ·
                    rfl

theorem cell23_7845799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 8].length) (baseStart_7845799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845799 prefixEnd_7845799 := by exact prefixLift 7845799
  have htrace : WordTrace (prefixWord ++ tailWord_7845799) baseStart_7845799 baseEnd_7845799 := by
    simpa [prefixWord, tailWord_7845799, baseEnd_7845799] using wordTrace_append hprefix tailTrace_7845799
  have hstable : (prefixWord ++ tailWord_7845799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845799).length < 2 ^ (prefixWord ++ tailWord_7845799).sum := by decide
  have hdescent : baseEnd_7845799 < baseStart_7845799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845820 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 3, 4]
def baseStart_7845820 : Nat := 118140960795 + 7845820 * 2 ^ 59
def prefixEnd_7845820 : Nat := 4983230072969 + 3 ^ 40 * 7845820 * 2
def baseEnd_7845820 : Nat := 1342892262886199475622579

theorem tailTrace_7845820 : CollatzResearch.WordTrace tailWord_7845820 prefixEnd_7845820 1342892262886199475622579 := by
  unfold tailWord_7845820
  simp only [CollatzResearch.WordTrace]
  refine ⟨143080282217970787110747457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190773709623961049480996609 143080282217970787110747457)
  ·
    refine ⟨107310211663478090333060593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143080282217970787110747457 107310211663478090333060593)
    ·
      refine ⟨80482658747608567749795445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107310211663478090333060593 80482658747608567749795445)
      ·
        refine ⟨7545249257588303226543323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80482658747608567749795445 7545249257588303226543323)
        ·
          refine ⟨11317873886382454839814985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7545249257588303226543323 11317873886382454839814985)
          ·
            refine ⟨8488405414786841129861239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11317873886382454839814985 8488405414786841129861239)
            ·
              refine ⟨12732608122180261694791859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8488405414786841129861239 12732608122180261694791859)
              ·
                refine ⟨19098912183270392542187789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12732608122180261694791859 19098912183270392542187789)
                ·
                  refine ⟨7162092068726397203320421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19098912183270392542187789 7162092068726397203320421)
                  ·
                    refine ⟨1342892262886199475622579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7162092068726397203320421 1342892262886199475622579)
                    ·
                      rfl

theorem cell23_7845820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_7845820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845820 prefixEnd_7845820 := by exact prefixLift 7845820
  have htrace : WordTrace (prefixWord ++ tailWord_7845820) baseStart_7845820 baseEnd_7845820 := by
    simpa [prefixWord, tailWord_7845820, baseEnd_7845820] using wordTrace_append hprefix tailTrace_7845820
  have hstable : (prefixWord ++ tailWord_7845820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845820).length < 2 ^ (prefixWord ++ tailWord_7845820).sum := by decide
  have hdescent : baseEnd_7845820 < baseStart_7845820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845859 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 3, 6]
def baseStart_7845859 : Nat := 118140960795 + 7845859 * 2 ^ 59
def prefixEnd_7845859 : Nat := 4983230072969 + 3 ^ 40 * 7845859 * 2
def baseEnd_7845859 : Nat := 1342898938134707924760019

theorem tailTrace_7845859 : CollatzResearch.WordTrace tailWord_7845859 prefixEnd_7845859 1342898938134707924760019 := by
  unfold tailWord_7845859
  simp only [CollatzResearch.WordTrace]
  refine ⟨286161986882800283882164631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190774657921866855921443087 286161986882800283882164631)
  ·
    refine ⟨429242980324200425823246947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286161986882800283882164631 429242980324200425823246947)
    ·
      refine ⟨643864470486300638734870421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429242980324200425823246947 643864470486300638734870421)
      ·
        refine ⟨30181147054045342440697051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 643864470486300638734870421 30181147054045342440697051)
        ·
          refine ⟨45271720581068013661045577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30181147054045342440697051 45271720581068013661045577)
          ·
            refine ⟨33953790435801010245784183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45271720581068013661045577 33953790435801010245784183)
            ·
              refine ⟨50930685653701515368676275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33953790435801010245784183 50930685653701515368676275)
              ·
                refine ⟨76396028480552273053014413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50930685653701515368676275 76396028480552273053014413)
                ·
                  refine ⟨28648510680207102394880405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76396028480552273053014413 28648510680207102394880405)
                  ·
                    refine ⟨1342898938134707924760019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28648510680207102394880405 1342898938134707924760019)
                    ·
                      rfl

theorem cell23_7845859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 6].length) (baseStart_7845859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845859 prefixEnd_7845859 := by exact prefixLift 7845859
  have htrace : WordTrace (prefixWord ++ tailWord_7845859) baseStart_7845859 baseEnd_7845859 := by
    simpa [prefixWord, tailWord_7845859, baseEnd_7845859] using wordTrace_append hprefix tailTrace_7845859
  have hstable : (prefixWord ++ tailWord_7845859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845859).length < 2 ^ (prefixWord ++ tailWord_7845859).sum := by decide
  have hdescent : baseEnd_7845859 < baseStart_7845859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845896 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_7845896 : Nat := 118140960795 + 7845896 * 2 ^ 59
def prefixEnd_7845896 : Nat := 4983230072969 + 3 ^ 40 * 7845896 * 2
def baseEnd_7845896 : Nat := 4028715813188340129517387

theorem tailTrace_7845896 : CollatzResearch.WordTrace tailWord_7845896 prefixEnd_7845896 4028715813188340129517387 := by
  unfold tailWord_7845896
  simp only [CollatzResearch.WordTrace]
  refine ⟨143081668191833119600630771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190775557589110826134174361 143081668191833119600630771)
  ·
    refine ⟨214622502287749679400946157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143081668191833119600630771 214622502287749679400946157)
    ·
      refine ⟨80483438357906129775354809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214622502287749679400946157 80483438357906129775354809)
      ·
        refine ⟨60362578768429597331516107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80483438357906129775354809 60362578768429597331516107)
        ·
          refine ⟨90543868152644395997274161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60362578768429597331516107 90543868152644395997274161)
          ·
            refine ⟨67907901114483296997955621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90543868152644395997274161 67907901114483296997955621)
            ·
              refine ⟨12732731458965618187116679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67907901114483296997955621 12732731458965618187116679)
              ·
                refine ⟨19099097188448427280675019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12732731458965618187116679 19099097188448427280675019)
                ·
                  refine ⟨28648645782672640921012529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19099097188448427280675019 28648645782672640921012529)
                  ·
                    refine ⟨21486484337004480690759397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28648645782672640921012529 21486484337004480690759397)
                    ·
                      refine ⟨4028715813188340129517387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21486484337004480690759397 4028715813188340129517387)
                      ·
                        rfl

theorem cell23_7845896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_7845896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845896 prefixEnd_7845896 := by exact prefixLift 7845896
  have htrace : WordTrace (prefixWord ++ tailWord_7845896) baseStart_7845896 baseEnd_7845896 := by
    simpa [prefixWord, tailWord_7845896, baseEnd_7845896] using wordTrace_append hprefix tailTrace_7845896
  have hstable : (prefixWord ++ tailWord_7845896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845896).length < 2 ^ (prefixWord ++ tailWord_7845896).sum := by decide
  have hdescent : baseEnd_7845896 < baseStart_7845896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845917 : List Nat := [1, 4, 2, 2, 2, 1, 1, 5, 1, 2, 2]
def baseStart_7845917 : Nat := 118140960795 + 7845917 * 2 ^ 59
def prefixEnd_7845917 : Nat := 4983230072969 + 3 ^ 40 * 7845917 * 2
def baseEnd_7845917 : Nat := 4028726596282084547354791

theorem tailTrace_7845917 : CollatzResearch.WordTrace tailWord_7845917 prefixEnd_7845917 4028726596282084547354791 := by
  unfold tailWord_7845917
  simp only [CollatzResearch.WordTrace]
  refine ⟨286164102316590159787776005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190776068211060106525184003 286164102316590159787776005)
  ·
    refine ⟨53655769184360654960208001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286164102316590159787776005 53655769184360654960208001)
    ·
      refine ⟨40241826888270491220156001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53655769184360654960208001 40241826888270491220156001)
      ·
        refine ⟨30181370166202868415117001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40241826888270491220156001 30181370166202868415117001)
        ·
          refine ⟨22636027624652151311337751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30181370166202868415117001 22636027624652151311337751)
          ·
            refine ⟨33954041436978226967006627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22636027624652151311337751 33954041436978226967006627)
            ·
              refine ⟨50931062155467340450509941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33954041436978226967006627 50931062155467340450509941)
              ·
                refine ⟨4774787077075063167235307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50931062155467340450509941 4774787077075063167235307)
                ·
                  refine ⟨7162180615612594750852961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4774787077075063167235307 7162180615612594750852961)
                  ·
                    refine ⟨5371635461709446063139721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7162180615612594750852961 5371635461709446063139721)
                    ·
                      refine ⟨4028726596282084547354791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5371635461709446063139721 4028726596282084547354791)
                      ·
                        rfl

theorem cell23_7845917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_7845917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845917 prefixEnd_7845917 := by exact prefixLift 7845917
  have htrace : WordTrace (prefixWord ++ tailWord_7845917) baseStart_7845917 baseEnd_7845917 := by
    simpa [prefixWord, tailWord_7845917, baseEnd_7845917] using wordTrace_append hprefix tailTrace_7845917
  have hstable : (prefixWord ++ tailWord_7845917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845917).length < 2 ^ (prefixWord ++ tailWord_7845917).sum := by decide
  have hdescent : baseEnd_7845917 < baseStart_7845917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845927 : List Nat := [1, 1, 7, 1, 2, 2, 1, 2, 2, 4]
def baseStart_7845927 : Nat := 118140960795 + 7845927 * 2 ^ 59
def prefixEnd_7845927 : Nat := 4983230072969 + 3 ^ 40 * 7845927 * 2
def baseEnd_7845927 : Nat := 1342910577029543169409915

theorem tailTrace_7845927 : CollatzResearch.WordTrace tailWord_7845927 prefixEnd_7845927 1342910577029543169409915 := by
  unfold tailWord_7845927
  simp only [CollatzResearch.WordTrace]
  refine ⟨286164467046553931495640035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190776311364369287663760023 286164467046553931495640035)
  ·
    refine ⟨429246700569830897243460053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286164467046553931495640035 429246700569830897243460053)
    ·
      refine ⟨10060469544605411654143595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 429246700569830897243460053 10060469544605411654143595)
      ·
        refine ⟨15090704316908117481215393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10060469544605411654143595 15090704316908117481215393)
        ·
          refine ⟨11318028237681088110911545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15090704316908117481215393 11318028237681088110911545)
          ·
            refine ⟨8488521178260816083183659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11318028237681088110911545 8488521178260816083183659)
            ·
              refine ⟨12732781767391224124775489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8488521178260816083183659 12732781767391224124775489)
              ·
                refine ⟨9549586325543418093581617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12732781767391224124775489 9549586325543418093581617)
                ·
                  refine ⟨7162189744157563570186213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9549586325543418093581617 7162189744157563570186213)
                  ·
                    refine ⟨1342910577029543169409915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7162189744157563570186213 1342910577029543169409915)
                    ·
                      rfl

theorem cell23_7845927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_7845927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845927 prefixEnd_7845927 := by exact prefixLift 7845927
  have htrace : WordTrace (prefixWord ++ tailWord_7845927) baseStart_7845927 baseEnd_7845927 := by
    simpa [prefixWord, tailWord_7845927, baseEnd_7845927] using wordTrace_append hprefix tailTrace_7845927
  have hstable : (prefixWord ++ tailWord_7845927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845927).length < 2 ^ (prefixWord ++ tailWord_7845927).sum := by decide
  have hdescent : baseEnd_7845927 < baseStart_7845927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845939 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 4]
def baseStart_7845939 : Nat := 118140960795 + 7845939 * 2 ^ 59
def prefixEnd_7845939 : Nat := 4983230072969 + 3 ^ 40 * 7845939 * 2
def baseEnd_7845939 : Nat := 4028737892856483461279689

theorem tailTrace_7845939 : CollatzResearch.WordTrace tailWord_7845939 prefixEnd_7845939 4028737892856483461279689 := by
  unfold tailWord_7845939
  simp only [CollatzResearch.WordTrace]
  refine ⟨286164904722510457545076871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190776603148340305030051247 286164904722510457545076871)
  ·
    refine ⟨429247357083765686317615307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286164904722510457545076871 429247357083765686317615307)
    ·
      refine ⟨643871035625648529476422961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429247357083765686317615307 643871035625648529476422961)
      ·
        refine ⟨482903276719236397107317221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643871035625648529476422961 482903276719236397107317221)
        ·
          refine ⟨90544364384856824457621979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 482903276719236397107317221 90544364384856824457621979)
          ·
            refine ⟨135816546577285236686432969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90544364384856824457621979 135816546577285236686432969)
            ·
              refine ⟨101862409932963927514824727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135816546577285236686432969 101862409932963927514824727)
              ·
                refine ⟨152793614899445891272237091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101862409932963927514824727 152793614899445891272237091)
                ·
                  refine ⟨229190422349168836908355637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152793614899445891272237091 229190422349168836908355637)
                  ·
                    refine ⟨21486602095234578460158341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 229190422349168836908355637 21486602095234578460158341)
                    ·
                      refine ⟨4028737892856483461279689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21486602095234578460158341 4028737892856483461279689)
                      ·
                        rfl

theorem cell23_7845939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_7845939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845939 prefixEnd_7845939 := by exact prefixLift 7845939
  have htrace : WordTrace (prefixWord ++ tailWord_7845939) baseStart_7845939 baseEnd_7845939 := by
    simpa [prefixWord, tailWord_7845939, baseEnd_7845939] using wordTrace_append hprefix tailTrace_7845939
  have hstable : (prefixWord ++ tailWord_7845939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845939).length < 2 ^ (prefixWord ++ tailWord_7845939).sum := by decide
  have hdescent : baseEnd_7845939 < baseStart_7845939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845976 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 2, 1, 5]
def baseStart_7845976 : Nat := 118140960795 + 7845976 * 2 ^ 59
def prefixEnd_7845976 : Nat := 4983230072969 + 3 ^ 40 * 7845976 * 2
def baseEnd_7845976 : Nat := 4028756891640699816517019

theorem tailTrace_7845976 : CollatzResearch.WordTrace tailWord_7845976 prefixEnd_7845976 4028756891640699816517019 := by
  unfold tailWord_7845976
  simp only [CollatzResearch.WordTrace]
  refine ⟨143083127111688206432086891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190777502815584275242782521 143083127111688206432086891)
  ·
    refine ⟨214624690667532309648130337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143083127111688206432086891 214624690667532309648130337)
    ·
      refine ⟨160968518000649232236097753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214624690667532309648130337 160968518000649232236097753)
      ·
        refine ⟨120726388500486924177073315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160968518000649232236097753 120726388500486924177073315)
        ·
          refine ⟨181089582750730386265609973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120726388500486924177073315 181089582750730386265609973)
          ·
            refine ⟨16977148382880973712400935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181089582750730386265609973 16977148382880973712400935)
            ·
              refine ⟨25465722574321460568601403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16977148382880973712400935 25465722574321460568601403)
              ·
                refine ⟨38198583861482190852902105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25465722574321460568601403 38198583861482190852902105)
                ·
                  refine ⟨28648937896111643139676579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38198583861482190852902105 28648937896111643139676579)
                  ·
                    refine ⟨42973406844167464709514869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28648937896111643139676579 42973406844167464709514869)
                    ·
                      refine ⟨4028756891640699816517019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42973406844167464709514869 4028756891640699816517019)
                      ·
                        rfl

theorem cell23_7845976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_7845976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845976 prefixEnd_7845976 := by exact prefixLift 7845976
  have htrace : WordTrace (prefixWord ++ tailWord_7845976) baseStart_7845976 baseEnd_7845976 := by
    simpa [prefixWord, tailWord_7845976, baseEnd_7845976] using wordTrace_append hprefix tailTrace_7845976
  have hstable : (prefixWord ++ tailWord_7845976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845976).length < 2 ^ (prefixWord ++ tailWord_7845976).sum := by decide
  have hdescent : baseEnd_7845976 < baseStart_7845976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7845996 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 7]
def baseStart_7845996 : Nat := 118140960795 + 7845996 * 2 ^ 59
def prefixEnd_7845996 : Nat := 4983230072969 + 3 ^ 40 * 7845996 * 2
def baseEnd_7845996 : Nat := 447640795694865526474103

theorem tailTrace_7845996 : CollatzResearch.WordTrace tailWord_7845996 prefixEnd_7845996 447640795694865526474103 := by
  unfold tailWord_7845996
  simp only [CollatzResearch.WordTrace]
  refine ⟨143083491841651978139950921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190777989122202637519934561 143083491841651978139950921)
  ·
    refine ⟨107312618881238983604963191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143083491841651978139950921 107312618881238983604963191)
    ·
      refine ⟨160968928321858475407444787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107312618881238983604963191 160968928321858475407444787)
      ·
        refine ⟨241453392482787713111167181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160968928321858475407444787 241453392482787713111167181)
        ·
          refine ⟨90545022181045392416687693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241453392482787713111167181 90545022181045392416687693)
          ·
            refine ⟨33954383317892022156257885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90545022181045392416687693 33954383317892022156257885)
            ·
              refine ⟨12732893744209508308596707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33954383317892022156257885 12732893744209508308596707)
              ·
                refine ⟨19099340616314262462895061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12732893744209508308596707 19099340616314262462895061)
                ·
                  refine ⟨447640795694865526474103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19099340616314262462895061 447640795694865526474103)
                  ·
                    rfl

theorem cell23_7845996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 7].length) (baseStart_7845996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7845996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7845996 prefixEnd_7845996 := by exact prefixLift 7845996
  have htrace : WordTrace (prefixWord ++ tailWord_7845996) baseStart_7845996 baseEnd_7845996 := by
    simpa [prefixWord, tailWord_7845996, baseEnd_7845996] using wordTrace_append hprefix tailTrace_7845996
  have hstable : (prefixWord ++ tailWord_7845996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7845996).length < 2 ^ (prefixWord ++ tailWord_7845996).sum := by decide
  have hdescent : baseEnd_7845996 < baseStart_7845996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7845996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846007 : List Nat := [1, 1, 3, 1, 1, 5, 4, 1, 2, 2, 2]
def baseStart_7846007 : Nat := 118140960795 + 7846007 * 2 ^ 59
def prefixEnd_7846007 : Nat := 4983230072969 + 3 ^ 40 * 7846007 * 2
def baseEnd_7846007 : Nat := 4028772809540989195229377

theorem tailTrace_7846007 : CollatzResearch.WordTrace tailWord_7846007 prefixEnd_7846007 4028772809540989195229377 := by
  unfold tailWord_7846007
  simp only [CollatzResearch.WordTrace]
  refine ⟨286167384886264105158552275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190778256590842736772368183 286167384886264105158552275)
  ·
    refine ⟨429251077329396157737828413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286167384886264105158552275 429251077329396157737828413)
    ·
      refine ⟨160969153998523559151685655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429251077329396157737828413 160969153998523559151685655)
      ·
        refine ⟨241453730997785338727528483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160969153998523559151685655 241453730997785338727528483)
        ·
          refine ⟨362180596496678008091292725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241453730997785338727528483 362180596496678008091292725)
          ·
            refine ⟨33954430921563563258558693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 362180596496678008091292725 33954430921563563258558693)
            ·
              refine ⟨6366455797793168110979755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33954430921563563258558693 6366455797793168110979755)
              ·
                refine ⟨9549683696689752166469633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6366455797793168110979755 9549683696689752166469633)
                ·
                  refine ⟨7162262772517314124852225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9549683696689752166469633 7162262772517314124852225)
                  ·
                    refine ⟨5371697079387985593639169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7162262772517314124852225 5371697079387985593639169)
                    ·
                      refine ⟨4028772809540989195229377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5371697079387985593639169 4028772809540989195229377)
                      ·
                        rfl

theorem cell23_7846007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 2, 2, 2].length) (baseStart_7846007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846007 prefixEnd_7846007 := by exact prefixLift 7846007
  have htrace : WordTrace (prefixWord ++ tailWord_7846007) baseStart_7846007 baseEnd_7846007 := by
    simpa [prefixWord, tailWord_7846007, baseEnd_7846007] using wordTrace_append hprefix tailTrace_7846007
  have hstable : (prefixWord ++ tailWord_7846007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846007).length < 2 ^ (prefixWord ++ tailWord_7846007).sum := by decide
  have hdescent : baseEnd_7846007 < baseStart_7846007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846047 : List Nat := [1, 1, 2, 6, 1, 3, 2, 2, 5]
def baseStart_7846047 : Nat := 118140960795 + 7846047 * 2 ^ 59
def prefixEnd_7846047 : Nat := 4983230072969 + 3 ^ 40 * 7846047 * 2
def baseEnd_7846047 : Nat := 447643705418574337636577

theorem tailTrace_7846047 : CollatzResearch.WordTrace tailWord_7846047 prefixEnd_7846047 447643705418574337636577 := by
  unfold tailWord_7846047
  simp only [CollatzResearch.WordTrace]
  refine ⟨286168843806119191990008395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190779229204079461326672263 286168843806119191990008395)
  ·
    refine ⟨429253265709178787985012593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286168843806119191990008395 429253265709178787985012593)
    ·
      refine ⟨321939949281884090988759445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429253265709178787985012593 321939949281884090988759445)
      ·
        refine ⟨15090935122588316765098099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 321939949281884090988759445 15090935122588316765098099)
        ·
          refine ⟨22636402683882475147647149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15090935122588316765098099 22636402683882475147647149)
          ·
            refine ⟨8488651006455928180367681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22636402683882475147647149 8488651006455928180367681)
            ·
              refine ⟨6366488254841946135275761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8488651006455928180367681 6366488254841946135275761)
              ·
                refine ⟨4774866191131459601456821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6366488254841946135275761 4774866191131459601456821)
                ·
                  refine ⟨447643705418574337636577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4774866191131459601456821 447643705418574337636577)
                  ·
                    rfl

theorem cell23_7846047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 5].length) (baseStart_7846047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846047 prefixEnd_7846047 := by exact prefixLift 7846047
  have htrace : WordTrace (prefixWord ++ tailWord_7846047) baseStart_7846047 baseEnd_7846047 := by
    simpa [prefixWord, tailWord_7846047, baseEnd_7846047] using wordTrace_append hprefix tailTrace_7846047
  have hstable : (prefixWord ++ tailWord_7846047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846047).length < 2 ^ (prefixWord ++ tailWord_7846047).sum := by decide
  have hdescent : baseEnd_7846047 < baseStart_7846047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846050 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_7846050 : Nat := 118140960795 + 7846050 * 2 ^ 59
def prefixEnd_7846050 : Nat := 4983230072969 + 3 ^ 40 * 7846050 * 2
def baseEnd_7846050 : Nat := 4028794889209132526991679

theorem tailTrace_7846050 : CollatzResearch.WordTrace tailWord_7846050 prefixEnd_7846050 4028794889209132526991679 := by
  unfold tailWord_7846050
  simp only [CollatzResearch.WordTrace]
  refine ⟨71542238306277080875591901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190779302150072215668245069 71542238306277080875591901)
  ·
    refine ⟨26828339364853905328346963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71542238306277080875591901 26828339364853905328346963)
    ·
      refine ⟨40242509047280857992520445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26828339364853905328346963 40242509047280857992520445)
      ·
        refine ⟨15090940892730321747195167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40242509047280857992520445 15090940892730321747195167)
        ·
          refine ⟨22636411339095482620792751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15090940892730321747195167 22636411339095482620792751)
          ·
            refine ⟨33954617008643223931189127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22636411339095482620792751 33954617008643223931189127)
            ·
              refine ⟨50931925512964835896783691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33954617008643223931189127 50931925512964835896783691)
              ·
                refine ⟨76397888269447253845175537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50931925512964835896783691 76397888269447253845175537)
                ·
                  refine ⟨57298416202085440383881653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76397888269447253845175537 57298416202085440383881653)
                  ·
                    refine ⟨5371726518945510035988905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57298416202085440383881653 5371726518945510035988905)
                    ·
                      refine ⟨4028794889209132526991679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5371726518945510035988905 4028794889209132526991679)
                      ·
                        rfl

theorem cell23_7846050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_7846050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846050 prefixEnd_7846050 := by exact prefixLift 7846050
  have htrace : WordTrace (prefixWord ++ tailWord_7846050) baseStart_7846050 baseEnd_7846050 := by
    simpa [prefixWord, tailWord_7846050, baseEnd_7846050] using wordTrace_append hprefix tailTrace_7846050
  have hstable : (prefixWord ++ tailWord_7846050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846050).length < 2 ^ (prefixWord ++ tailWord_7846050).sum := by decide
  have hdescent : baseEnd_7846050 < baseStart_7846050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846073 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 3, 4]
def baseStart_7846073 : Nat := 118140960795 + 7846073 * 2 ^ 59
def prefixEnd_7846073 : Nat := 4983230072969 + 3 ^ 40 * 7846073 * 2
def baseEnd_7846073 : Nat := 1342935566421395312334691

theorem tailTrace_7846073 : CollatzResearch.WordTrace tailWord_7846073 prefixEnd_7846073 1342935566421395312334691 := by
  unfold tailWord_7846073
  simp only [CollatzResearch.WordTrace]
  refine ⟨286169792104024998430454873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190779861402683332286969915 286169792104024998430454873)
  ·
    refine ⟨214627344078018748822841155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286169792104024998430454873 214627344078018748822841155)
    ·
      refine ⟨321941016117028123234261733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214627344078018748822841155 321941016117028123234261733)
      ·
        refine ⟨60363940521942773106424075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321941016117028123234261733 60363940521942773106424075)
        ·
          refine ⟨90545910782914159659636113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60363940521942773106424075 90545910782914159659636113)
          ·
            refine ⟨67909433087185619744727085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90545910782914159659636113 67909433087185619744727085)
            ·
              refine ⟨25466037407694607404272657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67909433087185619744727085 25466037407694607404272657)
              ·
                refine ⟨19099528055770955553204493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25466037407694607404272657 19099528055770955553204493)
                ·
                  refine ⟨7162323020914108332451685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19099528055770955553204493 7162323020914108332451685)
                  ·
                    refine ⟨1342935566421395312334691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7162323020914108332451685 1342935566421395312334691)
                    ·
                      rfl

theorem cell23_7846073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 4].length) (baseStart_7846073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846073 prefixEnd_7846073 := by exact prefixLift 7846073
  have htrace : WordTrace (prefixWord ++ tailWord_7846073) baseStart_7846073 baseEnd_7846073 := by
    simpa [prefixWord, tailWord_7846073, baseEnd_7846073] using wordTrace_append hprefix tailTrace_7846073
  have hstable : (prefixWord ++ tailWord_7846073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846073).length < 2 ^ (prefixWord ++ tailWord_7846073).sum := by decide
  have hdescent : baseEnd_7846073 < baseStart_7846073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846080 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 4]
def baseStart_7846080 : Nat := 118140960795 + 7846080 * 2 ^ 59
def prefixEnd_7846080 : Nat := 4983230072969 + 3 ^ 40 * 7846080 * 2
def baseEnd_7846080 : Nat := 4028810293628767409616541

theorem tailTrace_7846080 : CollatzResearch.WordTrace tailWord_7846080 prefixEnd_7846080 4028810293628767409616541 := by
  unfold tailWord_7846080
  simp only [CollatzResearch.WordTrace]
  refine ⟨143085023707499819312979847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190780031609999759083973129 143085023707499819312979847)
  ·
    refine ⟨214627535561249728969469771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143085023707499819312979847 214627535561249728969469771)
    ·
      refine ⟨321941303341874593454204657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214627535561249728969469771 321941303341874593454204657)
      ·
        refine ⟨241455977506405945090653493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321941303341874593454204657 241455977506405945090653493)
        ·
          refine ⟨22636497891225557352248765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241455977506405945090653493 22636497891225557352248765)
          ·
            refine ⟨8488686709209584007093287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22636497891225557352248765 8488686709209584007093287)
            ·
              refine ⟨12733030063814376010639931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8488686709209584007093287 12733030063814376010639931)
              ·
                refine ⟨19099545095721564015959897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12733030063814376010639931 19099545095721564015959897)
                ·
                  refine ⟨14324658821791173011969923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19099545095721564015959897 14324658821791173011969923)
                  ·
                    refine ⟨21486988232686759517954885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14324658821791173011969923 21486988232686759517954885)
                    ·
                      refine ⟨4028810293628767409616541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21486988232686759517954885 4028810293628767409616541)
                      ·
                        rfl

theorem cell23_7846080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_7846080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846080 prefixEnd_7846080 := by exact prefixLift 7846080
  have htrace : WordTrace (prefixWord ++ tailWord_7846080) baseStart_7846080 baseEnd_7846080 := by
    simpa [prefixWord, tailWord_7846080, baseEnd_7846080] using wordTrace_append hprefix tailTrace_7846080
  have hstable : (prefixWord ++ tailWord_7846080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846080).length < 2 ^ (prefixWord ++ tailWord_7846080).sum := by decide
  have hdescent : baseEnd_7846080 < baseStart_7846080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846096 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 3]
def baseStart_7846096 : Nat := 118140960795 + 7846096 * 2 ^ 59
def prefixEnd_7846096 : Nat := 4983230072969 + 3 ^ 40 * 7846096 * 2
def baseEnd_7846096 : Nat := 4028818509319239347016467

theorem tailTrace_7846096 : CollatzResearch.WordTrace tailWord_7846096 prefixEnd_7846096 4028818509319239347016467 := by
  unfold tailWord_7846096
  simp only [CollatzResearch.WordTrace]
  refine ⟨143085315491470836679271071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190780420655294448905694761 143085315491470836679271071)
  ·
    refine ⟨214627973237206255018906607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143085315491470836679271071 214627973237206255018906607)
    ·
      refine ⟨321941959855809382528359911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214627973237206255018906607 321941959855809382528359911)
      ·
        refine ⟨482912939783714073792539867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321941959855809382528359911 482912939783714073792539867)
        ·
          refine ⟨724369409675571110688809801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482912939783714073792539867 724369409675571110688809801)
          ·
            refine ⟨543277057256678333016607351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724369409675571110688809801 543277057256678333016607351)
            ·
              refine ⟨814915585885017499524911027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543277057256678333016607351 814915585885017499524911027)
              ·
                refine ⟨1222373378827526249287366541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814915585885017499524911027 1222373378827526249287366541)
                ·
                  refine ⟨458390017060322343482762453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1222373378827526249287366541 458390017060322343482762453)
                  ·
                    refine ⟨10743516024851304925377245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 458390017060322343482762453 10743516024851304925377245)
                    ·
                      refine ⟨4028818509319239347016467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10743516024851304925377245 4028818509319239347016467)
                      ·
                        rfl

theorem cell23_7846096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 3].length) (baseStart_7846096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846096 prefixEnd_7846096 := by exact prefixLift 7846096
  have htrace : WordTrace (prefixWord ++ tailWord_7846096) baseStart_7846096 baseEnd_7846096 := by
    simpa [prefixWord, tailWord_7846096, baseEnd_7846096] using wordTrace_append hprefix tailTrace_7846096
  have hstable : (prefixWord ++ tailWord_7846096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846096).length < 2 ^ (prefixWord ++ tailWord_7846096).sum := by decide
  have hdescent : baseEnd_7846096 < baseStart_7846096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846106 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_7846106 : Nat := 118140960795 + 7846106 * 2 ^ 59
def prefixEnd_7846106 : Nat := 4983230072969 + 3 ^ 40 * 7846106 * 2
def baseEnd_7846106 : Nat := 4028823644125784307891421

theorem tailTrace_7846106 : CollatzResearch.WordTrace tailWord_7846106 prefixEnd_7846106 4028823644125784307891421 := by
  unfold tailWord_7846106
  simp only [CollatzResearch.WordTrace]
  refine ⟨71542748928226361266601543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190780663808603630044270781 71542748928226361266601543)
  ·
    refine ⟨107314123392339541899902315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71542748928226361266601543 107314123392339541899902315)
    ·
      refine ⟨160971185088509312849853473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107314123392339541899902315 160971185088509312849853473)
      ·
        refine ⟨120728388816381984637390105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160971185088509312849853473 120728388816381984637390105)
        ·
          refine ⟨90546291612286488478042579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120728388816381984637390105 90546291612286488478042579)
          ·
            refine ⟨135819437418429732717063869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90546291612286488478042579 135819437418429732717063869)
            ·
              refine ⟨50932289031911149768898951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135819437418429732717063869 50932289031911149768898951)
              ·
                refine ⟨76398433547866724653348427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50932289031911149768898951 76398433547866724653348427)
                ·
                  refine ⟨114597650321800086980022641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76398433547866724653348427 114597650321800086980022641)
                  ·
                    refine ⟨85948237741350065235016981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114597650321800086980022641 85948237741350065235016981)
                    ·
                      refine ⟨4028823644125784307891421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85948237741350065235016981 4028823644125784307891421)
                      ·
                        rfl

theorem cell23_7846106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_7846106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846106 prefixEnd_7846106 := by exact prefixLift 7846106
  have htrace : WordTrace (prefixWord ++ tailWord_7846106) baseStart_7846106 baseEnd_7846106 := by
    simpa [prefixWord, tailWord_7846106, baseEnd_7846106] using wordTrace_append hprefix tailTrace_7846106
  have hstable : (prefixWord ++ tailWord_7846106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846106).length < 2 ^ (prefixWord ++ tailWord_7846106).sum := by decide
  have hdescent : baseEnd_7846106 < baseStart_7846106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846120 : List Nat := [2, 1, 4, 1, 2, 3, 3, 1, 6]
def baseStart_7846120 : Nat := 118140960795 + 7846120 * 2 ^ 59
def prefixEnd_7846120 : Nat := 4983230072969 + 3 ^ 40 * 7846120 * 2
def baseEnd_7846120 : Nat := 447647870317216361457373

theorem tailTrace_7846120 : CollatzResearch.WordTrace tailWord_7846120 prefixEnd_7846120 447647870317216361457373 := by
  unfold tailWord_7846120
  simp only [CollatzResearch.WordTrace]
  refine ⟨143085753167427362728707907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190781004223236483638277209 143085753167427362728707907)
  ·
    refine ⟨214628629751141044093061861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143085753167427362728707907 214628629751141044093061861)
    ·
      refine ⟨40242868078338945767449099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214628629751141044093061861 40242868078338945767449099)
      ·
        refine ⟨60364302117508418651173649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40242868078338945767449099 60364302117508418651173649)
        ·
          refine ⟨45273226588131313988380237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60364302117508418651173649 45273226588131313988380237)
          ·
            refine ⟨16977459970549242745642589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45273226588131313988380237 16977459970549242745642589)
            ·
              refine ⟨6366547488955966029615971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16977459970549242745642589 6366547488955966029615971)
              ·
                refine ⟨9549821233433949044423957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6366547488955966029615971 9549821233433949044423957)
                ·
                  refine ⟨447647870317216361457373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9549821233433949044423957 447647870317216361457373)
                  ·
                    rfl

theorem cell23_7846120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 6].length) (baseStart_7846120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846120 prefixEnd_7846120 := by exact prefixLift 7846120
  have htrace : WordTrace (prefixWord ++ tailWord_7846120) baseStart_7846120 baseEnd_7846120 := by
    simpa [prefixWord, tailWord_7846120, baseEnd_7846120] using wordTrace_append hprefix tailTrace_7846120
  have hstable : (prefixWord ++ tailWord_7846120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846120).length < 2 ^ (prefixWord ++ tailWord_7846120).sum := by decide
  have hdescent : baseEnd_7846120 < baseStart_7846120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846123 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 3, 5, 2]
def baseStart_7846123 : Nat := 118140960795 + 7846123 * 2 ^ 59
def prefixEnd_7846123 : Nat := 4983230072969 + 3 ^ 40 * 7846123 * 2
def baseEnd_7846123 : Nat := 4028832373296910741378843

theorem tailTrace_7846123 : CollatzResearch.WordTrace tailWord_7846123 prefixEnd_7846123 4028832373296910741378843 := by
  unfold tailWord_7846123
  simp only [CollatzResearch.WordTrace]
  refine ⟨286171615753843856969775023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190781077169229237979850015 286171615753843856969775023)
  ·
    refine ⟨429257423630765785454662535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286171615753843856969775023 429257423630765785454662535)
    ·
      refine ⟨643886135446148678181993803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429257423630765785454662535 643886135446148678181993803)
      ·
        refine ⟨965829203169223017272990705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643886135446148678181993803 965829203169223017272990705)
        ·
          refine ⟨724371902376917262954743029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965829203169223017272990705 724371902376917262954743029)
          ·
            refine ⟨67909865847835993402007159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 724371902376917262954743029 67909865847835993402007159)
            ·
              refine ⟨101864798771753990103010739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67909865847835993402007159 101864798771753990103010739)
              ·
                refine ⟨152797198157630985154516109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101864798771753990103010739 152797198157630985154516109)
                ·
                  refine ⟨57298949309111619432943541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152797198157630985154516109 57298949309111619432943541)
                  ·
                    refine ⟨5371776497729214321838457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57298949309111619432943541 5371776497729214321838457)
                    ·
                      refine ⟨4028832373296910741378843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5371776497729214321838457 4028832373296910741378843)
                      ·
                        rfl

theorem cell23_7846123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 5, 2].length) (baseStart_7846123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846123 prefixEnd_7846123 := by exact prefixLift 7846123
  have htrace : WordTrace (prefixWord ++ tailWord_7846123) baseStart_7846123 baseEnd_7846123 := by
    simpa [prefixWord, tailWord_7846123, baseEnd_7846123] using wordTrace_append hprefix tailTrace_7846123
  have hstable : (prefixWord ++ tailWord_7846123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846123).length < 2 ^ (prefixWord ++ tailWord_7846123).sum := by decide
  have hdescent : baseEnd_7846123 < baseStart_7846123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846136 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_7846136 : Nat := 118140960795 + 7846136 * 2 ^ 59
def prefixEnd_7846136 : Nat := 4983230072969 + 3 ^ 40 * 7846136 * 2
def baseEnd_7846136 : Nat := 4028839048545419190516283

theorem tailTrace_7846136 : CollatzResearch.WordTrace tailWord_7846136 prefixEnd_7846136 4028839048545419190516283 := by
  unfold tailWord_7846136
  simp only [CollatzResearch.WordTrace]
  refine ⟨143086044951398380094999131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190781393268531173459998841 143086044951398380094999131)
  ·
    refine ⟨214629067427097570142498697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143086044951398380094999131 214629067427097570142498697)
    ·
      refine ⟨160971800570323177606874023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214629067427097570142498697 160971800570323177606874023)
      ·
        refine ⟨241457700855484766410311035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160971800570323177606874023 241457700855484766410311035)
        ·
          refine ⟨362186551283227149615466553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241457700855484766410311035 362186551283227149615466553)
          ·
            refine ⟨271639913462420362211599915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362186551283227149615466553 271639913462420362211599915)
            ·
              refine ⟨407459870193630543317399873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271639913462420362211599915 407459870193630543317399873)
              ·
                refine ⟨305594902645222907488049905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407459870193630543317399873 305594902645222907488049905)
                ·
                  refine ⟨229196176983917180616037429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305594902645222907488049905 229196176983917180616037429)
                  ·
                    refine ⟨21487141592242235682753509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 229196176983917180616037429 21487141592242235682753509)
                    ·
                      refine ⟨4028839048545419190516283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21487141592242235682753509 4028839048545419190516283)
                      ·
                        rfl

theorem cell23_7846136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_7846136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846136 prefixEnd_7846136 := by exact prefixLift 7846136
  have htrace : WordTrace (prefixWord ++ tailWord_7846136) baseStart_7846136 baseEnd_7846136 := by
    simpa [prefixWord, tailWord_7846136, baseEnd_7846136] using wordTrace_append hprefix tailTrace_7846136
  have hstable : (prefixWord ++ tailWord_7846136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846136).length < 2 ^ (prefixWord ++ tailWord_7846136).sum := by decide
  have hdescent : baseEnd_7846136 < baseStart_7846136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846140 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 1, 5, 2]
def baseStart_7846140 : Nat := 118140960795 + 7846140 * 2 ^ 59
def prefixEnd_7846140 : Nat := 4983230072969 + 3 ^ 40 * 7846140 * 2
def baseEnd_7846140 : Nat := 4028841102468037174866265

theorem tailTrace_7846140 : CollatzResearch.WordTrace tailWord_7846140 prefixEnd_7846140 4028841102468037174866265 := by
  unfold tailWord_7846140
  simp only [CollatzResearch.WordTrace]
  refine ⟨143086117897391134436571937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190781490529854845915429249 143086117897391134436571937)
  ·
    refine ⟨107314588423043350827428953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143086117897391134436571937 107314588423043350827428953)
    ·
      refine ⟨80485941317282513120571715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107314588423043350827428953 80485941317282513120571715)
      ·
        refine ⟨120728911975923769680857573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80485941317282513120571715 120728911975923769680857573)
        ·
          refine ⟨22636670995485706815160795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120728911975923769680857573 22636670995485706815160795)
          ·
            refine ⟨33955006493228560222741193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22636670995485706815160795 33955006493228560222741193)
            ·
              refine ⟨25466254869921420167055895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33955006493228560222741193 25466254869921420167055895)
              ·
                refine ⟨38199382304882130250583843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25466254869921420167055895 38199382304882130250583843)
                ·
                  refine ⟨57299073457323195375875765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38199382304882130250583843 57299073457323195375875765)
                  ·
                    refine ⟨5371788136624049566488353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57299073457323195375875765 5371788136624049566488353)
                    ·
                      refine ⟨4028841102468037174866265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5371788136624049566488353 4028841102468037174866265)
                      ·
                        rfl

theorem cell23_7846140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_7846140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846140 prefixEnd_7846140 := by exact prefixLift 7846140
  have htrace : WordTrace (prefixWord ++ tailWord_7846140) baseStart_7846140 baseEnd_7846140 := by
    simpa [prefixWord, tailWord_7846140, baseEnd_7846140] using wordTrace_append hprefix tailTrace_7846140
  have hstable : (prefixWord ++ tailWord_7846140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846140).length < 2 ^ (prefixWord ++ tailWord_7846140).sum := by decide
  have hdescent : baseEnd_7846140 < baseStart_7846140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846184 : List Nat := [2, 1, 5, 1, 4, 1, 1, 2, 1, 5]
def baseStart_7846184 : Nat := 118140960795 + 7846184 * 2 ^ 59
def prefixEnd_7846184 : Nat := 4983230072969 + 3 ^ 40 * 7846184 * 2
def baseEnd_7846184 : Nat := 1342954565205611667572021

theorem tailTrace_7846184 : CollatzResearch.WordTrace tailWord_7846184 prefixEnd_7846184 1342954565205611667572021 := by
  unfold tailWord_7846184
  simp only [CollatzResearch.WordTrace]
  refine ⟨143086920303311432193872803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190782560404415242925163737 143086920303311432193872803)
  ·
    refine ⟨214630380454967148290809205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143086920303311432193872803 214630380454967148290809205)
    ·
      refine ⟨20121598167653170152263363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214630380454967148290809205 20121598167653170152263363)
      ·
        refine ⟨30182397251479755228395045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20121598167653170152263363 30182397251479755228395045)
        ·
          refine ⟨5659199484652454105324071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30182397251479755228395045 5659199484652454105324071)
          ·
            refine ⟨8488799226978681157986107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5659199484652454105324071 8488799226978681157986107)
            ·
              refine ⟨12733198840468021736979161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8488799226978681157986107 12733198840468021736979161)
              ·
                refine ⟨9549899130351016302734371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12733198840468021736979161 9549899130351016302734371)
                ·
                  refine ⟨14324848695526524454101557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9549899130351016302734371 14324848695526524454101557)
                  ·
                    refine ⟨1342954565205611667572021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14324848695526524454101557 1342954565205611667572021)
                    ·
                      rfl

theorem cell23_7846184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_7846184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846184 prefixEnd_7846184 := by exact prefixLift 7846184
  have htrace : WordTrace (prefixWord ++ tailWord_7846184) baseStart_7846184 baseEnd_7846184 := by
    simpa [prefixWord, tailWord_7846184, baseEnd_7846184] using wordTrace_append hprefix tailTrace_7846184
  have hstable : (prefixWord ++ tailWord_7846184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846184).length < 2 ^ (prefixWord ++ tailWord_7846184).sum := by decide
  have hdescent : baseEnd_7846184 < baseStart_7846184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846204 : List Nat := [2, 2, 2, 2, 1, 2, 2, 5, 1, 2, 2]
def baseStart_7846204 : Nat := 118140960795 + 7846204 * 2 ^ 59
def prefixEnd_7846204 : Nat := 4983230072969 + 3 ^ 40 * 7846204 * 2
def baseEnd_7846204 : Nat := 4028873965229924924465971

theorem tailTrace_7846204 : CollatzResearch.WordTrace tailWord_7846204 prefixEnd_7846204 4028873965229924924465971 := by
  unfold tailWord_7846204
  simp only [CollatzResearch.WordTrace]
  refine ⟨143087285033275203901736833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190783046711033605202315777 143087285033275203901736833)
  ·
    refine ⟨107315463774956402926302625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143087285033275203901736833 107315463774956402926302625)
    ·
      refine ⟨80486597831217302194726969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107315463774956402926302625 80486597831217302194726969)
      ·
        refine ⟨60364948373412976646045227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80486597831217302194726969 60364948373412976646045227)
        ·
          refine ⟨90547422560119464969067841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60364948373412976646045227 90547422560119464969067841)
          ·
            refine ⟨67910566920089598726800881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90547422560119464969067841 67910566920089598726800881)
            ·
              refine ⟨50932925190067199045100661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67910566920089598726800881 50932925190067199045100661)
              ·
                refine ⟨4774961736568799910478187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50932925190067199045100661 4774961736568799910478187)
                ·
                  refine ⟨7162442604853199865717281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4774961736568799910478187 7162442604853199865717281)
                  ·
                    refine ⟨5371831953639899899287961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7162442604853199865717281 5371831953639899899287961)
                    ·
                      refine ⟨4028873965229924924465971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5371831953639899899287961 4028873965229924924465971)
                      ·
                        rfl

theorem cell23_7846204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_7846204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846204 prefixEnd_7846204 := by exact prefixLift 7846204
  have htrace : WordTrace (prefixWord ++ tailWord_7846204) baseStart_7846204 baseEnd_7846204 := by
    simpa [prefixWord, tailWord_7846204, baseEnd_7846204] using wordTrace_append hprefix tailTrace_7846204
  have hstable : (prefixWord ++ tailWord_7846204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846204).length < 2 ^ (prefixWord ++ tailWord_7846204).sum := by decide
  have hdescent : baseEnd_7846204 < baseStart_7846204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846207 : List Nat := [1, 1, 2, 2, 4, 1, 5, 1, 1, 2, 3]
def baseStart_7846207 : Nat := 118140960795 + 7846207 * 2 ^ 59
def prefixEnd_7846207 : Nat := 4983230072969 + 3 ^ 40 * 7846207 * 2
def baseEnd_7846207 : Nat := 4028875505671888412728457

theorem tailTrace_7846207 : CollatzResearch.WordTrace tailWord_7846207 prefixEnd_7846207 4028875505671888412728457 := by
  unfold tailWord_7846207
  simp only [CollatzResearch.WordTrace]
  refine ⟨286174679485539539315832875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190783119657026359543888583 286174679485539539315832875)
  ·
    refine ⟨429262019228309308973749313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286174679485539539315832875 429262019228309308973749313)
    ·
      refine ⟨321946514421231981730311985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429262019228309308973749313 321946514421231981730311985)
      ·
        refine ⟨241459885815923986297733989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321946514421231981730311985 241459885815923986297733989)
        ·
          refine ⟨45273728590485747430825123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241459885815923986297733989 45273728590485747430825123)
          ·
            refine ⟨67910592885728621146237685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45273728590485747430825123 67910592885728621146237685)
            ·
              refine ⟨6366618083037058232459783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67910592885728621146237685 6366618083037058232459783)
              ·
                refine ⟨9549927124555587348689675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6366618083037058232459783 9549927124555587348689675)
                ·
                  refine ⟨14324890686833381023034513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9549927124555587348689675 14324890686833381023034513)
                  ·
                    refine ⟨10743668015125035767275885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14324890686833381023034513 10743668015125035767275885)
                    ·
                      refine ⟨4028875505671888412728457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10743668015125035767275885 4028875505671888412728457)
                      ·
                        rfl

theorem cell23_7846207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 1, 2, 3].length) (baseStart_7846207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846207 prefixEnd_7846207 := by exact prefixLift 7846207
  have htrace : WordTrace (prefixWord ++ tailWord_7846207) baseStart_7846207 baseEnd_7846207 := by
    simpa [prefixWord, tailWord_7846207, baseEnd_7846207] using wordTrace_append hprefix tailTrace_7846207
  have hstable : (prefixWord ++ tailWord_7846207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846207).length < 2 ^ (prefixWord ++ tailWord_7846207).sum := by decide
  have hdescent : baseEnd_7846207 < baseStart_7846207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846243 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 4]
def baseStart_7846243 : Nat := 118140960795 + 7846243 * 2 ^ 59
def prefixEnd_7846243 : Nat := 4983230072969 + 3 ^ 40 * 7846243 * 2
def baseEnd_7846243 : Nat := 4028893990975450271878291

theorem tailTrace_7846243 : CollatzResearch.WordTrace tailWord_7846243 prefixEnd_7846243 4028893990975450271878291 := by
  unfold tailWord_7846243
  simp only [CollatzResearch.WordTrace]
  refine ⟨286175992513409117464143383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190783995008939411642762255 286175992513409117464143383)
  ·
    refine ⟨429263988770113676196215075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286175992513409117464143383 429263988770113676196215075)
    ·
      refine ⟨643895983155170514294322613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429263988770113676196215075 643895983155170514294322613)
      ·
        refine ⟨60365248420797235715092745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 643895983155170514294322613 60365248420797235715092745)
        ·
          refine ⟨45273936315597926786319559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60365248420797235715092745 45273936315597926786319559)
          ·
            refine ⟨67910904473396890179479339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45273936315597926786319559 67910904473396890179479339)
            ·
              refine ⟨101866356710095335269219009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67910904473396890179479339 101866356710095335269219009)
              ·
                refine ⟨76399767532571501451914257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101866356710095335269219009 76399767532571501451914257)
                ·
                  refine ⟨57299825649428626088935693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76399767532571501451914257 57299825649428626088935693)
                  ·
                    refine ⟨21487434618535734783350885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57299825649428626088935693 21487434618535734783350885)
                    ·
                      refine ⟨4028893990975450271878291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21487434618535734783350885 4028893990975450271878291)
                      ·
                        rfl

theorem cell23_7846243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_7846243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846243 prefixEnd_7846243 := by exact prefixLift 7846243
  have htrace : WordTrace (prefixWord ++ tailWord_7846243) baseStart_7846243 baseEnd_7846243 := by
    simpa [prefixWord, tailWord_7846243, baseEnd_7846243] using wordTrace_append hprefix tailTrace_7846243
  have hstable : (prefixWord ++ tailWord_7846243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846243).length < 2 ^ (prefixWord ++ tailWord_7846243).sum := by decide
  have hdescent : baseEnd_7846243 < baseStart_7846243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846247 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_7846247 : Nat := 118140960795 + 7846247 * 2 ^ 59
def prefixEnd_7846247 : Nat := 4983230072969 + 3 ^ 40 * 7846247 * 2
def baseEnd_7846247 : Nat := 4028896044898068256228273

theorem tailTrace_7846247 : CollatzResearch.WordTrace tailWord_7846247 prefixEnd_7846247 4028896044898068256228273 := by
  unfold tailWord_7846247
  simp only [CollatzResearch.WordTrace]
  refine ⟨286176138405394626147288995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190784092270263084098192663 286176138405394626147288995)
  ·
    refine ⟨429264207608091939220933493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286176138405394626147288995 429264207608091939220933493)
    ·
      refine ⟨40243519463258619301962515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 429264207608091939220933493 40243519463258619301962515)
      ·
        refine ⟨60365279194887928952943773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40243519463258619301962515 60365279194887928952943773)
        ·
          refine ⟨22636979698082973357353915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60365279194887928952943773 22636979698082973357353915)
          ·
            refine ⟨33955469547124460036030873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22636979698082973357353915 33955469547124460036030873)
            ·
              refine ⟨25466602160343345027023155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33955469547124460036030873 25466602160343345027023155)
              ·
                refine ⟨38199903240515017540534733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25466602160343345027023155 38199903240515017540534733)
                ·
                  refine ⟨14324963715193131577700525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38199903240515017540534733 14324963715193131577700525)
                  ·
                    refine ⟨5371861393197424341637697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14324963715193131577700525 5371861393197424341637697)
                    ·
                      refine ⟨4028896044898068256228273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5371861393197424341637697 4028896044898068256228273)
                      ·
                        rfl

theorem cell23_7846247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_7846247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846247 prefixEnd_7846247 := by exact prefixLift 7846247
  have htrace : WordTrace (prefixWord ++ tailWord_7846247) baseStart_7846247 baseEnd_7846247 := by
    simpa [prefixWord, tailWord_7846247, baseEnd_7846247] using wordTrace_append hprefix tailTrace_7846247
  have hstable : (prefixWord ++ tailWord_7846247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846247).length < 2 ^ (prefixWord ++ tailWord_7846247).sum := by decide
  have hdescent : baseEnd_7846247 < baseStart_7846247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846253 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_7846253 : Nat := 118140960795 + 7846253 * 2 ^ 59
def prefixEnd_7846253 : Nat := 4983230072969 + 3 ^ 40 * 7846253 * 2
def baseEnd_7846253 : Nat := 1342966375260665077584415

theorem tailTrace_7846253 : CollatzResearch.WordTrace tailWord_7846253 prefixEnd_7846253 1342966375260665077584415 := by
  unfold tailWord_7846253
  simp only [CollatzResearch.WordTrace]
  refine ⟨286176357243372889172007413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190784238162248592781338275 286176357243372889172007413)
  ·
    refine ⟨26829033491566208359875695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286176357243372889172007413 26829033491566208359875695)
    ·
      refine ⟨40243550237349312539813543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26829033491566208359875695 40243550237349312539813543)
      ·
        refine ⟨60365325356023968809720315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40243550237349312539813543 60365325356023968809720315)
        ·
          refine ⟨90547988034035953214580473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60365325356023968809720315 90547988034035953214580473)
          ·
            refine ⟨67910991025526964910935355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90547988034035953214580473 67910991025526964910935355)
            ·
              refine ⟨101866486538290447366403033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67910991025526964910935355 101866486538290447366403033)
              ·
                refine ⟨76399864903717835524802275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101866486538290447366403033 76399864903717835524802275)
                ·
                  refine ⟨114599797355576753287203413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76399864903717835524802275 114599797355576753287203413)
                  ·
                    refine ⟨1342966375260665077584415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114599797355576753287203413 1342966375260665077584415)
                    ·
                      rfl

theorem cell23_7846253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_7846253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846253 prefixEnd_7846253 := by exact prefixLift 7846253
  have htrace : WordTrace (prefixWord ++ tailWord_7846253) baseStart_7846253 baseEnd_7846253 := by
    simpa [prefixWord, tailWord_7846253, baseEnd_7846253] using wordTrace_append hprefix tailTrace_7846253
  have hstable : (prefixWord ++ tailWord_7846253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846253).length < 2 ^ (prefixWord ++ tailWord_7846253).sum := by decide
  have hdescent : baseEnd_7846253 < baseStart_7846253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846263 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 3]
def baseStart_7846263 : Nat := 118140960795 + 7846263 * 2 ^ 59
def prefixEnd_7846263 : Nat := 4983230072969 + 3 ^ 40 * 7846263 * 2
def baseEnd_7846263 : Nat := 4028904260588540193628199

theorem tailTrace_7846263 : CollatzResearch.WordTrace tailWord_7846263 prefixEnd_7846263 4028904260588540193628199 := by
  unfold tailWord_7846263
  simp only [CollatzResearch.WordTrace]
  refine ⟨286176721973336660879871443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190784481315557773919914295 286176721973336660879871443)
  ·
    refine ⟨429265082960004991319807165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286176721973336660879871443 429265082960004991319807165)
    ·
      refine ⟨160974406110001871744927687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429265082960004991319807165 160974406110001871744927687)
      ·
        refine ⟨241461609165002807617391531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160974406110001871744927687 241461609165002807617391531)
        ·
          refine ⟨362192413747504211426087297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241461609165002807617391531 362192413747504211426087297)
          ·
            refine ⟨271644310310628158569565473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362192413747504211426087297 271644310310628158569565473)
            ·
              refine ⟨203733232732971118927174105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271644310310628158569565473 203733232732971118927174105)
              ·
                refine ⟨152799924549728339195380579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203733232732971118927174105 152799924549728339195380579)
                ·
                  refine ⟨229199886824592508793070869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152799924549728339195380579 229199886824592508793070869)
                  ·
                    refine ⟨10743744694902773849675197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 229199886824592508793070869 10743744694902773849675197)
                    ·
                      refine ⟨4028904260588540193628199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10743744694902773849675197 4028904260588540193628199)
                      ·
                        rfl

theorem cell23_7846263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_7846263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846263 prefixEnd_7846263 := by exact prefixLift 7846263
  have htrace : WordTrace (prefixWord ++ tailWord_7846263) baseStart_7846263 baseEnd_7846263 := by
    simpa [prefixWord, tailWord_7846263, baseEnd_7846263] using wordTrace_append hprefix tailTrace_7846263
  have hstable : (prefixWord ++ tailWord_7846263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846263).length < 2 ^ (prefixWord ++ tailWord_7846263).sum := by decide
  have hdescent : baseEnd_7846263 < baseStart_7846263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846283 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 7]
def baseStart_7846283 : Nat := 118140960795 + 7846283 * 2 ^ 59
def prefixEnd_7846283 : Nat := 4983230072969 + 3 ^ 40 * 7846283 * 2
def baseEnd_7846283 : Nat := 447657170022403346153123

theorem tailTrace_7846283 : CollatzResearch.WordTrace tailWord_7846283 prefixEnd_7846283 447657170022403346153123 := by
  unfold tailWord_7846283
  simp only [CollatzResearch.WordTrace]
  refine ⟨286177451433264204295599503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190784967622176136197066335 286177451433264204295599503)
  ·
    refine ⟨429266177149896306443399255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286177451433264204295599503 429266177149896306443399255)
    ·
      refine ⟨643899265724844459665098883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429266177149896306443399255 643899265724844459665098883)
      ·
        refine ⟨965848898587266689497648325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643899265724844459665098883 965848898587266689497648325)
        ·
          refine ⟨181096668485112504280809061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 965848898587266689497648325 181096668485112504280809061)
          ·
            refine ⟨33955625340958594552651699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181096668485112504280809061 33955625340958594552651699)
            ·
              refine ⟨50933438011437891828977549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33955625340958594552651699 50933438011437891828977549)
              ·
                refine ⟨19100039254289209435866581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50933438011437891828977549 19100039254289209435866581)
                ·
                  refine ⟨447657170022403346153123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19100039254289209435866581 447657170022403346153123)
                  ·
                    rfl

theorem cell23_7846283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 7].length) (baseStart_7846283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846283 prefixEnd_7846283 := by exact prefixLift 7846283
  have htrace : WordTrace (prefixWord ++ tailWord_7846283) baseStart_7846283 baseEnd_7846283 := by
    simpa [prefixWord, tailWord_7846283, baseEnd_7846283] using wordTrace_append hprefix tailTrace_7846283
  have hstable : (prefixWord ++ tailWord_7846283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846283).length < 2 ^ (prefixWord ++ tailWord_7846283).sum := by decide
  have hdescent : baseEnd_7846283 < baseStart_7846283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846313 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 6, 5]
def baseStart_7846313 : Nat := 118140960795 + 7846313 * 2 ^ 59
def prefixEnd_7846313 : Nat := 4983230072969 + 3 ^ 40 * 7846313 * 2
def baseEnd_7846313 : Nat := 1342976644873754999334323

theorem tailTrace_7846313 : CollatzResearch.WordTrace tailWord_7846313 prefixEnd_7846313 1342976644873754999334323 := by
  unfold tailWord_7846313
  simp only [CollatzResearch.WordTrace]
  refine ⟨286178545623155519419191593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190785697082103679612794395 286178545623155519419191593)
  ·
    refine ⟨214633909217366639564393695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286178545623155519419191593 214633909217366639564393695)
    ·
      refine ⟨321950863826049959346590543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214633909217366639564393695 321950863826049959346590543)
      ·
        refine ⟨482926295739074939019885815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321950863826049959346590543 482926295739074939019885815)
        ·
          refine ⟨724389443608612408529828723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482926295739074939019885815 724389443608612408529828723)
          ·
            refine ⟨1086584165412918612794743085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724389443608612408529828723 1086584165412918612794743085)
            ·
              refine ⟨407469062029844479798028657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1086584165412918612794743085 407469062029844479798028657)
              ·
                refine ⟨305601796522383359848521493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407469062029844479798028657 305601796522383359848521493)
                ·
                  refine ⟨14325084211986719992899445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 305601796522383359848521493 14325084211986719992899445)
                  ·
                    refine ⟨1342976644873754999334323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14325084211986719992899445 1342976644873754999334323)
                    ·
                      rfl

theorem cell23_7846313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 5].length) (baseStart_7846313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846313 prefixEnd_7846313 := by exact prefixLift 7846313
  have htrace : WordTrace (prefixWord ++ tailWord_7846313) baseStart_7846313 baseEnd_7846313 := by
    simpa [prefixWord, tailWord_7846313, baseEnd_7846313] using wordTrace_append hprefix tailTrace_7846313
  have hstable : (prefixWord ++ tailWord_7846313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846313).length < 2 ^ (prefixWord ++ tailWord_7846313).sum := by decide
  have hdescent : baseEnd_7846313 < baseStart_7846313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846350 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_7846350 : Nat := 118140960795 + 7846350 * 2 ^ 59
def prefixEnd_7846350 : Nat := 4983230072969 + 3 ^ 40 * 7846350 * 2
def baseEnd_7846350 : Nat := 4028948933405481353240299

theorem tailTrace_7846350 : CollatzResearch.WordTrace tailWord_7846350 prefixEnd_7846350 4028948933405481353240299 := by
  unfold tailWord_7846350
  simp only [CollatzResearch.WordTrace]
  refine ⟨35772486890502684342286063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190786596749347649825525669 35772486890502684342286063)
  ·
    refine ⟨53658730335754026513429095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35772486890502684342286063 53658730335754026513429095)
    ·
      refine ⟨80488095503631039770143643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53658730335754026513429095 80488095503631039770143643)
      ·
        refine ⟨120732143255446559655215465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80488095503631039770143643 120732143255446559655215465)
        ·
          refine ⟨90549107441584919741411599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120732143255446559655215465 90549107441584919741411599)
          ·
            refine ⟨135823661162377379612117399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90549107441584919741411599 135823661162377379612117399)
            ·
              refine ⟨203735491743566069418176099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135823661162377379612117399 203735491743566069418176099)
              ·
                refine ⟨305603237615349104127264149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203735491743566069418176099 305603237615349104127264149)
                ·
                  refine ⟨14325151763219489255965507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 305603237615349104127264149 14325151763219489255965507)
                  ·
                    refine ⟨21487727644829233883948261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14325151763219489255965507 21487727644829233883948261)
                    ·
                      refine ⟨4028948933405481353240299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21487727644829233883948261 4028948933405481353240299)
                      ·
                        rfl

theorem cell23_7846350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_7846350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846350 prefixEnd_7846350 := by exact prefixLift 7846350
  have htrace : WordTrace (prefixWord ++ tailWord_7846350) baseStart_7846350 baseEnd_7846350 := by
    simpa [prefixWord, tailWord_7846350, baseEnd_7846350] using wordTrace_append hprefix tailTrace_7846350
  have hstable : (prefixWord ++ tailWord_7846350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846350).length < 2 ^ (prefixWord ++ tailWord_7846350).sum := by decide
  have hdescent : baseEnd_7846350 < baseStart_7846350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846353 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_7846353 : Nat := 118140960795 + 7846353 * 2 ^ 59
def prefixEnd_7846353 : Nat := 4983230072969 + 3 ^ 40 * 7846353 * 2
def baseEnd_7846353 : Nat := 4028950473847444841502785

theorem tailTrace_7846353 : CollatzResearch.WordTrace tailWord_7846353 prefixEnd_7846353 4028950473847444841502785 := by
  unfold tailWord_7846353
  simp only [CollatzResearch.WordTrace]
  refine ⟨286180004543010606250647713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190786669695340404167098475 286180004543010606250647713)
  ·
    refine ⟨214635003407257954687985785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286180004543010606250647713 214635003407257954687985785)
    ·
      refine ⟨160976252555443466015989339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214635003407257954687985785 160976252555443466015989339)
      ·
        refine ⟨241464378833165199023984009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160976252555443466015989339 241464378833165199023984009)
        ·
          refine ⟨181098284124873899267988007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241464378833165199023984009 181098284124873899267988007)
          ·
            refine ⟨271647426187310848901982011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181098284124873899267988007 271647426187310848901982011)
            ·
              refine ⟨407471139280966273352973017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271647426187310848901982011 407471139280966273352973017)
              ·
                refine ⟨305603354460724705014729763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407471139280966273352973017 305603354460724705014729763)
                ·
                  refine ⟨458405031691087057522094645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305603354460724705014729763 458405031691087057522094645)
                  ·
                    refine ⟨42975471721039411642696373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 458405031691087057522094645 42975471721039411642696373)
                    ·
                      refine ⟨4028950473847444841502785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42975471721039411642696373 4028950473847444841502785)
                      ·
                        rfl

theorem cell23_7846353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_7846353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846353 prefixEnd_7846353 := by exact prefixLift 7846353
  have htrace : WordTrace (prefixWord ++ tailWord_7846353) baseStart_7846353 baseEnd_7846353 := by
    simpa [prefixWord, tailWord_7846353, baseEnd_7846353] using wordTrace_append hprefix tailTrace_7846353
  have hstable : (prefixWord ++ tailWord_7846353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846353).length < 2 ^ (prefixWord ++ tailWord_7846353).sum := by decide
  have hdescent : baseEnd_7846353 < baseStart_7846353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846360 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 5, 4]
def baseStart_7846360 : Nat := 118140960795 + 7846360 * 2 ^ 59
def prefixEnd_7846360 : Nat := 4983230072969 + 3 ^ 40 * 7846360 * 2
def baseEnd_7846360 : Nat := 1342984689404008771371751

theorem tailTrace_7846360 : CollatzResearch.WordTrace tailWord_7846360 prefixEnd_7846360 1342984689404008771371751 := by
  unfold tailWord_7846360
  simp only [CollatzResearch.WordTrace]
  refine ⟨143090129926992623223076267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190786839902656830964101689 143090129926992623223076267)
  ·
    refine ⟨214635194890488934834614401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143090129926992623223076267 214635194890488934834614401)
    ·
      refine ⟨160976396167866701125960801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214635194890488934834614401 160976396167866701125960801)
      ·
        refine ⟨120732297125900025844470601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160976396167866701125960801 120732297125900025844470601)
        ·
          refine ⟨90549222844425019383352951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120732297125900025844470601 90549222844425019383352951)
          ·
            refine ⟨135823834266637529075029427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90549222844425019383352951 135823834266637529075029427)
            ·
              refine ⟨203735751399956293612544141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135823834266637529075029427 203735751399956293612544141)
              ·
                refine ⟨76400906774983610104704053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203735751399956293612544141 76400906774983610104704053)
                ·
                  refine ⟨7162585010154713447316005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76400906774983610104704053 7162585010154713447316005)
                  ·
                    refine ⟨1342984689404008771371751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7162585010154713447316005 1342984689404008771371751)
                    ·
                      rfl

theorem cell23_7846360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_7846360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846360 prefixEnd_7846360 := by exact prefixLift 7846360
  have htrace : WordTrace (prefixWord ++ tailWord_7846360) baseStart_7846360 baseEnd_7846360 := by
    simpa [prefixWord, tailWord_7846360, baseEnd_7846360] using wordTrace_append hprefix tailTrace_7846360
  have hstable : (prefixWord ++ tailWord_7846360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846360).length < 2 ^ (prefixWord ++ tailWord_7846360).sum := by decide
  have hdescent : baseEnd_7846360 < baseStart_7846360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846367 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 4]
def baseStart_7846367 : Nat := 118140960795 + 7846367 * 2 ^ 59
def prefixEnd_7846367 : Nat := 4983230072969 + 3 ^ 40 * 7846367 * 2
def baseEnd_7846367 : Nat := 4028957662576607786727721

theorem tailTrace_7846367 : CollatzResearch.WordTrace tailWord_7846367 prefixEnd_7846367 4028957662576607786727721 := by
  unfold tailWord_7846367
  simp only [CollatzResearch.WordTrace]
  refine ⟨286180515164959886641657355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190787010109973257761104903 286180515164959886641657355)
  ·
    refine ⟨429270772747439829962486033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286180515164959886641657355 429270772747439829962486033)
    ·
      refine ⟨321953079560579872471864525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429270772747439829962486033 321953079560579872471864525)
      ·
        refine ⟨120732404835217452176949197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321953079560579872471864525 120732404835217452176949197)
        ·
          refine ⟨45274651813206544566355949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120732404835217452176949197 45274651813206544566355949)
          ·
            refine ⟨16977994429952454212383481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45274651813206544566355949 16977994429952454212383481)
            ·
              refine ⟨12733495822464340659287611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16977994429952454212383481 12733495822464340659287611)
              ·
                refine ⟨19100243733696510988931417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12733495822464340659287611 19100243733696510988931417)
                ·
                  refine ⟨14325182800272383241698563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19100243733696510988931417 14325182800272383241698563)
                  ·
                    refine ⟨21487774200408574862547845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14325182800272383241698563 21487774200408574862547845)
                    ·
                      refine ⟨4028957662576607786727721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21487774200408574862547845 4028957662576607786727721)
                      ·
                        rfl

theorem cell23_7846367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_7846367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846367 prefixEnd_7846367 := by exact prefixLift 7846367
  have htrace : WordTrace (prefixWord ++ tailWord_7846367) baseStart_7846367 baseEnd_7846367 := by
    simpa [prefixWord, tailWord_7846367, baseEnd_7846367] using wordTrace_append hprefix tailTrace_7846367
  have hstable : (prefixWord ++ tailWord_7846367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846367).length < 2 ^ (prefixWord ++ tailWord_7846367).sum := by decide
  have hdescent : baseEnd_7846367 < baseStart_7846367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846450 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_7846450 : Nat := 118140960795 + 7846450 * 2 ^ 59
def prefixEnd_7846450 : Nat := 4983230072969 + 3 ^ 40 * 7846450 * 2
def baseEnd_7846450 : Nat := 1343000093823643653996613

theorem tailTrace_7846450 : CollatzResearch.WordTrace tailWord_7846450 prefixEnd_7846450 1343000093823643653996613 := by
  unfold tailWord_7846450
  simp only [CollatzResearch.WordTrace]
  refine ⟨71545885605914797954232201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190789028282439461211285869 71545885605914797954232201)
  ·
    refine ⟨53659414204436098465674151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71545885605914797954232201 53659414204436098465674151)
    ·
      refine ⟨80489121306654147698511227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53659414204436098465674151 80489121306654147698511227)
      ·
        refine ⟨120733681959981221547766841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80489121306654147698511227 120733681959981221547766841)
        ·
          refine ⟨90550261469985916160825131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120733681959981221547766841 90550261469985916160825131)
          ·
            refine ⟨135825392204978874241237697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90550261469985916160825131 135825392204978874241237697)
            ·
              refine ⟨101869044153734155680928273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135825392204978874241237697 101869044153734155680928273)
              ·
                refine ⟨76401783115300616760696205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101869044153734155680928273 76401783115300616760696205)
                ·
                  refine ⟨28650668668237731285261077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76401783115300616760696205 28650668668237731285261077)
                  ·
                    refine ⟨1343000093823643653996613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28650668668237731285261077 1343000093823643653996613)
                    ·
                      rfl

theorem cell23_7846450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_7846450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846450 prefixEnd_7846450 := by exact prefixLift 7846450
  have htrace : WordTrace (prefixWord ++ tailWord_7846450) baseStart_7846450 baseEnd_7846450 := by
    simpa [prefixWord, tailWord_7846450, baseEnd_7846450] using wordTrace_append hprefix tailTrace_7846450
  have hstable : (prefixWord ++ tailWord_7846450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846450).length < 2 ^ (prefixWord ++ tailWord_7846450).sum := by decide
  have hdescent : baseEnd_7846450 < baseStart_7846450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846467 : List Nat := [1, 1, 1, 3, 1, 2, 1, 7, 2, 4]
def baseStart_7846467 : Nat := 118140960795 + 7846467 * 2 ^ 59
def prefixEnd_7846467 : Nat := 4983230072969 + 3 ^ 40 * 7846467 * 2
def baseEnd_7846467 : Nat := 1343003003547352465159087

theorem tailTrace_7846467 : CollatzResearch.WordTrace tailWord_7846467 prefixEnd_7846467 1343003003547352465159087 := by
  unfold tailWord_7846467
  simp only [CollatzResearch.WordTrace]
  refine ⟨286184162464597603720297655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190789441643065069146865103 286184162464597603720297655)
  ·
    refine ⟨429276243696896405580446483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286184162464597603720297655 429276243696896405580446483)
    ·
      refine ⟨643914365545344608370669725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429276243696896405580446483 643914365545344608370669725)
      ·
        refine ⟨241467887079504228139001147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 643914365545344608370669725 241467887079504228139001147)
        ·
          refine ⟨362201830619256342208501721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241467887079504228139001147 362201830619256342208501721)
          ·
            refine ⟨271651372964442256656376291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362201830619256342208501721 271651372964442256656376291)
            ·
              refine ⟨407477059446663384984564437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271651372964442256656376291 407477059446663384984564437)
              ·
                refine ⟨9550243580781173085575729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 407477059446663384984564437 9550243580781173085575729)
                ·
                  refine ⟨7162682685585879814181797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9550243580781173085575729 7162682685585879814181797)
                  ·
                    refine ⟨1343003003547352465159087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7162682685585879814181797 1343003003547352465159087)
                    ·
                      rfl

theorem cell23_7846467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 4].length) (baseStart_7846467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846467 prefixEnd_7846467 := by exact prefixLift 7846467
  have htrace : WordTrace (prefixWord ++ tailWord_7846467) baseStart_7846467 baseEnd_7846467 := by
    simpa [prefixWord, tailWord_7846467, baseEnd_7846467] using wordTrace_append hprefix tailTrace_7846467
  have hstable : (prefixWord ++ tailWord_7846467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846467).length < 2 ^ (prefixWord ++ tailWord_7846467).sum := by decide
  have hdescent : baseEnd_7846467 < baseStart_7846467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846474 : List Nat := [3, 1, 2, 1, 1, 5, 2, 2, 1, 1, 4]
def baseStart_7846474 : Nat := 118140960795 + 7846474 * 2 ^ 59
def prefixEnd_7846474 : Nat := 4983230072969 + 3 ^ 40 * 7846474 * 2
def baseEnd_7846474 : Nat := 4029012605006638868089729

theorem tailTrace_7846474 : CollatzResearch.WordTrace tailWord_7846474 prefixEnd_7846474 4029012605006638868089729 := by
  unfold tailWord_7846474
  simp only [CollatzResearch.WordTrace]
  refine ⟨71546104443893060978950619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190789611850381495943868317 71546104443893060978950619)
  ·
    refine ⟨107319156665839591468425929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71546104443893060978950619 107319156665839591468425929)
    ·
      refine ⟨80489367499379693601319447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107319156665839591468425929 80489367499379693601319447)
      ·
        refine ⟨120734051249069540401979171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80489367499379693601319447 120734051249069540401979171)
        ·
          refine ⟨181101076873604310602968757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120734051249069540401979171 181101076873604310602968757)
          ·
            refine ⟨16978225956900404119028321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181101076873604310602968757 16978225956900404119028321)
            ·
              refine ⟨12733669467675303089271241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16978225956900404119028321 12733669467675303089271241)
              ·
                refine ⟨9550252100756477316953431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12733669467675303089271241 9550252100756477316953431)
                ·
                  refine ⟨14325378151134715975430147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9550252100756477316953431 14325378151134715975430147)
                  ·
                    refine ⟨21488067226702073963145221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14325378151134715975430147 21488067226702073963145221)
                    ·
                      refine ⟨4029012605006638868089729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21488067226702073963145221 4029012605006638868089729)
                      ·
                        rfl

theorem cell23_7846474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_7846474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846474 prefixEnd_7846474 := by exact prefixLift 7846474
  have htrace : WordTrace (prefixWord ++ tailWord_7846474) baseStart_7846474 baseEnd_7846474 := by
    simpa [prefixWord, tailWord_7846474, baseEnd_7846474] using wordTrace_append hprefix tailTrace_7846474
  have hstable : (prefixWord ++ tailWord_7846474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846474).length < 2 ^ (prefixWord ++ tailWord_7846474).sum := by decide
  have hdescent : baseEnd_7846474 < baseStart_7846474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846520 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_7846520 : Nat := 118140960795 + 7846520 * 2 ^ 59
def prefixEnd_7846520 : Nat := 4983230072969 + 3 ^ 40 * 7846520 * 2
def baseEnd_7846520 : Nat := 4029036225116745688114517

theorem tailTrace_7846520 : CollatzResearch.WordTrace tailWord_7846520 prefixEnd_7846520 4029036225116745688114517 := by
  unfold tailWord_7846520
  simp only [CollatzResearch.WordTrace]
  refine ⟨143093047766702796885988507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190790730355603729181318009 143093047766702796885988507)
  ·
    refine ⟨214639571650054195328982761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143093047766702796885988507 214639571650054195328982761)
    ·
      refine ⟨160979678737540646496737071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214639571650054195328982761 160979678737540646496737071)
      ·
        refine ⟨241469518106310969745105607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160979678737540646496737071 241469518106310969745105607)
        ·
          refine ⟨362204277159466454617658411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241469518106310969745105607 362204277159466454617658411)
          ·
            refine ⟨543306415739199681926487617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362204277159466454617658411 543306415739199681926487617)
            ·
              refine ⟨407479811804399761444865713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543306415739199681926487617 407479811804399761444865713)
              ·
                refine ⟨305609858853299821083649285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407479811804399761444865713 305609858853299821083649285)
                ·
                  refine ⟨57301848534993716453184241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305609858853299821083649285 57301848534993716453184241)
                  ·
                    refine ⟨42976386401245287339888181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57301848534993716453184241 42976386401245287339888181)
                    ·
                      refine ⟨4029036225116745688114517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42976386401245287339888181 4029036225116745688114517)
                      ·
                        rfl

theorem cell23_7846520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_7846520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846520 prefixEnd_7846520 := by exact prefixLift 7846520
  have htrace : WordTrace (prefixWord ++ tailWord_7846520) baseStart_7846520 baseEnd_7846520 := by
    simpa [prefixWord, tailWord_7846520, baseEnd_7846520] using wordTrace_append hprefix tailTrace_7846520
  have hstable : (prefixWord ++ tailWord_7846520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846520).length < 2 ^ (prefixWord ++ tailWord_7846520).sum := by decide
  have hdescent : baseEnd_7846520 < baseStart_7846520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846540 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 3, 8]
def baseStart_7846540 : Nat := 118140960795 + 7846540 * 2 ^ 59
def prefixEnd_7846540 : Nat := 4983230072969 + 3 ^ 40 * 7846540 * 2
def baseEnd_7846540 : Nat := 1343015498243278536621475

theorem tailTrace_7846540 : CollatzResearch.WordTrace tailWord_7846540 prefixEnd_7846540 1343015498243278536621475 := by
  unfold tailWord_7846540
  simp only [CollatzResearch.WordTrace]
  refine ⟨143093412496666568593852537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190791216662222091458470049 143093412496666568593852537)
  ·
    refine ⟨107320059372499926445389403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143093412496666568593852537 107320059372499926445389403)
    ·
      refine ⟨160980089058749889668084105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107320059372499926445389403 160980089058749889668084105)
      ·
        refine ⟨120735066794062417251063079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160980089058749889668084105 120735066794062417251063079)
        ·
          refine ⟨181102600191093625876594619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120735066794062417251063079 181102600191093625876594619)
          ·
            refine ⟨271653900286640438814891929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181102600191093625876594619 271653900286640438814891929)
            ·
              refine ⟨203740425214980329111168947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271653900286640438814891929 203740425214980329111168947)
              ·
                refine ⟨305610637822470493666753421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203740425214980329111168947 305610637822470493666753421)
                ·
                  refine ⟨114603989183426435125032533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305610637822470493666753421 114603989183426435125032533)
                  ·
                    refine ⟨1343015498243278536621475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114603989183426435125032533 1343015498243278536621475)
                    ·
                      rfl

theorem cell23_7846540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_7846540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846540 prefixEnd_7846540 := by exact prefixLift 7846540
  have htrace : WordTrace (prefixWord ++ tailWord_7846540) baseStart_7846540 baseEnd_7846540 := by
    simpa [prefixWord, tailWord_7846540, baseEnd_7846540] using wordTrace_append hprefix tailTrace_7846540
  have hstable : (prefixWord ++ tailWord_7846540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846540).length < 2 ^ (prefixWord ++ tailWord_7846540).sum := by decide
  have hdescent : baseEnd_7846540 < baseStart_7846540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846558 : List Nat := [4, 3, 1, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_7846558 : Nat := 118140960795 + 7846558 * 2 ^ 59
def prefixEnd_7846558 : Nat := 4983230072969 + 3 ^ 40 * 7846558 * 2
def baseEnd_7846558 : Nat := 4029055737381616539439343

theorem tailTrace_7846558 : CollatzResearch.WordTrace tailWord_7846558 prefixEnd_7846558 4029055737381616539439343 := by
  unfold tailWord_7846558
  simp only [CollatzResearch.WordTrace]
  refine ⟨35773435188408490782732541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190791654338178617507906885 35773435188408490782732541)
  ·
    refine ⟨13415038195653184043524703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35773435188408490782732541 13415038195653184043524703)
    ·
      refine ⟨20122557293479776065287055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13415038195653184043524703 20122557293479776065287055)
      ·
        refine ⟨30183835940219664097930583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20122557293479776065287055 30183835940219664097930583)
        ·
          refine ⟨45275753910329496146895875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30183835940219664097930583 45275753910329496146895875)
          ·
            refine ⟨67913630865494244220343813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45275753910329496146895875 67913630865494244220343813)
            ·
              refine ⟨12733805787280170791314465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67913630865494244220343813 12733805787280170791314465)
              ·
                refine ⟨9550354340460128093485849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12733805787280170791314465 9550354340460128093485849)
                ·
                  refine ⟨7162765755345096070114387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9550354340460128093485849 7162765755345096070114387)
                  ·
                    refine ⟨10744148633017644105171581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7162765755345096070114387 10744148633017644105171581)
                    ·
                      refine ⟨4029055737381616539439343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10744148633017644105171581 4029055737381616539439343)
                      ·
                        rfl

theorem cell23_7846558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_7846558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846558 prefixEnd_7846558 := by exact prefixLift 7846558
  have htrace : WordTrace (prefixWord ++ tailWord_7846558) baseStart_7846558 baseEnd_7846558 := by
    simpa [prefixWord, tailWord_7846558, baseEnd_7846558] using wordTrace_append hprefix tailTrace_7846558
  have hstable : (prefixWord ++ tailWord_7846558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846558).length < 2 ^ (prefixWord ++ tailWord_7846558).sum := by decide
  have hdescent : baseEnd_7846558 < baseStart_7846558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846564 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 3, 4, 2]
def baseStart_7846564 : Nat := 118140960795 + 7846564 * 2 ^ 59
def prefixEnd_7846564 : Nat := 4983230072969 + 3 ^ 40 * 7846564 * 2
def baseEnd_7846564 : Nat := 4029058818265543515964315

theorem tailTrace_7846564 : CollatzResearch.WordTrace tailWord_7846564 prefixEnd_7846564 4029058818265543515964315 := by
  unfold tailWord_7846564
  simp only [CollatzResearch.WordTrace]
  refine ⟨143093850172623094643289373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190791800230164126191052497 143093850172623094643289373)
  ·
    refine ⟨53660193814733660491233515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143093850172623094643289373 53660193814733660491233515)
    ·
      refine ⟨80490290722100490736850273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53660193814733660491233515 80490290722100490736850273)
      ·
        refine ⟨60367718041575368052637705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80490290722100490736850273 60367718041575368052637705)
        ·
          refine ⟨45275788531181526039478279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60367718041575368052637705 45275788531181526039478279)
          ·
            refine ⟨67913682796772289059217419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45275788531181526039478279 67913682796772289059217419)
            ·
              refine ⟨101870524195158433588826129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67913682796772289059217419 101870524195158433588826129)
              ·
                refine ⟨76402893146368825191619597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101870524195158433588826129 76402893146368825191619597)
                ·
                  refine ⟨28651084929888309446857349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76402893146368825191619597 28651084929888309446857349)
                  ·
                    refine ⟨5372078424354058021285753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28651084929888309446857349 5372078424354058021285753)
                    ·
                      refine ⟨4029058818265543515964315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5372078424354058021285753 4029058818265543515964315)
                      ·
                        rfl

theorem cell23_7846564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_7846564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846564 prefixEnd_7846564 := by exact prefixLift 7846564
  have htrace : WordTrace (prefixWord ++ tailWord_7846564) baseStart_7846564 baseEnd_7846564 := by
    simpa [prefixWord, tailWord_7846564, baseEnd_7846564] using wordTrace_append hprefix tailTrace_7846564
  have hstable : (prefixWord ++ tailWord_7846564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846564).length < 2 ^ (prefixWord ++ tailWord_7846564).sum := by decide
  have hdescent : baseEnd_7846564 < baseStart_7846564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846574 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_7846574 : Nat := 118140960795 + 7846574 * 2 ^ 59
def prefixEnd_7846574 : Nat := 4983230072969 + 3 ^ 40 * 7846574 * 2
def baseEnd_7846574 : Nat := 1343021317690696158946423

theorem tailTrace_7846574 : CollatzResearch.WordTrace tailWord_7846574 prefixEnd_7846574 1343021317690696158946423 := by
  unfold tailWord_7846574
  simp only [CollatzResearch.WordTrace]
  refine ⟨35773508134401245124305347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190792043383473307329628517 35773508134401245124305347)
  ·
    refine ⟨53660262201601867686458021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35773508134401245124305347 53660262201601867686458021)
    ·
      refine ⟨10061299162800350191210879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53660262201601867686458021 10061299162800350191210879)
      ·
        refine ⟨15091948744200525286816319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10061299162800350191210879 15091948744200525286816319)
        ·
          refine ⟨22637923116300787930224479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15091948744200525286816319 22637923116300787930224479)
          ·
            refine ⟨33956884674451181895336719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22637923116300787930224479 33956884674451181895336719)
            ·
              refine ⟨50935327011676772843005079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33956884674451181895336719 50935327011676772843005079)
              ·
                refine ⟨76402990517515159264507619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50935327011676772843005079 76402990517515159264507619)
                ·
                  refine ⟨114604485776272738896761429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76402990517515159264507619 114604485776272738896761429)
                  ·
                    refine ⟨1343021317690696158946423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114604485776272738896761429 1343021317690696158946423)
                    ·
                      rfl

theorem cell23_7846574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_7846574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846574 prefixEnd_7846574 := by exact prefixLift 7846574
  have htrace : WordTrace (prefixWord ++ tailWord_7846574) baseStart_7846574 baseEnd_7846574 := by
    simpa [prefixWord, tailWord_7846574, baseEnd_7846574] using wordTrace_append hprefix tailTrace_7846574
  have hstable : (prefixWord ++ tailWord_7846574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846574).length < 2 ^ (prefixWord ++ tailWord_7846574).sum := by decide
  have hdescent : baseEnd_7846574 < baseStart_7846574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846581 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_7846581 : Nat := 118140960795 + 7846581 * 2 ^ 59
def prefixEnd_7846581 : Nat := 4983230072969 + 3 ^ 40 * 7846581 * 2
def baseEnd_7846581 : Nat := 4029067547436669949451737

theorem tailTrace_7846581 : CollatzResearch.WordTrace tailWord_7846581 prefixEnd_7846581 4029067547436669949451737 := by
  unfold tailWord_7846581
  simp only [CollatzResearch.WordTrace]
  refine ⟨286188320386184601189947597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190792213590789734126631731 286188320386184601189947597)
  ·
    refine ⟨107320620144819225446230349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286188320386184601189947597 107320620144819225446230349)
    ·
      refine ⟨40245232554307209542336381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107320620144819225446230349 40245232554307209542336381)
      ·
        refine ⟨15091962207865203578376143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40245232554307209542336381 15091962207865203578376143)
        ·
          refine ⟨22637943311797805367564215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15091962207865203578376143 22637943311797805367564215)
          ·
            refine ⟨33956914967696708051346323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22637943311797805367564215 33956914967696708051346323)
            ·
              refine ⟨50935372451545062077019485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33956914967696708051346323 50935372451545062077019485)
              ·
                refine ⟨19100764669329398278882307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50935372451545062077019485 19100764669329398278882307)
                ·
                  refine ⟨28651147003994097418323461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19100764669329398278882307 28651147003994097418323461)
                  ·
                    refine ⟨5372090063248893265935649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28651147003994097418323461 5372090063248893265935649)
                    ·
                      refine ⟨4029067547436669949451737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5372090063248893265935649 4029067547436669949451737)
                      ·
                        rfl

theorem cell23_7846581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_7846581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846581 prefixEnd_7846581 := by exact prefixLift 7846581
  have htrace : WordTrace (prefixWord ++ tailWord_7846581) baseStart_7846581 baseEnd_7846581 := by
    simpa [prefixWord, tailWord_7846581, baseEnd_7846581] using wordTrace_append hprefix tailTrace_7846581
  have hstable : (prefixWord ++ tailWord_7846581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846581).length < 2 ^ (prefixWord ++ tailWord_7846581).sum := by decide
  have hdescent : baseEnd_7846581 < baseStart_7846581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846597 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 6, 3, 3]
def baseStart_7846597 : Nat := 118140960795 + 7846597 * 2 ^ 59
def prefixEnd_7846597 : Nat := 4983230072969 + 3 ^ 40 * 7846597 * 2
def baseEnd_7846597 : Nat := 4029075763127141886851663

theorem tailTrace_7846597 : CollatzResearch.WordTrace tailWord_7846597 prefixEnd_7846597 4029075763127141886851663 := by
  unfold tailWord_7846597
  simp only [CollatzResearch.WordTrace]
  refine ⟨286188903954126635922530045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190792602636084423948353363 286188903954126635922530045)
  ·
    refine ⟨107320838982797488470948767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286188903954126635922530045 107320838982797488470948767)
    ·
      refine ⟨160981258474196232706423151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107320838982797488470948767 160981258474196232706423151)
      ·
        refine ⟨241471887711294349059634727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160981258474196232706423151 241471887711294349059634727)
        ·
          refine ⟨362207831566941523589452091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241471887711294349059634727 362207831566941523589452091)
          ·
            refine ⟨543311747350412285384178137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362207831566941523589452091 543311747350412285384178137)
            ·
              refine ⟨407483810512809214038133603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543311747350412285384178137 407483810512809214038133603)
              ·
                refine ⟨611225715769213821057200405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407483810512809214038133603 611225715769213821057200405)
                ·
                  refine ⟨28651205426681897862056269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 611225715769213821057200405 28651205426681897862056269)
                  ·
                    refine ⟨10744202035005711698271101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28651205426681897862056269 10744202035005711698271101)
                    ·
                      refine ⟨4029075763127141886851663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10744202035005711698271101 4029075763127141886851663)
                      ·
                        rfl

theorem cell23_7846597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_7846597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846597 prefixEnd_7846597 := by exact prefixLift 7846597
  have htrace : WordTrace (prefixWord ++ tailWord_7846597) baseStart_7846597 baseEnd_7846597 := by
    simpa [prefixWord, tailWord_7846597, baseEnd_7846597] using wordTrace_append hprefix tailTrace_7846597
  have hstable : (prefixWord ++ tailWord_7846597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846597).length < 2 ^ (prefixWord ++ tailWord_7846597).sum := by decide
  have hdescent : baseEnd_7846597 < baseStart_7846597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846617 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 4, 5]
def baseStart_7846617 : Nat := 118140960795 + 7846617 * 2 ^ 59
def prefixEnd_7846617 : Nat := 4983230072969 + 3 ^ 40 * 7846617 * 2
def baseEnd_7846617 : Nat := 1343028677580077269533857

theorem tailTrace_7846617 : CollatzResearch.WordTrace tailWord_7846617 prefixEnd_7846617 1343028677580077269533857 := by
  unfold tailWord_7846617
  simp only [CollatzResearch.WordTrace]
  refine ⟨286189633414054179338258105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190793088942702786225505403 286189633414054179338258105)
  ·
    refine ⟨214642225060540634503693579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286189633414054179338258105 214642225060540634503693579)
    ·
      refine ⟨321963337590810951755540369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214642225060540634503693579 321963337590810951755540369)
      ·
        refine ⟨241472503193108213816655277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321963337590810951755540369 241472503193108213816655277)
        ·
          refine ⟨90552188697415580181245729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241472503193108213816655277 90552188697415580181245729)
          ·
            refine ⟨67914141523061685135934297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90552188697415580181245729 67914141523061685135934297)
            ·
              refine ⟨50935606142296263851950723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67914141523061685135934297 50935606142296263851950723)
              ·
                refine ⟨76403409213444395777926085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50935606142296263851950723 76403409213444395777926085)
                ·
                  refine ⟨14325639227520824208361141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76403409213444395777926085 14325639227520824208361141)
                  ·
                    refine ⟨1343028677580077269533857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14325639227520824208361141 1343028677580077269533857)
                    ·
                      rfl

theorem cell23_7846617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 5].length) (baseStart_7846617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846617 prefixEnd_7846617 := by exact prefixLift 7846617
  have htrace : WordTrace (prefixWord ++ tailWord_7846617) baseStart_7846617 baseEnd_7846617 := by
    simpa [prefixWord, tailWord_7846617, baseEnd_7846617] using wordTrace_append hprefix tailTrace_7846617
  have hstable : (prefixWord ++ tailWord_7846617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846617).length < 2 ^ (prefixWord ++ tailWord_7846617).sum := by decide
  have hdescent : baseEnd_7846617 < baseStart_7846617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846657 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_7846657 : Nat := 118140960795 + 7846657 * 2 ^ 59
def prefixEnd_7846657 : Nat := 4983230072969 + 3 ^ 40 * 7846657 * 2
def baseEnd_7846657 : Nat := 4029106571966411652101387

theorem tailTrace_7846657 : CollatzResearch.WordTrace tailWord_7846657 prefixEnd_7846657 4029106571966411652101387 := by
  unfold tailWord_7846657
  simp only [CollatzResearch.WordTrace]
  refine ⟨286191092333909266169714225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190794061555939510779809483 286191092333909266169714225)
  ·
    refine ⟨214643319250431949627285669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286191092333909266169714225 214643319250431949627285669)
    ·
      refine ⟨40245622359455990555116063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214643319250431949627285669 40245622359455990555116063)
      ·
        refine ⟨60368433539183985832674095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40245622359455990555116063 60368433539183985832674095)
        ·
          refine ⟨90552650308775978749011143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60368433539183985832674095 90552650308775978749011143)
          ·
            refine ⟨135828975463163968123516715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90552650308775978749011143 135828975463163968123516715)
            ·
              refine ⟨203743463194745952185275073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135828975463163968123516715 203743463194745952185275073)
              ·
                refine ⟨152807597396059464138956305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203743463194745952185275073 152807597396059464138956305)
                ·
                  refine ⟨114605698047044598104217229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152807597396059464138956305 114605698047044598104217229)
                  ·
                    refine ⟨42977136767641724289081461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114605698047044598104217229 42977136767641724289081461)
                    ·
                      refine ⟨4029106571966411652101387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42977136767641724289081461 4029106571966411652101387)
                      ·
                        rfl

theorem cell23_7846657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_7846657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846657 prefixEnd_7846657 := by exact prefixLift 7846657
  have htrace : WordTrace (prefixWord ++ tailWord_7846657) baseStart_7846657 baseEnd_7846657 := by
    simpa [prefixWord, tailWord_7846657, baseEnd_7846657] using wordTrace_append hprefix tailTrace_7846657
  have hstable : (prefixWord ++ tailWord_7846657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846657).length < 2 ^ (prefixWord ++ tailWord_7846657).sum := by decide
  have hdescent : baseEnd_7846657 < baseStart_7846657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846677 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 8]
def baseStart_7846677 : Nat := 118140960795 + 7846677 * 2 ^ 59
def prefixEnd_7846677 : Nat := 4983230072969 + 3 ^ 40 * 7846677 * 2
def baseEnd_7846677 : Nat := 447679649064389063761255

theorem tailTrace_7846677 : CollatzResearch.WordTrace tailWord_7846677 prefixEnd_7846677 447679649064389063761255 := by
  unfold tailWord_7846677
  simp only [CollatzResearch.WordTrace]
  refine ⟨286191821793836809585442285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190794547862557873056961523 286191821793836809585442285)
  ·
    refine ⟨107321933172688803594540857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286191821793836809585442285 107321933172688803594540857)
    ·
      refine ⟨80491449879516602695905643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107321933172688803594540857 80491449879516602695905643)
      ·
        refine ⟨120737174819274904043858465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80491449879516602695905643 120737174819274904043858465)
        ·
          refine ⟨90552881114456178032893849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120737174819274904043858465 90552881114456178032893849)
          ·
            refine ⟨67914660835842133524670387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90552881114456178032893849 67914660835842133524670387)
            ·
              refine ⟨101871991253763200287005581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67914660835842133524670387 101871991253763200287005581)
              ·
                refine ⟨38201996720161200107627093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101871991253763200287005581 38201996720161200107627093)
                ·
                  refine ⟨447679649064389063761255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38201996720161200107627093 447679649064389063761255)
                  ·
                    rfl

theorem cell23_7846677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_7846677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846677 prefixEnd_7846677 := by exact prefixLift 7846677
  have htrace : WordTrace (prefixWord ++ tailWord_7846677) baseStart_7846677 baseEnd_7846677 := by
    simpa [prefixWord, tailWord_7846677, baseEnd_7846677] using wordTrace_append hprefix tailTrace_7846677
  have hstable : (prefixWord ++ tailWord_7846677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846677).length < 2 ^ (prefixWord ++ tailWord_7846677).sum := by decide
  have hdescent : baseEnd_7846677 < baseStart_7846677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846767 : List Nat := [1, 1, 2, 1, 3, 1, 1, 13]
def baseStart_7846767 : Nat := 118140960795 + 7846767 * 2 ^ 59
def prefixEnd_7846767 : Nat := 4983230072969 + 3 ^ 40 * 7846767 * 2
def baseEnd_7846767 : Nat := 149228261290311341545403

theorem tailTrace_7846767 : CollatzResearch.WordTrace tailWord_7846767 prefixEnd_7846767 149228261290311341545403 := by
  unfold tailWord_7846767
  simp only [CollatzResearch.WordTrace]
  refine ⟨286195104363510754956218555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190796736242340503304145703 286195104363510754956218555)
  ·
    refine ⟨429292656545266132434327833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286195104363510754956218555 429292656545266132434327833)
    ·
      refine ⟨321969492408949599325745875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429292656545266132434327833 321969492408949599325745875)
      ·
        refine ⟨482954238613424398988618813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321969492408949599325745875 482954238613424398988618813)
        ·
          refine ⟨181107839480034149620732055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482954238613424398988618813 181107839480034149620732055)
          ·
            refine ⟨271661759220051224431098083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181107839480034149620732055 271661759220051224431098083)
            ·
              refine ⟨407492638830076836646647125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271661759220051224431098083 407492638830076836646647125)
              ·
                refine ⟨149228261290311341545403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 407492638830076836646647125 149228261290311341545403)
                ·
                  rfl

theorem cell23_7846767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 13].length) (baseStart_7846767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846767 prefixEnd_7846767 := by exact prefixLift 7846767
  have htrace : WordTrace (prefixWord ++ tailWord_7846767) baseStart_7846767 baseEnd_7846767 := by
    simpa [prefixWord, tailWord_7846767, baseEnd_7846767] using wordTrace_append hprefix tailTrace_7846767
  have hstable : (prefixWord ++ tailWord_7846767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846767).length < 2 ^ (prefixWord ++ tailWord_7846767).sum := by decide
  have hdescent : baseEnd_7846767 < baseStart_7846767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846795 : List Nat := [1, 1, 1, 1, 4, 2, 4, 4, 1, 2, 2]
def baseStart_7846795 : Nat := 118140960795 + 7846795 * 2 ^ 59
def prefixEnd_7846795 : Nat := 4983230072969 + 3 ^ 40 * 7846795 * 2
def baseEnd_7846795 : Nat := 4029177432296732112175753

theorem tailTrace_7846795 : CollatzResearch.WordTrace tailWord_7846795 prefixEnd_7846795 4029177432296732112175753 := by
  unfold tailWord_7846795
  simp only [CollatzResearch.WordTrace]
  refine ⟨286196125607409315738237839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190797417071606210492158559 286196125607409315738237839)
  ·
    refine ⟨429294188411113973607356759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286196125607409315738237839 429294188411113973607356759)
    ·
      refine ⟨643941282616670960411035139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429294188411113973607356759 643941282616670960411035139)
      ·
        refine ⟨965911923925006440616552709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643941282616670960411035139 965911923925006440616552709)
        ·
          refine ⟨181108485735938707615603633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 965911923925006440616552709 181108485735938707615603633)
          ·
            refine ⟨135831364301954030711702725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181108485735938707615603633 135831364301954030711702725)
            ·
              refine ⟨25468380806616380758444261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135831364301954030711702725 25468380806616380758444261)
              ·
                refine ⟨4775321401240571392208299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25468380806616380758444261 4775321401240571392208299)
                ·
                  refine ⟨7162982101860857088312449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775321401240571392208299 7162982101860857088312449)
                  ·
                    refine ⟨5372236576395642816234337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7162982101860857088312449 5372236576395642816234337)
                    ·
                      refine ⟨4029177432296732112175753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5372236576395642816234337 4029177432296732112175753)
                      ·
                        rfl

theorem cell23_7846795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 1, 2, 2].length) (baseStart_7846795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846795 prefixEnd_7846795 := by exact prefixLift 7846795
  have htrace : WordTrace (prefixWord ++ tailWord_7846795) baseStart_7846795 baseEnd_7846795 := by
    simpa [prefixWord, tailWord_7846795, baseEnd_7846795] using wordTrace_append hprefix tailTrace_7846795
  have hstable : (prefixWord ++ tailWord_7846795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846795).length < 2 ^ (prefixWord ++ tailWord_7846795).sum := by decide
  have hdescent : baseEnd_7846795 < baseStart_7846795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846818 : List Nat := [3, 3, 1, 2, 2, 3, 2, 7]
def baseStart_7846818 : Nat := 118140960795 + 7846818 * 2 ^ 59
def prefixEnd_7846818 : Nat := 4983230072969 + 3 ^ 40 * 7846818 * 2
def baseEnd_7846818 : Nat := 149229231198214278599561

theorem tailTrace_7846818 : CollatzResearch.WordTrace tailWord_7846818 prefixEnd_7846818 149229231198214278599561 := by
  unfold tailWord_7846818
  simp only [CollatzResearch.WordTrace]
  refine ⟨71549241121581497666581277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190797976324217327110883405 71549241121581497666581277)
  ·
    refine ⟨26830965420593061624967979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71549241121581497666581277 26830965420593061624967979)
    ·
      refine ⟨40246448130889592437451969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26830965420593061624967979 40246448130889592437451969)
      ·
        refine ⟨30184836098167194328088977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40246448130889592437451969 30184836098167194328088977)
        ·
          refine ⟨22638627073625395746066733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30184836098167194328088977 22638627073625395746066733)
          ·
            refine ⟨8489485152609523404775025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22638627073625395746066733 8489485152609523404775025)
            ·
              refine ⟨6367113864457142553581269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8489485152609523404775025 6367113864457142553581269)
              ·
                refine ⟨149229231198214278599561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6367113864457142553581269 149229231198214278599561)
                ·
                  rfl

theorem cell23_7846818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 7].length) (baseStart_7846818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846818 prefixEnd_7846818 := by exact prefixLift 7846818
  have htrace : WordTrace (prefixWord ++ tailWord_7846818) baseStart_7846818 baseEnd_7846818 := by
    simpa [prefixWord, tailWord_7846818, baseEnd_7846818] using wordTrace_append hprefix tailTrace_7846818
  have hstable : (prefixWord ++ tailWord_7846818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846818).length < 2 ^ (prefixWord ++ tailWord_7846818).sum := by decide
  have hdescent : baseEnd_7846818 < baseStart_7846818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846834 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_7846834 : Nat := 118140960795 + 7846834 * 2 ^ 59
def prefixEnd_7846834 : Nat := 4983230072969 + 3 ^ 40 * 7846834 * 2
def baseEnd_7846834 : Nat := 4029197458042257459588073

theorem tailTrace_7846834 : CollatzResearch.WordTrace tailWord_7846834 prefixEnd_7846834 4029197458042257459588073 := by
  unfold tailWord_7846834
  simp only [CollatzResearch.WordTrace]
  refine ⟨71549387013567006349726889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190798365369512016932605037 71549387013567006349726889)
  ·
    refine ⟨53662040260175254762295167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71549387013567006349726889 53662040260175254762295167)
    ·
      refine ⟨80493060390262882143442751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53662040260175254762295167 80493060390262882143442751)
      ·
        refine ⟨120739590585394323215164127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80493060390262882143442751 120739590585394323215164127)
        ·
          refine ⟨181109385878091484822746191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120739590585394323215164127 181109385878091484822746191)
          ·
            refine ⟨271664078817137227234119287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181109385878091484822746191 271664078817137227234119287)
            ·
              refine ⟨407496118225705840851178931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271664078817137227234119287 407496118225705840851178931)
              ·
                refine ⟨611244177338558761276768397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407496118225705840851178931 611244177338558761276768397)
                ·
                  refine ⟨229216566501959535478788149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611244177338558761276768397 229216566501959535478788149)
                  ·
                    refine ⟨21489053109558706451136389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 229216566501959535478788149 21489053109558706451136389)
                    ·
                      refine ⟨4029197458042257459588073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21489053109558706451136389 4029197458042257459588073)
                      ·
                        rfl

theorem cell23_7846834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_7846834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846834 prefixEnd_7846834 := by exact prefixLift 7846834
  have htrace : WordTrace (prefixWord ++ tailWord_7846834) baseStart_7846834 baseEnd_7846834 := by
    simpa [prefixWord, tailWord_7846834, baseEnd_7846834] using wordTrace_append hprefix tailTrace_7846834
  have hstable : (prefixWord ++ tailWord_7846834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846834).length < 2 ^ (prefixWord ++ tailWord_7846834).sum := by decide
  have hdescent : baseEnd_7846834 < baseStart_7846834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846851 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 3, 4, 2]
def baseStart_7846851 : Nat := 118140960795 + 7846851 * 2 ^ 59
def prefixEnd_7846851 : Nat := 4983230072969 + 3 ^ 40 * 7846851 * 2
def baseEnd_7846851 : Nat := 4029206187213383893075495

theorem tailTrace_7846851 : CollatzResearch.WordTrace tailWord_7846851 prefixEnd_7846851 4029206187213383893075495 := by
  unfold tailWord_7846851
  simp only [CollatzResearch.WordTrace]
  refine ⟨286198168095206437302276407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190798778730137624868184271 286198168095206437302276407)
  ·
    refine ⟨429297252142809655953414611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286198168095206437302276407 429297252142809655953414611)
    ·
      refine ⟨643945878214214483930121917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429297252142809655953414611 643945878214214483930121917)
      ·
        refine ⟨241479704330330431473795719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 643945878214214483930121917 241479704330330431473795719)
        ·
          refine ⟨362219556495495647210693579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241479704330330431473795719 362219556495495647210693579)
          ·
            refine ⟨543329334743243470816040369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362219556495495647210693579 543329334743243470816040369)
            ·
              refine ⟨407497001057432603112030277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543329334743243470816040369 407497001057432603112030277)
              ·
                refine ⟨76405687698268613083505677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407497001057432603112030277 76405687698268613083505677)
                ·
                  refine ⟨28652132886850729906314629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76405687698268613083505677 28652132886850729906314629)
                  ·
                    refine ⟨5372274916284511857433993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28652132886850729906314629 5372274916284511857433993)
                    ·
                      refine ⟨4029206187213383893075495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5372274916284511857433993 4029206187213383893075495)
                      ·
                        rfl

theorem cell23_7846851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 4, 2].length) (baseStart_7846851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846851 prefixEnd_7846851 := by exact prefixLift 7846851
  have htrace : WordTrace (prefixWord ++ tailWord_7846851) baseStart_7846851 baseEnd_7846851 := by
    simpa [prefixWord, tailWord_7846851, baseEnd_7846851] using wordTrace_append hprefix tailTrace_7846851
  have hstable : (prefixWord ++ tailWord_7846851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846851).length < 2 ^ (prefixWord ++ tailWord_7846851).sum := by decide
  have hdescent : baseEnd_7846851 < baseStart_7846851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846862 : List Nat := [4, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3]
def baseStart_7846862 : Nat := 118140960795 + 7846862 * 2 ^ 59
def prefixEnd_7846862 : Nat := 4983230072969 + 3 ^ 40 * 7846862 * 2
def baseEnd_7846862 : Nat := 4029211835500583350037945

theorem tailTrace_7846862 : CollatzResearch.WordTrace tailWord_7846862 prefixEnd_7846862 4029211835500583350037945 := by
  unfold tailWord_7846862
  simp only [CollatzResearch.WordTrace]
  refine ⟨35774821162270823272615855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190799046198777724120617893 35774821162270823272615855)
  ·
    refine ⟨53662231743406234908923783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35774821162270823272615855 53662231743406234908923783)
    ·
      refine ⟨80493347615109352363385675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53662231743406234908923783 80493347615109352363385675)
      ·
        refine ⟨120740021422664028545078513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80493347615109352363385675 120740021422664028545078513)
        ·
          refine ⟨90555016066998021408808885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120740021422664028545078513 90555016066998021408808885)
          ·
            refine ⟨8489532756281064507075833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90555016066998021408808885 8489532756281064507075833)
            ·
              refine ⟨6367149567210798380306875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8489532756281064507075833 6367149567210798380306875)
              ·
                refine ⟨9550724350816197570460313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6367149567210798380306875 9550724350816197570460313)
                ·
                  refine ⟨7163043263112148177845235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9550724350816197570460313 7163043263112148177845235)
                  ·
                    refine ⟨10744564894668222266767853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7163043263112148177845235 10744564894668222266767853)
                    ·
                      refine ⟨4029211835500583350037945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10744564894668222266767853 4029211835500583350037945)
                      ·
                        rfl

theorem cell23_7846862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_7846862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846862 prefixEnd_7846862 := by exact prefixLift 7846862
  have htrace : WordTrace (prefixWord ++ tailWord_7846862) baseStart_7846862 baseEnd_7846862 := by
    simpa [prefixWord, tailWord_7846862, baseEnd_7846862] using wordTrace_append hprefix tailTrace_7846862
  have hstable : (prefixWord ++ tailWord_7846862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846862).length < 2 ^ (prefixWord ++ tailWord_7846862).sum := by decide
  have hdescent : baseEnd_7846862 < baseStart_7846862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846864 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 4]
def baseStart_7846864 : Nat := 118140960795 + 7846864 * 2 ^ 59
def prefixEnd_7846864 : Nat := 4983230072969 + 3 ^ 40 * 7846864 * 2
def baseEnd_7846864 : Nat := 4029212862461892342212935

theorem tailTrace_7846864 : CollatzResearch.WordTrace tailWord_7846864 prefixEnd_7846864 4029212862461892342212935 := by
  unfold tailWord_7846864
  simp only [CollatzResearch.WordTrace]
  refine ⟨143099321122079670261249823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190799094829439560348333097 143099321122079670261249823)
  ·
    refine ⟨214648981683119505391874735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143099321122079670261249823 214648981683119505391874735)
    ·
      refine ⟨321973472524679258087812103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214648981683119505391874735 321973472524679258087812103)
      ·
        refine ⟨482960208787018887131718155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321973472524679258087812103 482960208787018887131718155)
        ·
          refine ⟨724440313180528330697577233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482960208787018887131718155 724440313180528330697577233)
          ·
            refine ⟨543330234885396248023182925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724440313180528330697577233 543330234885396248023182925)
            ·
              refine ⟨203748838082023593008693597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 543330234885396248023182925 203748838082023593008693597)
              ·
                refine ⟨76405814280758847378260099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203748838082023593008693597 76405814280758847378260099)
                ·
                  refine ⟨114608721421138271067390149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76405814280758847378260099 114608721421138271067390149)
                  ·
                    refine ⟨21489135266463425825135653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114608721421138271067390149 21489135266463425825135653)
                    ·
                      refine ⟨4029212862461892342212935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21489135266463425825135653 4029212862461892342212935)
                      ·
                        rfl

theorem cell23_7846864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_7846864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846864 prefixEnd_7846864 := by exact prefixLift 7846864
  have htrace : WordTrace (prefixWord ++ tailWord_7846864) baseStart_7846864 baseEnd_7846864 := by
    simpa [prefixWord, tailWord_7846864, baseEnd_7846864] using wordTrace_append hprefix tailTrace_7846864
  have hstable : (prefixWord ++ tailWord_7846864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846864).length < 2 ^ (prefixWord ++ tailWord_7846864).sum := by decide
  have hdescent : baseEnd_7846864 < baseStart_7846864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846884 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_7846884 : Nat := 118140960795 + 7846884 * 2 ^ 59
def prefixEnd_7846884 : Nat := 4983230072969 + 3 ^ 40 * 7846884 * 2
def baseEnd_7846884 : Nat := 4029223132074982263962843

theorem tailTrace_7846884 : CollatzResearch.WordTrace tailWord_7846884 prefixEnd_7846884 4029223132074982263962843 := by
  unfold tailWord_7846884
  simp only [CollatzResearch.WordTrace]
  refine ⟨143099685852043441969113853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190799581136057922625485137 143099685852043441969113853)
  ·
    refine ⟨53662382194516290738417695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143099685852043441969113853 53662382194516290738417695)
    ·
      refine ⟨80493573291774436107626543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53662382194516290738417695 80493573291774436107626543)
      ·
        refine ⟨120740359937661654161439815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80493573291774436107626543 120740359937661654161439815)
        ·
          refine ⟨181110539906492481242159723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120740359937661654161439815 181110539906492481242159723)
          ·
            refine ⟨271665809859738721863239585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181110539906492481242159723 271665809859738721863239585)
            ·
              refine ⟨203749357394804041397429689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271665809859738721863239585 203749357394804041397429689)
              ·
                refine ⟨152812018046103031048072267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203749357394804041397429689 152812018046103031048072267)
                ·
                  refine ⟨229218027069154546572108401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152812018046103031048072267 229218027069154546572108401)
                  ·
                    refine ⟨171913520301865909929081301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 229218027069154546572108401 171913520301865909929081301)
                    ·
                      refine ⟨4029223132074982263962843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171913520301865909929081301 4029223132074982263962843)
                      ·
                        rfl

theorem cell23_7846884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_7846884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846884 prefixEnd_7846884 := by exact prefixLift 7846884
  have htrace : WordTrace (prefixWord ++ tailWord_7846884) baseStart_7846884 baseEnd_7846884 := by
    simpa [prefixWord, tailWord_7846884, baseEnd_7846884] using wordTrace_append hprefix tailTrace_7846884
  have hstable : (prefixWord ++ tailWord_7846884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846884).length < 2 ^ (prefixWord ++ tailWord_7846884).sum := by decide
  have hdescent : baseEnd_7846884 < baseStart_7846884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846902 : List Nat := [5, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_7846902 : Nat := 118140960795 + 7846902 * 2 ^ 59
def prefixEnd_7846902 : Nat := 4983230072969 + 3 ^ 40 * 7846902 * 2
def baseEnd_7846902 : Nat := 4029232374726763193537761

theorem tailTrace_7846902 : CollatzResearch.WordTrace tailWord_7846902 prefixEnd_7846902 4029232374726763193537761 := by
  unfold tailWord_7846902
  simp only [CollatzResearch.WordTrace]
  refine ⟨17887501763626354563273935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190800018812014448674921973 17887501763626354563273935)
  ·
    refine ⟨26831252645439531844910903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17887501763626354563273935 26831252645439531844910903)
    ·
      refine ⟨40246878968159297767366355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26831252645439531844910903 40246878968159297767366355)
      ·
        refine ⟨60370318452238946651049533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40246878968159297767366355 60370318452238946651049533)
        ·
          refine ⟨22638869419589604994143575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60370318452238946651049533 22638869419589604994143575)
          ·
            refine ⟨33958304129384407491215363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22638869419589604994143575 33958304129384407491215363)
            ·
              refine ⟨50937456194076611236823045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33958304129384407491215363 50937456194076611236823045)
              ·
                refine ⟨9550773036389364606904321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50937456194076611236823045 9550773036389364606904321)
                ·
                  refine ⟨7163079777292023455178241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9550773036389364606904321 7163079777292023455178241)
                  ·
                    refine ⟨5372309832969017591383681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7163079777292023455178241 5372309832969017591383681)
                    ·
                      refine ⟨4029232374726763193537761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5372309832969017591383681 4029232374726763193537761)
                      ·
                        rfl

theorem cell23_7846902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_7846902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846902 prefixEnd_7846902 := by exact prefixLift 7846902
  have htrace : WordTrace (prefixWord ++ tailWord_7846902) baseStart_7846902 baseEnd_7846902 := by
    simpa [prefixWord, tailWord_7846902, baseEnd_7846902] using wordTrace_append hprefix tailTrace_7846902
  have hstable : (prefixWord ++ tailWord_7846902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846902).length < 2 ^ (prefixWord ++ tailWord_7846902).sum := by decide
  have hdescent : baseEnd_7846902 < baseStart_7846902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846904 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 3, 7]
def baseStart_7846904 : Nat := 118140960795 + 7846904 * 2 ^ 59
def prefixEnd_7846904 : Nat := 4983230072969 + 3 ^ 40 * 7846904 * 2
def baseEnd_7846904 : Nat := 1343077800562690728570917

theorem tailTrace_7846904 : CollatzResearch.WordTrace tailWord_7846904 prefixEnd_7846904 1343077800562690728570917 := by
  unfold tailWord_7846904
  simp only [CollatzResearch.WordTrace]
  refine ⟨143100050582007213676977883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190800067442676284902637177 143100050582007213676977883)
  ·
    refine ⟨214650075873010820515466825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143100050582007213676977883 214650075873010820515466825)
    ·
      refine ⟨160987556904758115386600119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214650075873010820515466825 160987556904758115386600119)
      ·
        refine ⟨241481335357137173079900179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160987556904758115386600119 241481335357137173079900179)
        ·
          refine ⟨362222003035705759619850269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241481335357137173079900179 362222003035705759619850269)
          ·
            refine ⟨135833251138389659857443851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362222003035705759619850269 135833251138389659857443851)
            ·
              refine ⟨203749876707584489786165777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135833251138389659857443851 203749876707584489786165777)
              ·
                refine ⟨152812407530688367339624333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203749876707584489786165777 152812407530688367339624333)
                ·
                  refine ⟨57304652824008137752359125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152812407530688367339624333 57304652824008137752359125)
                  ·
                    refine ⟨1343077800562690728570917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57304652824008137752359125 1343077800562690728570917)
                    ·
                      rfl

theorem cell23_7846904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_7846904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846904 prefixEnd_7846904 := by exact prefixLift 7846904
  have htrace : WordTrace (prefixWord ++ tailWord_7846904) baseStart_7846904 baseEnd_7846904 := by
    simpa [prefixWord, tailWord_7846904, baseEnd_7846904] using wordTrace_append hprefix tailTrace_7846904
  have hstable : (prefixWord ++ tailWord_7846904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846904).length < 2 ^ (prefixWord ++ tailWord_7846904).sum := by decide
  have hdescent : baseEnd_7846904 < baseStart_7846904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846908 : List Nat := [2, 2, 2, 1, 2, 4, 1, 4, 5]
def baseStart_7846908 : Nat := 118140960795 + 7846908 * 2 ^ 59
def prefixEnd_7846908 : Nat := 4983230072969 + 3 ^ 40 * 7846908 * 2
def baseEnd_7846908 : Nat := 447692828401187796673637

theorem tailTrace_7846908 : CollatzResearch.WordTrace tailWord_7846908 prefixEnd_7846908 447692828401187796673637 := by
  unfold tailWord_7846908
  simp only [CollatzResearch.WordTrace]
  refine ⟨143100123527999968018550689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190800164703999957358067585 143100123527999968018550689)
  ·
    refine ⟨107325092645999976013913017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143100123527999968018550689 107325092645999976013913017)
    ·
      refine ⟨80493819484499982010434763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107325092645999976013913017 80493819484499982010434763)
      ·
        refine ⟨120740729226749973015652145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80493819484499982010434763 120740729226749973015652145)
        ·
          refine ⟨90555546920062479761739109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120740729226749973015652145 90555546920062479761739109)
          ·
            refine ⟨16979165047511714955326083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90555546920062479761739109 16979165047511714955326083)
            ·
              refine ⟨25468747571267572432989125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16979165047511714955326083 25468747571267572432989125)
              ·
                refine ⟨4775390169612669831185461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25468747571267572432989125 4775390169612669831185461)
                ·
                  refine ⟨447692828401187796673637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4775390169612669831185461 447692828401187796673637)
                  ·
                    rfl

theorem cell23_7846908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 5].length) (baseStart_7846908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846908 prefixEnd_7846908 := by exact prefixLift 7846908
  have htrace : WordTrace (prefixWord ++ tailWord_7846908) baseStart_7846908 baseEnd_7846908 := by
    simpa [prefixWord, tailWord_7846908, baseEnd_7846908] using wordTrace_append hprefix tailTrace_7846908
  have hstable : (prefixWord ++ tailWord_7846908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846908).length < 2 ^ (prefixWord ++ tailWord_7846908).sum := by decide
  have hdescent : baseEnd_7846908 < baseStart_7846908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846958 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_7846958 : Nat := 118140960795 + 7846958 * 2 ^ 59
def prefixEnd_7846958 : Nat := 4983230072969 + 3 ^ 40 * 7846958 * 2
def baseEnd_7846958 : Nat := 4029261129643414974437503

theorem tailTrace_7846958 : CollatzResearch.WordTrace tailWord_7846958 prefixEnd_7846958 4029261129643414974437503 := by
  unfold tailWord_7846958
  simp only [CollatzResearch.WordTrace]
  refine ⟨35775258838227349322052691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190801380470545863050947685 35775258838227349322052691)
  ·
    refine ⟨53662888257341023983079037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35775258838227349322052691 53662888257341023983079037)
    ·
      refine ⟨20123583096502883993654639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53662888257341023983079037 20123583096502883993654639)
      ·
        refine ⟨30185374644754325990481959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20123583096502883993654639 30185374644754325990481959)
        ·
          refine ⟨45278061967131488985722939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30185374644754325990481959 45278061967131488985722939)
          ·
            refine ⟨67917092950697233478584409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45278061967131488985722939 67917092950697233478584409)
            ·
              refine ⟨50937819713022925108938307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67917092950697233478584409 50937819713022925108938307)
              ·
                refine ⟨76406729569534387663407461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50937819713022925108938307 76406729569534387663407461)
                ·
                  refine ⟨14326261794287697686888899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76406729569534387663407461 14326261794287697686888899)
                  ·
                    refine ⟨21489392691431546530333349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14326261794287697686888899 21489392691431546530333349)
                    ·
                      refine ⟨4029261129643414974437503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21489392691431546530333349 4029261129643414974437503)
                      ·
                        rfl

theorem cell23_7846958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_7846958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846958 prefixEnd_7846958 := by exact prefixLift 7846958
  have htrace : WordTrace (prefixWord ++ tailWord_7846958) baseStart_7846958 baseEnd_7846958 := by
    simpa [prefixWord, tailWord_7846958, baseEnd_7846958] using wordTrace_append hprefix tailTrace_7846958
  have hstable : (prefixWord ++ tailWord_7846958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846958).length < 2 ^ (prefixWord ++ tailWord_7846958).sum := by decide
  have hdescent : baseEnd_7846958 < baseStart_7846958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846968 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 3, 4]
def baseStart_7846968 : Nat := 118140960795 + 7846968 * 2 ^ 59
def prefixEnd_7846968 : Nat := 4983230072969 + 3 ^ 40 * 7846968 * 2
def baseEnd_7846968 : Nat := 1343088754816653311770819

theorem tailTrace_7846968 : CollatzResearch.WordTrace tailWord_7846968 prefixEnd_7846968 1343088754816653311770819 := by
  unfold tailWord_7846968
  simp only [CollatzResearch.WordTrace]
  refine ⟨143101217717891283142142779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190801623623855044189523705 143101217717891283142142779)
  ·
    refine ⟨214651826576836924713214169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143101217717891283142142779 214651826576836924713214169)
    ·
      refine ⟨160988869932627693534910627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214651826576836924713214169 160988869932627693534910627)
      ·
        refine ⟨241483304898941540302365941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160988869932627693534910627 241483304898941540302365941)
        ·
          refine ⟨22639059834275769403346807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241483304898941540302365941 22639059834275769403346807)
          ·
            refine ⟨33958589751413654105020211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22639059834275769403346807 33958589751413654105020211)
            ·
              refine ⟨50937884627120481157530317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33958589751413654105020211 50937884627120481157530317)
              ·
                refine ⟨19101706735170180434073869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50937884627120481157530317 19101706735170180434073869)
                ·
                  refine ⟨7163140025688817662777701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19101706735170180434073869 7163140025688817662777701)
                  ·
                    refine ⟨1343088754816653311770819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7163140025688817662777701 1343088754816653311770819)
                    ·
                      rfl

theorem cell23_7846968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_7846968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846968 prefixEnd_7846968 := by exact prefixLift 7846968
  have htrace : WordTrace (prefixWord ++ tailWord_7846968) baseStart_7846968 baseEnd_7846968 := by
    simpa [prefixWord, tailWord_7846968, baseEnd_7846968] using wordTrace_append hprefix tailTrace_7846968
  have hstable : (prefixWord ++ tailWord_7846968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846968).length < 2 ^ (prefixWord ++ tailWord_7846968).sum := by decide
  have hdescent : baseEnd_7846968 < baseStart_7846968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7846981 : List Nat := [1, 3, 1, 1, 1, 3, 2, 5, 6]
def baseStart_7846981 : Nat := 118140960795 + 7846981 * 2 ^ 59
def prefixEnd_7846981 : Nat := 4983230072969 + 3 ^ 40 * 7846981 * 2
def baseEnd_7846981 : Nat := 447696993299829820494433

theorem tailTrace_7846981 : CollatzResearch.WordTrace tailWord_7846981 prefixEnd_7846981 447696993299829820494433 := by
  unfold tailWord_7846981
  simp only [CollatzResearch.WordTrace]
  refine ⟨286202909584735469504508797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190801939723156979669672531 286202909584735469504508797)
  ·
    refine ⟨107326091094275801064190799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286202909584735469504508797 107326091094275801064190799)
    ·
      refine ⟨160989136641413701596286199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107326091094275801064190799 160989136641413701596286199)
      ·
        refine ⟨241483704962120552394429299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160989136641413701596286199 241483704962120552394429299)
        ·
          refine ⟨362225557443180828591643949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241483704962120552394429299 362225557443180828591643949)
          ·
            refine ⟨135834584041192810721866481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362225557443180828591643949 135834584041192810721866481)
            ·
              refine ⟨101875938030894608041399861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135834584041192810721866481 101875938030894608041399861)
              ·
                refine ⟨9550869190396369503881237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101875938030894608041399861 9550869190396369503881237)
                ·
                  refine ⟨447696993299829820494433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9550869190396369503881237 447696993299829820494433)
                  ·
                    rfl

theorem cell23_7846981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 6].length) (baseStart_7846981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7846981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7846981 prefixEnd_7846981 := by exact prefixLift 7846981
  have htrace : WordTrace (prefixWord ++ tailWord_7846981) baseStart_7846981 baseEnd_7846981 := by
    simpa [prefixWord, tailWord_7846981, baseEnd_7846981] using wordTrace_append hprefix tailTrace_7846981
  have hstable : (prefixWord ++ tailWord_7846981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7846981).length < 2 ^ (prefixWord ++ tailWord_7846981).sum := by decide
  have hdescent : baseEnd_7846981 < baseStart_7846981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7846981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847011 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 5, 5]
def baseStart_7847011 : Nat := 118140960795 + 7847011 * 2 ^ 59
def prefixEnd_7847011 : Nat := 4983230072969 + 3 ^ 40 * 7847011 * 2
def baseEnd_7847011 : Nat := 1343096114706034422358253

theorem tailTrace_7847011 : CollatzResearch.WordTrace tailWord_7847011 prefixEnd_7847011 1343096114706034422358253 := by
  unfold tailWord_7847011
  simp only [CollatzResearch.WordTrace]
  refine ⟨286204003774626784628100887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190802669183084523085400591 286204003774626784628100887)
  ·
    refine ⟨429306005661940176942151331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286204003774626784628100887 429306005661940176942151331)
    ·
      refine ⟨643959008492910265413226997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429306005661940176942151331 643959008492910265413226997)
      ·
        refine ⟨60371157046210337382490031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 643959008492910265413226997 60371157046210337382490031)
        ·
          refine ⟨90556735569315506073735047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60371157046210337382490031 90556735569315506073735047)
          ·
            refine ⟨135835103353973259110602571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90556735569315506073735047 135835103353973259110602571)
            ·
              refine ⟨203752655030959888665903857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135835103353973259110602571 203752655030959888665903857)
              ·
                refine ⟨152814491273219916499427893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203752655030959888665903857 152814491273219916499427893)
                ·
                  refine ⟨14326358556864367171821365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152814491273219916499427893 14326358556864367171821365)
                  ·
                    refine ⟨1343096114706034422358253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14326358556864367171821365 1343096114706034422358253)
                    ·
                      rfl

theorem cell23_7847011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 5].length) (baseStart_7847011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847011 prefixEnd_7847011 := by exact prefixLift 7847011
  have htrace : WordTrace (prefixWord ++ tailWord_7847011) baseStart_7847011 baseEnd_7847011 := by
    simpa [prefixWord, tailWord_7847011, baseEnd_7847011] using wordTrace_append hprefix tailTrace_7847011
  have hstable : (prefixWord ++ tailWord_7847011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847011).length < 2 ^ (prefixWord ++ tailWord_7847011).sum := by decide
  have hdescent : baseEnd_7847011 < baseStart_7847011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847051 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 5]
def baseStart_7847051 : Nat := 118140960795 + 7847051 * 2 ^ 59
def prefixEnd_7847051 : Nat := 4983230072969 + 3 ^ 40 * 7847051 * 2
def baseEnd_7847051 : Nat := 4029308883344283110574575

theorem tailTrace_7847051 : CollatzResearch.WordTrace tailWord_7847051 prefixEnd_7847051 4029308883344283110574575 := by
  unfold tailWord_7847051
  simp only [CollatzResearch.WordTrace]
  refine ⟨286205462694481871459557007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190803641796321247639704671 286205462694481871459557007)
  ·
    refine ⟨429308194041722807189335511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286205462694481871459557007 429308194041722807189335511)
    ·
      refine ⟨643962291062584210784003267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429308194041722807189335511 643962291062584210784003267)
      ·
        refine ⟨965943436593876316176004901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643962291062584210784003267 965943436593876316176004901)
        ·
          refine ⟨181114394361351809283000919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 965943436593876316176004901 181114394361351809283000919)
          ·
            refine ⟨271671591542027713924501379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181114394361351809283000919 271671591542027713924501379)
            ·
              refine ⟨407507387313041570886752069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271671591542027713924501379 407507387313041570886752069)
              ·
                refine ⟨76407635121195294541266013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407507387313041570886752069 76407635121195294541266013)
                ·
                  refine ⟨28652863170448235452974755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76407635121195294541266013 28652863170448235452974755)
                  ·
                    refine ⟨42979294755672353179462133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28652863170448235452974755 42979294755672353179462133)
                    ·
                      refine ⟨4029308883344283110574575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42979294755672353179462133 4029308883344283110574575)
                      ·
                        rfl

theorem cell23_7847051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 5].length) (baseStart_7847051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847051 prefixEnd_7847051 := by exact prefixLift 7847051
  have htrace : WordTrace (prefixWord ++ tailWord_7847051) baseStart_7847051 baseEnd_7847051 := by
    simpa [prefixWord, tailWord_7847051, baseEnd_7847051] using wordTrace_append hprefix tailTrace_7847051
  have hstable : (prefixWord ++ tailWord_7847051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847051).length < 2 ^ (prefixWord ++ tailWord_7847051).sum := by decide
  have hdescent : baseEnd_7847051 < baseStart_7847051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847058 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_7847058 : Nat := 118140960795 + 7847058 * 2 ^ 59
def prefixEnd_7847058 : Nat := 4983230072969 + 3 ^ 40 * 7847058 * 2
def baseEnd_7847058 : Nat := 1343104159236288194395681

theorem tailTrace_7847058 : CollatzResearch.WordTrace tailWord_7847058 prefixEnd_7847058 1343104159236288194395681 := by
  unfold tailWord_7847058
  simp only [CollatzResearch.WordTrace]
  refine ⟨71551429501364127913765457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190803812003637674436707885 71551429501364127913765457)
  ·
    refine ⟨53663572126023095935324093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71551429501364127913765457 53663572126023095935324093)
    ·
      refine ⟨20123839547258660975746535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53663572126023095935324093 20123839547258660975746535)
      ·
        refine ⟨30185759320887991463619803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20123839547258660975746535 30185759320887991463619803)
        ·
          refine ⟨45278638981331987195429705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30185759320887991463619803 45278638981331987195429705)
          ·
            refine ⟨33958979235998990396572279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45278638981331987195429705 33958979235998990396572279)
            ·
              refine ⟨50938468853998485594858419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33958979235998990396572279 50938468853998485594858419)
              ·
                refine ⟨76407703280997728392287629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50938468853998485594858419 76407703280997728392287629)
                ·
                  refine ⟨28652888730374148147107861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76407703280997728392287629 28652888730374148147107861)
                  ·
                    refine ⟨1343104159236288194395681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28652888730374148147107861 1343104159236288194395681)
                    ·
                      rfl

theorem cell23_7847058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_7847058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847058 prefixEnd_7847058 := by exact prefixLift 7847058
  have htrace : WordTrace (prefixWord ++ tailWord_7847058) baseStart_7847058 baseEnd_7847058 := by
    simpa [prefixWord, tailWord_7847058, baseEnd_7847058] using wordTrace_append hprefix tailTrace_7847058
  have hstable : (prefixWord ++ tailWord_7847058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847058).length < 2 ^ (prefixWord ++ tailWord_7847058).sum := by decide
  have hdescent : baseEnd_7847058 < baseStart_7847058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847061 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_7847061 : Nat := 118140960795 + 7847061 * 2 ^ 59
def prefixEnd_7847061 : Nat := 4983230072969 + 3 ^ 40 * 7847061 * 2
def baseEnd_7847061 : Nat := 4029314018150828071449529

theorem tailTrace_7847061 : CollatzResearch.WordTrace tailWord_7847061 prefixEnd_7847061 4029314018150828071449529 := by
  unfold tailWord_7847061
  simp only [CollatzResearch.WordTrace]
  refine ⟨286205827424445643167421037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190803884949630428778280691 286205827424445643167421037)
  ·
    refine ⟨107327185284167116187782889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286205827424445643167421037 107327185284167116187782889)
    ·
      refine ⟨80495388963125337140837167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107327185284167116187782889 80495388963125337140837167)
      ·
        refine ⟨120743083444688005711255751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80495388963125337140837167 120743083444688005711255751)
        ·
          refine ⟨181114625167032008566883627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120743083444688005711255751 181114625167032008566883627)
          ·
            refine ⟨271671937750548012850325441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181114625167032008566883627 271671937750548012850325441)
            ·
              refine ⟨203753953312911009637744081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271671937750548012850325441 203753953312911009637744081)
              ·
                refine ⟨152815464984683257228308061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203753953312911009637744081 152815464984683257228308061)
                ·
                  refine ⟨57305799369256221460615523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152815464984683257228308061 57305799369256221460615523)
                  ·
                    refine ⟨85958699053884332190923285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57305799369256221460615523 85958699053884332190923285)
                    ·
                      refine ⟨4029314018150828071449529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85958699053884332190923285 4029314018150828071449529)
                      ·
                        rfl

theorem cell23_7847061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_7847061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847061 prefixEnd_7847061 := by exact prefixLift 7847061
  have htrace : WordTrace (prefixWord ++ tailWord_7847061) baseStart_7847061 baseEnd_7847061 := by
    simpa [prefixWord, tailWord_7847061, baseEnd_7847061] using wordTrace_append hprefix tailTrace_7847061
  have hstable : (prefixWord ++ tailWord_7847061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847061).length < 2 ^ (prefixWord ++ tailWord_7847061).sum := by decide
  have hdescent : baseEnd_7847061 < baseStart_7847061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847071 : List Nat := [1, 1, 2, 6, 13]
def baseStart_7847071 : Nat := 118140960795 + 7847071 * 2 ^ 59
def prefixEnd_7847071 : Nat := 4983230072969 + 3 ^ 40 * 7847071 * 2
def baseEnd_7847071 : Nat := 5527186766745367671227

theorem tailTrace_7847071 : CollatzResearch.WordTrace tailWord_7847071 prefixEnd_7847071 5527186766745367671227 := by
  unfold tailWord_7847071
  simp only [CollatzResearch.WordTrace]
  refine ⟨286206192154409414875285067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190804128102939609916856711 286206192154409414875285067)
  ·
    refine ⟨429309288231614122312927601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286206192154409414875285067 429309288231614122312927601)
    ·
      refine ⟨321981966173710591734695701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429309288231614122312927601 321981966173710591734695701)
      ·
        refine ⟨15092904664392683987563861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 321981966173710591734695701 15092904664392683987563861)
        ·
          refine ⟨5527186766745367671227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 15092904664392683987563861 5527186766745367671227)
          ·
            rfl

theorem cell23_7847071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 13].length) (baseStart_7847071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847071 prefixEnd_7847071 := by exact prefixLift 7847071
  have htrace : WordTrace (prefixWord ++ tailWord_7847071) baseStart_7847071 baseEnd_7847071 := by
    simpa [prefixWord, tailWord_7847071, baseEnd_7847071] using wordTrace_append hprefix tailTrace_7847071
  have hstable : (prefixWord ++ tailWord_7847071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847071).length < 2 ^ (prefixWord ++ tailWord_7847071).sum := by decide
  have hdescent : baseEnd_7847071 < baseStart_7847071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847076 : List Nat := [2, 3, 1, 2, 3, 3, 2, 2, 1, 1, 3]
def baseStart_7847076 : Nat := 118140960795 + 7847076 * 2 ^ 59
def prefixEnd_7847076 : Nat := 4983230072969 + 3 ^ 40 * 7847076 * 2
def baseEnd_7847076 : Nat := 4029321720360645512761961

theorem tailTrace_7847076 : CollatzResearch.WordTrace tailWord_7847076 prefixEnd_7847076 4029321720360645512761961 := by
  unfold tailWord_7847076
  simp only [CollatzResearch.WordTrace]
  refine ⟨143103187259695650364608541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190804249679594200486144721 143103187259695650364608541)
  ·
    refine ⟨53663695222385868886728203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143103187259695650364608541 53663695222385868886728203)
    ·
      refine ⟨80495542833578803330092305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53663695222385868886728203 80495542833578803330092305)
      ·
        refine ⟨60371657125184102497569229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80495542833578803330092305 60371657125184102497569229)
        ·
          refine ⟨22639371421944038436588461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60371657125184102497569229 22639371421944038436588461)
          ·
            refine ⟨8489764283229014413720673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22639371421944038436588461 8489764283229014413720673)
            ·
              refine ⟨6367323212421760810290505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8489764283229014413720673 6367323212421760810290505)
              ·
                refine ⟨4775492409316320607717879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6367323212421760810290505 4775492409316320607717879)
                ·
                  refine ⟨7163238613974480911576819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775492409316320607717879 7163238613974480911576819)
                  ·
                    refine ⟨10744857920961721367365229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7163238613974480911576819 10744857920961721367365229)
                    ·
                      refine ⟨4029321720360645512761961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10744857920961721367365229 4029321720360645512761961)
                      ·
                        rfl

theorem cell23_7847076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_7847076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847076 prefixEnd_7847076 := by exact prefixLift 7847076
  have htrace : WordTrace (prefixWord ++ tailWord_7847076) baseStart_7847076 baseEnd_7847076 := by
    simpa [prefixWord, tailWord_7847076, baseEnd_7847076] using wordTrace_append hprefix tailTrace_7847076
  have hstable : (prefixWord ++ tailWord_7847076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847076).length < 2 ^ (prefixWord ++ tailWord_7847076).sum := by decide
  have hdescent : baseEnd_7847076 < baseStart_7847076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847091 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 6]
def baseStart_7847091 : Nat := 118140960795 + 7847091 * 2 ^ 59
def prefixEnd_7847091 : Nat := 4983230072969 + 3 ^ 40 * 7847091 * 2
def baseEnd_7847091 : Nat := 4029329422570462954074391

theorem tailTrace_7847091 : CollatzResearch.WordTrace tailWord_7847091 prefixEnd_7847091 4029329422570462954074391 := by
  unfold tailWord_7847091
  simp only [CollatzResearch.WordTrace]
  refine ⟨286206921614336958291013127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190804614409557972194008751 286206921614336958291013127)
  ·
    refine ⟨429310382421505437436519691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286206921614336958291013127 429310382421505437436519691)
    ·
      refine ⟨643965573632258156154779537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429310382421505437436519691 643965573632258156154779537)
      ·
        refine ⟨482974180224193617116084653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643965573632258156154779537 482974180224193617116084653)
        ·
          refine ⟨181115317584072606418531745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482974180224193617116084653 181115317584072606418531745)
          ·
            refine ⟨135836488188054454813898809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181115317584072606418531745 135836488188054454813898809)
            ·
              refine ⟨101877366141040841110424107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135836488188054454813898809 101877366141040841110424107)
              ·
                refine ⟨152816049211561261665636161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101877366141040841110424107 152816049211561261665636161)
                ·
                  refine ⟨114612036908670946249227121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152816049211561261665636161 114612036908670946249227121)
                  ·
                    refine ⟨85959027681503209686920341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114612036908670946249227121 85959027681503209686920341)
                    ·
                      refine ⟨4029329422570462954074391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85959027681503209686920341 4029329422570462954074391)
                      ·
                        rfl

theorem cell23_7847091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_7847091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847091 prefixEnd_7847091 := by exact prefixLift 7847091
  have htrace : WordTrace (prefixWord ++ tailWord_7847091) baseStart_7847091 baseEnd_7847091 := by
    simpa [prefixWord, tailWord_7847091, baseEnd_7847091] using wordTrace_append hprefix tailTrace_7847091
  have hstable : (prefixWord ++ tailWord_7847091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847091).length < 2 ^ (prefixWord ++ tailWord_7847091).sum := by decide
  have hdescent : baseEnd_7847091 < baseStart_7847091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847110 : List Nat := [6, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_7847110 : Nat := 118140960795 + 7847110 * 2 ^ 59
def prefixEnd_7847110 : Nat := 4983230072969 + 3 ^ 40 * 7847110 * 2
def baseEnd_7847110 : Nat := 4029339178702898379736805

theorem tailTrace_7847110 : CollatzResearch.WordTrace tailWord_7847110 prefixEnd_7847110 4029339178702898379736805 := by
  unfold tailWord_7847110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8943987956289628891748587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190805076400845416357303189 8943987956289628891748587)
  ·
    refine ⟨13415981934434443337622881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8943987956289628891748587 13415981934434443337622881)
    ·
      refine ⟨10061986450825832503217161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13415981934434443337622881 10061986450825832503217161)
      ·
        refine ⟨7546489838119374377412871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10061986450825832503217161 7546489838119374377412871)
        ·
          refine ⟨11319734757179061566119307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7546489838119374377412871 11319734757179061566119307)
          ·
            refine ⟨16979602135768592349178961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11319734757179061566119307 16979602135768592349178961)
            ·
              refine ⟨12734701601826444261884221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16979602135768592349178961 12734701601826444261884221)
              ·
                refine ⟨4775513100684916598206583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12734701601826444261884221 4775513100684916598206583)
                ·
                  refine ⟨7163269651027374897309875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775513100684916598206583 7163269651027374897309875)
                  ·
                    refine ⟨10744904476541062345964813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7163269651027374897309875 10744904476541062345964813)
                    ·
                      refine ⟨4029339178702898379736805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10744904476541062345964813 4029339178702898379736805)
                      ·
                        rfl

theorem cell23_7847110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_7847110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847110 prefixEnd_7847110 := by exact prefixLift 7847110
  have htrace : WordTrace (prefixWord ++ tailWord_7847110) baseStart_7847110 baseEnd_7847110 := by
    simpa [prefixWord, tailWord_7847110, baseEnd_7847110] using wordTrace_append hprefix tailTrace_7847110
  have hstable : (prefixWord ++ tailWord_7847110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847110).length < 2 ^ (prefixWord ++ tailWord_7847110).sum := by decide
  have hdescent : baseEnd_7847110 < baseStart_7847110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847126 : List Nat := [5, 2, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_7847126 : Nat := 118140960795 + 7847126 * 2 ^ 59
def prefixEnd_7847126 : Nat := 4983230072969 + 3 ^ 40 * 7847126 * 2
def baseEnd_7847126 : Nat := 1343115798131123439045577

theorem tailTrace_7847126 : CollatzResearch.WordTrace tailWord_7847126 prefixEnd_7847126 1343115798131123439045577 := by
  unfold tailWord_7847126
  simp only [CollatzResearch.WordTrace]
  refine ⟨17888012385575634954283577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190805465446140106179024821 17888012385575634954283577)
  ·
    refine ⟨13416009289181726215712683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17888012385575634954283577 13416009289181726215712683)
    ·
      refine ⟨20124013933772589323569025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13416009289181726215712683 20124013933772589323569025)
      ·
        refine ⟨15093010450329441992676769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20124013933772589323569025 15093010450329441992676769)
        ·
          refine ⟨11319757837747081494507577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15093010450329441992676769 11319757837747081494507577)
          ·
            refine ⟨8489818378310311120880683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11319757837747081494507577 8489818378310311120880683)
            ·
              refine ⟨12734727567465466681321025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8489818378310311120880683 12734727567465466681321025)
              ·
                refine ⟨9551045675599100010990769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12734727567465466681321025 9551045675599100010990769)
                ·
                  refine ⟨7163284256699325008243077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9551045675599100010990769 7163284256699325008243077)
                  ·
                    refine ⟨1343115798131123439045577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7163284256699325008243077 1343115798131123439045577)
                    ·
                      rfl

theorem cell23_7847126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_7847126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847126 prefixEnd_7847126 := by exact prefixLift 7847126
  have htrace : WordTrace (prefixWord ++ tailWord_7847126) baseStart_7847126 baseEnd_7847126 := by
    simpa [prefixWord, tailWord_7847126, baseEnd_7847126] using wordTrace_append hprefix tailTrace_7847126
  have hstable : (prefixWord ++ tailWord_7847126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847126).length < 2 ^ (prefixWord ++ tailWord_7847126).sum := by decide
  have hdescent : baseEnd_7847126 < baseStart_7847126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847148 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 2, 6]
def baseStart_7847148 : Nat := 118140960795 + 7847148 * 2 ^ 59
def prefixEnd_7847148 : Nat := 4983230072969 + 3 ^ 40 * 7847148 * 2
def baseEnd_7847148 : Nat := 1343119563655923077020543

theorem tailTrace_7847148 : CollatzResearch.WordTrace tailWord_7847148 prefixEnd_7847148 1343119563655923077020543 := by
  unfold tailWord_7847148
  simp only [CollatzResearch.WordTrace]
  refine ⟨143104500287565228512919049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190806000383420304683892065 143104500287565228512919049)
  ·
    refine ⟨107328375215673921384689287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143104500287565228512919049 107328375215673921384689287)
    ·
      refine ⟨160992562823510882077033931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107328375215673921384689287 160992562823510882077033931)
      ·
        refine ⟨241488844235266323115550897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160992562823510882077033931 241488844235266323115550897)
        ·
          refine ⟨181116633176449742336663173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241488844235266323115550897 181116633176449742336663173)
          ·
            refine ⟨33959368720584326688124345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181116633176449742336663173 33959368720584326688124345)
            ·
              refine ⟨25469526540438245016093259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33959368720584326688124345 25469526540438245016093259)
              ·
                refine ⟨38204289810657367524139889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25469526540438245016093259 38204289810657367524139889)
                ·
                  refine ⟨28653217357993025643104917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38204289810657367524139889 28653217357993025643104917)
                  ·
                    refine ⟨1343119563655923077020543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28653217357993025643104917 1343119563655923077020543)
                    ·
                      rfl

theorem cell23_7847148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_7847148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847148 prefixEnd_7847148 := by exact prefixLift 7847148
  have htrace : WordTrace (prefixWord ++ tailWord_7847148) baseStart_7847148 baseEnd_7847148 := by
    simpa [prefixWord, tailWord_7847148, baseEnd_7847148] using wordTrace_append hprefix tailTrace_7847148
  have hstable : (prefixWord ++ tailWord_7847148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847148).length < 2 ^ (prefixWord ++ tailWord_7847148).sum := by decide
  have hdescent : baseEnd_7847148 < baseStart_7847148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847156 : List Nat := [2, 6, 1, 2, 1, 2, 2, 7]
def baseStart_7847156 : Nat := 118140960795 + 7847156 * 2 ^ 59
def prefixEnd_7847156 : Nat := 4983230072969 + 3 ^ 40 * 7847156 * 2
def baseEnd_7847156 : Nat := 149235659215296488880059

theorem tailTrace_7847156 : CollatzResearch.WordTrace tailWord_7847156 prefixEnd_7847156 149235659215296488880059 := by
  unfold tailWord_7847156
  simp only [CollatzResearch.WordTrace]
  refine ⟨143104646179550737196064661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190806194906067649594752881 143104646179550737196064661)
  ·
    refine ⟨6708030289666440806065531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143104646179550737196064661 6708030289666440806065531)
    ·
      refine ⟨10062045434499661209098297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6708030289666440806065531 10062045434499661209098297)
      ·
        refine ⟨7546534075874745906823723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10062045434499661209098297 7546534075874745906823723)
        ·
          refine ⟨11319801113812118860235585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7546534075874745906823723 11319801113812118860235585)
          ·
            refine ⟨8489850835359089145176689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11319801113812118860235585 8489850835359089145176689)
            ·
              refine ⟨6367388126519316858882517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8489850835359089145176689 6367388126519316858882517)
              ·
                refine ⟨149235659215296488880059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6367388126519316858882517 149235659215296488880059)
                ·
                  rfl

theorem cell23_7847156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 7].length) (baseStart_7847156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847156 prefixEnd_7847156 := by exact prefixLift 7847156
  have htrace : WordTrace (prefixWord ++ tailWord_7847156) baseStart_7847156 baseEnd_7847156 := by
    simpa [prefixWord, tailWord_7847156, baseEnd_7847156] using wordTrace_append hprefix tailTrace_7847156
  have hstable : (prefixWord ++ tailWord_7847156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847156).length < 2 ^ (prefixWord ++ tailWord_7847156).sum := by decide
  have hdescent : baseEnd_7847156 < baseStart_7847156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847248 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 5]
def baseStart_7847248 : Nat := 118140960795 + 7847248 * 2 ^ 59
def prefixEnd_7847248 : Nat := 4983230072969 + 3 ^ 40 * 7847248 * 2
def baseEnd_7847248 : Nat := 4029410039033218839811169

theorem tailTrace_7847248 : CollatzResearch.WordTrace tailWord_7847248 prefixEnd_7847248 4029410039033218839811169 := by
  unfold tailWord_7847248
  simp only [CollatzResearch.WordTrace]
  refine ⟨143106323937384087052239199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190808431916512116069652265 143106323937384087052239199)
  ·
    refine ⟨214659485906076130578358799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143106323937384087052239199 214659485906076130578358799)
    ·
      refine ⟨321989228859114195867538199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214659485906076130578358799 321989228859114195867538199)
      ·
        refine ⟨482983843288671293801307299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321989228859114195867538199 482983843288671293801307299)
        ·
          refine ⟨724475764933006940701960949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482983843288671293801307299 724475764933006940701960949)
          ·
            refine ⟨67919602962469400690808839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 724475764933006940701960949 67919602962469400690808839)
            ·
              refine ⟨101879404443704101036213259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67919602962469400690808839 101879404443704101036213259)
              ·
                refine ⟨152819106665556151554319889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101879404443704101036213259 152819106665556151554319889)
                ·
                  refine ⟨114614329999167113665739917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152819106665556151554319889 114614329999167113665739917)
                  ·
                    refine ⟨42980373749687667624652469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114614329999167113665739917 42980373749687667624652469)
                    ·
                      refine ⟨4029410039033218839811169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42980373749687667624652469 4029410039033218839811169)
                      ·
                        rfl

theorem cell23_7847248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_7847248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847248 prefixEnd_7847248 := by exact prefixLift 7847248
  have htrace : WordTrace (prefixWord ++ tailWord_7847248) baseStart_7847248 baseEnd_7847248 := by
    simpa [prefixWord, tailWord_7847248, baseEnd_7847248] using wordTrace_append hprefix tailTrace_7847248
  have hstable : (prefixWord ++ tailWord_7847248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847248).length < 2 ^ (prefixWord ++ tailWord_7847248).sum := by decide
  have hdescent : baseEnd_7847248 < baseStart_7847248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847265 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_7847265 : Nat := 118140960795 + 7847265 * 2 ^ 59
def prefixEnd_7847265 : Nat := 4983230072969 + 3 ^ 40 * 7847265 * 2
def baseEnd_7847265 : Nat := 4029418768204345273298591

theorem tailTrace_7847265 : CollatzResearch.WordTrace tailWord_7847265 prefixEnd_7847265 4029418768204345273298591 := by
  unfold tailWord_7847265
  simp only [CollatzResearch.WordTrace]
  refine ⟨286213267915706586007847249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190808845277137724005231499 286213267915706586007847249)
  ·
    refine ⟨214659950936779939505885437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286213267915706586007847249 214659950936779939505885437)
    ·
      refine ⟨80497481601292477314707039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214659950936779939505885437 80497481601292477314707039)
      ·
        refine ⟨120746222401938715972060559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80497481601292477314707039 120746222401938715972060559)
        ·
          refine ⟨181119333602908073958090839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120746222401938715972060559 181119333602908073958090839)
          ·
            refine ⟨271679000404362110937136259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181119333602908073958090839 271679000404362110937136259)
            ·
              refine ⟨407518500606543166405704389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271679000404362110937136259 407518500606543166405704389)
              ·
                refine ⟨76409718863726843701069573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407518500606543166405704389 76409718863726843701069573)
                ·
                  refine ⟨14326822286948783193950545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76409718863726843701069573 14326822286948783193950545)
                  ·
                    refine ⟨10745116715211587395462909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14326822286948783193950545 10745116715211587395462909)
                    ·
                      refine ⟨4029418768204345273298591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10745116715211587395462909 4029418768204345273298591)
                      ·
                        rfl

theorem cell23_7847265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_7847265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847265 prefixEnd_7847265 := by exact prefixLift 7847265
  have htrace : WordTrace (prefixWord ++ tailWord_7847265) baseStart_7847265 baseEnd_7847265 := by
    simpa [prefixWord, tailWord_7847265, baseEnd_7847265] using wordTrace_append hprefix tailTrace_7847265
  have hstable : (prefixWord ++ tailWord_7847265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847265).length < 2 ^ (prefixWord ++ tailWord_7847265).sum := by decide
  have hdescent : baseEnd_7847265 < baseStart_7847265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847288 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_7847288 : Nat := 118140960795 + 7847288 * 2 ^ 59
def prefixEnd_7847288 : Nat := 4983230072969 + 3 ^ 40 * 7847288 * 2
def baseEnd_7847288 : Nat := 4029430578259398683310985

theorem tailTrace_7847288 : CollatzResearch.WordTrace tailWord_7847288 prefixEnd_7847288 4029430578259398683310985 := by
  unfold tailWord_7847288
  simp only [CollatzResearch.WordTrace]
  refine ⟨143107053397311630467967259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190809404529748840623956345 143107053397311630467967259)
  ·
    refine ⟨214660580095967445701950889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143107053397311630467967259 214660580095967445701950889)
    ·
      refine ⟨160995435071975584276463167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214660580095967445701950889 160995435071975584276463167)
      ·
        refine ⟨241493152607963376414694751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160995435071975584276463167 241493152607963376414694751)
        ·
          refine ⟨362239728911945064622042127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241493152607963376414694751 362239728911945064622042127)
          ·
            refine ⟨543359593367917596933063191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362239728911945064622042127 543359593367917596933063191)
            ·
              refine ⟨815039390051876395399594787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543359593367917596933063191 815039390051876395399594787)
              ·
                refine ⟨1222559085077814593099392181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815039390051876395399594787 1222559085077814593099392181)
                ·
                  refine ⟨114614914226045118103068017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1222559085077814593099392181 114614914226045118103068017)
                  ·
                    refine ⟨85961185669533838577301013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114614914226045118103068017 85961185669533838577301013)
                    ·
                      refine ⟨4029430578259398683310985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85961185669533838577301013 4029430578259398683310985)
                      ·
                        rfl

theorem cell23_7847288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_7847288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847288 prefixEnd_7847288 := by exact prefixLift 7847288
  have htrace : WordTrace (prefixWord ++ tailWord_7847288) baseStart_7847288 baseEnd_7847288 := by
    simpa [prefixWord, tailWord_7847288, baseEnd_7847288] using wordTrace_append hprefix tailTrace_7847288
  have hstable : (prefixWord ++ tailWord_7847288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847288).length < 2 ^ (prefixWord ++ tailWord_7847288).sum := by decide
  have hdescent : baseEnd_7847288 < baseStart_7847288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847322 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2]
def baseStart_7847322 : Nat := 118140960795 + 7847322 * 2 ^ 59
def prefixEnd_7847322 : Nat := 4983230072969 + 3 ^ 40 * 7847322 * 2
def baseEnd_7847322 : Nat := 4029448036601651550285829

theorem tailTrace_7847322 : CollatzResearch.WordTrace tailWord_7847322 prefixEnd_7847322 4029448036601651550285829 := by
  unfold tailWord_7847322
  simp only [CollatzResearch.WordTrace]
  refine ⟨71553836719125021185668055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190810231251000056495114813 71553836719125021185668055)
  ·
    refine ⟨107330755078687531778502083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71553836719125021185668055 107330755078687531778502083)
    ·
      refine ⟨160996132618031297667753125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107330755078687531778502083 160996132618031297667753125)
      ·
        refine ⟨30186774865880868312703711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160996132618031297667753125 30186774865880868312703711)
        ·
          refine ⟨45280162298821302469055567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30186774865880868312703711 45280162298821302469055567)
          ·
            refine ⟨67920243448231953703583351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45280162298821302469055567 67920243448231953703583351)
            ·
              refine ⟨101880365172347930555375027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67920243448231953703583351 101880365172347930555375027)
              ·
                refine ⟨152820547758521895833062541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101880365172347930555375027 152820547758521895833062541)
                ·
                  refine ⟨57307705409445710937398453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152820547758521895833062541 57307705409445710937398453)
                  ·
                    refine ⟨5372597382135535400381105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57307705409445710937398453 5372597382135535400381105)
                    ·
                      refine ⟨4029448036601651550285829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5372597382135535400381105 4029448036601651550285829)
                      ·
                        rfl

theorem cell23_7847322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_7847322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847322 prefixEnd_7847322 := by exact prefixLift 7847322
  have htrace : WordTrace (prefixWord ++ tailWord_7847322) baseStart_7847322 baseEnd_7847322 := by
    simpa [prefixWord, tailWord_7847322, baseEnd_7847322] using wordTrace_append hprefix tailTrace_7847322
  have hstable : (prefixWord ++ tailWord_7847322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847322).length < 2 ^ (prefixWord ++ tailWord_7847322).sum := by decide
  have hdescent : baseEnd_7847322 < baseStart_7847322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847345 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 3, 6]
def baseStart_7847345 : Nat := 118140960795 + 7847345 * 2 ^ 59
def prefixEnd_7847345 : Nat := 4983230072969 + 3 ^ 40 * 7847345 * 2
def baseEnd_7847345 : Nat := 1343153282218901653432741

theorem tailTrace_7847345 : CollatzResearch.WordTrace tailWord_7847345 prefixEnd_7847345 1343153282218901653432741 := by
  unfold tailWord_7847345
  simp only [CollatzResearch.WordTrace]
  refine ⟨286216185755416759670759489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190810790503611173113839659 286216185755416759670759489)
  ·
    refine ⟨214662139316562569753069617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286216185755416759670759489 214662139316562569753069617)
    ·
      refine ⟨160996604487421927314802213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214662139316562569753069617 160996604487421927314802213)
      ·
        refine ⟨30186863341391611371525415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160996604487421927314802213 30186863341391611371525415)
        ·
          refine ⟨45280295012087417057288123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30186863341391611371525415 45280295012087417057288123)
          ·
            refine ⟨67920442518131125585932185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45280295012087417057288123 67920442518131125585932185)
            ·
              refine ⟨50940331888598344189449139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67920442518131125585932185 50940331888598344189449139)
              ·
                refine ⟨76410497832897516284173709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50940331888598344189449139 76410497832897516284173709)
                ·
                  refine ⟨28653936687336568606565141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76410497832897516284173709 28653936687336568606565141)
                  ·
                    refine ⟨1343153282218901653432741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28653936687336568606565141 1343153282218901653432741)
                    ·
                      rfl

theorem cell23_7847345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_7847345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847345 prefixEnd_7847345 := by exact prefixLift 7847345
  have htrace : WordTrace (prefixWord ++ tailWord_7847345) baseStart_7847345 baseEnd_7847345 := by
    simpa [prefixWord, tailWord_7847345, baseEnd_7847345] using wordTrace_append hprefix tailTrace_7847345
  have hstable : (prefixWord ++ tailWord_7847345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847345).length < 2 ^ (prefixWord ++ tailWord_7847345).sum := by decide
  have hdescent : baseEnd_7847345 < baseStart_7847345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847352 : List Nat := [2, 1, 2, 1, 2, 2, 4, 3, 1, 1, 4]
def baseStart_7847352 : Nat := 118140960795 + 7847352 * 2 ^ 59
def prefixEnd_7847352 : Nat := 4983230072969 + 3 ^ 40 * 7847352 * 2
def baseEnd_7847352 : Nat := 4029463441021286432910691

theorem tailTrace_7847352 : CollatzResearch.WordTrace tailWord_7847352 prefixEnd_7847352 4029463441021286432910691 := by
  unfold tailWord_7847352
  simp only [CollatzResearch.WordTrace]
  refine ⟨143108220533195699933132155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190810960710927599910842873 143108220533195699933132155)
  ·
    refine ⟨214662330799793549899698233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143108220533195699933132155 214662330799793549899698233)
    ·
      refine ⟨160996748099845162424773675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214662330799793549899698233 160996748099845162424773675)
      ·
        refine ⟨241495122149767743637160513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160996748099845162424773675 241495122149767743637160513)
        ·
          refine ⟨181121341612325807727870385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241495122149767743637160513 181121341612325807727870385)
          ·
            refine ⟨135841006209244355795902789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181121341612325807727870385 135841006209244355795902789)
            ·
              refine ⟨25470188664233316711731773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135841006209244355795902789 25470188664233316711731773)
              ·
                refine ⟨9551320749087493766899415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25470188664233316711731773 9551320749087493766899415)
                ·
                  refine ⟨14326981123631240650349123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9551320749087493766899415 14326981123631240650349123)
                  ·
                    refine ⟨21490471685446860975523685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14326981123631240650349123 21490471685446860975523685)
                    ·
                      refine ⟨4029463441021286432910691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21490471685446860975523685 4029463441021286432910691)
                      ·
                        rfl

theorem cell23_7847352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_7847352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847352 prefixEnd_7847352 := by exact prefixLift 7847352
  have htrace : WordTrace (prefixWord ++ tailWord_7847352) baseStart_7847352 baseEnd_7847352 := by
    simpa [prefixWord, tailWord_7847352, baseEnd_7847352] using wordTrace_append hprefix tailTrace_7847352
  have hstable : (prefixWord ++ tailWord_7847352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847352).length < 2 ^ (prefixWord ++ tailWord_7847352).sum := by decide
  have hdescent : baseEnd_7847352 < baseStart_7847352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847356 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 2, 3, 2]
def baseStart_7847356 : Nat := 118140960795 + 7847356 * 2 ^ 59
def prefixEnd_7847356 : Nat := 4983230072969 + 3 ^ 40 * 7847356 * 2
def baseEnd_7847356 : Nat := 4029465494943904417260673

theorem tailTrace_7847356 : CollatzResearch.WordTrace tailWord_7847356 prefixEnd_7847356 4029465494943904417260673 := by
  unfold tailWord_7847356
  simp only [CollatzResearch.WordTrace]
  refine ⟨143108293479188454274704961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190811057972251272366273281 143108293479188454274704961)
  ·
    refine ⟨107331220109391340706028721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143108293479188454274704961 107331220109391340706028721)
    ·
      refine ⟨80498415082043505529521541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107331220109391340706028721 80498415082043505529521541)
      ·
        refine ⟨15093452827883157286785289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80498415082043505529521541 15093452827883157286785289)
        ·
          refine ⟨11320089620912367965088967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15093452827883157286785289 11320089620912367965088967)
          ·
            refine ⟨16980134431368551947633451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11320089620912367965088967 16980134431368551947633451)
            ·
              refine ⟨25470201647052827921450177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16980134431368551947633451 25470201647052827921450177)
              ·
                refine ⟨19102651235289620941087633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25470201647052827921450177 19102651235289620941087633)
                ·
                  refine ⟨14326988426467215705815725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19102651235289620941087633 14326988426467215705815725)
                  ·
                    refine ⟨5372620659925205889680897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14326988426467215705815725 5372620659925205889680897)
                    ·
                      refine ⟨4029465494943904417260673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5372620659925205889680897 4029465494943904417260673)
                      ·
                        rfl

theorem cell23_7847356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_7847356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847356 prefixEnd_7847356 := by exact prefixLift 7847356
  have htrace : WordTrace (prefixWord ++ tailWord_7847356) baseStart_7847356 baseEnd_7847356 := by
    simpa [prefixWord, tailWord_7847356, baseEnd_7847356] using wordTrace_append hprefix tailTrace_7847356
  have hstable : (prefixWord ++ tailWord_7847356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847356).length < 2 ^ (prefixWord ++ tailWord_7847356).sum := by decide
  have hdescent : baseEnd_7847356 < baseStart_7847356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847372 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 1, 1, 5]
def baseStart_7847372 : Nat := 118140960795 + 7847372 * 2 ^ 59
def prefixEnd_7847372 : Nat := 4983230072969 + 3 ^ 40 * 7847372 * 2
def baseEnd_7847372 : Nat := 4029473710634376354660599

theorem tailTrace_7847372 : CollatzResearch.WordTrace tailWord_7847372 prefixEnd_7847372 4029473710634376354660599 := by
  unfold tailWord_7847372
  simp only [CollatzResearch.WordTrace]
  refine ⟨143108585263159471640996185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190811447017545962187994913 143108585263159471640996185)
  ·
    refine ⟨107331438947369603730747139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143108585263159471640996185 107331438947369603730747139)
    ·
      refine ⟨160997158421054405596120709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107331438947369603730747139 160997158421054405596120709)
      ·
        refine ⟨30186967203947701049272633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160997158421054405596120709 30186967203947701049272633)
        ·
          refine ⟨22640225402960775786954475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30186967203947701049272633 22640225402960775786954475)
          ·
            refine ⟨33960338104441163680431713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22640225402960775786954475 33960338104441163680431713)
            ·
              refine ⟨25470253578330872760323785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33960338104441163680431713 25470253578330872760323785)
              ·
                refine ⟨19102690183748154570242839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25470253578330872760323785 19102690183748154570242839)
                ·
                  refine ⟨28654035275622231855364259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19102690183748154570242839 28654035275622231855364259)
                  ·
                    refine ⟨42981052913433347783046389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28654035275622231855364259 42981052913433347783046389)
                    ·
                      refine ⟨4029473710634376354660599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42981052913433347783046389 4029473710634376354660599)
                      ·
                        rfl

theorem cell23_7847372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_7847372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847372 prefixEnd_7847372 := by exact prefixLift 7847372
  have htrace : WordTrace (prefixWord ++ tailWord_7847372) baseStart_7847372 baseEnd_7847372 := by
    simpa [prefixWord, tailWord_7847372, baseEnd_7847372] using wordTrace_append hprefix tailTrace_7847372
  have hstable : (prefixWord ++ tailWord_7847372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847372).length < 2 ^ (prefixWord ++ tailWord_7847372).sum := by decide
  have hdescent : baseEnd_7847372 < baseStart_7847372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847389 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_7847389 : Nat := 118140960795 + 7847389 * 2 ^ 59
def prefixEnd_7847389 : Nat := 4983230072969 + 3 ^ 40 * 7847389 * 2
def baseEnd_7847389 : Nat := 4029482439805502788148021

theorem tailTrace_7847389 : CollatzResearch.WordTrace tailWord_7847389 prefixEnd_7847389 4029482439805502788148021 := by
  unfold tailWord_7847389
  simp only [CollatzResearch.WordTrace]
  refine ⟨286217790567257355185361221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190811860378171570123574147 286217790567257355185361221)
  ·
    refine ⟨53665835731360754097255229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286217790567257355185361221 53665835731360754097255229)
    ·
      refine ⟨20124688399260282786470711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53665835731360754097255229 20124688399260282786470711)
      ·
        refine ⟨30187032598890424179706067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20124688399260282786470711 30187032598890424179706067)
        ·
          refine ⟨45280548898335636269559101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30187032598890424179706067 45280548898335636269559101)
          ·
            refine ⟨16980205836875863601084663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45280548898335636269559101 16980205836875863601084663)
            ·
              refine ⟨25470308755313795401626995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16980205836875863601084663 25470308755313795401626995)
              ·
                refine ⟨38205463132970693102440493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25470308755313795401626995 38205463132970693102440493)
                ·
                  refine ⟨14327048674864009913415185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38205463132970693102440493 14327048674864009913415185)
                  ·
                    refine ⟨10745286506148007435061389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14327048674864009913415185 10745286506148007435061389)
                    ·
                      refine ⟨4029482439805502788148021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10745286506148007435061389 4029482439805502788148021)
                      ·
                        rfl

theorem cell23_7847389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_7847389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847389 prefixEnd_7847389 := by exact prefixLift 7847389
  have htrace : WordTrace (prefixWord ++ tailWord_7847389) baseStart_7847389 baseEnd_7847389 := by
    simpa [prefixWord, tailWord_7847389, baseEnd_7847389] using wordTrace_append hprefix tailTrace_7847389
  have hstable : (prefixWord ++ tailWord_7847389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847389).length < 2 ^ (prefixWord ++ tailWord_7847389).sum := by decide
  have hdescent : baseEnd_7847389 < baseStart_7847389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847406 : List Nat := [4, 1, 2, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_7847406 : Nat := 118140960795 + 7847406 * 2 ^ 59
def prefixEnd_7847406 : Nat := 4983230072969 + 3 ^ 40 * 7847406 * 2
def baseEnd_7847406 : Nat := 4029491168976629221635443

theorem tailTrace_7847406 : CollatzResearch.WordTrace tailWord_7847406 prefixEnd_7847406 4029491168976629221635443 := by
  unfold tailWord_7847406
  simp only [CollatzResearch.WordTrace]
  refine ⟨35777301326024470886091259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190812273738797178059153381 35777301326024470886091259)
  ·
    refine ⟨53665951989036706329136889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35777301326024470886091259 53665951989036706329136889)
    ·
      refine ⟨40249463991777529746852667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53665951989036706329136889 40249463991777529746852667)
      ·
        refine ⟨60374195987666294620279001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40249463991777529746852667 60374195987666294620279001)
        ·
          refine ⟨45280646990749720965209251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60374195987666294620279001 45280646990749720965209251)
          ·
            refine ⟨67920970486124581447813877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45280646990749720965209251 67920970486124581447813877)
            ·
              refine ⟨6367590983074179510732551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67920970486124581447813877 6367590983074179510732551)
              ·
                refine ⟨9551386474611269266098827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6367590983074179510732551 9551386474611269266098827)
                ·
                  refine ⟨14327079711916903899148241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9551386474611269266098827 14327079711916903899148241)
                  ·
                    refine ⟨10745309783937677924361181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14327079711916903899148241 10745309783937677924361181)
                    ·
                      refine ⟨4029491168976629221635443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10745309783937677924361181 4029491168976629221635443)
                      ·
                        rfl

theorem cell23_7847406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_7847406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847406 prefixEnd_7847406 := by exact prefixLift 7847406
  have htrace : WordTrace (prefixWord ++ tailWord_7847406) baseStart_7847406 baseEnd_7847406 := by
    simpa [prefixWord, tailWord_7847406, baseEnd_7847406] using wordTrace_append hprefix tailTrace_7847406
  have hstable : (prefixWord ++ tailWord_7847406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847406).length < 2 ^ (prefixWord ++ tailWord_7847406).sum := by decide
  have hdescent : baseEnd_7847406 < baseStart_7847406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847454 : List Nat := [4, 3, 3, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7847454 : Nat := 118140960795 + 7847454 * 2 ^ 59
def prefixEnd_7847454 : Nat := 4983230072969 + 3 ^ 40 * 7847454 * 2
def baseEnd_7847454 : Nat := 4029515816048045033835223

theorem tailTrace_7847454 : CollatzResearch.WordTrace tailWord_7847454 prefixEnd_7847454 4029515816048045033835223 := by
  unfold tailWord_7847454
  simp only [CollatzResearch.WordTrace]
  refine ⟨35777520164002733910809677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190813440874681247524318277 35777520164002733910809677)
  ·
    refine ⟨13416570061501025216553629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35777520164002733910809677 13416570061501025216553629)
    ·
      refine ⟨5031213773062884456207611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13416570061501025216553629 5031213773062884456207611)
      ·
        refine ⟨7546820659594326684311417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5031213773062884456207611 7546820659594326684311417)
        ·
          refine ⟨5660115494695745013233563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7546820659594326684311417 5660115494695745013233563)
          ·
            refine ⟨8490173242043617519850345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5660115494695745013233563 8490173242043617519850345)
            ·
              refine ⟨6367629931532713139887759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8490173242043617519850345 6367629931532713139887759)
              ·
                refine ⟨9551444897299069709831639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6367629931532713139887759 9551444897299069709831639)
                ·
                  refine ⟨14327167345948604564747459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9551444897299069709831639 14327167345948604564747459)
                  ·
                    refine ⟨21490751018922906847121189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14327167345948604564747459 21490751018922906847121189)
                    ·
                      refine ⟨4029515816048045033835223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21490751018922906847121189 4029515816048045033835223)
                      ·
                        rfl

theorem cell23_7847454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7847454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847454 prefixEnd_7847454 := by exact prefixLift 7847454
  have htrace : WordTrace (prefixWord ++ tailWord_7847454) baseStart_7847454 baseEnd_7847454 := by
    simpa [prefixWord, tailWord_7847454, baseEnd_7847454] using wordTrace_append hprefix tailTrace_7847454
  have hstable : (prefixWord ++ tailWord_7847454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847454).length < 2 ^ (prefixWord ++ tailWord_7847454).sum := by decide
  have hdescent : baseEnd_7847454 < baseStart_7847454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847482 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 7]
def baseStart_7847482 : Nat := 118140960795 + 7847482 * 2 ^ 59
def prefixEnd_7847482 : Nat := 4983230072969 + 3 ^ 40 * 7847482 * 2
def baseEnd_7847482 : Nat := 447725577056263436031677

theorem tailTrace_7847482 : CollatzResearch.WordTrace tailWord_7847482 prefixEnd_7847482 447725577056263436031677 := by
  unfold tailWord_7847482
  simp only [CollatzResearch.WordTrace]
  refine ⟨71555295638980108017124175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190814121703946954712331133 71555295638980108017124175)
  ·
    refine ⟨107332943458470162025686263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71555295638980108017124175 107332943458470162025686263)
    ·
      refine ⟨160999415187705243038529395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107332943458470162025686263 160999415187705243038529395)
      ·
        refine ⟨241499122781557864557794093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160999415187705243038529395 241499122781557864557794093)
        ·
          refine ⟨90562171043084199209172785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241499122781557864557794093 90562171043084199209172785)
          ·
            refine ⟨67921628282313149406879589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90562171043084199209172785 67921628282313149406879589)
            ·
              refine ⟨12735305302933715513789923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67921628282313149406879589 12735305302933715513789923)
              ·
                refine ⟨19102957954400573270684885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12735305302933715513789923 19102957954400573270684885)
                ·
                  refine ⟨447725577056263436031677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19102957954400573270684885 447725577056263436031677)
                  ·
                    rfl

theorem cell23_7847482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 7].length) (baseStart_7847482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847482 prefixEnd_7847482 := by exact prefixLift 7847482
  have htrace : WordTrace (prefixWord ++ tailWord_7847482) baseStart_7847482 baseEnd_7847482 := by
    simpa [prefixWord, tailWord_7847482, baseEnd_7847482] using wordTrace_append hprefix tailTrace_7847482
  have hstable : (prefixWord ++ tailWord_7847482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847482).length < 2 ^ (prefixWord ++ tailWord_7847482).sum := by decide
  have hdescent : baseEnd_7847482 < baseStart_7847482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847493 : List Nat := [1, 3, 1, 1, 1, 4, 5, 1, 2, 2, 2]
def baseStart_7847493 : Nat := 118140960795 + 7847493 * 2 ^ 59
def prefixEnd_7847493 : Nat := 4983230072969 + 3 ^ 40 * 7847493 * 2
def baseEnd_7847493 : Nat := 4029535841793570381247543

theorem tailTrace_7847493 : CollatzResearch.WordTrace tailWord_7847493 prefixEnd_7847493 4029535841793570381247543 := by
  unfold tailWord_7847493
  simp only [CollatzResearch.WordTrace]
  refine ⟨286221583758880580947147133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190814389172587053964764755 286221583758880580947147133)
  ·
    refine ⟨107333093909580217855180175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286221583758880580947147133 107333093909580217855180175)
    ·
      refine ⟨160999640864370326782770263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107333093909580217855180175 160999640864370326782770263)
      ·
        refine ⟨241499461296555490174155395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160999640864370326782770263 241499461296555490174155395)
        ·
          refine ⟨362249191944833235261233093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241499461296555490174155395 362249191944833235261233093)
          ·
            refine ⟨67921723489656231611481205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 362249191944833235261233093 67921723489656231611481205)
            ·
              refine ⟨6367661577155271713576363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67921723489656231611481205 6367661577155271713576363)
              ·
                refine ⟨9551492365732907570364545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6367661577155271713576363 9551492365732907570364545)
                ·
                  refine ⟨7163619274299680677773409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9551492365732907570364545 7163619274299680677773409)
                  ·
                    refine ⟨5372714455724760508330057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7163619274299680677773409 5372714455724760508330057)
                    ·
                      refine ⟨4029535841793570381247543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5372714455724760508330057 4029535841793570381247543)
                      ·
                        rfl

theorem cell23_7847493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 2, 2, 2].length) (baseStart_7847493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847493 prefixEnd_7847493 := by exact prefixLift 7847493
  have htrace : WordTrace (prefixWord ++ tailWord_7847493) baseStart_7847493 baseEnd_7847493 := by
    simpa [prefixWord, tailWord_7847493, baseEnd_7847493] using wordTrace_append hprefix tailTrace_7847493
  have hstable : (prefixWord ++ tailWord_7847493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847493).length < 2 ^ (prefixWord ++ tailWord_7847493).sum := by decide
  have hdescent : baseEnd_7847493 < baseStart_7847493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847512 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 2, 5]
def baseStart_7847512 : Nat := 118140960795 + 7847512 * 2 ^ 59
def prefixEnd_7847512 : Nat := 4983230072969 + 3 ^ 40 * 7847512 * 2
def baseEnd_7847512 : Nat := 1343181865975335268969985

theorem tailTrace_7847512 : CollatzResearch.WordTrace tailWord_7847512 prefixEnd_7847512 1343181865975335268969985 := by
  unfold tailWord_7847512
  simp only [CollatzResearch.WordTrace]
  refine ⟨143111138372905873596044395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190814851163874498128059193 143111138372905873596044395)
  ·
    refine ⟨214666707559358810394066593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143111138372905873596044395 214666707559358810394066593)
    ·
      refine ⟨161000030669519107795549945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214666707559358810394066593 161000030669519107795549945)
      ·
        refine ⟨120750023002139330846662459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161000030669519107795549945 120750023002139330846662459)
        ·
          refine ⟨181125034503208996269993689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120750023002139330846662459 181125034503208996269993689)
          ·
            refine ⟨135843775877406747202495267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181125034503208996269993689 135843775877406747202495267)
            ·
              refine ⟨203765663816110120803742901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135843775877406747202495267 203765663816110120803742901)
              ·
                refine ⟨19103030982760323825350897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203765663816110120803742901 19103030982760323825350897)
                ·
                  refine ⟨14327273237070242869013173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19103030982760323825350897 14327273237070242869013173)
                  ·
                    refine ⟨1343181865975335268969985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14327273237070242869013173 1343181865975335268969985)
                    ·
                      rfl

theorem cell23_7847512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_7847512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847512 prefixEnd_7847512 := by exact prefixLift 7847512
  have htrace : WordTrace (prefixWord ++ tailWord_7847512) baseStart_7847512 baseEnd_7847512 := by
    simpa [prefixWord, tailWord_7847512, baseEnd_7847512] using wordTrace_append hprefix tailTrace_7847512
  have hstable : (prefixWord ++ tailWord_7847512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847512).length < 2 ^ (prefixWord ++ tailWord_7847512).sum := by decide
  have hdescent : baseEnd_7847512 < baseStart_7847512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847516 : List Nat := [2, 2, 4, 1, 2, 1, 3, 3, 5]
def baseStart_7847516 : Nat := 118140960795 + 7847516 * 2 ^ 59
def prefixEnd_7847516 : Nat := 4983230072969 + 3 ^ 40 * 7847516 * 2
def baseEnd_7847516 : Nat := 447727516872069310139993

theorem tailTrace_7847516 : CollatzResearch.WordTrace tailWord_7847516 prefixEnd_7847516 447727516872069310139993 := by
  unfold tailWord_7847516
  simp only [CollatzResearch.WordTrace]
  refine ⟨143111211318898627937617201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190814948425198170583489601 143111211318898627937617201)
  ·
    refine ⟨107333408489173970953212901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143111211318898627937617201 107333408489173970953212901)
    ·
      refine ⟨20125014091720119553727419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107333408489173970953212901 20125014091720119553727419)
      ·
        refine ⟨30187521137580179330591129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20125014091720119553727419 30187521137580179330591129)
        ·
          refine ⟨22640640853185134497943347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30187521137580179330591129 22640640853185134497943347)
          ·
            refine ⟨33960961279777701746915021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22640640853185134497943347 33960961279777701746915021)
            ·
              refine ⟨12735360479916638155093133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33960961279777701746915021 12735360479916638155093133)
              ·
                refine ⟨4775760179968739308159925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12735360479916638155093133 4775760179968739308159925)
                ·
                  refine ⟨447727516872069310139993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4775760179968739308159925 447727516872069310139993)
                  ·
                    rfl

theorem cell23_7847516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 5].length) (baseStart_7847516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847516 prefixEnd_7847516 := by exact prefixLift 7847516
  have htrace : WordTrace (prefixWord ++ tailWord_7847516) baseStart_7847516 baseEnd_7847516 := by
    simpa [prefixWord, tailWord_7847516, baseEnd_7847516] using wordTrace_append hprefix tailTrace_7847516
  have hstable : (prefixWord ++ tailWord_7847516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847516).length < 2 ^ (prefixWord ++ tailWord_7847516).sum := by decide
  have hdescent : baseEnd_7847516 < baseStart_7847516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847533 : List Nat := [1, 5, 1, 1, 4, 1, 3, 2, 5]
def baseStart_7847533 : Nat := 118140960795 + 7847533 * 2 ^ 59
def prefixEnd_7847533 : Nat := 4983230072969 + 3 ^ 40 * 7847533 * 2
def baseEnd_7847533 : Nat := 447728486779972247194151

theorem tailTrace_7847533 : CollatzResearch.WordTrace tailWord_7847533 prefixEnd_7847533 447728486779972247194151 := by
  unfold tailWord_7847533
  simp only [CollatzResearch.WordTrace]
  refine ⟨286223042678735667778603253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190815361785823778519068835 286223042678735667778603253)
  ·
    refine ⟨26833410251131468854244055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286223042678735667778603253 26833410251131468854244055)
    ·
      refine ⟨40250115376697203281366083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26833410251131468854244055 40250115376697203281366083)
      ·
        refine ⟨60375173065045804922049125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40250115376697203281366083 60375173065045804922049125)
        ·
          refine ⟨11320344949696088422884211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60375173065045804922049125 11320344949696088422884211)
          ·
            refine ⟨16980517424544132634326317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11320344949696088422884211 16980517424544132634326317)
            ·
              refine ⟨6367694034204049737872369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16980517424544132634326317 6367694034204049737872369)
              ·
                refine ⟨4775770525653037303404277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6367694034204049737872369 4775770525653037303404277)
                ·
                  refine ⟨447728486779972247194151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4775770525653037303404277 447728486779972247194151)
                  ·
                    rfl

theorem cell23_7847533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_7847533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847533 prefixEnd_7847533 := by exact prefixLift 7847533
  have htrace : WordTrace (prefixWord ++ tailWord_7847533) baseStart_7847533 baseEnd_7847533 := by
    simpa [prefixWord, tailWord_7847533, baseEnd_7847533] using wordTrace_append hprefix tailTrace_7847533
  have hstable : (prefixWord ++ tailWord_7847533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847533).length < 2 ^ (prefixWord ++ tailWord_7847533).sum := by decide
  have hdescent : baseEnd_7847533 < baseStart_7847533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847566 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_7847566 : Nat := 118140960795 + 7847566 * 2 ^ 59
def prefixEnd_7847566 : Nat := 4983230072969 + 3 ^ 40 * 7847566 * 2
def baseEnd_7847566 : Nat := 4029573325881348595634707

theorem tailTrace_7847566 : CollatzResearch.WordTrace tailWord_7847566 prefixEnd_7847566 4029573325881348595634707 := by
  unfold tailWord_7847566
  simp only [CollatzResearch.WordTrace]
  refine ⟨35778030785952014301819319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190816164191744076276369701 35778030785952014301819319)
  ·
    refine ⟨53667046178928021452728979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35778030785952014301819319 53667046178928021452728979)
    ·
      refine ⟨80500569268392032179093469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53667046178928021452728979 80500569268392032179093469)
      ·
        refine ⟨30187713475647012067160051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80500569268392032179093469 30187713475647012067160051)
        ·
          refine ⟨45281570213470518100740077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30187713475647012067160051 45281570213470518100740077)
          ·
            refine ⟨16980588830051444287777529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45281570213470518100740077 16980588830051444287777529)
            ·
              refine ⟨12735441622538583215833147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16980588830051444287777529 12735441622538583215833147)
              ·
                refine ⟨19103162433807874823749721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12735441622538583215833147 19103162433807874823749721)
                ·
                  refine ⟨14327371825355906117812291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19103162433807874823749721 14327371825355906117812291)
                  ·
                    refine ⟨21491057738033859176718437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14327371825355906117812291 21491057738033859176718437)
                    ·
                      refine ⟨4029573325881348595634707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21491057738033859176718437 4029573325881348595634707)
                      ·
                        rfl

theorem cell23_7847566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_7847566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847566 prefixEnd_7847566 := by exact prefixLift 7847566
  have htrace : WordTrace (prefixWord ++ tailWord_7847566) baseStart_7847566 baseEnd_7847566 := by
    simpa [prefixWord, tailWord_7847566, baseEnd_7847566] using wordTrace_append hprefix tailTrace_7847566
  have hstable : (prefixWord ++ tailWord_7847566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847566).length < 2 ^ (prefixWord ++ tailWord_7847566).sum := by decide
  have hdescent : baseEnd_7847566 < baseStart_7847566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847616 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 3, 1, 3]
def baseStart_7847616 : Nat := 118140960795 + 7847616 * 2 ^ 59
def prefixEnd_7847616 : Nat := 4983230072969 + 3 ^ 40 * 7847616 * 2
def baseEnd_7847616 : Nat := 4029598999914073400009477

theorem tailTrace_7847616 : CollatzResearch.WordTrace tailWord_7847616 prefixEnd_7847616 4029598999914073400009477 := by
  unfold tailWord_7847616
  simp only [CollatzResearch.WordTrace]
  refine ⟨143113034968717486476937351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190817379958289981969249801 143113034968717486476937351)
  ·
    refine ⟨214669552453076229715406027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143113034968717486476937351 214669552453076229715406027)
    ·
      refine ⟨322004328679614344573109041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214669552453076229715406027 322004328679614344573109041)
      ·
        refine ⟨241503246509710758429831781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322004328679614344573109041 241503246509710758429831781)
        ·
          refine ⟨45281858720570767205593459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241503246509710758429831781 45281858720570767205593459)
          ·
            refine ⟨67922788080856150808390189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45281858720570767205593459 67922788080856150808390189)
            ·
              refine ⟨25471045530321056553146321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67922788080856150808390189 25471045530321056553146321)
              ·
                refine ⟨19103284147740792414859741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25471045530321056553146321 19103284147740792414859741)
                ·
                  refine ⟨7163731555402797155572403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19103284147740792414859741 7163731555402797155572403)
                  ·
                    refine ⟨10745597333104195733358605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7163731555402797155572403 10745597333104195733358605)
                    ·
                      refine ⟨4029598999914073400009477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10745597333104195733358605 4029598999914073400009477)
                      ·
                        rfl

theorem cell23_7847616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_7847616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847616 prefixEnd_7847616 := by exact prefixLift 7847616
  have htrace : WordTrace (prefixWord ++ tailWord_7847616) baseStart_7847616 baseEnd_7847616 := by
    simpa [prefixWord, tailWord_7847616, baseEnd_7847616] using wordTrace_append hprefix tailTrace_7847616
  have hstable : (prefixWord ++ tailWord_7847616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847616).length < 2 ^ (prefixWord ++ tailWord_7847616).sum := by decide
  have hdescent : baseEnd_7847616 < baseStart_7847616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847632 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 3, 6]
def baseStart_7847632 : Nat := 118140960795 + 7847632 * 2 ^ 59
def prefixEnd_7847632 : Nat := 4983230072969 + 3 ^ 40 * 7847632 * 2
def baseEnd_7847632 : Nat := 1343202405201515112469801

theorem tailTrace_7847632 : CollatzResearch.WordTrace tailWord_7847632 prefixEnd_7847632 1343202405201515112469801 := by
  unfold tailWord_7847632
  simp only [CollatzResearch.WordTrace]
  refine ⟨143113326752688503843228575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190817769003584671790971433 143113326752688503843228575)
  ·
    refine ⟨214669990129032755764842863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143113326752688503843228575 214669990129032755764842863)
    ·
      refine ⟨322004985193549133647264295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214669990129032755764842863 322004985193549133647264295)
      ·
        refine ⟨483007477790323700470896443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322004985193549133647264295 483007477790323700470896443)
        ·
          refine ⟨724511216685485550706344665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483007477790323700470896443 724511216685485550706344665)
          ·
            refine ⟨543383412514114163029758499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724511216685485550706344665 543383412514114163029758499)
            ·
              refine ⟨815075118771171244544637749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543383412514114163029758499 815075118771171244544637749)
              ·
                refine ⟨76413292384797304176059789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 815075118771171244544637749 76413292384797304176059789)
                ·
                  refine ⟨28654984644298989066022421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76413292384797304176059789 28654984644298989066022421)
                  ·
                    refine ⟨1343202405201515112469801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28654984644298989066022421 1343202405201515112469801)
                    ·
                      rfl

theorem cell23_7847632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3, 6].length) (baseStart_7847632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847632 prefixEnd_7847632 := by exact prefixLift 7847632
  have htrace : WordTrace (prefixWord ++ tailWord_7847632) baseStart_7847632 baseEnd_7847632 := by
    simpa [prefixWord, tailWord_7847632, baseEnd_7847632] using wordTrace_append hprefix tailTrace_7847632
  have hstable : (prefixWord ++ tailWord_7847632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847632).length < 2 ^ (prefixWord ++ tailWord_7847632).sum := by decide
  have hdescent : baseEnd_7847632 < baseStart_7847632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847633 : List Nat := [1, 2, 2, 1, 2, 4, 1, 5, 1, 1, 3]
def baseStart_7847633 : Nat := 118140960795 + 7847633 * 2 ^ 59
def prefixEnd_7847633 : Nat := 4983230072969 + 3 ^ 40 * 7847633 * 2
def baseEnd_7847633 : Nat := 4029607729085199833496899

theorem tailTrace_7847633 : CollatzResearch.WordTrace tailWord_7847633 prefixEnd_7847633 4029607729085199833496899 := by
  unfold tailWord_7847633
  simp only [CollatzResearch.WordTrace]
  refine ⟨286226689978373384857243553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190817793318915589904829035 286226689978373384857243553)
  ·
    refine ⟨214670017483780038642932665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286226689978373384857243553 214670017483780038642932665)
    ·
      refine ⟨161002513112835028982199499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214670017483780038642932665 161002513112835028982199499)
      ·
        refine ⟨241503769669252543473299249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161002513112835028982199499 241503769669252543473299249)
        ·
          refine ⟨181127827251939407604974437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241503769669252543473299249 181127827251939407604974437)
          ·
            refine ⟨33961467609738638925932707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181127827251939407604974437 33961467609738638925932707)
            ·
              refine ⟨50942201414607958388899061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33961467609738638925932707 50942201414607958388899061)
              ·
                refine ⟨4775831382619496098959287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50942201414607958388899061 4775831382619496098959287)
                ·
                  refine ⟨7163747073929244148438931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775831382619496098959287 7163747073929244148438931)
                  ·
                    refine ⟨10745620610893866222658397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7163747073929244148438931 10745620610893866222658397)
                    ·
                      refine ⟨4029607729085199833496899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10745620610893866222658397 4029607729085199833496899)
                      ·
                        rfl

theorem cell23_7847633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 1, 1, 3].length) (baseStart_7847633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847633 prefixEnd_7847633 := by exact prefixLift 7847633
  have htrace : WordTrace (prefixWord ++ tailWord_7847633) baseStart_7847633 baseEnd_7847633 := by
    simpa [prefixWord, tailWord_7847633, baseEnd_7847633] using wordTrace_append hprefix tailTrace_7847633
  have hstable : (prefixWord ++ tailWord_7847633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847633).length < 2 ^ (prefixWord ++ tailWord_7847633).sum := by decide
  have hdescent : baseEnd_7847633 < baseStart_7847633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847659 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 3]
def baseStart_7847659 : Nat := 118140960795 + 7847659 * 2 ^ 59
def prefixEnd_7847659 : Nat := 4983230072969 + 3 ^ 40 * 7847659 * 2
def baseEnd_7847659 : Nat := 4029621079582216731771779

theorem tailTrace_7847659 : CollatzResearch.WordTrace tailWord_7847659 prefixEnd_7847659 4029621079582216731771779 := by
  unfold tailWord_7847659
  simp only [CollatzResearch.WordTrace]
  refine ⟨286227638276279191297690031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190818425517519460865126687 286227638276279191297690031)
  ·
    refine ⟨429341457414418786946535047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286227638276279191297690031 429341457414418786946535047)
    ·
      refine ⟨644012186121628180419802571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429341457414418786946535047 644012186121628180419802571)
      ·
        refine ⟨966018279182442270629703857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644012186121628180419802571 966018279182442270629703857)
        ·
          refine ⟨724513709386831702972277893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 966018279182442270629703857 724513709386831702972277893)
          ·
            refine ⟨135846320510030944307302105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 724513709386831702972277893 135846320510030944307302105)
            ·
              refine ⟨101884740382523208230476579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135846320510030944307302105 101884740382523208230476579)
              ·
                refine ⟨152827110573784812345714869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101884740382523208230476579 152827110573784812345714869)
                ·
                  refine ⟨14327541616292326157410769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152827110573784812345714869 14327541616292326157410769)
                  ·
                    refine ⟨10745656212219244618058077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14327541616292326157410769 10745656212219244618058077)
                    ·
                      refine ⟨4029621079582216731771779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10745656212219244618058077 4029621079582216731771779)
                      ·
                        rfl

theorem cell23_7847659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 3].length) (baseStart_7847659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847659 prefixEnd_7847659 := by exact prefixLift 7847659
  have htrace : WordTrace (prefixWord ++ tailWord_7847659) baseStart_7847659 baseEnd_7847659 := by
    simpa [prefixWord, tailWord_7847659, baseEnd_7847659] using wordTrace_append hprefix tailTrace_7847659
  have hstable : (prefixWord ++ tailWord_7847659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847659).length < 2 ^ (prefixWord ++ tailWord_7847659).sum := by decide
  have hdescent : baseEnd_7847659 < baseStart_7847659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847679 : List Nat := [1, 1, 2, 2, 1, 3, 6, 7]
def baseStart_7847679 : Nat := 118140960795 + 7847679 * 2 ^ 59
def prefixEnd_7847679 : Nat := 4983230072969 + 3 ^ 40 * 7847679 * 2
def baseEnd_7847679 : Nat := 149245605525752098278581

theorem tailTrace_7847679 : CollatzResearch.WordTrace tailWord_7847679 prefixEnd_7847679 149245605525752098278581 := by
  unfold tailWord_7847679
  simp only [CollatzResearch.WordTrace]
  refine ⟨286228367736206734713418091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190818911824137823142278727 286228367736206734713418091)
  ·
    refine ⟨429342551604310102070127137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286228367736206734713418091 429342551604310102070127137)
    ·
      refine ⟨322006913703232576552595353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429342551604310102070127137 322006913703232576552595353)
      ·
        refine ⟨241505185277424432414446515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322006913703232576552595353 241505185277424432414446515)
        ·
          refine ⟨362257777916136648621669773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241505185277424432414446515 362257777916136648621669773)
          ·
            refine ⟨135846666718551243233126165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362257777916136648621669773 135846666718551243233126165)
            ·
              refine ⟨6367812502432089526552789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135846666718551243233126165 6367812502432089526552789)
              ·
                refine ⟨149245605525752098278581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6367812502432089526552789 149245605525752098278581)
                ·
                  rfl

theorem cell23_7847679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 7].length) (baseStart_7847679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847679 prefixEnd_7847679 := by exact prefixLift 7847679
  have htrace : WordTrace (prefixWord ++ tailWord_7847679) baseStart_7847679 baseEnd_7847679 := by
    simpa [prefixWord, tailWord_7847679, baseEnd_7847679] using wordTrace_append hprefix tailTrace_7847679
  have hstable : (prefixWord ++ tailWord_7847679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847679).length < 2 ^ (prefixWord ++ tailWord_7847679).sum := by decide
  have hdescent : baseEnd_7847679 < baseStart_7847679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847689 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 3, 3, 3]
def baseStart_7847689 : Nat := 118140960795 + 7847689 * 2 ^ 59
def prefixEnd_7847689 : Nat := 4983230072969 + 3 ^ 40 * 7847689 * 2
def baseEnd_7847689 : Nat := 4029636484001851614396641

theorem tailTrace_7847689 : CollatzResearch.WordTrace tailWord_7847689 prefixEnd_7847689 4029636484001851614396641 := by
  unfold tailWord_7847689
  simp only [CollatzResearch.WordTrace]
  refine ⟨286228732466170506421282121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190819154977447004280854747 286228732466170506421282121)
  ·
    refine ⟨214671549349627879815961591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286228732466170506421282121 214671549349627879815961591)
    ·
      refine ⟨322007324024441819723942387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214671549349627879815961591 322007324024441819723942387)
      ·
        refine ⟨483010986036662729585913581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322007324024441819723942387 483010986036662729585913581)
        ·
          refine ⟨181129119763748523594717593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483010986036662729585913581 181129119763748523594717593)
          ·
            refine ⟨135846839822811392696038195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181129119763748523594717593 135846839822811392696038195)
            ·
              refine ⟨203770259734217089044057293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135846839822811392696038195 203770259734217089044057293)
              ·
                refine ⟨76413847400331408391521485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203770259734217089044057293 76413847400331408391521485)
                ·
                  refine ⟨28655192775124278146820557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76413847400331408391521485 28655192775124278146820557)
                  ·
                    refine ⟨10745697290671604305057709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28655192775124278146820557 10745697290671604305057709)
                    ·
                      refine ⟨4029636484001851614396641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10745697290671604305057709 4029636484001851614396641)
                      ·
                        rfl

theorem cell23_7847689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 3, 3].length) (baseStart_7847689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847689 prefixEnd_7847689 := by exact prefixLift 7847689
  have htrace : WordTrace (prefixWord ++ tailWord_7847689) baseStart_7847689 baseEnd_7847689 := by
    simpa [prefixWord, tailWord_7847689, baseEnd_7847689] using wordTrace_append hprefix tailTrace_7847689
  have hstable : (prefixWord ++ tailWord_7847689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847689).length < 2 ^ (prefixWord ++ tailWord_7847689).sum := by decide
  have hdescent : baseEnd_7847689 < baseStart_7847689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847749 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_7847749 : Nat := 118140960795 + 7847749 * 2 ^ 59
def prefixEnd_7847749 : Nat := 4983230072969 + 3 ^ 40 * 7847749 * 2
def baseEnd_7847749 : Nat := 4029667292841121379646365

theorem tailTrace_7847749 : CollatzResearch.WordTrace tailWord_7847749 prefixEnd_7847749 4029667292841121379646365 := by
  unfold tailWord_7847749
  simp only [CollatzResearch.WordTrace]
  refine ⟨286230920845953136668466301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190820613897302091112310867 286230920845953136668466301)
  ·
    refine ⟨107336595317232426250674863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286230920845953136668466301 107336595317232426250674863)
    ·
      refine ⟨161004892975848639376012295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107336595317232426250674863 161004892975848639376012295)
      ·
        refine ⟨241507339463772959064018443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161004892975848639376012295 241507339463772959064018443)
        ·
          refine ⟨362261009195659438596027665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241507339463772959064018443 362261009195659438596027665)
          ·
            refine ⟨271695756896744578947020749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362261009195659438596027665 271695756896744578947020749)
            ·
              refine ⟨101885908836279217105132781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271695756896744578947020749 101885908836279217105132781)
              ·
                refine ⟨38207215813604706414424793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101885908836279217105132781 38207215813604706414424793)
                ·
                  refine ⟨28655411860203529810818595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38207215813604706414424793 28655411860203529810818595)
                  ·
                    refine ⟨42983117790305294716227893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28655411860203529810818595 42983117790305294716227893)
                    ·
                      refine ⟨4029667292841121379646365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42983117790305294716227893 4029667292841121379646365)
                      ·
                        rfl

theorem cell23_7847749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_7847749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847749 prefixEnd_7847749 := by exact prefixLift 7847749
  have htrace : WordTrace (prefixWord ++ tailWord_7847749) baseStart_7847749 baseEnd_7847749 := by
    simpa [prefixWord, tailWord_7847749, baseEnd_7847749] using wordTrace_append hprefix tailTrace_7847749
  have hstable : (prefixWord ++ tailWord_7847749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847749).length < 2 ^ (prefixWord ++ tailWord_7847749).sum := by decide
  have hdescent : baseEnd_7847749 < baseStart_7847749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847757 : List Nat := [1, 6, 1, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_7847757 : Nat := 118140960795 + 7847757 * 2 ^ 59
def prefixEnd_7847757 : Nat := 4983230072969 + 3 ^ 40 * 7847757 * 2
def baseEnd_7847757 : Nat := 4029671400686357348346329

theorem tailTrace_7847757 : CollatzResearch.WordTrace tailWord_7847757 prefixEnd_7847757 4029671400686357348346329 := by
  unfold tailWord_7847757
  simp only [CollatzResearch.WordTrace]
  refine ⟨286231212629924154034757525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190820808419949436023171683 286231212629924154034757525)
  ·
    refine ⟨13417088092027694720379259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 286231212629924154034757525 13417088092027694720379259)
    ·
      refine ⟨20125632138041542080568889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13417088092027694720379259 20125632138041542080568889)
      ·
        refine ⟨15094224103531156560426667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20125632138041542080568889 15094224103531156560426667)
        ·
          refine ⟨22641336155296734840640001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15094224103531156560426667 22641336155296734840640001)
          ·
            refine ⟨16981002116472551130480001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22641336155296734840640001 16981002116472551130480001)
            ·
              refine ⟨12735751587354413347860001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16981002116472551130480001 12735751587354413347860001)
              ·
                refine ⟨9551813690515810010895001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12735751587354413347860001 9551813690515810010895001)
                ·
                  refine ⟨7163860267886857508171251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9551813690515810010895001 7163860267886857508171251)
                  ·
                    refine ⟨10745790401830286262256877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7163860267886857508171251 10745790401830286262256877)
                    ·
                      refine ⟨4029671400686357348346329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10745790401830286262256877 4029671400686357348346329)
                      ·
                        rfl

theorem cell23_7847757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_7847757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847757 prefixEnd_7847757 := by exact prefixLift 7847757
  have htrace : WordTrace (prefixWord ++ tailWord_7847757) baseStart_7847757 baseEnd_7847757 := by
    simpa [prefixWord, tailWord_7847757, baseEnd_7847757] using wordTrace_append hprefix tailTrace_7847757
  have hstable : (prefixWord ++ tailWord_7847757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847757).length < 2 ^ (prefixWord ++ tailWord_7847757).sum := by decide
  have hdescent : baseEnd_7847757 < baseStart_7847757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847769 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 7]
def baseStart_7847769 : Nat := 118140960795 + 7847769 * 2 ^ 59
def prefixEnd_7847769 : Nat := 4983230072969 + 3 ^ 40 * 7847769 * 2
def baseEnd_7847769 : Nat := 447741951383801255710697

theorem tailTrace_7847769 : CollatzResearch.WordTrace tailWord_7847769 prefixEnd_7847769 447741951383801255710697 := by
  unfold tailWord_7847769
  simp only [CollatzResearch.WordTrace]
  refine ⟨286231650305880680084194361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190821100203920453389462907 286231650305880680084194361)
  ·
    refine ⟨214673737729410510063145771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286231650305880680084194361 214673737729410510063145771)
    ·
      refine ⟨322010606594115765094718657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214673737729410510063145771 322010606594115765094718657)
      ·
        refine ⟨241507954945586823821038993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322010606594115765094718657 241507954945586823821038993)
        ·
          refine ⟨181130966209190117865779245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241507954945586823821038993 181130966209190117865779245)
          ·
            refine ⟨67924112328446294199667217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181130966209190117865779245 67924112328446294199667217)
            ·
              refine ⟨50943084246334720649750413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67924112328446294199667217 50943084246334720649750413)
              ·
                refine ⟨19103656592375520243656405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50943084246334720649750413 19103656592375520243656405)
                ·
                  refine ⟨447741951383801255710697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19103656592375520243656405 447741951383801255710697)
                  ·
                    rfl

theorem cell23_7847769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 7].length) (baseStart_7847769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847769 prefixEnd_7847769 := by exact prefixLift 7847769
  have htrace : WordTrace (prefixWord ++ tailWord_7847769) baseStart_7847769 baseEnd_7847769 := by
    simpa [prefixWord, tailWord_7847769, baseEnd_7847769] using wordTrace_append hprefix tailTrace_7847769
  have hstable : (prefixWord ++ tailWord_7847769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847769).length < 2 ^ (prefixWord ++ tailWord_7847769).sum := by decide
  have hdescent : baseEnd_7847769 < baseStart_7847769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847776 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 4]
def baseStart_7847776 : Nat := 118140960795 + 7847776 * 2 ^ 59
def prefixEnd_7847776 : Nat := 4983230072969 + 3 ^ 40 * 7847776 * 2
def baseEnd_7847776 : Nat := 4029681156818792774008741

theorem tailTrace_7847776 : CollatzResearch.WordTrace tailWord_7847776 prefixEnd_7847776 4029681156818792774008741 := by
  unfold tailWord_7847776
  simp only [CollatzResearch.WordTrace]
  refine ⟨143115952808427660139849591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190821270411236880186466121 143115952808427660139849591)
  ·
    refine ⟨214673929212641490209774387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143115952808427660139849591 214673929212641490209774387)
    ·
      refine ⟨322010893818962235314661581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214673929212641490209774387 322010893818962235314661581)
      ·
        refine ⟨120754085182110838242998093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322010893818962235314661581 120754085182110838242998093)
        ·
          refine ⟨45282781943291564341124285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120754085182110838242998093 45282781943291564341124285)
          ·
            refine ⟨16981043228734336627921607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45282781943291564341124285 16981043228734336627921607)
            ·
              refine ⟨25471564843101504941882411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16981043228734336627921607 25471564843101504941882411)
              ·
                refine ⟨38207347264652257412823617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25471564843101504941882411 38207347264652257412823617)
                ·
                  refine ⟨28655510448489193059617713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38207347264652257412823617 28655510448489193059617713)
                  ·
                    refine ⟨21491632836366894794713285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28655510448489193059617713 21491632836366894794713285)
                    ·
                      refine ⟨4029681156818792774008741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21491632836366894794713285 4029681156818792774008741)
                      ·
                        rfl

theorem cell23_7847776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_7847776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847776 prefixEnd_7847776 := by exact prefixLift 7847776
  have htrace : WordTrace (prefixWord ++ tailWord_7847776) baseStart_7847776 baseEnd_7847776 := by
    simpa [prefixWord, tailWord_7847776, baseEnd_7847776] using wordTrace_append hprefix tailTrace_7847776
  have hstable : (prefixWord ++ tailWord_7847776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847776).length < 2 ^ (prefixWord ++ tailWord_7847776).sum := by decide
  have hdescent : baseEnd_7847776 < baseStart_7847776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847780 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 1, 4, 2]
def baseStart_7847780 : Nat := 118140960795 + 7847780 * 2 ^ 59
def prefixEnd_7847780 : Nat := 4983230072969 + 3 ^ 40 * 7847780 * 2
def baseEnd_7847780 : Nat := 4029683210741410758358723

theorem tailTrace_7847780 : CollatzResearch.WordTrace tailWord_7847780 prefixEnd_7847780 4029683210741410758358723 := by
  unfold tailWord_7847780
  simp only [CollatzResearch.WordTrace]
  refine ⟨143116025754420414481422397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190821367672560552641896529 143116025754420414481422397)
  ·
    refine ⟨53668509657907655430533399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143116025754420414481422397 53668509657907655430533399)
    ·
      refine ⟨80502764486861483145800099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53668509657907655430533399 80502764486861483145800099)
      ·
        refine ⟨120754146730292224718700149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80502764486861483145800099 120754146730292224718700149)
        ·
          refine ⟨11320701255964896067378139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120754146730292224718700149 11320701255964896067378139)
          ·
            refine ⟨16981051883947344101067209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11320701255964896067378139 16981051883947344101067209)
            ·
              refine ⟨12735788912960508075800407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16981051883947344101067209 12735788912960508075800407)
              ·
                refine ⟨19103683369440762113700611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12735788912960508075800407 19103683369440762113700611)
                ·
                  refine ⟨28655525054161143170550917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19103683369440762113700611 28655525054161143170550917)
                  ·
                    refine ⟨5372910947655214344478297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28655525054161143170550917 5372910947655214344478297)
                    ·
                      refine ⟨4029683210741410758358723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5372910947655214344478297 4029683210741410758358723)
                      ·
                        rfl

theorem cell23_7847780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_7847780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847780 prefixEnd_7847780 := by exact prefixLift 7847780
  have htrace : WordTrace (prefixWord ++ tailWord_7847780) baseStart_7847780 baseEnd_7847780 := by
    simpa [prefixWord, tailWord_7847780, baseEnd_7847780] using wordTrace_append hprefix tailTrace_7847780
  have hstable : (prefixWord ++ tailWord_7847780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847780).length < 2 ^ (prefixWord ++ tailWord_7847780).sum := by decide
  have hdescent : baseEnd_7847780 < baseStart_7847780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847849 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 6]
def baseStart_7847849 : Nat := 118140960795 + 7847849 * 2 ^ 59
def prefixEnd_7847849 : Nat := 4983230072969 + 3 ^ 40 * 7847849 * 2
def baseEnd_7847849 : Nat := 4029718640906570988395905

theorem tailTrace_7847849 : CollatzResearch.WordTrace tailWord_7847849 prefixEnd_7847849 4029718640906570988395905 := by
  unfold tailWord_7847849
  simp only [CollatzResearch.WordTrace]
  refine ⟨286234568145590853747106601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190823045430393902498071067 286234568145590853747106601)
  ·
    refine ⟨214675926109193140310329951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286234568145590853747106601 214675926109193140310329951)
    ·
      refine ⟨322013889163789710465494927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214675926109193140310329951 322013889163789710465494927)
      ·
        refine ⟨483020833745684565698242391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322013889163789710465494927 483020833745684565698242391)
        ·
          refine ⟨724531250618526848547363587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483020833745684565698242391 724531250618526848547363587)
          ·
            refine ⟨1086796875927790272821045381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724531250618526848547363587 1086796875927790272821045381)
            ·
              refine ⟨203774414236460676153946009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1086796875927790272821045381 203774414236460676153946009)
              ·
                refine ⟨152830810677345507115459507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203774414236460676153946009 152830810677345507115459507)
                ·
                  refine ⟨229246216016018260673189261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152830810677345507115459507 229246216016018260673189261)
                  ·
                    refine ⟨85967331006006847752445973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 229246216016018260673189261 85967331006006847752445973)
                    ·
                      refine ⟨4029718640906570988395905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85967331006006847752445973 4029718640906570988395905)
                      ·
                        rfl

theorem cell23_7847849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_7847849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847849 prefixEnd_7847849 := by exact prefixLift 7847849
  have htrace : WordTrace (prefixWord ++ tailWord_7847849) baseStart_7847849 baseEnd_7847849 := by
    simpa [prefixWord, tailWord_7847849, baseEnd_7847849] using wordTrace_append hprefix tailTrace_7847849
  have hstable : (prefixWord ++ tailWord_7847849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847849).length < 2 ^ (prefixWord ++ tailWord_7847849).sum := by decide
  have hdescent : baseEnd_7847849 < baseStart_7847849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847856 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 3]
def baseStart_7847856 : Nat := 118140960795 + 7847856 * 2 ^ 59
def prefixEnd_7847856 : Nat := 4983230072969 + 3 ^ 40 * 7847856 * 2
def baseEnd_7847856 : Nat := 4029722235271152461008373

theorem tailTrace_7847856 : CollatzResearch.WordTrace tailWord_7847856 prefixEnd_7847856 4029722235271152461008373 := by
  unfold tailWord_7847856
  simp only [CollatzResearch.WordTrace]
  refine ⟨143117411728282746971305711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190823215637710329295074281 143117411728282746971305711)
  ·
    refine ⟨214676117592424120456958567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143117411728282746971305711 214676117592424120456958567)
    ·
      refine ⟨322014176388636180685437851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214676117592424120456958567 322014176388636180685437851)
      ·
        refine ⟨483021264582954271028156777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322014176388636180685437851 483021264582954271028156777)
        ·
          refine ⟨362265948437215703271117583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483021264582954271028156777 362265948437215703271117583)
          ·
            refine ⟨543398922655823554906676375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362265948437215703271117583 543398922655823554906676375)
            ·
              refine ⟨815098383983735332360014563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543398922655823554906676375 815098383983735332360014563)
              ·
                refine ⟨1222647575975602998540021845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815098383983735332360014563 1222647575975602998540021845)
                ·
                  refine ⟨14327901280964097639140881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1222647575975602998540021845 14327901280964097639140881)
                  ·
                    refine ⟨10745925960723073229355661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14327901280964097639140881 10745925960723073229355661)
                    ·
                      refine ⟨4029722235271152461008373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10745925960723073229355661 4029722235271152461008373)
                      ·
                        rfl

theorem cell23_7847856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 3].length) (baseStart_7847856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847856 prefixEnd_7847856 := by exact prefixLift 7847856
  have htrace : WordTrace (prefixWord ++ tailWord_7847856) baseStart_7847856 baseEnd_7847856 := by
    simpa [prefixWord, tailWord_7847856, baseEnd_7847856] using wordTrace_append hprefix tailTrace_7847856
  have hstable : (prefixWord ++ tailWord_7847856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847856).length < 2 ^ (prefixWord ++ tailWord_7847856).sum := by decide
  have hdescent : baseEnd_7847856 < baseStart_7847856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847859 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 10]
def baseStart_7847859 : Nat := 118140960795 + 7847859 * 2 ^ 59
def prefixEnd_7847859 : Nat := 4983230072969 + 3 ^ 40 * 7847859 * 2
def baseEnd_7847859 : Nat := 447747086190346216585651

theorem tailTrace_7847859 : CollatzResearch.WordTrace tailWord_7847859 prefixEnd_7847859 447747086190346216585651 := by
  unfold tailWord_7847859
  simp only [CollatzResearch.WordTrace]
  refine ⟨286234932875554625454970631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190823288583703083636647087 286234932875554625454970631)
  ·
    refine ⟨429352399313331938182455947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286234932875554625454970631 429352399313331938182455947)
    ·
      refine ⟨644028598969997907273683921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429352399313331938182455947 644028598969997907273683921)
      ·
        refine ⟨483021449227498430455262941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644028598969997907273683921 483021449227498430455262941)
        ·
          refine ⟨181133043460311911420723603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483021449227498430455262941 181133043460311911420723603)
          ·
            refine ⟨271699565190467867131085405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181133043460311911420723603 271699565190467867131085405)
            ·
              refine ⟨101887336946425450174157027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271699565190467867131085405 101887336946425450174157027)
              ·
                refine ⟨152831005419638175261235541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101887336946425450174157027 152831005419638175261235541)
                ·
                  refine ⟨447747086190346216585651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 152831005419638175261235541 447747086190346216585651)
                  ·
                    rfl

theorem cell23_7847859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 10].length) (baseStart_7847859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847859 prefixEnd_7847859 := by exact prefixLift 7847859
  have htrace : WordTrace (prefixWord ++ tailWord_7847859) baseStart_7847859 baseEnd_7847859 := by
    simpa [prefixWord, tailWord_7847859, baseEnd_7847859] using wordTrace_append hprefix tailTrace_7847859
  have hstable : (prefixWord ++ tailWord_7847859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847859).length < 2 ^ (prefixWord ++ tailWord_7847859).sum := by decide
  have hdescent : baseEnd_7847859 < baseStart_7847859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847880 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 3, 4]
def baseStart_7847880 : Nat := 118140960795 + 7847880 * 2 ^ 59
def prefixEnd_7847880 : Nat := 4983230072969 + 3 ^ 40 * 7847880 * 2
def baseEnd_7847880 : Nat := 1343244852935620122369421

theorem tailTrace_7847880 : CollatzResearch.WordTrace tailWord_7847880 prefixEnd_7847880 1343244852935620122369421 := by
  unfold tailWord_7847880
  simp only [CollatzResearch.WordTrace]
  refine ⟨143117849404239273020742547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190823799205652364027656729 143117849404239273020742547)
  ·
    refine ⟨214676774106358909531113821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143117849404239273020742547 214676774106358909531113821)
    ·
      refine ⟨80503790289884591074167683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214676774106358909531113821 80503790289884591074167683)
      ·
        refine ⟨120755685434826886611251525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80503790289884591074167683 120755685434826886611251525)
        ·
          refine ⟨22641691019030041239609661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120755685434826886611251525 22641691019030041239609661)
          ·
            refine ⟨8490634132136265464853623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22641691019030041239609661 8490634132136265464853623)
            ·
              refine ⟨12735951198204398197280435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8490634132136265464853623 12735951198204398197280435)
              ·
                refine ⟨19103926797306597295920653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12735951198204398197280435 19103926797306597295920653)
                ·
                  refine ⟨7163972548989973985970245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19103926797306597295920653 7163972548989973985970245)
                  ·
                    refine ⟨1343244852935620122369421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7163972548989973985970245 1343244852935620122369421)
                    ·
                      rfl

theorem cell23_7847880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_7847880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847880 prefixEnd_7847880 := by exact prefixLift 7847880
  have htrace : WordTrace (prefixWord ++ tailWord_7847880) baseStart_7847880 baseEnd_7847880 := by
    simpa [prefixWord, tailWord_7847880, baseEnd_7847880] using wordTrace_append hprefix tailTrace_7847880
  have hstable : (prefixWord ++ tailWord_7847880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847880).length < 2 ^ (prefixWord ++ tailWord_7847880).sum := by decide
  have hdescent : baseEnd_7847880 < baseStart_7847880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847893 : List Nat := [1, 3, 2, 3, 2, 2, 1, 3, 6]
def baseStart_7847893 : Nat := 118140960795 + 7847893 * 2 ^ 59
def prefixEnd_7847893 : Nat := 4983230072969 + 3 ^ 40 * 7847893 * 2
def baseEnd_7847893 : Nat := 447749026006152090693967

theorem tailTrace_7847893 : CollatzResearch.WordTrace tailWord_7847893 prefixEnd_7847893 447749026006152090693967 := by
  unfold tailWord_7847893
  simp only [CollatzResearch.WordTrace]
  refine ⟨286236172957431449261708333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190824115304954299507805555 286236172957431449261708333)
  ·
    refine ⟨107338564859036793473140625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286236172957431449261708333 107338564859036793473140625)
    ·
      refine ⟨80503923644277595104855469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107338564859036793473140625 80503923644277595104855469)
      ·
        refine ⟨30188971366604098164320801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80503923644277595104855469 30188971366604098164320801)
        ·
          refine ⟨22641728524953073623240601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30188971366604098164320801 22641728524953073623240601)
          ·
            refine ⟨16981296393714805217430451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22641728524953073623240601 16981296393714805217430451)
            ·
              refine ⟨25471944590572207826145677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16981296393714805217430451 25471944590572207826145677)
              ·
                refine ⟨9551979221464577934804629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25471944590572207826145677 9551979221464577934804629)
                ·
                  refine ⟨447749026006152090693967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9551979221464577934804629 447749026006152090693967)
                  ·
                    rfl

theorem cell23_7847893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 6].length) (baseStart_7847893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847893 prefixEnd_7847893 := by exact prefixLift 7847893
  have htrace : WordTrace (prefixWord ++ tailWord_7847893) baseStart_7847893 baseEnd_7847893 := by
    simpa [prefixWord, tailWord_7847893, baseEnd_7847893] using wordTrace_append hprefix tailTrace_7847893
  have hstable : (prefixWord ++ tailWord_7847893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847893).length < 2 ^ (prefixWord ++ tailWord_7847893).sum := by decide
  have hdescent : baseEnd_7847893 < baseStart_7847893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
