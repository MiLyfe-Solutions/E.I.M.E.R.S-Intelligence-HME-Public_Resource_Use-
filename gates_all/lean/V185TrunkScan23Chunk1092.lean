import V185TrunkScan23Chunk1091

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6465206 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_6465206 : Nat := 118140960795 + 6465206 * 2 ^ 59
def prefixEnd_6465206 : Nat := 4983230072969 + 3 ^ 40 * 6465206 * 2
def baseEnd_6465206 : Nat := 3319758208332137085492065

theorem tailTrace_6465206 : CollatzResearch.WordTrace tailWord_6465206 prefixEnd_6465206 3319758208332137085492065 := by
  unfold tailWord_6465206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14737839688479394132656467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157203623343780204081668981 14737839688479394132656467)
  ·
    refine ⟨22106759532719091198984701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14737839688479394132656467 22106759532719091198984701)
    ·
      refine ⟨8290034824769659199619263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22106759532719091198984701 8290034824769659199619263)
      ·
        refine ⟨12435052237154488799428895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8290034824769659199619263 12435052237154488799428895)
        ·
          refine ⟨18652578355731733199143343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12435052237154488799428895 18652578355731733199143343)
          ·
            refine ⟨27978867533597599798715015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18652578355731733199143343 27978867533597599798715015)
            ·
              refine ⟨41968301300396399698072523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27978867533597599798715015 41968301300396399698072523)
              ·
                refine ⟨62952451950594599547108785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41968301300396399698072523 62952451950594599547108785)
                ·
                  refine ⟨47214338962945949660331589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62952451950594599547108785 47214338962945949660331589)
                  ·
                    refine ⟨8852688555552365561312173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47214338962945949660331589 8852688555552365561312173)
                    ·
                      refine ⟨3319758208332137085492065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8852688555552365561312173 3319758208332137085492065)
                      ·
                        rfl

theorem cell23_6465206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_6465206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465206 prefixEnd_6465206 := by exact prefixLift 6465206
  have htrace : WordTrace (prefixWord ++ tailWord_6465206) baseStart_6465206 baseEnd_6465206 := by
    simpa [prefixWord, tailWord_6465206, baseEnd_6465206] using wordTrace_append hprefix tailTrace_6465206
  have hstable : (prefixWord ++ tailWord_6465206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465206).length < 2 ^ (prefixWord ++ tailWord_6465206).sum := by decide
  have hdescent : baseEnd_6465206 < baseStart_6465206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465259 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 2, 4, 2]
def baseStart_6465259 : Nat := 118140960795 + 6465259 * 2 ^ 59
def prefixEnd_6465259 : Nat := 4983230072969 + 3 ^ 40 * 6465259 * 2
def baseEnd_6465259 : Nat := 3319785422806825378129321

theorem tailTrace_6465259 : CollatzResearch.WordTrace tailWord_6465259 prefixEnd_6465259 3319785422806825378129321 := by
  unfold tailWord_6465259
  simp only [CollatzResearch.WordTrace]
  refine ⟨235807368084478296174182831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157204912056318864116121887 235807368084478296174182831)
  ·
    refine ⟨353711052126717444261274247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235807368084478296174182831 353711052126717444261274247)
    ·
      refine ⟨530566578190076166391911371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353711052126717444261274247 530566578190076166391911371)
      ·
        refine ⟨795849867285114249587867057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530566578190076166391911371 795849867285114249587867057)
        ·
          refine ⟨596887400463835687190900293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 795849867285114249587867057 596887400463835687190900293)
          ·
            refine ⟨111916387586969191348293805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 596887400463835687190900293 111916387586969191348293805)
            ·
              refine ⟨41968645345113446755610177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111916387586969191348293805 41968645345113446755610177)
              ·
                refine ⟨31476484008835085066707633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41968645345113446755610177 31476484008835085066707633)
                ·
                  refine ⟨23607363006626313800030725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31476484008835085066707633 23607363006626313800030725)
                  ·
                    refine ⟨4426380563742433837505761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23607363006626313800030725 4426380563742433837505761)
                    ·
                      refine ⟨3319785422806825378129321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4426380563742433837505761 3319785422806825378129321)
                      ·
                        rfl

theorem cell23_6465259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 4, 2].length) (baseStart_6465259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465259 prefixEnd_6465259 := by exact prefixLift 6465259
  have htrace : WordTrace (prefixWord ++ tailWord_6465259) baseStart_6465259 baseEnd_6465259 := by
    simpa [prefixWord, tailWord_6465259, baseEnd_6465259] using wordTrace_append hprefix tailTrace_6465259
  have hstable : (prefixWord ++ tailWord_6465259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465259).length < 2 ^ (prefixWord ++ tailWord_6465259).sum := by decide
  have hdescent : baseEnd_6465259 < baseStart_6465259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465303 : List Nat := [1, 1, 3, 4, 2, 1, 3, 3, 1, 4]
def baseStart_6465303 : Nat := 118140960795 + 6465303 * 2 ^ 59
def prefixEnd_6465303 : Nat := 4983230072969 + 3 ^ 40 * 6465303 * 2
def baseEnd_6465303 : Nat := 1106602671985207735326373

theorem tailTrace_6465303 : CollatzResearch.WordTrace tailWord_6465303 prefixEnd_6465303 1106602671985207735326373 := by
  unfold tailWord_6465303
  simp only [CollatzResearch.WordTrace]
  refine ⟨235808972896318891688784563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157205981930879261125856375 235808972896318891688784563)
  ·
    refine ⟨353713459344478337533176845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235808972896318891688784563 353713459344478337533176845)
    ·
      refine ⟨132642547254179376574941317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353713459344478337533176845 132642547254179376574941317)
      ·
        refine ⟨24870477610158633107801497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132642547254179376574941317 24870477610158633107801497)
        ·
          refine ⟨18652858207618974830851123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24870477610158633107801497 18652858207618974830851123)
          ·
            refine ⟨27979287311428462246276685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18652858207618974830851123 27979287311428462246276685)
            ·
              refine ⟨10492232741785673342353757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27979287311428462246276685 10492232741785673342353757)
              ·
                refine ⟨3934587278169627503382659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10492232741785673342353757 3934587278169627503382659)
                ·
                  refine ⟨5901880917254441255073989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3934587278169627503382659 5901880917254441255073989)
                  ·
                    refine ⟨1106602671985207735326373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5901880917254441255073989 1106602671985207735326373)
                    ·
                      rfl

theorem cell23_6465303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_6465303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465303 prefixEnd_6465303 := by exact prefixLift 6465303
  have htrace : WordTrace (prefixWord ++ tailWord_6465303) baseStart_6465303 baseEnd_6465303 := by
    simpa [prefixWord, tailWord_6465303, baseEnd_6465303] using wordTrace_append hprefix tailTrace_6465303
  have hstable : (prefixWord ++ tailWord_6465303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465303).length < 2 ^ (prefixWord ++ tailWord_6465303).sum := by decide
  have hdescent : baseEnd_6465303 < baseStart_6465303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465310 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6465310 : Nat := 118140960795 + 6465310 * 2 ^ 59
def prefixEnd_6465310 : Nat := 4983230072969 + 3 ^ 40 * 6465310 * 2
def baseEnd_6465310 : Nat := 3319811610320204678591587

theorem tailTrace_6465310 : CollatzResearch.WordTrace tailWord_6465310 prefixEnd_6465310 3319811610320204678591587 := by
  unfold tailWord_6465310
  simp only [CollatzResearch.WordTrace]
  refine ⟨29476153525911691485536173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157206152138195687922859589 29476153525911691485536173)
  ·
    refine ⟨11053557572216884307076065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29476153525911691485536173 11053557572216884307076065)
    ·
      refine ⟨8290168179162663230307049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11053557572216884307076065 8290168179162663230307049)
      ·
        refine ⟨6217626134371997422730287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8290168179162663230307049 6217626134371997422730287)
        ·
          refine ⟨9326439201557996134095431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6217626134371997422730287 9326439201557996134095431)
          ·
            refine ⟨13989658802336994201143147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9326439201557996134095431 13989658802336994201143147)
            ·
              refine ⟨20984488203505491301714721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13989658802336994201143147 20984488203505491301714721)
              ·
                refine ⟨15738366152629118476286041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20984488203505491301714721 15738366152629118476286041)
                ·
                  refine ⟨11803774614471838857214531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15738366152629118476286041 11803774614471838857214531)
                  ·
                    refine ⟨17705661921707758285821797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11803774614471838857214531 17705661921707758285821797)
                    ·
                      refine ⟨3319811610320204678591587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17705661921707758285821797 3319811610320204678591587)
                      ·
                        rfl

theorem cell23_6465310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6465310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465310 prefixEnd_6465310 := by exact prefixLift 6465310
  have htrace : WordTrace (prefixWord ++ tailWord_6465310) baseStart_6465310 baseEnd_6465310 := by
    simpa [prefixWord, tailWord_6465310, baseEnd_6465310] using wordTrace_append hprefix tailTrace_6465310
  have hstable : (prefixWord ++ tailWord_6465310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465310).length < 2 ^ (prefixWord ++ tailWord_6465310).sum := by decide
  have hdescent : baseEnd_6465310 < baseStart_6465310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465320 : List Nat := [2, 1, 5, 1, 1, 3, 3, 2, 1, 4]
def baseStart_6465320 : Nat := 118140960795 + 6465320 * 2 ^ 59
def prefixEnd_6465320 : Nat := 4983230072969 + 3 ^ 40 * 6465320 * 2
def baseEnd_6465320 : Nat := 1106605581708916546488847

theorem tailTrace_6465320 : CollatzResearch.WordTrace tailWord_6465320 prefixEnd_6465320 1106605581708916546488847 := by
  unfold tailWord_6465320
  simp only [CollatzResearch.WordTrace]
  refine ⟨117904796468628651796076707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157206395291504869061435609 117904796468628651796076707)
  ·
    refine ⟨176857194702942977694115061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117904796468628651796076707 176857194702942977694115061)
    ·
      refine ⟨16580362003400904158823287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176857194702942977694115061 16580362003400904158823287)
      ·
        refine ⟨24870543005101356238234931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16580362003400904158823287 24870543005101356238234931)
        ·
          refine ⟨37305814507652034357352397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24870543005101356238234931 37305814507652034357352397)
          ·
            refine ⟨13989680440369512884007149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37305814507652034357352397 13989680440369512884007149)
            ·
              refine ⟨5246130165138567331502681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13989680440369512884007149 5246130165138567331502681)
              ·
                refine ⟨3934597623853925498627011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5246130165138567331502681 3934597623853925498627011)
                ·
                  refine ⟨5901896435780888247940517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3934597623853925498627011 5901896435780888247940517)
                  ·
                    refine ⟨1106605581708916546488847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5901896435780888247940517 1106605581708916546488847)
                    ·
                      rfl

theorem cell23_6465320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_6465320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465320 prefixEnd_6465320 := by exact prefixLift 6465320
  have htrace : WordTrace (prefixWord ++ tailWord_6465320) baseStart_6465320 baseEnd_6465320 := by
    simpa [prefixWord, tailWord_6465320, baseEnd_6465320] using wordTrace_append hprefix tailTrace_6465320
  have hstable : (prefixWord ++ tailWord_6465320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465320).length < 2 ^ (prefixWord ++ tailWord_6465320).sum := by decide
  have hdescent : baseEnd_6465320 < baseStart_6465320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465333 : List Nat := [1, 3, 3, 1, 4, 2, 2, 1, 6]
def baseStart_6465333 : Nat := 118140960795 + 6465333 * 2 ^ 59
def prefixEnd_6465333 : Nat := 4983230072969 + 3 ^ 40 * 6465333 * 2
def baseEnd_6465333 : Nat := 368869268930584232067109

theorem tailTrace_6465333 : CollatzResearch.WordTrace tailWord_6465333 prefixEnd_6465333 368869268930584232067109 := by
  unfold tailWord_6465333
  simp only [CollatzResearch.WordTrace]
  refine ⟨235810067086210206812376653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157206711390806804541584435 235810067086210206812376653)
  ·
    refine ⟨88428775157328827554641245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235810067086210206812376653 88428775157328827554641245)
    ·
      refine ⟨33160790683998310332990467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88428775157328827554641245 33160790683998310332990467)
      ·
        refine ⟨49741186025997465499485701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33160790683998310332990467 49741186025997465499485701)
        ·
          refine ⟨9326472379874524781153569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49741186025997465499485701 9326472379874524781153569)
          ·
            refine ⟨6994854284905893585865177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9326472379874524781153569 6994854284905893585865177)
            ·
              refine ⟨5246140713679420189398883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6994854284905893585865177 5246140713679420189398883)
              ·
                refine ⟨7869211070519130284098325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5246140713679420189398883 7869211070519130284098325)
                ·
                  refine ⟨368869268930584232067109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7869211070519130284098325 368869268930584232067109)
                  ·
                    rfl

theorem cell23_6465333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 6].length) (baseStart_6465333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465333 prefixEnd_6465333 := by exact prefixLift 6465333
  have htrace : WordTrace (prefixWord ++ tailWord_6465333) baseStart_6465333 baseEnd_6465333 := by
    simpa [prefixWord, tailWord_6465333, baseEnd_6465333] using wordTrace_append hprefix tailTrace_6465333
  have hstable : (prefixWord ++ tailWord_6465333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465333).length < 2 ^ (prefixWord ++ tailWord_6465333).sum := by decide
  have hdescent : baseEnd_6465333 < baseStart_6465333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465349 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 3, 1, 4]
def baseStart_6465349 : Nat := 118140960795 + 6465349 * 2 ^ 59
def prefixEnd_6465349 : Nat := 4983230072969 + 3 ^ 40 * 6465349 * 2
def baseEnd_6465349 : Nat := 3319831636065730026003907

theorem tailTrace_6465349 : CollatzResearch.WordTrace tailWord_6465349 prefixEnd_6465349 3319831636065730026003907 := by
  unfold tailWord_6465349
  simp only [CollatzResearch.WordTrace]
  refine ⟨235810650654152241544959101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157207100436101494363306067 235810650654152241544959101)
  ·
    refine ⟨88428993995307090579359663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235810650654152241544959101 88428993995307090579359663)
    ·
      refine ⟨132643490992960635869039495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88428993995307090579359663 132643490992960635869039495)
      ·
        refine ⟨198965236489440953803559243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132643490992960635869039495 198965236489440953803559243)
        ·
          refine ⟨298447854734161430705338865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198965236489440953803559243 298447854734161430705338865)
          ·
            refine ⟨223835891050621073029004149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298447854734161430705338865 223835891050621073029004149)
            ·
              refine ⟨20984614785995725596469139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 223835891050621073029004149 20984614785995725596469139)
              ·
                refine ⟨31476922178993588394703709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20984614785995725596469139 31476922178993588394703709)
                ·
                  refine ⟨11803845817122595648013891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31476922178993588394703709 11803845817122595648013891)
                  ·
                    refine ⟨17705768725683893472020837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11803845817122595648013891 17705768725683893472020837)
                    ·
                      refine ⟨3319831636065730026003907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17705768725683893472020837 3319831636065730026003907)
                      ·
                        rfl

theorem cell23_6465349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_6465349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465349 prefixEnd_6465349 := by exact prefixLift 6465349
  have htrace : WordTrace (prefixWord ++ tailWord_6465349) baseStart_6465349 baseEnd_6465349 := by
    simpa [prefixWord, tailWord_6465349, baseEnd_6465349] using wordTrace_append hprefix tailTrace_6465349
  have hstable : (prefixWord ++ tailWord_6465349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465349).length < 2 ^ (prefixWord ++ tailWord_6465349).sum := by decide
  have hdescent : baseEnd_6465349 < baseStart_6465349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465376 : List Nat := [2, 1, 1, 3, 3, 2, 1, 4, 2, 4]
def baseStart_6465376 : Nat := 118140960795 + 6465376 * 2 ^ 59
def prefixEnd_6465376 : Nat := 4983230072969 + 3 ^ 40 * 6465376 * 2
def baseEnd_6465376 : Nat := 1106615166681133806788761

theorem tailTrace_6465376 : CollatzResearch.WordTrace tailWord_6465376 prefixEnd_6465376 1106615166681133806788761 := by
  unfold tailWord_6465376
  simp only [CollatzResearch.WordTrace]
  refine ⟨117905817712527212578095991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157207756950036283437461321 117905817712527212578095991)
  ·
    refine ⟨176858726568790818867143987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117905817712527212578095991 176858726568790818867143987)
    ·
      refine ⟨265288089853186228300715981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176858726568790818867143987 265288089853186228300715981)
      ·
        refine ⟨99483033694944835612768493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265288089853186228300715981 99483033694944835612768493)
        ·
          refine ⟨37306137635604313354788185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99483033694944835612768493 37306137635604313354788185)
          ·
            refine ⟨27979603226703235016091139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37306137635604313354788185 27979603226703235016091139)
            ·
              refine ⟨41969404840054852524136709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27979603226703235016091139 41969404840054852524136709)
              ·
                refine ⟨7869263407510284848275633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41969404840054852524136709 7869263407510284848275633)
                ·
                  refine ⟨5901947555632713636206725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7869263407510284848275633 5901947555632713636206725)
                  ·
                    refine ⟨1106615166681133806788761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5901947555632713636206725 1106615166681133806788761)
                    ·
                      rfl

theorem cell23_6465376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 2, 4].length) (baseStart_6465376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465376 prefixEnd_6465376 := by exact prefixLift 6465376
  have htrace : WordTrace (prefixWord ++ tailWord_6465376) baseStart_6465376 baseEnd_6465376 := by
    simpa [prefixWord, tailWord_6465376, baseEnd_6465376] using wordTrace_append hprefix tailTrace_6465376
  have hstable : (prefixWord ++ tailWord_6465376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465376).length < 2 ^ (prefixWord ++ tailWord_6465376).sum := by decide
  have hdescent : baseEnd_6465376 < baseStart_6465376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465383 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_6465383 : Nat := 118140960795 + 6465383 * 2 ^ 59
def prefixEnd_6465383 : Nat := 4983230072969 + 3 ^ 40 * 6465383 * 2
def baseEnd_6465383 : Nat := 3319849094407982892978751

theorem tailTrace_6465383 : CollatzResearch.WordTrace tailWord_6465383 prefixEnd_6465383 3319849094407982892978751 := by
  unfold tailWord_6465383
  simp only [CollatzResearch.WordTrace]
  refine ⟨235811890736029065351696803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157207927157352710234464535 235811890736029065351696803)
  ·
    refine ⟨353717836104043598027545205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235811890736029065351696803 353717836104043598027545205)
    ·
      refine ⟨33161047134754087315082363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 353717836104043598027545205 33161047134754087315082363)
      ·
        refine ⟨49741570702131130972623545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33161047134754087315082363 49741570702131130972623545)
        ·
          refine ⟨37306178026598348229467659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49741570702131130972623545 37306178026598348229467659)
          ·
            refine ⟨55959267039897522344201489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37306178026598348229467659 55959267039897522344201489)
            ·
              refine ⟨41969450279923141758151117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55959267039897522344201489 41969450279923141758151117)
              ·
                refine ⟨15738543854971178159306669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41969450279923141758151117 15738543854971178159306669)
                ·
                  refine ⟨5901953945614191809740001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15738543854971178159306669 5901953945614191809740001)
                  ·
                    refine ⟨4426465459210643857305001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5901953945614191809740001 4426465459210643857305001)
                    ·
                      refine ⟨3319849094407982892978751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4426465459210643857305001 3319849094407982892978751)
                      ·
                        rfl

theorem cell23_6465383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_6465383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465383 prefixEnd_6465383 := by exact prefixLift 6465383
  have htrace : WordTrace (prefixWord ++ tailWord_6465383) baseStart_6465383 baseEnd_6465383 := by
    simpa [prefixWord, tailWord_6465383, baseEnd_6465383] using wordTrace_append hprefix tailTrace_6465383
  have hstable : (prefixWord ++ tailWord_6465383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465383).length < 2 ^ (prefixWord ++ tailWord_6465383).sum := by decide
  have hdescent : baseEnd_6465383 < baseStart_6465383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465389 : List Nat := [1, 5, 1, 1, 1, 1, 5, 8]
def baseStart_6465389 : Nat := 118140960795 + 6465389 * 2 ^ 59
def prefixEnd_6465389 : Nat := 4983230072969 + 3 ^ 40 * 6465389 * 2
def baseEnd_6465389 : Nat := 122957487973774439611249

theorem tailTrace_6465389 : CollatzResearch.WordTrace tailWord_6465389 prefixEnd_6465389 122957487973774439611249 := by
  unfold tailWord_6465389
  simp only [CollatzResearch.WordTrace]
  refine ⟨235812109574007328376415221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157208073049338218917610147 235812109574007328376415221)
  ·
    refine ⟨22107385272563187035288927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235812109574007328376415221 22107385272563187035288927)
    ·
      refine ⟨33161077908844780552933391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22107385272563187035288927 33161077908844780552933391)
      ·
        refine ⟨49741616863267170829400087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33161077908844780552933391 49741616863267170829400087)
        ·
          refine ⟨74612425294900756244100131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49741616863267170829400087 74612425294900756244100131)
          ·
            refine ⟨111918637942351134366150197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74612425294900756244100131 111918637942351134366150197)
            ·
              refine ⟨10492372307095418846826581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111918637942351134366150197 10492372307095418846826581)
              ·
                refine ⟨122957487973774439611249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10492372307095418846826581 122957487973774439611249)
                ·
                  rfl

theorem cell23_6465389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 8].length) (baseStart_6465389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465389 prefixEnd_6465389 := by exact prefixLift 6465389
  have htrace : WordTrace (prefixWord ++ tailWord_6465389) baseStart_6465389 baseEnd_6465389 := by
    simpa [prefixWord, tailWord_6465389, baseEnd_6465389] using wordTrace_append hprefix tailTrace_6465389
  have hstable : (prefixWord ++ tailWord_6465389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465389).length < 2 ^ (prefixWord ++ tailWord_6465389).sum := by decide
  have hdescent : baseEnd_6465389 < baseStart_6465389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465433 : List Nat := [1, 2, 1, 2, 1, 3, 5, 2, 2, 1, 3]
def baseStart_6465433 : Nat := 118140960795 + 6465433 * 2 ^ 59
def prefixEnd_6465433 : Nat := 4983230072969 + 3 ^ 40 * 6465433 * 2
def baseEnd_6465433 : Nat := 3319874768440707697353521

theorem tailTrace_6465433 : CollatzResearch.WordTrace tailWord_6465433 prefixEnd_6465433 3319874768440707697353521 := by
  unfold tailWord_6465433
  simp only [CollatzResearch.WordTrace]
  refine ⟨235813714385847923891016953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157209142923898615927344635 235813714385847923891016953)
  ·
    refine ⟨176860285789385942918262715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235813714385847923891016953 176860285789385942918262715)
    ·
      refine ⟨265290428684078914377394073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176860285789385942918262715 265290428684078914377394073)
      ·
        refine ⟨198967821513059185783045555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265290428684078914377394073 198967821513059185783045555)
        ·
          refine ⟨298451732269588778674568333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198967821513059185783045555 298451732269588778674568333)
          ·
            refine ⟨111919399601095792002963125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298451732269588778674568333 111919399601095792002963125)
            ·
              refine ⟨10492443712602730500277793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111919399601095792002963125 10492443712602730500277793)
              ·
                refine ⟨7869332784452047875208345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10492443712602730500277793 7869332784452047875208345)
                ·
                  refine ⟨5901999588339035906406259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7869332784452047875208345 5901999588339035906406259)
                  ·
                    refine ⟨8852999382508553859609389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5901999588339035906406259 8852999382508553859609389)
                    ·
                      refine ⟨3319874768440707697353521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8852999382508553859609389 3319874768440707697353521)
                      ·
                        rfl

theorem cell23_6465433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_6465433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465433 prefixEnd_6465433 := by exact prefixLift 6465433
  have htrace : WordTrace (prefixWord ++ tailWord_6465433) baseStart_6465433 baseEnd_6465433 := by
    simpa [prefixWord, tailWord_6465433, baseEnd_6465433] using wordTrace_append hprefix tailTrace_6465433
  have hstable : (prefixWord ++ tailWord_6465433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465433).length < 2 ^ (prefixWord ++ tailWord_6465433).sum := by decide
  have hdescent : baseEnd_6465433 < baseStart_6465433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465454 : List Nat := [4, 1, 5, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6465454 : Nat := 118140960795 + 6465454 * 2 ^ 59
def prefixEnd_6465454 : Nat := 4983230072969 + 3 ^ 40 * 6465454 * 2
def baseEnd_6465454 : Nat := 3319885551534452115190925

theorem tailTrace_6465454 : CollatzResearch.WordTrace tailWord_6465454 prefixEnd_6465454 3319885551534452115190925 := by
  unfold tailWord_6465454
  simp only [CollatzResearch.WordTrace]
  refine ⟨29476810039846480559691427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157209653545847896318354277 29476810039846480559691427)
  ·
    refine ⟨44215215059769720839537141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29476810039846480559691427 44215215059769720839537141)
    ·
      refine ⟨4145176411853411328706607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44215215059769720839537141 4145176411853411328706607)
      ·
        refine ⟨6217764617780116993059911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4145176411853411328706607 6217764617780116993059911)
        ·
          refine ⟨9326646926670175489589867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6217764617780116993059911 9326646926670175489589867)
          ·
            refine ⟨13989970390005263234384801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9326646926670175489589867 13989970390005263234384801)
            ·
              refine ⟨10492477792503947425788601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13989970390005263234384801 10492477792503947425788601)
              ·
                refine ⟨7869358344377960569341451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10492477792503947425788601 7869358344377960569341451)
                ·
                  refine ⟨11804037516566940854012177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7869358344377960569341451 11804037516566940854012177)
                  ·
                    refine ⟨8853028137425205640509133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11804037516566940854012177 8853028137425205640509133)
                    ·
                      refine ⟨3319885551534452115190925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8853028137425205640509133 3319885551534452115190925)
                      ·
                        rfl

theorem cell23_6465454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6465454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465454 prefixEnd_6465454 := by exact prefixLift 6465454
  have htrace : WordTrace (prefixWord ++ tailWord_6465454) baseStart_6465454 baseEnd_6465454 := by
    simpa [prefixWord, tailWord_6465454, baseEnd_6465454] using wordTrace_append hprefix tailTrace_6465454
  have hstable : (prefixWord ++ tailWord_6465454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465454).length < 2 ^ (prefixWord ++ tailWord_6465454).sum := by decide
  have hdescent : baseEnd_6465454 < baseStart_6465454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465459 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 5]
def baseStart_6465459 : Nat := 118140960795 + 6465459 * 2 ^ 59
def prefixEnd_6465459 : Nat := 4983230072969 + 3 ^ 40 * 6465459 * 2
def baseEnd_6465459 : Nat := 3319888118937724595628401

theorem tailTrace_6465459 : CollatzResearch.WordTrace tailWord_6465459 prefixEnd_6465459 3319888118937724595628401 := by
  unfold tailWord_6465459
  simp only [CollatzResearch.WordTrace]
  refine ⟨235814662683753730331463431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157209775122502486887642287 235814662683753730331463431)
  ·
    refine ⟨353721994025630595497195147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235814662683753730331463431 353721994025630595497195147)
    ·
      refine ⟨530582991038445893245792721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353721994025630595497195147 530582991038445893245792721)
      ·
        refine ⟨397937243278834419934344541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530582991038445893245792721 397937243278834419934344541)
        ·
          refine ⟨149226466229562907475379203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397937243278834419934344541 149226466229562907475379203)
          ·
            refine ⟨223839699344344361213068805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149226466229562907475379203 223839699344344361213068805)
            ·
              refine ⟨41969943627064567727450401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223839699344344361213068805 41969943627064567727450401)
              ·
                refine ⟨31477457720298425795587801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41969943627064567727450401 31477457720298425795587801)
                ·
                  refine ⟨23608093290223819346690851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31477457720298425795587801 23608093290223819346690851)
                  ·
                    refine ⟨35412139935335729020036277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23608093290223819346690851 35412139935335729020036277)
                    ·
                      refine ⟨3319888118937724595628401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35412139935335729020036277 3319888118937724595628401)
                      ·
                        rfl

theorem cell23_6465459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_6465459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465459 prefixEnd_6465459 := by exact prefixLift 6465459
  have htrace : WordTrace (prefixWord ++ tailWord_6465459) baseStart_6465459 baseEnd_6465459 := by
    simpa [prefixWord, tailWord_6465459, baseEnd_6465459] using wordTrace_append hprefix tailTrace_6465459
  have hstable : (prefixWord ++ tailWord_6465459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465459).length < 2 ^ (prefixWord ++ tailWord_6465459).sum := by decide
  have hdescent : baseEnd_6465459 < baseStart_6465459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465507 : List Nat := [1, 1, 1, 6, 1, 2, 4, 1, 2, 2, 2]
def baseStart_6465507 : Nat := 118140960795 + 6465507 * 2 ^ 59
def prefixEnd_6465507 : Nat := 4983230072969 + 3 ^ 40 * 6465507 * 2
def baseEnd_6465507 : Nat := 3319912766009140407828181

theorem tailTrace_6465507 : CollatzResearch.WordTrace tailWord_6465507 prefixEnd_6465507 3319912766009140407828181 := by
  unfold tailWord_6465507
  simp only [CollatzResearch.WordTrace]
  refine ⟨235816413387579834529210775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157210942258386556352807183 235816413387579834529210775)
  ·
    refine ⟨353724620081369751793816163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235816413387579834529210775 353724620081369751793816163)
    ·
      refine ⟨530586930122054627690724245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353724620081369751793816163 530586930122054627690724245)
      ·
        refine ⟨24871262349471310673002699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 530586930122054627690724245 24871262349471310673002699)
        ·
          refine ⟨37306893524206966009504049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24871262349471310673002699 37306893524206966009504049)
          ·
            refine ⟨27980170143155224507128037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37306893524206966009504049 27980170143155224507128037)
            ·
              refine ⟨5246281901841604595086507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27980170143155224507128037 5246281901841604595086507)
              ·
                refine ⟨7869422852762406892629761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5246281901841604595086507 7869422852762406892629761)
                ·
                  refine ⟨5902067139571805169472321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7869422852762406892629761 5902067139571805169472321)
                  ·
                    refine ⟨4426550354678853877104241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5902067139571805169472321 4426550354678853877104241)
                    ·
                      refine ⟨3319912766009140407828181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4426550354678853877104241 3319912766009140407828181)
                      ·
                        rfl

theorem cell23_6465507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_6465507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465507 prefixEnd_6465507 := by exact prefixLift 6465507
  have htrace : WordTrace (prefixWord ++ tailWord_6465507) baseStart_6465507 baseEnd_6465507 := by
    simpa [prefixWord, tailWord_6465507, baseEnd_6465507] using wordTrace_append hprefix tailTrace_6465507
  have hstable : (prefixWord ++ tailWord_6465507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465507).length < 2 ^ (prefixWord ++ tailWord_6465507).sum := by decide
  have hdescent : baseEnd_6465507 < baseStart_6465507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465519 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 7]
def baseStart_6465519 : Nat := 118140960795 + 6465519 * 2 ^ 59
def prefixEnd_6465519 : Nat := 4983230072969 + 3 ^ 40 * 6465519 * 2
def baseEnd_6465519 : Nat := 3319918927776994360878125

theorem tailTrace_6465519 : CollatzResearch.WordTrace tailWord_6465519 prefixEnd_6465519 3319918927776994360878125 := by
  unfold tailWord_6465519
  simp only [CollatzResearch.WordTrace]
  refine ⟨235816851063536360578647611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157211234042357573719098407 235816851063536360578647611)
  ·
    refine ⟨353725276595304540867971417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235816851063536360578647611 353725276595304540867971417)
    ·
      refine ⟨265293957446478405650978563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353725276595304540867971417 265293957446478405650978563)
      ·
        refine ⟨397940936169717608476467845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265293957446478405650978563 397940936169717608476467845)
        ·
          refine ⟨74613925531822051589337721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397940936169717608476467845 74613925531822051589337721)
          ·
            refine ⟨55960444148866538692003291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74613925531822051589337721 55960444148866538692003291)
            ·
              refine ⟨83940666223299808038004937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55960444148866538692003291 83940666223299808038004937)
              ·
                refine ⟨62955499667474856028503703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83940666223299808038004937 62955499667474856028503703)
                ·
                  refine ⟨94433249501212284042755555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62955499667474856028503703 94433249501212284042755555)
                  ·
                    refine ⟨141649874251818426064133333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94433249501212284042755555 141649874251818426064133333)
                    ·
                      refine ⟨3319918927776994360878125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141649874251818426064133333 3319918927776994360878125)
                      ·
                        rfl

theorem cell23_6465519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_6465519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465519 prefixEnd_6465519 := by exact prefixLift 6465519
  have htrace : WordTrace (prefixWord ++ tailWord_6465519) baseStart_6465519 baseEnd_6465519 := by
    simpa [prefixWord, tailWord_6465519, baseEnd_6465519] using wordTrace_append hprefix tailTrace_6465519
  have hstable : (prefixWord ++ tailWord_6465519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465519).length < 2 ^ (prefixWord ++ tailWord_6465519).sum := by decide
  have hdescent : baseEnd_6465519 < baseStart_6465519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465573 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 3, 4]
def baseStart_6465573 : Nat := 118140960795 + 6465573 * 2 ^ 59
def prefixEnd_6465573 : Nat := 4983230072969 + 3 ^ 40 * 6465573 * 2
def baseEnd_6465573 : Nat := 1106648885244112383200959

theorem tailTrace_6465573 : CollatzResearch.WordTrace tailWord_6465573 prefixEnd_6465573 1106648885244112383200959 := by
  unfold tailWord_6465573
  simp only [CollatzResearch.WordTrace]
  refine ⟨235818820605340727801113373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157212547070227151867408915 235818820605340727801113373)
  ·
    refine ⟨88432057727002772925417515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235818820605340727801113373 88432057727002772925417515)
    ·
      refine ⟨132648086590504159388126273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88432057727002772925417515 132648086590504159388126273)
      ·
        refine ⟨99486064942878119541094705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132648086590504159388126273 99486064942878119541094705)
        ·
          refine ⟨74614548707158589655821029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99486064942878119541094705 74614548707158589655821029)
          ·
            refine ⟨13990227882592235560466443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74614548707158589655821029 13990227882592235560466443)
            ·
              refine ⟨20985341823888353340699665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13990227882592235560466443 20985341823888353340699665)
              ·
                refine ⟨15739006367916265005524749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20985341823888353340699665 15739006367916265005524749)
                ·
                  refine ⟨5902127387968599377071781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15739006367916265005524749 5902127387968599377071781)
                  ·
                    refine ⟨1106648885244112383200959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5902127387968599377071781 1106648885244112383200959)
                    ·
                      rfl

theorem cell23_6465573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_6465573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465573 prefixEnd_6465573 := by exact prefixLift 6465573
  have htrace : WordTrace (prefixWord ++ tailWord_6465573) baseStart_6465573 baseEnd_6465573 := by
    simpa [prefixWord, tailWord_6465573, baseEnd_6465573] using wordTrace_append hprefix tailTrace_6465573
  have hstable : (prefixWord ++ tailWord_6465573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465573).length < 2 ^ (prefixWord ++ tailWord_6465573).sum := by decide
  have hdescent : baseEnd_6465573 < baseStart_6465573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465623 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 1, 5, 2]
def baseStart_6465623 : Nat := 118140960795 + 6465623 * 2 ^ 59
def prefixEnd_6465623 : Nat := 4983230072969 + 3 ^ 40 * 6465623 * 2
def baseEnd_6465623 : Nat := 3319972329765061953977647

theorem tailTrace_6465623 : CollatzResearch.WordTrace tailWord_6465623 prefixEnd_6465623 3319972329765061953977647 := by
  unfold tailWord_6465623
  simp only [CollatzResearch.WordTrace]
  refine ⟨235820644255159586340433523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157213762836773057560289015 235820644255159586340433523)
  ·
    refine ⟨353730966382739379510650285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235820644255159586340433523 353730966382739379510650285)
    ·
      refine ⟨132649112393527267316493857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353730966382739379510650285 132649112393527267316493857)
      ·
        refine ⟨99486834295145450487370393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132649112393527267316493857 99486834295145450487370393)
        ·
          refine ⟨74615125721359087865527795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99486834295145450487370393 74615125721359087865527795)
          ·
            refine ⟨111922688582038631798291693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74615125721359087865527795 111922688582038631798291693)
            ·
              refine ⟨41971008218264486924359385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111922688582038631798291693 41971008218264486924359385)
              ·
                refine ⟨31478256163698365193269539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41971008218264486924359385 31478256163698365193269539)
                ·
                  refine ⟨47217384245547547789904309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31478256163698365193269539 47217384245547547789904309)
                  ·
                    refine ⟨4426629773020082605303529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47217384245547547789904309 4426629773020082605303529)
                    ·
                      refine ⟨3319972329765061953977647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4426629773020082605303529 3319972329765061953977647)
                      ·
                        rfl

theorem cell23_6465623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_6465623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465623 prefixEnd_6465623 := by exact prefixLift 6465623
  have htrace : WordTrace (prefixWord ++ tailWord_6465623) baseStart_6465623 baseEnd_6465623 := by
    simpa [prefixWord, tailWord_6465623, baseEnd_6465623] using wordTrace_append hprefix tailTrace_6465623
  have hstable : (prefixWord ++ tailWord_6465623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465623).length < 2 ^ (prefixWord ++ tailWord_6465623).sum := by decide
  have hdescent : baseEnd_6465623 < baseStart_6465623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465647 : List Nat := [1, 1, 2, 1, 3, 4, 3, 3, 1, 1, 3]
def baseStart_6465647 : Nat := 118140960795 + 6465647 * 2 ^ 59
def prefixEnd_6465647 : Nat := 4983230072969 + 3 ^ 40 * 6465647 * 2
def baseEnd_6465647 : Nat := 3319984653300769860077537

theorem tailTrace_6465647 : CollatzResearch.WordTrace tailWord_6465647 prefixEnd_6465647 3319984653300769860077537 := by
  unfold tailWord_6465647
  simp only [CollatzResearch.WordTrace]
  refine ⟨235821519607072638439307195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157214346404715092292871463 235821519607072638439307195)
  ·
    refine ⟨353732279410608957658960793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235821519607072638439307195 353732279410608957658960793)
    ·
      refine ⟨265299209557956718244220595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353732279410608957658960793 265299209557956718244220595)
      ·
        refine ⟨397948814336935077366330893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265299209557956718244220595 397948814336935077366330893)
        ·
          refine ⟨149230805376350654012374085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397948814336935077366330893 149230805376350654012374085)
          ·
            refine ⟨27980776008065747627320141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149230805376350654012374085 27980776008065747627320141)
            ·
              refine ⟨10492791003024655360245053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27980776008065747627320141 10492791003024655360245053)
              ·
                refine ⟨3934796626134245760091895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10492791003024655360245053 3934796626134245760091895)
                ·
                  refine ⟨5902194939201368640137843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3934796626134245760091895 5902194939201368640137843)
                  ·
                    refine ⟨8853292408802052960206765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5902194939201368640137843 8853292408802052960206765)
                    ·
                      refine ⟨3319984653300769860077537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8853292408802052960206765 3319984653300769860077537)
                      ·
                        rfl

theorem cell23_6465647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 1, 1, 3].length) (baseStart_6465647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465647 prefixEnd_6465647 := by exact prefixLift 6465647
  have htrace : WordTrace (prefixWord ++ tailWord_6465647) baseStart_6465647 baseEnd_6465647 := by
    simpa [prefixWord, tailWord_6465647, baseEnd_6465647] using wordTrace_append hprefix tailTrace_6465647
  have hstable : (prefixWord ++ tailWord_6465647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465647).length < 2 ^ (prefixWord ++ tailWord_6465647).sum := by decide
  have hdescent : baseEnd_6465647 < baseStart_6465647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465673 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 3, 2, 3]
def baseStart_6465673 : Nat := 118140960795 + 6465673 * 2 ^ 59
def prefixEnd_6465673 : Nat := 4983230072969 + 3 ^ 40 * 6465673 * 2
def baseEnd_6465673 : Nat := 3319998003797786758352417

theorem tailTrace_6465673 : CollatzResearch.WordTrace tailWord_6465673 prefixEnd_6465673 3319998003797786758352417 := by
  unfold tailWord_6465673
  simp only [CollatzResearch.WordTrace]
  refine ⟨235822467904978444879753673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157214978603318963253169115 235822467904978444879753673)
  ·
    refine ⟨176866850928733833659815255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235822467904978444879753673 176866850928733833659815255)
    ·
      refine ⟨265300276393100750489722883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176866850928733833659815255 265300276393100750489722883)
      ·
        refine ⟨397950414589651125734584325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265300276393100750489722883 397950414589651125734584325)
        ·
          refine ⟨74615702735559586075234561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397950414589651125734584325 74615702735559586075234561)
          ·
            refine ⟨55961777051669689556425921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74615702735559586075234561 55961777051669689556425921)
            ·
              refine ⟨41971332788752267167319441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55961777051669689556425921 41971332788752267167319441)
              ·
                refine ⟨31478499591564200375489581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41971332788752267167319441 31478499591564200375489581)
                ·
                  refine ⟨11804437346836575140808593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31478499591564200375489581 11804437346836575140808593)
                  ·
                    refine ⟨8853328010127431355606445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11804437346836575140808593 8853328010127431355606445)
                    ·
                      refine ⟨3319998003797786758352417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8853328010127431355606445 3319998003797786758352417)
                      ·
                        rfl

theorem cell23_6465673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 2, 3].length) (baseStart_6465673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465673 prefixEnd_6465673 := by exact prefixLift 6465673
  have htrace : WordTrace (prefixWord ++ tailWord_6465673) baseStart_6465673 baseEnd_6465673 := by
    simpa [prefixWord, tailWord_6465673, baseEnd_6465673] using wordTrace_append hprefix tailTrace_6465673
  have hstable : (prefixWord ++ tailWord_6465673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465673).length < 2 ^ (prefixWord ++ tailWord_6465673).sum := by decide
  have hdescent : baseEnd_6465673 < baseStart_6465673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465684 : List Nat := [2, 4, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_6465684 : Nat := 118140960795 + 6465684 * 2 ^ 59
def prefixEnd_6465684 : Nat := 4983230072969 + 3 ^ 40 * 6465684 * 2
def baseEnd_6465684 : Nat := 1106667884028328738438289

theorem tailTrace_6465684 : CollatzResearch.WordTrace tailWord_6465684 prefixEnd_6465684 1106667884028328738438289 := by
  unfold tailWord_6465684
  simp only [CollatzResearch.WordTrace]
  refine ⟨117911434553969296879202053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157215246071959062505602737 117911434553969296879202053)
  ·
    refine ⟨22108393978869243164850385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117911434553969296879202053 22108393978869243164850385)
    ·
      refine ⟨16581295484151932373637789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22108393978869243164850385 16581295484151932373637789)
      ·
        refine ⟨6217985806556974640114171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16581295484151932373637789 6217985806556974640114171)
        ·
          refine ⟨9326978709835461960171257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6217985806556974640114171 9326978709835461960171257)
          ·
            refine ⟨6995234032376596470128443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9326978709835461960171257 6995234032376596470128443)
            ·
              refine ⟨10492851048564894705192665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6995234032376596470128443 10492851048564894705192665)
              ·
                refine ⟨7869638286423671028894499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10492851048564894705192665 7869638286423671028894499)
                ·
                  refine ⟨11804457429635506543341749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7869638286423671028894499 11804457429635506543341749)
                  ·
                    refine ⟨1106667884028328738438289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11804457429635506543341749 1106667884028328738438289)
                    ·
                      rfl

theorem cell23_6465684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_6465684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465684 prefixEnd_6465684 := by exact prefixLift 6465684
  have htrace : WordTrace (prefixWord ++ tailWord_6465684) baseStart_6465684 baseEnd_6465684 := by
    simpa [prefixWord, tailWord_6465684, baseEnd_6465684] using wordTrace_append hprefix tailTrace_6465684
  have hstable : (prefixWord ++ tailWord_6465684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465684).length < 2 ^ (prefixWord ++ tailWord_6465684).sum := by decide
  have hdescent : baseEnd_6465684 < baseStart_6465684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465687 : List Nat := [1, 1, 3, 3, 4, 2, 1, 2, 1, 1, 4]
def baseStart_6465687 : Nat := 118140960795 + 6465687 * 2 ^ 59
def prefixEnd_6465687 : Nat := 4983230072969 + 3 ^ 40 * 6465687 * 2
def baseEnd_6465687 : Nat := 3320005192526949703577353

theorem tailTrace_6465687 : CollatzResearch.WordTrace tailWord_6465687 prefixEnd_6465687 3320005192526949703577353 := by
  unfold tailWord_6465687
  simp only [CollatzResearch.WordTrace]
  refine ⟨235822978526927725270763315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157215319017951816847175543 235822978526927725270763315)
  ·
    refine ⟨353734467790391587906144973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235822978526927725270763315 353734467790391587906144973)
    ·
      refine ⟨132650425421396845464804365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353734467790391587906144973 132650425421396845464804365)
      ·
        refine ⟨49743909533023817049301637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132650425421396845464804365 49743909533023817049301637)
        ·
          refine ⟨9326983037441965696744057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49743909533023817049301637 9326983037441965696744057)
          ·
            refine ⟨6995237278081474272558043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9326983037441965696744057 6995237278081474272558043)
            ·
              refine ⟨10492855917122211408837065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6995237278081474272558043 10492855917122211408837065)
              ·
                refine ⟨7869641937841658556627799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10492855917122211408837065 7869641937841658556627799)
                ·
                  refine ⟨11804462906762487834941699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7869641937841658556627799 11804462906762487834941699)
                  ·
                    refine ⟨17706694360143731752412549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11804462906762487834941699 17706694360143731752412549)
                    ·
                      refine ⟨3320005192526949703577353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17706694360143731752412549 3320005192526949703577353)
                      ·
                        rfl

theorem cell23_6465687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_6465687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465687 prefixEnd_6465687 := by exact prefixLift 6465687
  have htrace : WordTrace (prefixWord ++ tailWord_6465687) baseStart_6465687 baseEnd_6465687 := by
    simpa [prefixWord, tailWord_6465687, baseEnd_6465687] using wordTrace_append hprefix tailTrace_6465687
  have hstable : (prefixWord ++ tailWord_6465687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465687).length < 2 ^ (prefixWord ++ tailWord_6465687).sum := by decide
  have hdescent : baseEnd_6465687 < baseStart_6465687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465700 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_6465700 : Nat := 118140960795 + 6465700 * 2 ^ 59
def prefixEnd_6465700 : Nat := 4983230072969 + 3 ^ 40 * 6465700 * 2
def baseEnd_6465700 : Nat := 3320011867775458152714793

theorem tailTrace_6465700 : CollatzResearch.WordTrace tailWord_6465700 prefixEnd_6465700 3320011867775458152714793 := by
  unfold tailWord_6465700
  simp only [CollatzResearch.WordTrace]
  refine ⟨117911726337940314245493277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157215635117253752327324369 117911726337940314245493277)
  ·
    refine ⟨44216897376727617842059979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117911726337940314245493277 44216897376727617842059979)
    ·
      refine ⟨66325346065091426763089969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44216897376727617842059979 66325346065091426763089969)
      ·
        refine ⟨49744009548818570072317477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66325346065091426763089969 49744009548818570072317477)
        ·
          refine ⟨9327001790403481888559527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49744009548818570072317477 9327001790403481888559527)
          ·
            refine ⟨13990502685605222832839291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9327001790403481888559527 13990502685605222832839291)
            ·
              refine ⟨20985754028407834249258937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13990502685605222832839291 20985754028407834249258937)
              ·
                refine ⟨15739315521305875686944203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20985754028407834249258937 15739315521305875686944203)
                ·
                  refine ⟨23608973281958813530416305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15739315521305875686944203 23608973281958813530416305)
                  ·
                    refine ⟨17706729961469110147812229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23608973281958813530416305 17706729961469110147812229)
                    ·
                      refine ⟨3320011867775458152714793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17706729961469110147812229 3320011867775458152714793)
                      ·
                        rfl

theorem cell23_6465700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_6465700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465700 prefixEnd_6465700 := by exact prefixLift 6465700
  have htrace : WordTrace (prefixWord ++ tailWord_6465700) baseStart_6465700 baseEnd_6465700 := by
    simpa [prefixWord, tailWord_6465700, baseEnd_6465700] using wordTrace_append hprefix tailTrace_6465700
  have hstable : (prefixWord ++ tailWord_6465700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465700).length < 2 ^ (prefixWord ++ tailWord_6465700).sum := by decide
  have hdescent : baseEnd_6465700 < baseStart_6465700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465710 : List Nat := [4, 1, 4, 2, 1, 11]
def baseStart_6465710 : Nat := 118140960795 + 6465710 * 2 ^ 59
def prefixEnd_6465710 : Nat := 4983230072969 + 3 ^ 40 * 6465710 * 2
def baseEnd_6465710 : Nat := 13662621409802481948929

theorem tailTrace_6465710 : CollatzResearch.WordTrace tailWord_6465710 prefixEnd_6465710 13662621409802481948929 := by
  unfold tailWord_6465710
  simp only [CollatzResearch.WordTrace]
  refine ⟨29477977175730550024856323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157215878270562933465900389 29477977175730550024856323)
  ·
    refine ⟨44216965763595825037284485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29477977175730550024856323 44216965763595825037284485)
    ·
      refine ⟨8290681080674217194490841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44216965763595825037284485 8290681080674217194490841)
      ·
        refine ⟨6218010810505662895868131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8290681080674217194490841 6218010810505662895868131)
        ·
          refine ⟨9327016215758494343802197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6218010810505662895868131 9327016215758494343802197)
          ·
            refine ⟨13662621409802481948929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9327016215758494343802197 13662621409802481948929)
            ·
              rfl

theorem cell23_6465710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 11].length) (baseStart_6465710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465710 prefixEnd_6465710 := by exact prefixLift 6465710
  have htrace : WordTrace (prefixWord ++ tailWord_6465710) baseStart_6465710 baseEnd_6465710 := by
    simpa [prefixWord, tailWord_6465710, baseEnd_6465710] using wordTrace_append hprefix tailTrace_6465710
  have hstable : (prefixWord ++ tailWord_6465710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465710).length < 2 ^ (prefixWord ++ tailWord_6465710).sum := by decide
  have hdescent : baseEnd_6465710 < baseStart_6465710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465760 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 1, 4, 2]
def baseStart_6465760 : Nat := 118140960795 + 6465760 * 2 ^ 59
def prefixEnd_6465760 : Nat := 4983230072969 + 3 ^ 40 * 6465760 * 2
def baseEnd_6465760 : Nat := 3320042676614727917964517

theorem tailTrace_6465760 : CollatzResearch.WordTrace tailWord_6465760 prefixEnd_6465760 3320042676614727917964517 := by
  unfold tailWord_6465760
  simp only [CollatzResearch.WordTrace]
  refine ⟨117912820527831629369085367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157217094037108839158780489 117912820527831629369085367)
  ·
    refine ⟨176869230791747444053628051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117912820527831629369085367 176869230791747444053628051)
    ·
      refine ⟨265303846187621166080442077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176869230791747444053628051 265303846187621166080442077)
      ·
        refine ⟨99488942320357937280165779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265303846187621166080442077 99488942320357937280165779)
        ·
          refine ⟨149233413480536905920248669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99488942320357937280165779 149233413480536905920248669)
          ·
            refine ⟨55962530055201339720093251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149233413480536905920248669 55962530055201339720093251)
            ·
              refine ⟨83943795082802009580139877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55962530055201339720093251 83943795082802009580139877)
              ·
                refine ⟨15739461578025376796276227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83943795082802009580139877 15739461578025376796276227)
                ·
                  refine ⟨23609192367038065194414341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15739461578025376796276227 23609192367038065194414341)
                  ·
                    refine ⟨4426723568819637223952689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23609192367038065194414341 4426723568819637223952689)
                    ·
                      refine ⟨3320042676614727917964517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4426723568819637223952689 3320042676614727917964517)
                      ·
                        rfl

theorem cell23_6465760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_6465760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465760 prefixEnd_6465760 := by exact prefixLift 6465760
  have htrace : WordTrace (prefixWord ++ tailWord_6465760) baseStart_6465760 baseEnd_6465760 := by
    simpa [prefixWord, tailWord_6465760, baseEnd_6465760] using wordTrace_append hprefix tailTrace_6465760
  have hstable : (prefixWord ++ tailWord_6465760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465760).length < 2 ^ (prefixWord ++ tailWord_6465760).sum := by decide
  have hdescent : baseEnd_6465760 < baseStart_6465760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465790 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_6465790 : Nat := 118140960795 + 6465790 * 2 ^ 59
def prefixEnd_6465790 : Nat := 4983230072969 + 3 ^ 40 * 6465790 * 2
def baseEnd_6465790 : Nat := 3320058081034362800589379

theorem tailTrace_6465790 : CollatzResearch.WordTrace tailWord_6465790 prefixEnd_6465790 3320058081034362800589379 := by
  unfold tailWord_6465790
  simp only [CollatzResearch.WordTrace]
  refine ⟨29478341905694321732720353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157217823497036382574508549 29478341905694321732720353)
  ·
    refine ⟨22108756429270741299540265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29478341905694321732720353 22108756429270741299540265)
    ·
      refine ⟨16581567321953055974655199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22108756429270741299540265 16581567321953055974655199)
      ·
        refine ⟨24872350982929583961982799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16581567321953055974655199 24872350982929583961982799)
        ·
          refine ⟨37308526474394375942974199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24872350982929583961982799 37308526474394375942974199)
          ·
            refine ⟨55962789711591563914461299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37308526474394375942974199 55962789711591563914461299)
            ·
              refine ⟨83944184567387345871691949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55962789711591563914461299 83944184567387345871691949)
              ·
                refine ⟨31479069212770254701884481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83944184567387345871691949 31479069212770254701884481)
                ·
                  refine ⟨23609301909577691026413361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31479069212770254701884481 23609301909577691026413361)
                  ·
                    refine ⟨17706976432183268269810021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23609301909577691026413361 17706976432183268269810021)
                    ·
                      refine ⟨3320058081034362800589379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17706976432183268269810021 3320058081034362800589379)
                      ·
                        rfl

theorem cell23_6465790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_6465790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465790 prefixEnd_6465790 := by exact prefixLift 6465790
  have htrace : WordTrace (prefixWord ++ tailWord_6465790) baseStart_6465790 baseEnd_6465790 := by
    simpa [prefixWord, tailWord_6465790, baseEnd_6465790] using wordTrace_append hprefix tailTrace_6465790
  have hstable : (prefixWord ++ tailWord_6465790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465790).length < 2 ^ (prefixWord ++ tailWord_6465790).sum := by decide
  have hdescent : baseEnd_6465790 < baseStart_6465790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465794 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_6465794 : Nat := 118140960795 + 6465794 * 2 ^ 59
def prefixEnd_6465794 : Nat := 4983230072969 + 3 ^ 40 * 6465794 * 2
def baseEnd_6465794 : Nat := 3320060134956980784939361

theorem tailTrace_6465794 : CollatzResearch.WordTrace tailWord_6465794 prefixEnd_6465794 3320060134956980784939361 := by
  unfold tailWord_6465794
  simp only [CollatzResearch.WordTrace]
  refine ⟨58956720284385020636227109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157217920758360055029938957 58956720284385020636227109)
  ·
    refine ⟨11054385053322191369292583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58956720284385020636227109 11054385053322191369292583)
    ·
      refine ⟨16581577579983287053938875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11054385053322191369292583 16581577579983287053938875)
      ·
        refine ⟨24872366369974930580908313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16581577579983287053938875 24872366369974930580908313)
        ·
          refine ⟨18654274777481197935681235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24872366369974930580908313 18654274777481197935681235)
          ·
            refine ⟨27981412166221796903521853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18654274777481197935681235 27981412166221796903521853)
            ·
              refine ⟨10493029562333173838820695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27981412166221796903521853 10493029562333173838820695)
              ·
                refine ⟨15739544343499760758231043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10493029562333173838820695 15739544343499760758231043)
                ·
                  refine ⟨23609316515249641137346565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15739544343499760758231043 23609316515249641137346565)
                  ·
                    refine ⟨4426746846609307713252481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23609316515249641137346565 4426746846609307713252481)
                    ·
                      refine ⟨3320060134956980784939361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4426746846609307713252481 3320060134956980784939361)
                      ·
                        rfl

theorem cell23_6465794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_6465794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465794 prefixEnd_6465794 := by exact prefixLift 6465794
  have htrace : WordTrace (prefixWord ++ tailWord_6465794) baseStart_6465794 baseEnd_6465794 := by
    simpa [prefixWord, tailWord_6465794, baseEnd_6465794] using wordTrace_append hprefix tailTrace_6465794
  have hstable : (prefixWord ++ tailWord_6465794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465794).length < 2 ^ (prefixWord ++ tailWord_6465794).sum := by decide
  have hdescent : baseEnd_6465794 < baseStart_6465794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465813 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 1, 7]
def baseStart_6465813 : Nat := 118140960795 + 6465813 * 2 ^ 59
def prefixEnd_6465813 : Nat := 4983230072969 + 3 ^ 40 * 6465813 * 2
def baseEnd_6465813 : Nat := 1106689963696472070200591

theorem tailTrace_6465813 : CollatzResearch.WordTrace tailWord_6465813 prefixEnd_6465813 1106689963696472070200591 := by
  unfold tailWord_6465813
  simp only [CollatzResearch.WordTrace]
  refine ⟨235827574124471248789850093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157218382749647499193233395 235827574124471248789850093)
  ·
    refine ⟨88435340296676718296193785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235827574124471248789850093 88435340296676718296193785)
    ·
      refine ⟨66326505222507538722145339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88435340296676718296193785 66326505222507538722145339)
      ·
        refine ⟨99489757833761308083218009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66326505222507538722145339 99489757833761308083218009)
        ·
          refine ⟨74617318375320981062413507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99489757833761308083218009 74617318375320981062413507)
          ·
            refine ⟨111925977562981471593620261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74617318375320981062413507 111925977562981471593620261)
            ·
              refine ⟨20986120793059025923803799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111925977562981471593620261 20986120793059025923803799)
              ·
                refine ⟨31479181189588538885705699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20986120793059025923803799 31479181189588538885705699)
                ·
                  refine ⟨47218771784382808328558549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31479181189588538885705699 47218771784382808328558549)
                  ·
                    refine ⟨1106689963696472070200591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47218771784382808328558549 1106689963696472070200591)
                    ·
                      rfl

theorem cell23_6465813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_6465813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465813 prefixEnd_6465813 := by exact prefixLift 6465813
  have htrace : WordTrace (prefixWord ++ tailWord_6465813) baseStart_6465813 baseEnd_6465813 := by
    simpa [prefixWord, tailWord_6465813, baseEnd_6465813] using wordTrace_append hprefix tailTrace_6465813
  have hstable : (prefixWord ++ tailWord_6465813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465813).length < 2 ^ (prefixWord ++ tailWord_6465813).sum := by decide
  have hdescent : baseEnd_6465813 < baseStart_6465813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465820 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_6465820 : Nat := 118140960795 + 6465820 * 2 ^ 59
def prefixEnd_6465820 : Nat := 4983230072969 + 3 ^ 40 * 6465820 * 2
def baseEnd_6465820 : Nat := 3320073485453997683214241

theorem tailTrace_6465820 : CollatzResearch.WordTrace tailWord_6465820 prefixEnd_6465820 3320073485453997683214241 := by
  unfold tailWord_6465820
  simp only [CollatzResearch.WordTrace]
  refine ⟨117913914717722944492677457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157218552956963925990236609 117913914717722944492677457)
  ·
    refine ⟨88435436038292208369508093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117913914717722944492677457 88435436038292208369508093)
    ·
      refine ⟨33163288514359578138565535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88435436038292208369508093 33163288514359578138565535)
      ·
        refine ⟨49744932771539367207848303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33163288514359578138565535 49744932771539367207848303)
        ·
          refine ⟨74617399157309050811772455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49744932771539367207848303 74617399157309050811772455)
          ·
            refine ⟨111926098735963576217658683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74617399157309050811772455 111926098735963576217658683)
            ·
              refine ⟨167889148103945364326488025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111926098735963576217658683 167889148103945364326488025)
              ·
                refine ⟨125916861077959023244866019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167889148103945364326488025 125916861077959023244866019)
                ·
                  refine ⟨188875291616938534867299029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125916861077959023244866019 188875291616938534867299029)
                  ·
                    refine ⟨4426764647271996910952321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 188875291616938534867299029 4426764647271996910952321)
                    ·
                      refine ⟨3320073485453997683214241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4426764647271996910952321 3320073485453997683214241)
                      ·
                        rfl

theorem cell23_6465820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_6465820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465820 prefixEnd_6465820 := by exact prefixLift 6465820
  have htrace : WordTrace (prefixWord ++ tailWord_6465820) baseStart_6465820 baseEnd_6465820 := by
    simpa [prefixWord, tailWord_6465820, baseEnd_6465820] using wordTrace_append hprefix tailTrace_6465820
  have hstable : (prefixWord ++ tailWord_6465820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465820).length < 2 ^ (prefixWord ++ tailWord_6465820).sum := by decide
  have hdescent : baseEnd_6465820 < baseStart_6465820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465834 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 7]
def baseStart_6465834 : Nat := 118140960795 + 6465834 * 2 ^ 59
def prefixEnd_6465834 : Nat := 4983230072969 + 3 ^ 40 * 6465834 * 2
def baseEnd_6465834 : Nat := 368897852687017847604353

theorem tailTrace_6465834 : CollatzResearch.WordTrace tailWord_6465834 prefixEnd_6465834 368897852687017847604353 := by
  unfold tailWord_6465834
  simp only [CollatzResearch.WordTrace]
  refine ⟨58957085014348792344091139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157218893371596779584243037 58957085014348792344091139)
  ·
    refine ⟨88435627521523188516136709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58957085014348792344091139 88435627521523188516136709)
    ·
      refine ⟨16581680160285597846775633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88435627521523188516136709 16581680160285597846775633)
      ·
        refine ⟨12436260120214198385081725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16581680160285597846775633 12436260120214198385081725)
        ·
          refine ⟨4663597545080324394405647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12436260120214198385081725 4663597545080324394405647)
          ·
            refine ⟨6995396317620486591608471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663597545080324394405647 6995396317620486591608471)
            ·
              refine ⟨10493094476430729887412707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6995396317620486591608471 10493094476430729887412707)
              ·
                refine ⟨15739641714646094831119061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10493094476430729887412707 15739641714646094831119061)
                ·
                  refine ⟨368897852687017847604353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15739641714646094831119061 368897852687017847604353)
                  ·
                    rfl

theorem cell23_6465834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 7].length) (baseStart_6465834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465834 prefixEnd_6465834 := by exact prefixLift 6465834
  have htrace : WordTrace (prefixWord ++ tailWord_6465834) baseStart_6465834 baseEnd_6465834 := by
    simpa [prefixWord, tailWord_6465834, baseEnd_6465834] using wordTrace_append hprefix tailTrace_6465834
  have hstable : (prefixWord ++ tailWord_6465834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465834).length < 2 ^ (prefixWord ++ tailWord_6465834).sum := by decide
  have hdescent : baseEnd_6465834 < baseStart_6465834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465913 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 7]
def baseStart_6465913 : Nat := 118140960795 + 6465913 * 2 ^ 59
def prefixEnd_6465913 : Nat := 4983230072969 + 3 ^ 40 * 6465913 * 2
def baseEnd_6465913 : Nat := 3320121239154865819351313

theorem tailTrace_6465913 : CollatzResearch.WordTrace tailWord_6465913 prefixEnd_6465913 3320121239154865819351313 := by
  unfold tailWord_6465913
  simp only [CollatzResearch.WordTrace]
  refine ⟨235831221424108965868490393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157220814282739310578993595 235831221424108965868490393)
  ·
    refine ⟨176873416068081724401367795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235831221424108965868490393 176873416068081724401367795)
    ·
      refine ⟨265310124102122586602051693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176873416068081724401367795 265310124102122586602051693)
      ·
        refine ⟨99491296538295969975769385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265310124102122586602051693 99491296538295969975769385)
        ·
          refine ⟨74618472403721977481827039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99491296538295969975769385 74618472403721977481827039)
          ·
            refine ⟨111927708605582966222740559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74618472403721977481827039 111927708605582966222740559)
            ·
              refine ⟨167891562908374449334110839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111927708605582966222740559 167891562908374449334110839)
              ·
                refine ⟨251837344362561674001166259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167891562908374449334110839 251837344362561674001166259)
                ·
                  refine ⟨377756016543842511001749389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251837344362561674001166259 377756016543842511001749389)
                  ·
                    refine ⟨141658506203940941625656021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 377756016543842511001749389 141658506203940941625656021)
                    ·
                      refine ⟨3320121239154865819351313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141658506203940941625656021 3320121239154865819351313)
                      ·
                        rfl

theorem cell23_6465913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_6465913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465913 prefixEnd_6465913 := by exact prefixLift 6465913
  have htrace : WordTrace (prefixWord ++ tailWord_6465913) baseStart_6465913 baseEnd_6465913 := by
    simpa [prefixWord, tailWord_6465913, baseEnd_6465913] using wordTrace_append hprefix tailTrace_6465913
  have hstable : (prefixWord ++ tailWord_6465913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465913).length < 2 ^ (prefixWord ++ tailWord_6465913).sum := by decide
  have hdescent : baseEnd_6465913 < baseStart_6465913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465917 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 5, 1, 3]
def baseStart_6465917 : Nat := 118140960795 + 6465917 * 2 ^ 59
def prefixEnd_6465917 : Nat := 4983230072969 + 3 ^ 40 * 6465917 * 2
def baseEnd_6465917 : Nat := 3320123293077483803701295

theorem tailTrace_6465917 : CollatzResearch.WordTrace tailWord_6465917 prefixEnd_6465917 3320123293077483803701295 := by
  unfold tailWord_6465917
  simp only [CollatzResearch.WordTrace]
  refine ⟨235831367316094474551636005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157220911544062983034424003 235831367316094474551636005)
  ·
    refine ⟨44218381371767713978431751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235831367316094474551636005 44218381371767713978431751)
    ·
      refine ⟨66327572057651570967647627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44218381371767713978431751 66327572057651570967647627)
      ·
        refine ⟨99491358086477356451471441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66327572057651570967647627 99491358086477356451471441)
        ·
          refine ⟨74618518564858017338603581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99491358086477356451471441 74618518564858017338603581)
          ·
            refine ⟨27981944461821756501976343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74618518564858017338603581 27981944461821756501976343)
            ·
              refine ⟨41972916692732634752964515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27981944461821756501976343 41972916692732634752964515)
              ·
                refine ⟨62959375039098952129446773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41972916692732634752964515 62959375039098952129446773)
                ·
                  refine ⟨5902441409915526762135635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62959375039098952129446773 5902441409915526762135635)
                  ·
                    refine ⟨8853662114873290143203453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5902441409915526762135635 8853662114873290143203453)
                    ·
                      refine ⟨3320123293077483803701295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8853662114873290143203453 3320123293077483803701295)
                      ·
                        rfl

theorem cell23_6465917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_6465917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465917 prefixEnd_6465917 := by exact prefixLift 6465917
  have htrace : WordTrace (prefixWord ++ tailWord_6465917) baseStart_6465917 baseEnd_6465917 := by
    simpa [prefixWord, tailWord_6465917, baseEnd_6465917] using wordTrace_append hprefix tailTrace_6465917
  have hstable : (prefixWord ++ tailWord_6465917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465917).length < 2 ^ (prefixWord ++ tailWord_6465917).sum := by decide
  have hdescent : baseEnd_6465917 < baseStart_6465917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465927 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 1, 5, 2]
def baseStart_6465927 : Nat := 118140960795 + 6465927 * 2 ^ 59
def prefixEnd_6465927 : Nat := 4983230072969 + 3 ^ 40 * 6465927 * 2
def baseEnd_6465927 : Nat := 3320128427884028764576249

theorem tailTrace_6465927 : CollatzResearch.WordTrace tailWord_6465927 prefixEnd_6465927 3320128427884028764576249 := by
  unfold tailWord_6465927
  simp only [CollatzResearch.WordTrace]
  refine ⟨235831732046058246259500035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157221154697372164173000023 235831732046058246259500035)
  ·
    refine ⟨353747598069087369389250053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235831732046058246259500035 353747598069087369389250053)
    ·
      refine ⟨66327674637953881760484385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353747598069087369389250053 66327674637953881760484385)
      ·
        refine ⟨49745755978465411320363289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66327674637953881760484385 49745755978465411320363289)
        ·
          refine ⟨37309316983849058490272467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49745755978465411320363289 37309316983849058490272467)
          ·
            refine ⟨55963975475773587735408701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37309316983849058490272467 55963975475773587735408701)
            ·
              refine ⟨20986490803415095400778263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55963975475773587735408701 20986490803415095400778263)
              ·
                refine ⟨31479736205122643101167395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20986490803415095400778263 31479736205122643101167395)
                ·
                  refine ⟨47219604307683964651751093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31479736205122643101167395 47219604307683964651751093)
                  ·
                    refine ⟨4426837903845371686101665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47219604307683964651751093 4426837903845371686101665)
                    ·
                      refine ⟨3320128427884028764576249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4426837903845371686101665 3320128427884028764576249)
                      ·
                        rfl

theorem cell23_6465927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_6465927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465927 prefixEnd_6465927 := by exact prefixLift 6465927
  have htrace : WordTrace (prefixWord ++ tailWord_6465927) baseStart_6465927 baseEnd_6465927 := by
    simpa [prefixWord, tailWord_6465927, baseEnd_6465927] using wordTrace_append hprefix tailTrace_6465927
  have hstable : (prefixWord ++ tailWord_6465927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465927).length < 2 ^ (prefixWord ++ tailWord_6465927).sum := by decide
  have hdescent : baseEnd_6465927 < baseStart_6465927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6465970 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_6465970 : Nat := 118140960795 + 6465970 * 2 ^ 59
def prefixEnd_6465970 : Nat := 4983230072969 + 3 ^ 40 * 6465970 * 2
def baseEnd_6465970 : Nat := 3320150507552172096338551

theorem tailTrace_6465970 : CollatzResearch.WordTrace tailWord_6465970 prefixEnd_6465970 3320150507552172096338551 := by
  unfold tailWord_6465970
  simp only [CollatzResearch.WordTrace]
  refine ⟨58958325096225616150828841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157222200256601643068876909 58958325096225616150828841)
  ·
    refine ⟨44218743822169212113121631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58958325096225616150828841 44218743822169212113121631)
    ·
      refine ⟨66328115733253818169682447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44218743822169212113121631 66328115733253818169682447)
      ·
        refine ⟨99492173599880727254523671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66328115733253818169682447 99492173599880727254523671)
        ·
          refine ⟨149238260399821090881785507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99492173599880727254523671 149238260399821090881785507)
          ·
            refine ⟨223857390599731636322678261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149238260399821090881785507 223857390599731636322678261)
            ·
              refine ⟨20986630368724840905251087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 223857390599731636322678261 20986630368724840905251087)
              ·
                refine ⟨31479945553087261357876631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20986630368724840905251087 31479945553087261357876631)
                ·
                  refine ⟨47219918329630892036814947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31479945553087261357876631 47219918329630892036814947)
                  ·
                    refine ⟨70829877494446338055222421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47219918329630892036814947 70829877494446338055222421)
                    ·
                      refine ⟨3320150507552172096338551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70829877494446338055222421 3320150507552172096338551)
                      ·
                        rfl

theorem cell23_6465970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_6465970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6465970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6465970 prefixEnd_6465970 := by exact prefixLift 6465970
  have htrace : WordTrace (prefixWord ++ tailWord_6465970) baseStart_6465970 baseEnd_6465970 := by
    simpa [prefixWord, tailWord_6465970, baseEnd_6465970] using wordTrace_append hprefix tailTrace_6465970
  have hstable : (prefixWord ++ tailWord_6465970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6465970).length < 2 ^ (prefixWord ++ tailWord_6465970).sum := by decide
  have hdescent : baseEnd_6465970 < baseStart_6465970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6465970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466010 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 2, 7]
def baseStart_6466010 : Nat := 118140960795 + 6466010 * 2 ^ 59
def prefixEnd_6466010 : Nat := 4983230072969 + 3 ^ 40 * 6466010 * 2
def baseEnd_6466010 : Nat := 1106723682259450646612789

theorem tailTrace_6466010 : CollatzResearch.WordTrace tailWord_6466010 prefixEnd_6466010 1106723682259450646612789 := by
  unfold tailWord_6466010
  simp only [CollatzResearch.WordTrace]
  refine ⟨58958689826189387858692871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157223172869838367623180989 58958689826189387858692871)
  ·
    refine ⟨88438034739284081788039307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58958689826189387858692871 88438034739284081788039307)
    ·
      refine ⟨132657052108926122682058961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88438034739284081788039307 132657052108926122682058961)
      ·
        refine ⟨99492789081694592011544221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132657052108926122682058961 99492789081694592011544221)
        ·
          refine ⟨37309795905635472004329083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99492789081694592011544221 37309795905635472004329083)
          ·
            refine ⟨55964693858453208006493625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37309795905635472004329083 55964693858453208006493625)
            ·
              refine ⟨41973520393839906004870219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55964693858453208006493625 41973520393839906004870219)
              ·
                refine ⟨62960280590759859007305329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41973520393839906004870219 62960280590759859007305329)
                ·
                  refine ⟨47220210443069894255478997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62960280590759859007305329 47220210443069894255478997)
                  ·
                    refine ⟨1106723682259450646612789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47220210443069894255478997 1106723682259450646612789)
                    ·
                      rfl

theorem cell23_6466010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_6466010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466010 prefixEnd_6466010 := by exact prefixLift 6466010
  have htrace : WordTrace (prefixWord ++ tailWord_6466010) baseStart_6466010 baseEnd_6466010 := by
    simpa [prefixWord, tailWord_6466010, baseEnd_6466010] using wordTrace_append hprefix tailTrace_6466010
  have hstable : (prefixWord ++ tailWord_6466010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466010).length < 2 ^ (prefixWord ++ tailWord_6466010).sum := by decide
  have hdescent : baseEnd_6466010 < baseStart_6466010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466018 : List Nat := [3, 3, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_6466018 : Nat := 118140960795 + 6466018 * 2 ^ 59
def prefixEnd_6466018 : Nat := 4983230072969 + 3 ^ 40 * 6466018 * 2
def baseEnd_6466018 : Nat := 1106725051541195969512777

theorem tailTrace_6466018 : CollatzResearch.WordTrace tailWord_6466018 prefixEnd_6466018 1106725051541195969512777 := by
  unfold tailWord_6466018
  simp only [CollatzResearch.WordTrace]
  refine ⟨58958762772182142200265677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157223367392485712534041805 58958762772182142200265677)
  ·
    refine ⟨22109536039568303325099629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58958762772182142200265677 22109536039568303325099629)
    ·
      refine ⟨8291076014838113746912361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22109536039568303325099629 8291076014838113746912361)
      ·
        refine ⟨6218307011128585310184271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8291076014838113746912361 6218307011128585310184271)
        ·
          refine ⟨9327460516692877965276407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6218307011128585310184271 9327460516692877965276407)
          ·
            refine ⟨13991190775039316947914611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9327460516692877965276407 13991190775039316947914611)
            ·
              refine ⟨20986786162558975421871917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13991190775039316947914611 20986786162558975421871917)
              ·
                refine ⟨7870044810959615783201969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20986786162558975421871917 7870044810959615783201969)
                ·
                  refine ⟨5902533608219711837401477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7870044810959615783201969 5902533608219711837401477)
                  ·
                    refine ⟨1106725051541195969512777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5902533608219711837401477 1106725051541195969512777)
                    ·
                      rfl

theorem cell23_6466018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_6466018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466018 prefixEnd_6466018 := by exact prefixLift 6466018
  have htrace : WordTrace (prefixWord ++ tailWord_6466018) baseStart_6466018 baseEnd_6466018 := by
    simpa [prefixWord, tailWord_6466018, baseEnd_6466018] using wordTrace_append hprefix tailTrace_6466018
  have hstable : (prefixWord ++ tailWord_6466018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466018).length < 2 ^ (prefixWord ++ tailWord_6466018).sum := by decide
  have hdescent : baseEnd_6466018 < baseStart_6466018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466051 : List Nat := [1, 1, 1, 3, 2, 1, 7, 1, 1, 3, 2]
def baseStart_6466051 : Nat := 118140960795 + 6466051 * 2 ^ 59
def prefixEnd_6466051 : Nat := 4983230072969 + 3 ^ 40 * 6466051 * 2
def baseEnd_6466051 : Nat := 3320192099485186279425679

theorem tailTrace_6466051 : CollatzResearch.WordTrace tailWord_6466051 prefixEnd_6466051 3320192099485186279425679 := by
  unfold tailWord_6466051
  simp only [CollatzResearch.WordTrace]
  refine ⟨235836254697609015437014007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157224169798406010291342671 235836254697609015437014007)
  ·
    refine ⟨353754382046413523155521011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235836254697609015437014007 353754382046413523155521011)
    ·
      refine ⟨530631573069620284733281517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353754382046413523155521011 530631573069620284733281517)
      ·
        refine ⟨198986839901107606774980569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 530631573069620284733281517 198986839901107606774980569)
        ·
          refine ⟨149240129925830705081235427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198986839901107606774980569 149240129925830705081235427)
          ·
            refine ⟨223860194888746057621853141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149240129925830705081235427 223860194888746057621853141)
            ·
              refine ⟨5246723317704985725512183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 223860194888746057621853141 5246723317704985725512183)
              ·
                refine ⟨7870084976557478588268275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5246723317704985725512183 7870084976557478588268275)
                ·
                  refine ⟨11805127464836217882402413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7870084976557478588268275 11805127464836217882402413)
                  ·
                    refine ⟨4426922799313581705900905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11805127464836217882402413 4426922799313581705900905)
                    ·
                      refine ⟨3320192099485186279425679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4426922799313581705900905 3320192099485186279425679)
                      ·
                        rfl

theorem cell23_6466051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 1, 3, 2].length) (baseStart_6466051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466051 prefixEnd_6466051 := by exact prefixLift 6466051
  have htrace : WordTrace (prefixWord ++ tailWord_6466051) baseStart_6466051 baseEnd_6466051 := by
    simpa [prefixWord, tailWord_6466051, baseEnd_6466051] using wordTrace_append hprefix tailTrace_6466051
  have hstable : (prefixWord ++ tailWord_6466051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466051).length < 2 ^ (prefixWord ++ tailWord_6466051).sum := by decide
  have hdescent : baseEnd_6466051 < baseStart_6466051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466077 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_6466077 : Nat := 118140960795 + 6466077 * 2 ^ 59
def prefixEnd_6466077 : Nat := 4983230072969 + 3 ^ 40 * 6466077 * 2
def baseEnd_6466077 : Nat := 3320205449982203177700559

theorem tailTrace_6466077 : CollatzResearch.WordTrace tailWord_6466077 prefixEnd_6466077 3320205449982203177700559 := by
  unfold tailWord_6466077
  simp only [CollatzResearch.WordTrace]
  refine ⟨235837202995514821877460485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157224801997009881251640323 235837202995514821877460485)
  ·
    refine ⟨44219475561659029102023841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235837202995514821877460485 44219475561659029102023841)
    ·
      refine ⟨33164606671244271826517881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44219475561659029102023841 33164606671244271826517881)
      ·
        refine ⟨24873455003433203869888411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33164606671244271826517881 24873455003433203869888411)
        ·
          refine ⟨37310182505149805804832617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24873455003433203869888411 37310182505149805804832617)
          ·
            refine ⟨27982636878862354353624463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37310182505149805804832617 27982636878862354353624463)
            ·
              refine ⟨41973955318293531530436695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27982636878862354353624463 41973955318293531530436695)
              ·
                refine ⟨62960932977440297295655043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41973955318293531530436695 62960932977440297295655043)
                ·
                  refine ⟨94441399466160445943482565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62960932977440297295655043 94441399466160445943482565)
                  ·
                    refine ⟨17707762399905083614402981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94441399466160445943482565 17707762399905083614402981)
                    ·
                      refine ⟨3320205449982203177700559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17707762399905083614402981 3320205449982203177700559)
                      ·
                        rfl

theorem cell23_6466077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_6466077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466077 prefixEnd_6466077 := by exact prefixLift 6466077
  have htrace : WordTrace (prefixWord ++ tailWord_6466077) baseStart_6466077 baseEnd_6466077 := by
    simpa [prefixWord, tailWord_6466077, baseEnd_6466077] using wordTrace_append hprefix tailTrace_6466077
  have hstable : (prefixWord ++ tailWord_6466077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466077).length < 2 ^ (prefixWord ++ tailWord_6466077).sum := by decide
  have hdescent : baseEnd_6466077 < baseStart_6466077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466081 : List Nat := [1, 2, 3, 2, 2, 1, 1, 5, 2, 2, 2]
def baseStart_6466081 : Nat := 118140960795 + 6466081 * 2 ^ 59
def prefixEnd_6466081 : Nat := 4983230072969 + 3 ^ 40 * 6466081 * 2
def baseEnd_6466081 : Nat := 3320207503904821162050541

theorem tailTrace_6466081 : CollatzResearch.WordTrace tailWord_6466081 prefixEnd_6466081 3320207503904821162050541 := by
  unfold tailWord_6466081
  simp only [CollatzResearch.WordTrace]
  refine ⟨235837348887500330560606097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157224899258333553707070731 235837348887500330560606097)
  ·
    refine ⟨176878011665625247920454573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235837348887500330560606097 176878011665625247920454573)
    ·
      refine ⟨66329254374609467970170465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176878011665625247920454573 66329254374609467970170465)
      ·
        refine ⟨49746940780957100977627849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66329254374609467970170465 49746940780957100977627849)
        ·
          refine ⟨37310205585717825733220887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49746940780957100977627849 37310205585717825733220887)
          ·
            refine ⟨55965308378576738599831331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37310205585717825733220887 55965308378576738599831331)
            ·
              refine ⟨83947962567865107899746997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55965308378576738599831331 83947962567865107899746997)
              ·
                refine ⟨7870121490737353865601281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83947962567865107899746997 7870121490737353865601281)
                ·
                  refine ⟨5902591118053015399200961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7870121490737353865601281 5902591118053015399200961)
                  ·
                    refine ⟨4426943338539761549400721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5902591118053015399200961 4426943338539761549400721)
                    ·
                      refine ⟨3320207503904821162050541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4426943338539761549400721 3320207503904821162050541)
                      ·
                        rfl

theorem cell23_6466081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_6466081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466081 prefixEnd_6466081 := by exact prefixLift 6466081
  have htrace : WordTrace (prefixWord ++ tailWord_6466081) baseStart_6466081 baseEnd_6466081 := by
    simpa [prefixWord, tailWord_6466081, baseEnd_6466081] using wordTrace_append hprefix tailTrace_6466081
  have hstable : (prefixWord ++ tailWord_6466081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466081).length < 2 ^ (prefixWord ++ tailWord_6466081).sum := by decide
  have hdescent : baseEnd_6466081 < baseStart_6466081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466104 : List Nat := [2, 1, 2, 1, 4, 1, 4, 3, 5]
def baseStart_6466104 : Nat := 118140960795 + 6466104 * 2 ^ 59
def prefixEnd_6466104 : Nat := 4983230072969 + 3 ^ 40 * 6466104 * 2
def baseEnd_6466104 : Nat := 368913257106652730229215

theorem tailTrace_6466104 : CollatzResearch.WordTrace tailWord_6466104 prefixEnd_6466104 368913257106652730229215 := by
  unfold tailWord_6466104
  simp only [CollatzResearch.WordTrace]
  refine ⟨117919093883208502744346683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157225458510944670325795577 117919093883208502744346683)
  ·
    refine ⟨176878640824812754116520025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117919093883208502744346683 176878640824812754116520025)
    ·
      refine ⟨132658980618609565587390019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176878640824812754116520025 132658980618609565587390019)
      ·
        refine ⟨198988470927914348381085029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132658980618609565587390019 198988470927914348381085029)
        ·
          refine ⟨37310338298983940321453443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198988470927914348381085029 37310338298983940321453443)
          ·
            refine ⟨55965507448475910482180165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37310338298983940321453443 55965507448475910482180165)
            ·
              refine ⟨10493532646589233215408781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55965507448475910482180165 10493532646589233215408781)
              ·
                refine ⟨3935074742470962455778293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10493532646589233215408781 3935074742470962455778293)
                ·
                  refine ⟨368913257106652730229215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3935074742470962455778293 368913257106652730229215)
                  ·
                    rfl

theorem cell23_6466104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 5].length) (baseStart_6466104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466104 prefixEnd_6466104 := by exact prefixLift 6466104
  have htrace : WordTrace (prefixWord ++ tailWord_6466104) baseStart_6466104 baseEnd_6466104 := by
    simpa [prefixWord, tailWord_6466104, baseEnd_6466104] using wordTrace_append hprefix tailTrace_6466104
  have hstable : (prefixWord ++ tailWord_6466104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466104).length < 2 ^ (prefixWord ++ tailWord_6466104).sum := by decide
  have hdescent : baseEnd_6466104 < baseStart_6466104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466154 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_6466154 : Nat := 118140960795 + 6466154 * 2 ^ 59
def prefixEnd_6466154 : Nat := 4983230072969 + 3 ^ 40 * 6466154 * 2
def baseEnd_6466154 : Nat := 3320244987992599376437705

theorem tailTrace_6466154 : CollatzResearch.WordTrace tailWord_6466154 prefixEnd_6466154 3320244987992599376437705 := by
  unfold tailWord_6466154
  simp only [CollatzResearch.WordTrace]
  refine ⟨58960002854058966007003379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157226674277490576018675677 58960002854058966007003379)
  ·
    refine ⟨88440004281088449010505069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58960002854058966007003379 88440004281088449010505069)
    ·
      refine ⟨33165001605408168378939401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88440004281088449010505069 33165001605408168378939401)
      ·
        refine ⟨24873751204056126284204551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33165001605408168378939401 24873751204056126284204551)
        ·
          refine ⟨37310626806084189426306827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24873751204056126284204551 37310626806084189426306827)
          ·
            refine ⟨55965940209126284139460241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37310626806084189426306827 55965940209126284139460241)
            ·
              refine ⟨41974455156844713104595181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55965940209126284139460241 41974455156844713104595181)
              ·
                refine ⟨15740420683816767414223193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41974455156844713104595181 15740420683816767414223193)
                ·
                  refine ⟨11805315512862575560667395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15740420683816767414223193 11805315512862575560667395)
                  ·
                    refine ⟨17707973269293863341001093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11805315512862575560667395 17707973269293863341001093)
                    ·
                      refine ⟨3320244987992599376437705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17707973269293863341001093 3320244987992599376437705)
                      ·
                        rfl

theorem cell23_6466154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_6466154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466154 prefixEnd_6466154 := by exact prefixLift 6466154
  have htrace : WordTrace (prefixWord ++ tailWord_6466154) baseStart_6466154 baseEnd_6466154 := by
    simpa [prefixWord, tailWord_6466154, baseEnd_6466154] using wordTrace_append hprefix tailTrace_6466154
  have hstable : (prefixWord ++ tailWord_6466154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466154).length < 2 ^ (prefixWord ++ tailWord_6466154).sum := by decide
  have hdescent : baseEnd_6466154 < baseStart_6466154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466177 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 8]
def baseStart_6466177 : Nat := 118140960795 + 6466177 * 2 ^ 59
def prefixEnd_6466177 : Nat := 4983230072969 + 3 ^ 40 * 6466177 * 2
def baseEnd_6466177 : Nat := 368917422005294754050011

theorem tailTrace_6466177 : CollatzResearch.WordTrace tailWord_6466177 prefixEnd_6466177 368917422005294754050011 := by
  unfold tailWord_6466177
  simp only [CollatzResearch.WordTrace]
  refine ⟨235840850295152538956100785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157227233530101692637400523 235840850295152538956100785)
  ·
    refine ⟨176880637721364404217075589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235840850295152538956100785 176880637721364404217075589)
    ·
      refine ⟨33165119572755825790701673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176880637721364404217075589 33165119572755825790701673)
      ·
        refine ⟨24873839679566869343026255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33165119572755825790701673 24873839679566869343026255)
        ·
          refine ⟨37310759519350304014539383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24873839679566869343026255 37310759519350304014539383)
          ·
            refine ⟨55966139279025456021809075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37310759519350304014539383 55966139279025456021809075)
            ·
              refine ⟨83949208918538184032713613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55966139279025456021809075 83949208918538184032713613)
              ·
                refine ⟨31480953344451819012267605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83949208918538184032713613 31480953344451819012267605)
                ·
                  refine ⟨368917422005294754050011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31480953344451819012267605 368917422005294754050011)
                  ·
                    rfl

theorem cell23_6466177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 8].length) (baseStart_6466177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466177 prefixEnd_6466177 := by exact prefixLift 6466177
  have htrace : WordTrace (prefixWord ++ tailWord_6466177) baseStart_6466177 baseEnd_6466177 := by
    simpa [prefixWord, tailWord_6466177, baseEnd_6466177] using wordTrace_append hprefix tailTrace_6466177
  have hstable : (prefixWord ++ tailWord_6466177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466177).length < 2 ^ (prefixWord ++ tailWord_6466177).sum := by decide
  have hdescent : baseEnd_6466177 < baseStart_6466177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466181 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 3, 4]
def baseStart_6466181 : Nat := 118140960795 + 6466181 * 2 ^ 59
def prefixEnd_6466181 : Nat := 4983230072969 + 3 ^ 40 * 6466181 * 2
def baseEnd_6466181 : Nat := 1106752950656756923600027

theorem tailTrace_6466181 : CollatzResearch.WordTrace tailWord_6466181 prefixEnd_6466181 1106752950656756923600027 := by
  unfold tailWord_6466181
  simp only [CollatzResearch.WordTrace]
  refine ⟨235840996187138047639246397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157227330791425365092830931 235840996187138047639246397)
  ·
    refine ⟨88440373570176767864717399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235840996187138047639246397 88440373570176767864717399)
    ·
      refine ⟨132660560355265151797076099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88440373570176767864717399 132660560355265151797076099)
      ·
        refine ⟨198990840532897727695614149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132660560355265151797076099 198990840532897727695614149)
        ·
          refine ⟨37310782599918323942927653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198990840532897727695614149 37310782599918323942927653)
          ·
            refine ⟨6995771737484685739298935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37310782599918323942927653 6995771737484685739298935)
            ·
              refine ⟨10493657606227028608948403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6995771737484685739298935 10493657606227028608948403)
              ·
                refine ⟨15740486409340542913422605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10493657606227028608948403 15740486409340542913422605)
                ·
                  refine ⟨5902682403502703592533477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15740486409340542913422605 5902682403502703592533477)
                  ·
                    refine ⟨1106752950656756923600027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5902682403502703592533477 1106752950656756923600027)
                    ·
                      rfl

theorem cell23_6466181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_6466181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466181 prefixEnd_6466181 := by exact prefixLift 6466181
  have htrace : WordTrace (prefixWord ++ tailWord_6466181) baseStart_6466181 baseEnd_6466181 := by
    simpa [prefixWord, tailWord_6466181, baseEnd_6466181] using wordTrace_append hprefix tailTrace_6466181
  have hstable : (prefixWord ++ tailWord_6466181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466181).length < 2 ^ (prefixWord ++ tailWord_6466181).sum := by decide
  have hdescent : baseEnd_6466181 < baseStart_6466181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466187 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 3]
def baseStart_6466187 : Nat := 118140960795 + 6466187 * 2 ^ 59
def prefixEnd_6466187 : Nat := 4983230072969 + 3 ^ 40 * 6466187 * 2
def baseEnd_6466187 : Nat := 3320261932854197747325053

theorem tailTrace_6466187 : CollatzResearch.WordTrace tailWord_6466187 prefixEnd_6466187 3320261932854197747325053 := by
  unfold tailWord_6466187
  simp only [CollatzResearch.WordTrace]
  refine ⟨235841215025116310663964815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157227476683410873775976543 235841215025116310663964815)
  ·
    refine ⟨353761822537674465995947223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235841215025116310663964815 353761822537674465995947223)
    ·
      refine ⟨530642733806511698993920835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353761822537674465995947223 530642733806511698993920835)
      ·
        refine ⟨795964100709767548490881253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530642733806511698993920835 795964100709767548490881253)
        ·
          refine ⟨149243268883081415342040235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 795964100709767548490881253 149243268883081415342040235)
          ·
            refine ⟨223864903324622123013060353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149243268883081415342040235 223864903324622123013060353)
            ·
              refine ⟨167898677493466592259795265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223864903324622123013060353 167898677493466592259795265)
              ·
                refine ⟨125924008120099944194846449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167898677493466592259795265 125924008120099944194846449)
                ·
                  refine ⟨94443006090074958146134837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125924008120099944194846449 94443006090074958146134837)
                  ·
                    refine ⟨8854031820944527326200141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94443006090074958146134837 8854031820944527326200141)
                    ·
                      refine ⟨3320261932854197747325053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8854031820944527326200141 3320261932854197747325053)
                      ·
                        rfl

theorem cell23_6466187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 3].length) (baseStart_6466187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466187 prefixEnd_6466187 := by exact prefixLift 6466187
  have htrace : WordTrace (prefixWord ++ tailWord_6466187) baseStart_6466187 baseEnd_6466187 := by
    simpa [prefixWord, tailWord_6466187, baseEnd_6466187] using wordTrace_append hprefix tailTrace_6466187
  have hstable : (prefixWord ++ tailWord_6466187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466187).length < 2 ^ (prefixWord ++ tailWord_6466187).sum := by decide
  have hdescent : baseEnd_6466187 < baseStart_6466187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466254 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_6466254 : Nat := 118140960795 + 6466254 * 2 ^ 59
def prefixEnd_6466254 : Nat := 4983230072969 + 3 ^ 40 * 6466254 * 2
def baseEnd_6466254 : Nat := 1106765445352682995062415

theorem tailTrace_6466254 : CollatzResearch.WordTrace tailWord_6466254 prefixEnd_6466254 1106765445352682995062415 := by
  unfold tailWord_6466254
  simp only [CollatzResearch.WordTrace]
  refine ⟨29480457339484197638331727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157229105810582387404435877 29480457339484197638331727)
  ·
    refine ⟨44220686009226296457497591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29480457339484197638331727 44220686009226296457497591)
    ·
      refine ⟨66331029013839444686246387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44220686009226296457497591 66331029013839444686246387)
      ·
        refine ⟨99496543520759167029369581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66331029013839444686246387 99496543520759167029369581)
        ·
          refine ⟨37311203820284687636013593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99496543520759167029369581 37311203820284687636013593)
          ·
            refine ⟨27983402865213515727010195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37311203820284687636013593 27983402865213515727010195)
            ·
              refine ⟨41975104297820273590515293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27983402865213515727010195 41975104297820273590515293)
              ·
                refine ⟨15740664111682602596443235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41975104297820273590515293 15740664111682602596443235)
                ·
                  refine ⟨23610996167523903894664853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15740664111682602596443235 23610996167523903894664853)
                  ·
                    refine ⟨1106765445352682995062415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23610996167523903894664853 1106765445352682995062415)
                    ·
                      rfl

theorem cell23_6466254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_6466254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466254 prefixEnd_6466254 := by exact prefixLift 6466254
  have htrace : WordTrace (prefixWord ++ tailWord_6466254) baseStart_6466254 baseEnd_6466254 := by
    simpa [prefixWord, tailWord_6466254, baseEnd_6466254] using wordTrace_append hprefix tailTrace_6466254
  have hstable : (prefixWord ++ tailWord_6466254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466254).length < 2 ^ (prefixWord ++ tailWord_6466254).sum := by decide
  have hdescent : baseEnd_6466254 < baseStart_6466254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466297 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 1, 9]
def baseStart_6466297 : Nat := 118140960795 + 6466297 * 2 ^ 59
def prefixEnd_6466297 : Nat := 4983230072969 + 3 ^ 40 * 6466297 * 2
def baseEnd_6466297 : Nat := 1106772805242064105649849

theorem tailTrace_6466297 : CollatzResearch.WordTrace tailWord_6466297 prefixEnd_6466297 1106772805242064105649849 := by
  unfold tailWord_6466297
  simp only [CollatzResearch.WordTrace]
  refine ⟨235845227054717799450469145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157230151369811866300312763 235845227054717799450469145)
  ·
    refine ⟨176883920291038349587851859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235845227054717799450469145 176883920291038349587851859)
    ·
      refine ⟨265325880436557524381777789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176883920291038349587851859 265325880436557524381777789)
      ·
        refine ⟨99497205163709071643166671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265325880436557524381777789 99497205163709071643166671)
        ·
          refine ⟨149245807745563607464750007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99497205163709071643166671 149245807745563607464750007)
          ·
            refine ⟨223868711618345411197125011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149245807745563607464750007 223868711618345411197125011)
            ·
              refine ⟨335803067427518116795687517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223868711618345411197125011 335803067427518116795687517)
              ·
                refine ⟨125926150285319293798382819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335803067427518116795687517 125926150285319293798382819)
                ·
                  refine ⟨188889225427978940697574229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125926150285319293798382819 188889225427978940697574229)
                  ·
                    refine ⟨1106772805242064105649849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 188889225427978940697574229 1106772805242064105649849)
                    ·
                      rfl

theorem cell23_6466297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_6466297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466297 prefixEnd_6466297 := by exact prefixLift 6466297
  have htrace : WordTrace (prefixWord ++ tailWord_6466297) baseStart_6466297 baseEnd_6466297 := by
    simpa [prefixWord, tailWord_6466297, baseEnd_6466297] using wordTrace_append hprefix tailTrace_6466297
  have hstable : (prefixWord ++ tailWord_6466297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466297).length < 2 ^ (prefixWord ++ tailWord_6466297).sum := by decide
  have hdescent : baseEnd_6466297 < baseStart_6466297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466321 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 3, 3, 2]
def baseStart_6466321 : Nat := 118140960795 + 6466321 * 2 ^ 59
def prefixEnd_6466321 : Nat := 4983230072969 + 3 ^ 40 * 6466321 * 2
def baseEnd_6466321 : Nat := 3320330739261900223049437

theorem tailTrace_6466321 : CollatzResearch.WordTrace tailWord_6466321 prefixEnd_6466321 3320330739261900223049437 := by
  unfold tailWord_6466321
  simp only [CollatzResearch.WordTrace]
  refine ⟨235846102406630851549342817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157230734937753901032895211 235846102406630851549342817)
  ·
    refine ⟨176884576804973138662007113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235846102406630851549342817 176884576804973138662007113)
    ·
      refine ⟨132663432603729853996505335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176884576804973138662007113 132663432603729853996505335)
      ·
        refine ⟨198995148905594780994758003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132663432603729853996505335 198995148905594780994758003)
        ·
          refine ⟨298492723358392171492137005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198995148905594780994758003 298492723358392171492137005)
          ·
            refine ⟨111934771259397064309551377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298492723358392171492137005 111934771259397064309551377)
            ·
              refine ⟨83951078444547798232163533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111934771259397064309551377 83951078444547798232163533)
              ·
                refine ⟨31481654416705424337061325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83951078444547798232163533 31481654416705424337061325)
                ·
                  refine ⟨11805620406264534126397997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31481654416705424337061325 11805620406264534126397997)
                  ·
                    refine ⟨4427107652349200297399249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11805620406264534126397997 4427107652349200297399249)
                    ·
                      refine ⟨3320330739261900223049437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427107652349200297399249 3320330739261900223049437)
                      ·
                        rfl

theorem cell23_6466321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 3, 2].length) (baseStart_6466321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466321 prefixEnd_6466321 := by exact prefixLift 6466321
  have htrace : WordTrace (prefixWord ++ tailWord_6466321) baseStart_6466321 baseEnd_6466321 := by
    simpa [prefixWord, tailWord_6466321, baseEnd_6466321] using wordTrace_append hprefix tailTrace_6466321
  have hstable : (prefixWord ++ tailWord_6466321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466321).length < 2 ^ (prefixWord ++ tailWord_6466321).sum := by decide
  have hdescent : baseEnd_6466321 < baseStart_6466321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466346 : List Nat := [3, 1, 4, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6466346 : Nat := 118140960795 + 6466346 * 2 ^ 59
def prefixEnd_6466346 : Nat := 4983230072969 + 3 ^ 40 * 6466346 * 2
def baseEnd_6466346 : Nat := 3320343576278262625236823

theorem tailTrace_6466346 : CollatzResearch.WordTrace tailWord_6466346 prefixEnd_6466346 3320343576278262625236823 := by
  unfold tailWord_6466346
  simp only [CollatzResearch.WordTrace]
  refine ⟨58961753557885070204750723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157231342821026853879335261 58961753557885070204750723)
  ·
    refine ⟨88442630336827605307126085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58961753557885070204750723 88442630336827605307126085)
    ·
      refine ⟨16582993188155175995086141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88442630336827605307126085 16582993188155175995086141)
      ·
        refine ⟨6218622445558190998157303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16582993188155175995086141 6218622445558190998157303)
        ·
          refine ⟨9327933668337286497235955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6218622445558190998157303 9327933668337286497235955)
          ·
            refine ⟨13991900502505929745853933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9327933668337286497235955 13991900502505929745853933)
            ·
              refine ⟨5246962688439723654695225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13991900502505929745853933 5246962688439723654695225)
              ·
                refine ⟨3935222016329792741021419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5246962688439723654695225 3935222016329792741021419)
                ·
                  refine ⟨5902833024494689111532129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3935222016329792741021419 5902833024494689111532129)
                  ·
                    refine ⟨4427124768371016833649097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5902833024494689111532129 4427124768371016833649097)
                    ·
                      refine ⟨3320343576278262625236823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427124768371016833649097 3320343576278262625236823)
                      ·
                        rfl

theorem cell23_6466346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6466346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466346 prefixEnd_6466346 := by exact prefixLift 6466346
  have htrace : WordTrace (prefixWord ++ tailWord_6466346) baseStart_6466346 baseEnd_6466346 := by
    simpa [prefixWord, tailWord_6466346, baseEnd_6466346] using wordTrace_append hprefix tailTrace_6466346
  have hstable : (prefixWord ++ tailWord_6466346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466346).length < 2 ^ (prefixWord ++ tailWord_6466346).sum := by decide
  have hdescent : baseEnd_6466346 < baseStart_6466346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466354 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_6466354 : Nat := 118140960795 + 6466354 * 2 ^ 59
def prefixEnd_6466354 : Nat := 4983230072969 + 3 ^ 40 * 6466354 * 2
def baseEnd_6466354 : Nat := 3320347684123498593936785

theorem tailTrace_6466354 : CollatzResearch.WordTrace tailWord_6466354 prefixEnd_6466354 3320347684123498593936785 := by
  unfold tailWord_6466354
  simp only [CollatzResearch.WordTrace]
  refine ⟨58961826503877824546323529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157231537343674198790196077 58961826503877824546323529)
  ·
    refine ⟨44221369877908368409742647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58961826503877824546323529 44221369877908368409742647)
    ·
      refine ⟨66332054816862552614613971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44221369877908368409742647 66332054816862552614613971)
      ·
        refine ⟨99498082225293828921920957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66332054816862552614613971 99498082225293828921920957)
        ·
          refine ⟨37311780834485185845720359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99498082225293828921920957 37311780834485185845720359)
          ·
            refine ⟨55967671251727778768580539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37311780834485185845720359 55967671251727778768580539)
            ·
              refine ⟨83951506877591668152870809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55967671251727778768580539 83951506877591668152870809)
              ·
                refine ⟨62963630158193751114653107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83951506877591668152870809 62963630158193751114653107)
                ·
                  refine ⟨94445445237290626671979661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62963630158193751114653107 94445445237290626671979661)
                  ·
                    refine ⟨35417041963983985001992373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94445445237290626671979661 35417041963983985001992373)
                    ·
                      refine ⟨3320347684123498593936785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35417041963983985001992373 3320347684123498593936785)
                      ·
                        rfl

theorem cell23_6466354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_6466354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466354 prefixEnd_6466354 := by exact prefixLift 6466354
  have htrace : WordTrace (prefixWord ++ tailWord_6466354) baseStart_6466354 baseEnd_6466354 := by
    simpa [prefixWord, tailWord_6466354, baseEnd_6466354] using wordTrace_append hprefix tailTrace_6466354
  have hstable : (prefixWord ++ tailWord_6466354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466354).length < 2 ^ (prefixWord ++ tailWord_6466354).sum := by decide
  have hdescent : baseEnd_6466354 < baseStart_6466354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466362 : List Nat := [3, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3]
def baseStart_6466362 : Nat := 118140960795 + 6466362 * 2 ^ 59
def prefixEnd_6466362 : Nat := 4983230072969 + 3 ^ 40 * 6466362 * 2
def baseEnd_6466362 : Nat := 3320351791968734562636749

theorem tailTrace_6466362 : CollatzResearch.WordTrace tailWord_6466362 prefixEnd_6466362 3320351791968734562636749 := by
  unfold tailWord_6466362
  simp only [CollatzResearch.WordTrace]
  refine ⟨58961899449870578887896335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157231731866321543701056893 58961899449870578887896335)
  ·
    refine ⟨88442849174805868331844503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58961899449870578887896335 88442849174805868331844503)
    ·
      refine ⟨132664273762208802497766755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88442849174805868331844503 132664273762208802497766755)
      ·
        refine ⟨198996410643313203746650133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132664273762208802497766755 198996410643313203746650133)
        ·
          refine ⟨9327956748905306425624225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 198996410643313203746650133 9327956748905306425624225)
          ·
            refine ⟨6995967561678979819218169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9327956748905306425624225 6995967561678979819218169)
            ·
              refine ⟨5246975671259234864413627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6995967561678979819218169 5246975671259234864413627)
              ·
                refine ⟨7870463506888852296620441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5246975671259234864413627 7870463506888852296620441)
                ·
                  refine ⟨5902847630166639222465331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7870463506888852296620441 5902847630166639222465331)
                  ·
                    refine ⟨8854271445249958833697997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5902847630166639222465331 8854271445249958833697997)
                    ·
                      refine ⟨3320351791968734562636749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8854271445249958833697997 3320351791968734562636749)
                      ·
                        rfl

theorem cell23_6466362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3].length) (baseStart_6466362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466362 prefixEnd_6466362 := by exact prefixLift 6466362
  have htrace : WordTrace (prefixWord ++ tailWord_6466362) baseStart_6466362 baseEnd_6466362 := by
    simpa [prefixWord, tailWord_6466362, baseEnd_6466362] using wordTrace_append hprefix tailTrace_6466362
  have hstable : (prefixWord ++ tailWord_6466362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466362).length < 2 ^ (prefixWord ++ tailWord_6466362).sum := by decide
  have hdescent : baseEnd_6466362 < baseStart_6466362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466364 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_6466364 : Nat := 118140960795 + 6466364 * 2 ^ 59
def prefixEnd_6466364 : Nat := 4983230072969 + 3 ^ 40 * 6466364 * 2
def baseEnd_6466364 : Nat := 3320352818930043554811739

theorem tailTrace_6466364 : CollatzResearch.WordTrace tailWord_6466364 prefixEnd_6466364 3320352818930043554811739 := by
  unfold tailWord_6466364
  simp only [CollatzResearch.WordTrace]
  refine ⟨117923835372737534946579073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157231780496983379928772097 117923835372737534946579073)
  ·
    refine ⟨88442876529553151209934305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117923835372737534946579073 88442876529553151209934305)
    ·
      refine ⟨66332157397164863407450729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88442876529553151209934305 66332157397164863407450729)
      ·
        refine ⟨49749118047873647555588047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66332157397164863407450729 49749118047873647555588047)
        ·
          refine ⟨74623677071810471333382071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49749118047873647555588047 74623677071810471333382071)
          ·
            refine ⟨111935515607715707000073107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74623677071810471333382071 111935515607715707000073107)
            ·
              refine ⟨167903273411573560500109661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111935515607715707000073107 167903273411573560500109661)
              ·
                refine ⟨62963727529340085187541123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167903273411573560500109661 62963727529340085187541123)
                ·
                  refine ⟨94445591294010127781311685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62963727529340085187541123 94445591294010127781311685)
                  ·
                    refine ⟨17708548367626898958995941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94445591294010127781311685 17708548367626898958995941)
                    ·
                      refine ⟨3320352818930043554811739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17708548367626898958995941 3320352818930043554811739)
                      ·
                        rfl

theorem cell23_6466364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_6466364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466364 prefixEnd_6466364 := by exact prefixLift 6466364
  have htrace : WordTrace (prefixWord ++ tailWord_6466364) baseStart_6466364 baseEnd_6466364 := by
    simpa [prefixWord, tailWord_6466364, baseEnd_6466364] using wordTrace_append hprefix tailTrace_6466364
  have hstable : (prefixWord ++ tailWord_6466364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466364).length < 2 ^ (prefixWord ++ tailWord_6466364).sum := by decide
  have hdescent : baseEnd_6466364 < baseStart_6466364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466372 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_6466372 : Nat := 118140960795 + 6466372 * 2 ^ 59
def prefixEnd_6466372 : Nat := 4983230072969 + 3 ^ 40 * 6466372 * 2
def baseEnd_6466372 : Nat := 3320356926775279523511703

theorem tailTrace_6466372 : CollatzResearch.WordTrace tailWord_6466372 prefixEnd_6466372 3320356926775279523511703 := by
  unfold tailWord_6466372
  simp only [CollatzResearch.WordTrace]
  refine ⟨117923981264723043629724685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157231975019630724839632913 117923981264723043629724685)
  ·
    refine ⟨44221492974271141361146757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117923981264723043629724685 44221492974271141361146757)
    ·
      refine ⟨8291529932675839005215017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44221492974271141361146757 8291529932675839005215017)
      ·
        refine ⟨6218647449506879253911263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8291529932675839005215017 6218647449506879253911263)
        ·
          refine ⟨9327971174260318880866895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6218647449506879253911263 9327971174260318880866895)
          ·
            refine ⟨13991956761390478321300343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9327971174260318880866895 13991956761390478321300343)
            ·
              refine ⟨20987935142085717481950515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13991956761390478321300343 20987935142085717481950515)
              ·
                refine ⟨31481902713128576222925773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20987935142085717481950515 31481902713128576222925773)
                ·
                  refine ⟨11805713517423216083597165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31481902713128576222925773 11805713517423216083597165)
                  ·
                    refine ⟨4427142569033706031348937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11805713517423216083597165 4427142569033706031348937)
                    ·
                      refine ⟨3320356926775279523511703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427142569033706031348937 3320356926775279523511703)
                      ·
                        rfl

theorem cell23_6466372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_6466372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466372 prefixEnd_6466372 := by exact prefixLift 6466372
  have htrace : WordTrace (prefixWord ++ tailWord_6466372) baseStart_6466372 baseEnd_6466372 := by
    simpa [prefixWord, tailWord_6466372, baseEnd_6466372] using wordTrace_append hprefix tailTrace_6466372
  have hstable : (prefixWord ++ tailWord_6466372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466372).length < 2 ^ (prefixWord ++ tailWord_6466372).sum := by decide
  have hdescent : baseEnd_6466372 < baseStart_6466372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466408 : List Nat := [2, 1, 4, 2, 1, 3, 1, 4, 5]
def baseStart_6466408 : Nat := 118140960795 + 6466408 * 2 ^ 59
def prefixEnd_6466408 : Nat := 4983230072969 + 3 ^ 40 * 6466408 * 2
def baseEnd_6466408 : Nat := 368930601342093486962393

theorem tailTrace_6466408 : CollatzResearch.WordTrace tailWord_6466408 prefixEnd_6466408 368930601342093486962393 := by
  unfold tailWord_6466408
  simp only [CollatzResearch.WordTrace]
  refine ⟨117924637778657832703879939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157232850371543776938506585 117924637778657832703879939)
  ·
    refine ⟨176886956667986749055819909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117924637778657832703879939 176886956667986749055819909)
    ·
      refine ⟨33166304375247515447966233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176886956667986749055819909 33166304375247515447966233)
      ·
        refine ⟨24874728281435636585974675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33166304375247515447966233 24874728281435636585974675)
        ·
          refine ⟨37312092422153454878962013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24874728281435636585974675 37312092422153454878962013)
          ·
            refine ⟨13992034658307545579610755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37312092422153454878962013 13992034658307545579610755)
            ·
              refine ⟨20988051987461318369416133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13992034658307545579610755 20988051987461318369416133)
              ·
                refine ⟨3935259747648997194265525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20988051987461318369416133 3935259747648997194265525)
                ·
                  refine ⟨368930601342093486962393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3935259747648997194265525 368930601342093486962393)
                  ·
                    rfl

theorem cell23_6466408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 5].length) (baseStart_6466408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466408 prefixEnd_6466408 := by exact prefixLift 6466408
  have htrace : WordTrace (prefixWord ++ tailWord_6466408) baseStart_6466408 baseEnd_6466408 := by
    simpa [prefixWord, tailWord_6466408, baseEnd_6466408] using wordTrace_append hprefix tailTrace_6466408
  have hstable : (prefixWord ++ tailWord_6466408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466408).length < 2 ^ (prefixWord ++ tailWord_6466408).sum := by decide
  have hdescent : baseEnd_6466408 < baseStart_6466408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466411 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 2, 5, 2]
def baseStart_6466411 : Nat := 118140960795 + 6466411 * 2 ^ 59
def prefixEnd_6466411 : Nat := 4983230072969 + 3 ^ 40 * 6466411 * 2
def baseEnd_6466411 : Nat := 3320376952520804870924023

theorem tailTrace_6466411 : CollatzResearch.WordTrace tailWord_6466411 prefixEnd_6466411 3320376952520804870924023 := by
  unfold tailWord_6466411
  simp only [CollatzResearch.WordTrace]
  refine ⟨235849384976304796920119087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157232923317536531280079391 235849384976304796920119087)
  ·
    refine ⟨353774077464457195380178631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235849384976304796920119087 353774077464457195380178631)
    ·
      refine ⟨530661116196685793070267947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353774077464457195380178631 530661116196685793070267947)
      ·
        refine ⟨795991674295028689605401921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530661116196685793070267947 795991674295028689605401921)
        ·
          refine ⟨596993755721271517204051441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 795991674295028689605401921 596993755721271517204051441)
          ·
            refine ⟨447745316790953637903038581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 596993755721271517204051441 447745316790953637903038581)
            ·
              refine ⟨41976123449151903553409867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 447745316790953637903038581 41976123449151903553409867)
              ·
                refine ⟨62964185173727855330114801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41976123449151903553409867 62964185173727855330114801)
                ·
                  refine ⟨47223138880295891497586101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62964185173727855330114801 47223138880295891497586101)
                  ·
                    refine ⟨4427169270027739827898697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47223138880295891497586101 4427169270027739827898697)
                    ·
                      refine ⟨3320376952520804870924023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427169270027739827898697 3320376952520804870924023)
                      ·
                        rfl

theorem cell23_6466411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 5, 2].length) (baseStart_6466411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466411 prefixEnd_6466411 := by exact prefixLift 6466411
  have htrace : WordTrace (prefixWord ++ tailWord_6466411) baseStart_6466411 baseEnd_6466411 := by
    simpa [prefixWord, tailWord_6466411, baseEnd_6466411] using wordTrace_append hprefix tailTrace_6466411
  have hstable : (prefixWord ++ tailWord_6466411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466411).length < 2 ^ (prefixWord ++ tailWord_6466411).sum := by decide
  have hdescent : baseEnd_6466411 < baseStart_6466411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466441 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 1, 3, 4]
def baseStart_6466441 : Nat := 118140960795 + 6466441 * 2 ^ 59
def prefixEnd_6466441 : Nat := 4983230072969 + 3 ^ 40 * 6466441 * 2
def baseEnd_6466441 : Nat := 3320392356940439753548885

theorem tailTrace_6466441 : CollatzResearch.WordTrace tailWord_6466441 prefixEnd_6466441 3320392356940439753548885 := by
  unfold tailWord_6466441
  simp only [CollatzResearch.WordTrace]
  refine ⟨235850479166196112043711177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157233652777464074695807451 235850479166196112043711177)
  ·
    refine ⟨176887859374647084032783383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235850479166196112043711177 176887859374647084032783383)
    ·
      refine ⟨265331789061970626049175075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176887859374647084032783383 265331789061970626049175075)
      ·
        refine ⟨397997683592955939073762613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265331789061970626049175075 397997683592955939073762613)
        ·
          refine ⟨37312282836839619288165245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 397997683592955939073762613 37312282836839619288165245)
          ·
            refine ⟨13992106063814857233061967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37312282836839619288165245 13992106063814857233061967)
            ·
              refine ⟨20988159095722285849592951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13992106063814857233061967 20988159095722285849592951)
              ·
                refine ⟨31482238643583428774389427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20988159095722285849592951 31482238643583428774389427)
                ·
                  refine ⟨47223357965375143161584141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31482238643583428774389427 47223357965375143161584141)
                  ·
                    refine ⟨17708759237015678685594053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47223357965375143161584141 17708759237015678685594053)
                    ·
                      refine ⟨3320392356940439753548885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17708759237015678685594053 3320392356940439753548885)
                      ·
                        rfl

theorem cell23_6466441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_6466441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466441 prefixEnd_6466441 := by exact prefixLift 6466441
  have htrace : WordTrace (prefixWord ++ tailWord_6466441) baseStart_6466441 baseEnd_6466441 := by
    simpa [prefixWord, tailWord_6466441, baseEnd_6466441] using wordTrace_append hprefix tailTrace_6466441
  have hstable : (prefixWord ++ tailWord_6466441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466441).length < 2 ^ (prefixWord ++ tailWord_6466441).sum := by decide
  have hdescent : baseEnd_6466441 < baseStart_6466441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466468 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_6466468 : Nat := 118140960795 + 6466468 * 2 ^ 59
def prefixEnd_6466468 : Nat := 4983230072969 + 3 ^ 40 * 6466468 * 2
def baseEnd_6466468 : Nat := 1106802073639370382637087

theorem tailTrace_6466468 : CollatzResearch.WordTrace tailWord_6466468 prefixEnd_6466468 1106802073639370382637087 := by
  unfold tailWord_6466468
  simp only [CollatzResearch.WordTrace]
  refine ⟨117925731968549147827472029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157234309291398863769962705 117925731968549147827472029)
  ·
    refine ⟨44222149488205930435302011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117925731968549147827472029 44222149488205930435302011)
    ·
      refine ⟨66333224232308895652953017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44222149488205930435302011 66333224232308895652953017)
      ·
        refine ⟨49749918174231671739714763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66333224232308895652953017 49749918174231671739714763)
        ·
          refine ⟨74624877261347507609572145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49749918174231671739714763 74624877261347507609572145)
          ·
            refine ⟨55968657946010630707179109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74624877261347507609572145 55968657946010630707179109)
            ·
              refine ⟨10494123364876993257596083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55968657946010630707179109 10494123364876993257596083)
              ·
                refine ⟨15741185047315489886394125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10494123364876993257596083 15741185047315489886394125)
                ·
                  refine ⟨5902944392743308707397797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15741185047315489886394125 5902944392743308707397797)
                  ·
                    refine ⟨1106802073639370382637087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5902944392743308707397797 1106802073639370382637087)
                    ·
                      rfl

theorem cell23_6466468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_6466468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466468 prefixEnd_6466468 := by exact prefixLift 6466468
  have htrace : WordTrace (prefixWord ++ tailWord_6466468) baseStart_6466468 baseEnd_6466468 := by
    simpa [prefixWord, tailWord_6466468, baseEnd_6466468] using wordTrace_append hprefix tailTrace_6466468
  have hstable : (prefixWord ++ tailWord_6466468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466468).length < 2 ^ (prefixWord ++ tailWord_6466468).sum := by decide
  have hdescent : baseEnd_6466468 < baseStart_6466468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466509 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6466509 : Nat := 118140960795 + 6466509 * 2 ^ 59
def prefixEnd_6466509 : Nat := 4983230072969 + 3 ^ 40 * 6466509 * 2
def baseEnd_6466509 : Nat := 3320427273624945487498573

theorem tailTrace_6466509 : CollatzResearch.WordTrace tailWord_6466509 prefixEnd_6466509 3320427273624945487498573 := by
  unfold tailWord_6466509
  simp only [CollatzResearch.WordTrace]
  refine ⟨235852959329949759657186581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157235306219966506438124387 235852959329949759657186581)
  ·
    refine ⟨11055607468591394983930621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 235852959329949759657186581 11055607468591394983930621)
    ·
      refine ⟨4145852800721773118973983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11055607468591394983930621 4145852800721773118973983)
      ·
        refine ⟨6218779201082659678460975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4145852800721773118973983 6218779201082659678460975)
        ·
          refine ⟨9328168801623989517691463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6218779201082659678460975 9328168801623989517691463)
          ·
            refine ⟨13992253202435984276537195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9328168801623989517691463 13992253202435984276537195)
            ·
              refine ⟨20988379803653976414805793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13992253202435984276537195 20988379803653976414805793)
              ·
                refine ⟨15741284852740482311104345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20988379803653976414805793 15741284852740482311104345)
                ·
                  refine ⟨11805963639555361733328259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15741284852740482311104345 11805963639555361733328259)
                  ·
                    refine ⟨17708945459333042599992389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11805963639555361733328259 17708945459333042599992389)
                    ·
                      refine ⟨3320427273624945487498573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17708945459333042599992389 3320427273624945487498573)
                      ·
                        rfl

theorem cell23_6466509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6466509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466509 prefixEnd_6466509 := by exact prefixLift 6466509
  have htrace : WordTrace (prefixWord ++ tailWord_6466509) baseStart_6466509 baseEnd_6466509 := by
    simpa [prefixWord, tailWord_6466509, baseEnd_6466509] using wordTrace_append hprefix tailTrace_6466509
  have hstable : (prefixWord ++ tailWord_6466509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466509).length < 2 ^ (prefixWord ++ tailWord_6466509).sum := by decide
  have hdescent : baseEnd_6466509 < baseStart_6466509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466545 : List Nat := [1, 2, 2, 2, 4, 3, 1, 2, 1, 5]
def baseStart_6466545 : Nat := 118140960795 + 6466545 * 2 ^ 59
def prefixEnd_6466545 : Nat := 4983230072969 + 3 ^ 40 * 6466545 * 2
def baseEnd_6466545 : Nat := 1106815252976169115549469

theorem tailTrace_6466545 : CollatzResearch.WordTrace tailWord_6466545 prefixEnd_6466545 1106815252976169115549469 := by
  unfold tailWord_6466545
  simp only [CollatzResearch.WordTrace]
  refine ⟨235854272357819337805497089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157236181571879558536998059 235854272357819337805497089)
  ·
    refine ⟨176890704268364503354122817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235854272357819337805497089 176890704268364503354122817)
    ·
      refine ⟨132668028201273377515592113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176890704268364503354122817 132668028201273377515592113)
      ·
        refine ⟨99501021150955033136694085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132668028201273377515592113 99501021150955033136694085)
        ·
          refine ⟨18656441465804068713130141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99501021150955033136694085 18656441465804068713130141)
          ·
            refine ⟨6996165549676525767423803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18656441465804068713130141 6996165549676525767423803)
            ·
              refine ⟨10494248324514788651135705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6996165549676525767423803 10494248324514788651135705)
              ·
                refine ⟨7870686243386091488351779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10494248324514788651135705 7870686243386091488351779)
                ·
                  refine ⟨11806029365079137232527669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7870686243386091488351779 11806029365079137232527669)
                  ·
                    refine ⟨1106815252976169115549469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11806029365079137232527669 1106815252976169115549469)
                    ·
                      rfl

theorem cell23_6466545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_6466545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466545 prefixEnd_6466545 := by exact prefixLift 6466545
  have htrace : WordTrace (prefixWord ++ tailWord_6466545) baseStart_6466545 baseEnd_6466545 := by
    simpa [prefixWord, tailWord_6466545, baseEnd_6466545] using wordTrace_append hprefix tailTrace_6466545
  have hstable : (prefixWord ++ tailWord_6466545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466545).length < 2 ^ (prefixWord ++ tailWord_6466545).sum := by decide
  have hdescent : baseEnd_6466545 < baseStart_6466545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466565 : List Nat := [1, 3, 1, 1, 2, 3, 5, 1, 1, 1, 4]
def baseStart_6466565 : Nat := 118140960795 + 6466565 * 2 ^ 59
def prefixEnd_6466565 : Nat := 4983230072969 + 3 ^ 40 * 6466565 * 2
def baseEnd_6466565 : Nat := 3320456028541597268398315

theorem tailTrace_6466565 : CollatzResearch.WordTrace tailWord_6466565 prefixEnd_6466565 3320456028541597268398315 := by
  unfold tailWord_6466565
  simp only [CollatzResearch.WordTrace]
  refine ⟨235855001817746881221225149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157236667878497920814150099 235855001817746881221225149)
  ·
    refine ⟨88445625681655080457959431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235855001817746881221225149 88445625681655080457959431)
    ·
      refine ⟨132668438522482620686939147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88445625681655080457959431 132668438522482620686939147)
      ·
        refine ⟨199002657783723931030408721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132668438522482620686939147 199002657783723931030408721)
        ·
          refine ⟨149251993337792948272806541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199002657783723931030408721 149251993337792948272806541)
          ·
            refine ⟨55969497501672355602302453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149251993337792948272806541 55969497501672355602302453)
            ·
              refine ⟨5247140390781783337715855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55969497501672355602302453 5247140390781783337715855)
              ·
                refine ⟨7870710586172675006573783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5247140390781783337715855 7870710586172675006573783)
                ·
                  refine ⟨11806065879259012509860675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7870710586172675006573783 11806065879259012509860675)
                  ·
                    refine ⟨17709098818888518764791013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11806065879259012509860675 17709098818888518764791013)
                    ·
                      refine ⟨3320456028541597268398315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17709098818888518764791013 3320456028541597268398315)
                      ·
                        rfl

theorem cell23_6466565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 1, 1, 4].length) (baseStart_6466565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466565 prefixEnd_6466565 := by exact prefixLift 6466565
  have htrace : WordTrace (prefixWord ++ tailWord_6466565) baseStart_6466565 baseEnd_6466565 := by
    simpa [prefixWord, tailWord_6466565, baseEnd_6466565] using wordTrace_append hprefix tailTrace_6466565
  have hstable : (prefixWord ++ tailWord_6466565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466565).length < 2 ^ (prefixWord ++ tailWord_6466565).sum := by decide
  have hdescent : baseEnd_6466565 < baseStart_6466565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466568 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_6466568 : Nat := 118140960795 + 6466568 * 2 ^ 59
def prefixEnd_6466568 : Nat := 4983230072969 + 3 ^ 40 * 6466568 * 2
def baseEnd_6466568 : Nat := 3320457568983560756660801

theorem tailTrace_6466568 : CollatzResearch.WordTrace tailWord_6466568 prefixEnd_6466568 3320457568983560756660801 := by
  unfold tailWord_6466568
  simp only [CollatzResearch.WordTrace]
  refine ⟨117927555618368006366792179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157236740824490675155722905 117927555618368006366792179)
  ·
    refine ⟨176891333427552009550188269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117927555618368006366792179 176891333427552009550188269)
    ·
      refine ⟨66334250035332003581320601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176891333427552009550188269 66334250035332003581320601)
      ·
        refine ⟨49750687526499002685990451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66334250035332003581320601 49750687526499002685990451)
        ·
          refine ⟨74626031289748504028985677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49750687526499002685990451 74626031289748504028985677)
          ·
            refine ⟨27984761733655689010869629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74626031289748504028985677 27984761733655689010869629)
            ·
              refine ⟨10494285650120883379076111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27984761733655689010869629 10494285650120883379076111)
              ·
                refine ⟨15741428475181325068614167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10494285650120883379076111 15741428475181325068614167)
                ·
                  refine ⟨23612142712771987602921251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15741428475181325068614167 23612142712771987602921251)
                  ·
                    refine ⟨35418214069157981404381877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23612142712771987602921251 35418214069157981404381877)
                    ·
                      refine ⟨3320457568983560756660801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35418214069157981404381877 3320457568983560756660801)
                      ·
                        rfl

theorem cell23_6466568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_6466568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466568 prefixEnd_6466568 := by exact prefixLift 6466568
  have htrace : WordTrace (prefixWord ++ tailWord_6466568) baseStart_6466568 baseEnd_6466568 := by
    simpa [prefixWord, tailWord_6466568, baseEnd_6466568] using wordTrace_append hprefix tailTrace_6466568
  have hstable : (prefixWord ++ tailWord_6466568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466568).length < 2 ^ (prefixWord ++ tailWord_6466568).sum := by decide
  have hdescent : baseEnd_6466568 < baseStart_6466568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466599 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_6466599 : Nat := 118140960795 + 6466599 * 2 ^ 59
def prefixEnd_6466599 : Nat := 4983230072969 + 3 ^ 40 * 6466599 * 2
def baseEnd_6466599 : Nat := 3320473486883850135373159

theorem tailTrace_6466599 : CollatzResearch.WordTrace tailWord_6466599 prefixEnd_6466599 3320473486883850135373159 := by
  unfold tailWord_6466599
  simp only [CollatzResearch.WordTrace]
  refine ⟨235856241899623705027962851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157237494599749136685308567 235856241899623705027962851)
  ·
    refine ⟨353784362849435557541944277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235856241899623705027962851 353784362849435557541944277)
    ·
      refine ⟨8291821004283645879889319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 353784362849435557541944277 8291821004283645879889319)
      ·
        refine ⟨12437731506425468819833979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8291821004283645879889319 12437731506425468819833979)
        ·
          refine ⟨18656597259638203229750969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12437731506425468819833979 18656597259638203229750969)
          ·
            refine ⟨13992447944728652422313227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18656597259638203229750969 13992447944728652422313227)
            ·
              refine ⟨20988671917092978633469841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13992447944728652422313227 20988671917092978633469841)
              ·
                refine ⟨15741503937819733975102381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20988671917092978633469841 15741503937819733975102381)
                ·
                  refine ⟨5903063976682400240663393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15741503937819733975102381 5903063976682400240663393)
                  ·
                    refine ⟨4427297982511800180497545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5903063976682400240663393 4427297982511800180497545)
                    ·
                      refine ⟨3320473486883850135373159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427297982511800180497545 3320473486883850135373159)
                      ·
                        rfl

theorem cell23_6466599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_6466599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466599 prefixEnd_6466599 := by exact prefixLift 6466599
  have htrace : WordTrace (prefixWord ++ tailWord_6466599) baseStart_6466599 baseEnd_6466599 := by
    simpa [prefixWord, tailWord_6466599, baseEnd_6466599] using wordTrace_append hprefix tailTrace_6466599
  have hstable : (prefixWord ++ tailWord_6466599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466599).length < 2 ^ (prefixWord ++ tailWord_6466599).sum := by decide
  have hdescent : baseEnd_6466599 < baseStart_6466599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466611 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 5]
def baseStart_6466611 : Nat := 118140960795 + 6466611 * 2 ^ 59
def prefixEnd_6466611 : Nat := 4983230072969 + 3 ^ 40 * 6466611 * 2
def baseEnd_6466611 : Nat := 3320479648651704088423103

theorem tailTrace_6466611 : CollatzResearch.WordTrace tailWord_6466611 prefixEnd_6466611 3320479648651704088423103 := by
  unfold tailWord_6466611
  simp only [CollatzResearch.WordTrace]
  refine ⟨235856679575580231077399687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157237786383720154051599791 235856679575580231077399687)
  ·
    refine ⟨353785019363370346616099531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235856679575580231077399687 353785019363370346616099531)
    ·
      refine ⟨530677529045055519924149297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353785019363370346616099531 530677529045055519924149297)
      ·
        refine ⟨398008146783791639943111973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530677529045055519924149297 398008146783791639943111973)
        ·
          refine ⟨74626527521960932489333495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 398008146783791639943111973 74626527521960932489333495)
          ·
            refine ⟨111939791282941398734000243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74626527521960932489333495 111939791282941398734000243)
            ·
              refine ⟨167909686924412098101000365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111939791282941398734000243 167909686924412098101000365)
              ·
                refine ⟨62966132596654536787875137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167909686924412098101000365 62966132596654536787875137)
                ·
                  refine ⟨47224599447490902590906353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62966132596654536787875137 47224599447490902590906353)
                  ·
                    refine ⟨35418449585618176943179765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47224599447490902590906353 35418449585618176943179765)
                    ·
                      refine ⟨3320479648651704088423103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35418449585618176943179765 3320479648651704088423103)
                      ·
                        rfl

theorem cell23_6466611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_6466611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466611 prefixEnd_6466611 := by exact prefixLift 6466611
  have htrace : WordTrace (prefixWord ++ tailWord_6466611) baseStart_6466611 baseEnd_6466611 := by
    simpa [prefixWord, tailWord_6466611, baseEnd_6466611] using wordTrace_append hprefix tailTrace_6466611
  have hstable : (prefixWord ++ tailWord_6466611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466611).length < 2 ^ (prefixWord ++ tailWord_6466611).sum := by decide
  have hdescent : baseEnd_6466611 < baseStart_6466611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466646 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_6466646 : Nat := 118140960795 + 6466646 * 2 ^ 59
def prefixEnd_6466646 : Nat := 4983230072969 + 3 ^ 40 * 6466646 * 2
def baseEnd_6466646 : Nat := 3320497620474611451485443

theorem tailTrace_6466646 : CollatzResearch.WordTrace tailWord_6466646 prefixEnd_6466646 3320497620474611451485443 := by
  unfold tailWord_6466646
  simp only [CollatzResearch.WordTrace]
  refine ⟨14741122258153339503432737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157238637420302288036615861 14741122258153339503432737)
  ·
    refine ⟨11055841693615004627574553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14741122258153339503432737 11055841693615004627574553)
    ·
      refine ⟨8291881270211253470680915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11055841693615004627574553 8291881270211253470680915)
      ·
        refine ⟨12437821905316880206021373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8291881270211253470680915 12437821905316880206021373)
        ·
          refine ⟨4664183214493830077258015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12437821905316880206021373 4664183214493830077258015)
          ·
            refine ⟨6996274821740745115887023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4664183214493830077258015 6996274821740745115887023)
            ·
              refine ⟨10494412232611117673830535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6996274821740745115887023 10494412232611117673830535)
              ·
                refine ⟨15741618348916676510745803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10494412232611117673830535 15741618348916676510745803)
                ·
                  refine ⟨23612427523375014766118705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15741618348916676510745803 23612427523375014766118705)
                  ·
                    refine ⟨17709320642531261074589029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23612427523375014766118705 17709320642531261074589029)
                    ·
                      refine ⟨3320497620474611451485443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17709320642531261074589029 3320497620474611451485443)
                      ·
                        rfl

theorem cell23_6466646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_6466646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466646 prefixEnd_6466646 := by exact prefixLift 6466646
  have htrace : WordTrace (prefixWord ++ tailWord_6466646) baseStart_6466646 baseEnd_6466646 := by
    simpa [prefixWord, tailWord_6466646, baseEnd_6466646] using wordTrace_append hprefix tailTrace_6466646
  have hstable : (prefixWord ++ tailWord_6466646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466646).length < 2 ^ (prefixWord ++ tailWord_6466646).sum := by decide
  have hdescent : baseEnd_6466646 < baseStart_6466646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466688 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 3]
def baseStart_6466688 : Nat := 118140960795 + 6466688 * 2 ^ 59
def prefixEnd_6466688 : Nat := 4983230072969 + 3 ^ 40 * 6466688 * 2
def baseEnd_6466688 : Nat := 3320519186662100287160249

theorem tailTrace_6466688 : CollatzResearch.WordTrace tailWord_6466688 prefixEnd_6466688 3320519186662100287160249 := by
  unfold tailWord_6466688
  simp only [CollatzResearch.WordTrace]
  refine ⟨117929743998150636613976359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157239658664200848818635145 117929743998150636613976359)
  ·
    refine ⟨176894615997225954920964539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117929743998150636613976359 176894615997225954920964539)
    ·
      refine ⟨265341923995838932381446809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176894615997225954920964539 265341923995838932381446809)
      ·
        refine ⟨199006442996879199286085107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265341923995838932381446809 199006442996879199286085107)
        ·
          refine ⟨298509664495318798929127661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199006442996879199286085107 298509664495318798929127661)
          ·
            refine ⟨111941124185744549598422873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298509664495318798929127661 111941124185744549598422873)
            ·
              refine ⟨83955843139308412198817155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111941124185744549598422873 83955843139308412198817155)
              ·
                refine ⟨125933764708962618298225733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83955843139308412198817155 125933764708962618298225733)
                ·
                  refine ⟨23612580882930490930917325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125933764708962618298225733 23612580882930490930917325)
                  ·
                    refine ⟨8854717831098934099093997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23612580882930490930917325 8854717831098934099093997)
                    ·
                      refine ⟨3320519186662100287160249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8854717831098934099093997 3320519186662100287160249)
                      ·
                        rfl

theorem cell23_6466688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_6466688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466688 prefixEnd_6466688 := by exact prefixLift 6466688
  have htrace : WordTrace (prefixWord ++ tailWord_6466688) baseStart_6466688 baseEnd_6466688 := by
    simpa [prefixWord, tailWord_6466688, baseEnd_6466688] using wordTrace_append hprefix tailTrace_6466688
  have hstable : (prefixWord ++ tailWord_6466688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466688).length < 2 ^ (prefixWord ++ tailWord_6466688).sum := by decide
  have hdescent : baseEnd_6466688 < baseStart_6466688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466706 : List Nat := [3, 2, 3, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_6466706 : Nat := 118140960795 + 6466706 * 2 ^ 59
def prefixEnd_6466706 : Nat := 4983230072969 + 3 ^ 40 * 6466706 * 2
def baseEnd_6466706 : Nat := 3320528429313881216735167

theorem tailTrace_6466706 : CollatzResearch.WordTrace tailWord_6466706 prefixEnd_6466706 3320528429313881216735167 := by
  unfold tailWord_6466706
  simp only [CollatzResearch.WordTrace]
  refine ⟨58965036127559015575526993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157240096340157374868071981 58965036127559015575526993)
  ·
    refine ⟨44223777095669261681645245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58965036127559015575526993 44223777095669261681645245)
    ·
      refine ⟨16583916410875973130616967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44223777095669261681645245 16583916410875973130616967)
      ·
        refine ⟨24875874616313959695925451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16583916410875973130616967 24875874616313959695925451)
        ·
          refine ⟨37313811924470939543888177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24875874616313959695925451 37313811924470939543888177)
          ·
            refine ⟨27985358943353204657916133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37313811924470939543888177 27985358943353204657916133)
            ·
              refine ⟨5247254801878725873359275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27985358943353204657916133 5247254801878725873359275)
              ·
                refine ⟨7870882202818088810038913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5247254801878725873359275 7870882202818088810038913)
                ·
                  refine ⟨5903161652113566607529185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7870882202818088810038913 5903161652113566607529185)
                  ·
                    refine ⟨4427371239085174955646889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5903161652113566607529185 4427371239085174955646889)
                    ·
                      refine ⟨3320528429313881216735167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427371239085174955646889 3320528429313881216735167)
                      ·
                        rfl

theorem cell23_6466706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_6466706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466706 prefixEnd_6466706 := by exact prefixLift 6466706
  have htrace : WordTrace (prefixWord ++ tailWord_6466706) baseStart_6466706 baseEnd_6466706 := by
    simpa [prefixWord, tailWord_6466706, baseEnd_6466706] using wordTrace_append hprefix tailTrace_6466706
  have hstable : (prefixWord ++ tailWord_6466706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466706).length < 2 ^ (prefixWord ++ tailWord_6466706).sum := by decide
  have hdescent : baseEnd_6466706 < baseStart_6466706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466725 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 2, 5]
def baseStart_6466725 : Nat := 118140960795 + 6466725 * 2 ^ 59
def prefixEnd_6466725 : Nat := 4983230072969 + 3 ^ 40 * 6466725 * 2
def baseEnd_6466725 : Nat := 1106846061815438880799193

theorem tailTrace_6466725 : CollatzResearch.WordTrace tailWord_6466725 prefixEnd_6466725 1106846061815438880799193 := by
  unfold tailWord_6466725
  simp only [CollatzResearch.WordTrace]
  refine ⟨235860837497167228547049629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157240558331444819031366419 235860837497167228547049629)
  ·
    refine ⟨88447814061437710705143611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235860837497167228547049629 88447814061437710705143611)
    ·
      refine ⟨132671721092156566057715417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88447814061437710705143611 132671721092156566057715417)
      ·
        refine ⟨99503790819117424543286563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132671721092156566057715417 99503790819117424543286563)
        ·
          refine ⟨149255686228676136814929845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99503790819117424543286563 149255686228676136814929845)
          ·
            refine ⟨13992720583938387826399673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149255686228676136814929845 13992720583938387826399673)
            ·
              refine ⟨10494540437953790869799755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13992720583938387826399673 10494540437953790869799755)
              ·
                refine ⟨15741810656930686304699633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10494540437953790869799755 15741810656930686304699633)
                ·
                  refine ⟨11806357992698014728524725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15741810656930686304699633 11806357992698014728524725)
                  ·
                    refine ⟨1106846061815438880799193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11806357992698014728524725 1106846061815438880799193)
                    ·
                      rfl

theorem cell23_6466725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_6466725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466725 prefixEnd_6466725 := by exact prefixLift 6466725
  have htrace : WordTrace (prefixWord ++ tailWord_6466725) baseStart_6466725 baseEnd_6466725 := by
    simpa [prefixWord, tailWord_6466725, baseEnd_6466725] using wordTrace_append hprefix tailTrace_6466725
  have hstable : (prefixWord ++ tailWord_6466725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466725).length < 2 ^ (prefixWord ++ tailWord_6466725).sum := by decide
  have hdescent : baseEnd_6466725 < baseStart_6466725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466745 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 2, 1, 4]
def baseStart_6466745 : Nat := 118140960795 + 6466745 * 2 ^ 59
def prefixEnd_6466745 : Nat := 4983230072969 + 3 ^ 40 * 6466745 * 2
def baseEnd_6466745 : Nat := 3320548455059406564147487

theorem tailTrace_6466745 : CollatzResearch.WordTrace tailWord_6466745 prefixEnd_6466745 3320548455059406564147487 := by
  unfold tailWord_6466745
  simp only [CollatzResearch.WordTrace]
  refine ⟨235861566957094771962777689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157241044638063181308518459 235861566957094771962777689)
  ·
    refine ⟨176896175217821078972083267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235861566957094771962777689 176896175217821078972083267)
    ·
      refine ⟨265344262826731618458124901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176896175217821078972083267 265344262826731618458124901)
      ·
        refine ⟨49752049280012178460898419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265344262826731618458124901 49752049280012178460898419)
        ·
          refine ⟨74628073920018267691347629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49752049280012178460898419 74628073920018267691347629)
          ·
            refine ⟨27985527720006850384255361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74628073920018267691347629 27985527720006850384255361)
            ·
              refine ⟨20989145790005137788191521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27985527720006850384255361 20989145790005137788191521)
              ·
                refine ⟨15741859342503853341143641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20989145790005137788191521 15741859342503853341143641)
                ·
                  refine ⟨11806394506877890005857731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15741859342503853341143641 11806394506877890005857731)
                  ·
                    refine ⟨17709591760316835008786597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11806394506877890005857731 17709591760316835008786597)
                    ·
                      refine ⟨3320548455059406564147487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17709591760316835008786597 3320548455059406564147487)
                      ·
                        rfl

theorem cell23_6466745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_6466745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466745 prefixEnd_6466745 := by exact prefixLift 6466745
  have htrace : WordTrace (prefixWord ++ tailWord_6466745) baseStart_6466745 baseEnd_6466745 := by
    simpa [prefixWord, tailWord_6466745, baseEnd_6466745] using wordTrace_append hprefix tailTrace_6466745
  have hstable : (prefixWord ++ tailWord_6466745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466745).length < 2 ^ (prefixWord ++ tailWord_6466745).sum := by decide
  have hdescent : baseEnd_6466745 < baseStart_6466745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466762 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 2, 4, 2]
def baseStart_6466762 : Nat := 118140960795 + 6466762 * 2 ^ 59
def prefixEnd_6466762 : Nat := 4983230072969 + 3 ^ 40 * 6466762 * 2
def baseEnd_6466762 : Nat := 3320557184230532997634909

theorem tailTrace_6466762 : CollatzResearch.WordTrace tailWord_6466762 prefixEnd_6466762 3320557184230532997634909 := by
  unfold tailWord_6466762
  simp only [CollatzResearch.WordTrace]
  refine ⟨58965546749508295966536635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157241457998688789244097693 58965546749508295966536635)
  ·
    refine ⟨88448320124262443949804953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58965546749508295966536635 88448320124262443949804953)
    ·
      refine ⟨66336240093196832962353715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88448320124262443949804953 66336240093196832962353715)
      ·
        refine ⟨99504360139795249443530573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66336240093196832962353715 99504360139795249443530573)
        ·
          refine ⟨37314135052423218541323965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99504360139795249443530573 37314135052423218541323965)
          ·
            refine ⟨13992800644658706952996487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37314135052423218541323965 13992800644658706952996487)
            ·
              refine ⟨20989200966988060429494731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13992800644658706952996487 20989200966988060429494731)
              ·
                refine ⟨31483801450482090644242097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20989200966988060429494731 31483801450482090644242097)
                ·
                  refine ⟨23612851087861567983181573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31483801450482090644242097 23612851087861567983181573)
                  ·
                    refine ⟨4427409578974043996846545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23612851087861567983181573 4427409578974043996846545)
                    ·
                      refine ⟨3320557184230532997634909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427409578974043996846545 3320557184230532997634909)
                      ·
                        rfl

theorem cell23_6466762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_6466762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466762 prefixEnd_6466762 := by exact prefixLift 6466762
  have htrace : WordTrace (prefixWord ++ tailWord_6466762) baseStart_6466762 baseEnd_6466762 := by
    simpa [prefixWord, tailWord_6466762, baseEnd_6466762] using wordTrace_append hprefix tailTrace_6466762
  have hstable : (prefixWord ++ tailWord_6466762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466762).length < 2 ^ (prefixWord ++ tailWord_6466762).sum := by decide
  have hdescent : baseEnd_6466762 < baseStart_6466762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466852 : List Nat := [2, 3, 1, 3, 1, 1, 1, 5, 1, 1, 4]
def baseStart_6466852 : Nat := 118140960795 + 6466852 * 2 ^ 59
def prefixEnd_6466852 : Nat := 4983230072969 + 3 ^ 40 * 6466852 * 2
def baseEnd_6466852 : Nat := 3320603397489437645509495

theorem tailTrace_6466852 : CollatzResearch.WordTrace tailWord_6466852 prefixEnd_6466852 3320603397489437645509495 := by
  unfold tailWord_6466852
  simp only [CollatzResearch.WordTrace]
  refine ⟨117932734783853564618461405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157243646378471419491281873 117932734783853564618461405)
  ·
    refine ⟨44224775543945086731923027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117932734783853564618461405 44224775543945086731923027)
    ·
      refine ⟨66337163315917630097884541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44224775543945086731923027 66337163315917630097884541)
      ·
        refine ⟨24876436243469111286706703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66337163315917630097884541 24876436243469111286706703)
        ·
          refine ⟨37314654365203666930060055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24876436243469111286706703 37314654365203666930060055)
          ·
            refine ⟨55971981547805500395090083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37314654365203666930060055 55971981547805500395090083)
            ·
              refine ⟨83957972321708250592635125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55971981547805500395090083 83957972321708250592635125)
              ·
                refine ⟨7871059905160148493059543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83957972321708250592635125 7871059905160148493059543)
                ·
                  refine ⟨11806589857740222739589315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7871059905160148493059543 11806589857740222739589315)
                  ·
                    refine ⟨17709884786610334109383973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11806589857740222739589315 17709884786610334109383973)
                    ·
                      refine ⟨3320603397489437645509495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17709884786610334109383973 3320603397489437645509495)
                      ·
                        rfl

theorem cell23_6466852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_6466852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466852 prefixEnd_6466852 := by exact prefixLift 6466852
  have htrace : WordTrace (prefixWord ++ tailWord_6466852) baseStart_6466852 baseEnd_6466852 := by
    simpa [prefixWord, tailWord_6466852, baseEnd_6466852] using wordTrace_append hprefix tailTrace_6466852
  have hstable : (prefixWord ++ tailWord_6466852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466852).length < 2 ^ (prefixWord ++ tailWord_6466852).sum := by decide
  have hdescent : baseEnd_6466852 < baseStart_6466852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466865 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_6466865 : Nat := 118140960795 + 6466865 * 2 ^ 59
def prefixEnd_6466865 : Nat := 4983230072969 + 3 ^ 40 * 6466865 * 2
def baseEnd_6466865 : Nat := 3320610072737946094646935

theorem tailTrace_6466865 : CollatzResearch.WordTrace tailWord_6466865 prefixEnd_6466865 3320610072737946094646935 := by
  unfold tailWord_6466865
  simp only [CollatzResearch.WordTrace]
  refine ⟨235865943716660032457146049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157243962477773354971430699 235865943716660032457146049)
  ·
    refine ⟨176899457787495024342859537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235865943716660032457146049 176899457787495024342859537)
    ·
      refine ⟨132674593340621268257144653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176899457787495024342859537 132674593340621268257144653)
      ·
        refine ⟨49752972502732975596429245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132674593340621268257144653 49752972502732975596429245)
        ·
          refine ⟨18657364688524865848660967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49752972502732975596429245 18657364688524865848660967)
          ·
            refine ⟨27986047032787298772991451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18657364688524865848660967 27986047032787298772991451)
            ·
              refine ⟨41979070549180948159487177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27986047032787298772991451 41979070549180948159487177)
              ·
                refine ⟨31484302911885711119615383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41979070549180948159487177 31484302911885711119615383)
                ·
                  refine ⟨47226454367828566679423075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31484302911885711119615383 47226454367828566679423075)
                  ·
                    refine ⟨70839681551742850019134613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47226454367828566679423075 70839681551742850019134613)
                    ·
                      refine ⟨3320610072737946094646935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70839681551742850019134613 3320610072737946094646935)
                      ·
                        rfl

theorem cell23_6466865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_6466865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466865 prefixEnd_6466865 := by exact prefixLift 6466865
  have htrace : WordTrace (prefixWord ++ tailWord_6466865) baseStart_6466865 baseEnd_6466865 := by
    simpa [prefixWord, tailWord_6466865, baseEnd_6466865] using wordTrace_append hprefix tailTrace_6466865
  have hstable : (prefixWord ++ tailWord_6466865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466865).length < 2 ^ (prefixWord ++ tailWord_6466865).sum := by decide
  have hdescent : baseEnd_6466865 < baseStart_6466865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466879 : List Nat := [1, 1, 2, 2, 4, 2, 4, 1, 2, 4]
def baseStart_6466879 : Nat := 118140960795 + 6466879 * 2 ^ 59
def prefixEnd_6466879 : Nat := 4983230072969 + 3 ^ 40 * 6466879 * 2
def baseEnd_6466879 : Nat := 1106872420489036346623957

theorem tailTrace_6466879 : CollatzResearch.WordTrace tailWord_6466879 prefixEnd_6466879 1106872420489036346623957 := by
  unfold tailWord_6466879
  simp only [CollatzResearch.WordTrace]
  refine ⟨235866454338609312848155691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157244302892406208565437127 235866454338609312848155691)
  ·
    refine ⟨353799681507913969272233537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235866454338609312848155691 353799681507913969272233537)
    ·
      refine ⟨265349761130935476954175153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353799681507913969272233537 265349761130935476954175153)
      ·
        refine ⟨199012320848201607715631365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265349761130935476954175153 199012320848201607715631365)
        ·
          refine ⟨37314810159037801446680881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199012320848201607715631365 37314810159037801446680881)
          ·
            refine ⟨27986107619278351085010661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37314810159037801446680881 27986107619278351085010661)
            ·
              refine ⟨5247395178614690828439499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27986107619278351085010661 5247395178614690828439499)
              ·
                refine ⟨7871092767922036242659249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5247395178614690828439499 7871092767922036242659249)
                ·
                  refine ⟨5903319575941527181994437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7871092767922036242659249 5903319575941527181994437)
                  ·
                    refine ⟨1106872420489036346623957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5903319575941527181994437 1106872420489036346623957)
                    ·
                      rfl

theorem cell23_6466879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 2, 4].length) (baseStart_6466879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466879 prefixEnd_6466879 := by exact prefixLift 6466879
  have htrace : WordTrace (prefixWord ++ tailWord_6466879) baseStart_6466879 baseEnd_6466879 := by
    simpa [prefixWord, tailWord_6466879, baseEnd_6466879] using wordTrace_append hprefix tailTrace_6466879
  have hstable : (prefixWord ++ tailWord_6466879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466879).length < 2 ^ (prefixWord ++ tailWord_6466879).sum := by decide
  have hdescent : baseEnd_6466879 < baseStart_6466879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466885 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 5, 3, 3]
def baseStart_6466885 : Nat := 118140960795 + 6466885 * 2 ^ 59
def prefixEnd_6466885 : Nat := 4983230072969 + 3 ^ 40 * 6466885 * 2
def baseEnd_6466885 : Nat := 3320620342351036016396843

theorem tailTrace_6466885 : CollatzResearch.WordTrace tailWord_6466885 prefixEnd_6466885 3320620342351036016396843 := by
  unfold tailWord_6466885
  simp only [CollatzResearch.WordTrace]
  refine ⟨235866673176587575872874109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157244448784391717248582739 235866673176587575872874109)
  ·
    refine ⟨88450002441220340952327791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235866673176587575872874109 88450002441220340952327791)
    ·
      refine ⟨132675003661830511428491687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88450002441220340952327791 132675003661830511428491687)
      ·
        refine ⟨199012505492745767142737531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132675003661830511428491687 199012505492745767142737531)
        ·
          refine ⟨298518758239118650714106297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199012505492745767142737531 298518758239118650714106297)
          ·
            refine ⟨223889068679338988035579723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298518758239118650714106297 223889068679338988035579723)
            ·
              refine ⟨335833603019008482053369585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223889068679338988035579723 335833603019008482053369585)
              ·
                refine ⟨251875202264256361540027189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335833603019008482053369585 251875202264256361540027189)
                ·
                  refine ⟨23613300212274033894377549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 251875202264256361540027189 23613300212274033894377549)
                  ·
                    refine ⟨8854987579602762710391581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23613300212274033894377549 8854987579602762710391581)
                    ·
                      refine ⟨3320620342351036016396843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8854987579602762710391581 3320620342351036016396843)
                      ·
                        rfl

theorem cell23_6466885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_6466885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466885 prefixEnd_6466885 := by exact prefixLift 6466885
  have htrace : WordTrace (prefixWord ++ tailWord_6466885) baseStart_6466885 baseEnd_6466885 := by
    simpa [prefixWord, tailWord_6466885, baseEnd_6466885] using wordTrace_append hprefix tailTrace_6466885
  have hstable : (prefixWord ++ tailWord_6466885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466885).length < 2 ^ (prefixWord ++ tailWord_6466885).sum := by decide
  have hdescent : baseEnd_6466885 < baseStart_6466885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466909 : List Nat := [1, 4, 5, 1, 1, 11]
def baseStart_6466909 : Nat := 118140960795 + 6466909 * 2 ^ 59
def prefixEnd_6466909 : Nat := 4983230072969 + 3 ^ 40 * 6466909 * 2
def baseEnd_6466909 : Nat := 13665155003649151944431

theorem tailTrace_6466909 : CollatzResearch.WordTrace tailWord_6466909 prefixEnd_6466909 13665155003649151944431 := by
  unfold tailWord_6466909
  simp only [CollatzResearch.WordTrace]
  refine ⟨235867548528500627971747781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157245032352333751981165187 235867548528500627971747781)
  ·
    refine ⟨44225165349093867744702709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235867548528500627971747781 44225165349093867744702709)
    ·
      refine ⟨4146109251477550101065879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44225165349093867744702709 4146109251477550101065879)
      ·
        refine ⟨6219163877216325151598819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4146109251477550101065879 6219163877216325151598819)
        ·
          refine ⟨9328745815824487727398229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6219163877216325151598819 9328745815824487727398229)
          ·
            refine ⟨13665155003649151944431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9328745815824487727398229 13665155003649151944431)
            ·
              rfl

theorem cell23_6466909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 11].length) (baseStart_6466909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466909 prefixEnd_6466909 := by exact prefixLift 6466909
  have htrace : WordTrace (prefixWord ++ tailWord_6466909) baseStart_6466909 baseEnd_6466909 := by
    simpa [prefixWord, tailWord_6466909, baseEnd_6466909] using wordTrace_append hprefix tailTrace_6466909
  have hstable : (prefixWord ++ tailWord_6466909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466909).length < 2 ^ (prefixWord ++ tailWord_6466909).sum := by decide
  have hdescent : baseEnd_6466909 < baseStart_6466909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466926 : List Nat := [4, 1, 2, 4, 2, 1, 1, 8]
def baseStart_6466926 : Nat := 118140960795 + 6466926 * 2 ^ 59
def prefixEnd_6466926 : Nat := 4983230072969 + 3 ^ 40 * 6466926 * 2
def baseEnd_6466926 : Nat := 122986718335476679851265

theorem tailTrace_6466926 : CollatzResearch.WordTrace tailWord_6466926 prefixEnd_6466926 122986718335476679851265 := by
  unfold tailWord_6466926
  simp only [CollatzResearch.WordTrace]
  refine ⟨29483521071179879984389579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157245445712959359916744421 29483521071179879984389579)
  ·
    refine ⟨44225281606769819976584369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29483521071179879984389579 44225281606769819976584369)
    ·
      refine ⟨33168961205077364982438277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44225281606769819976584369 33168961205077364982438277)
      ·
        refine ⟨6219180225952005934207177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33168961205077364982438277 6219180225952005934207177)
        ·
          refine ⟨4664385169464004450655383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6219180225952005934207177 4664385169464004450655383)
          ·
            refine ⟨6996577754196006675983075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4664385169464004450655383 6996577754196006675983075)
            ·
              refine ⟨10494866631294010013974613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6996577754196006675983075 10494866631294010013974613)
              ·
                refine ⟨122986718335476679851265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10494866631294010013974613 122986718335476679851265)
                ·
                  rfl

theorem cell23_6466926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_6466926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466926 prefixEnd_6466926 := by exact prefixLift 6466926
  have htrace : WordTrace (prefixWord ++ tailWord_6466926) baseStart_6466926 baseEnd_6466926 := by
    simpa [prefixWord, tailWord_6466926, baseEnd_6466926] using wordTrace_append hprefix tailTrace_6466926
  have hstable : (prefixWord ++ tailWord_6466926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466926).length < 2 ^ (prefixWord ++ tailWord_6466926).sum := by decide
  have hdescent : baseEnd_6466926 < baseStart_6466926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466935 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 2, 6]
def baseStart_6466935 : Nat := 118140960795 + 6466935 * 2 ^ 59
def prefixEnd_6466935 : Nat := 4983230072969 + 3 ^ 40 * 6466935 * 2
def baseEnd_6466935 : Nat := 1106882005461253606923871

theorem tailTrace_6466935 : CollatzResearch.WordTrace tailWord_6466935 prefixEnd_6466935 1106882005461253606923871 := by
  unfold tailWord_6466935
  simp only [CollatzResearch.WordTrace]
  refine ⟨235868496826406434412194259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157245664550937622941462839 235868496826406434412194259)
  ·
    refine ⟨353802745239609651618291389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235868496826406434412194259 353802745239609651618291389)
    ·
      refine ⟨132676029464853619356859271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353802745239609651618291389 132676029464853619356859271)
      ·
        refine ⟨199014044197280429035288907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132676029464853619356859271 199014044197280429035288907)
        ·
          refine ⟨298521066295920643552933361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199014044197280429035288907 298521066295920643552933361)
          ·
            refine ⟨223890799721940482664700021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298521066295920643552933361 223890799721940482664700021)
            ·
              refine ⟨20989762473931920249815627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 223890799721940482664700021 20989762473931920249815627)
              ·
                refine ⟨31484643710897880374723441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20989762473931920249815627 31484643710897880374723441)
                ·
                  refine ⟨23613482783173410281042581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31484643710897880374723441 23613482783173410281042581)
                  ·
                    refine ⟨1106882005461253606923871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23613482783173410281042581 1106882005461253606923871)
                    ·
                      rfl

theorem cell23_6466935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_6466935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466935 prefixEnd_6466935 := by exact prefixLift 6466935
  have htrace : WordTrace (prefixWord ++ tailWord_6466935) baseStart_6466935 baseEnd_6466935 := by
    simpa [prefixWord, tailWord_6466935, baseEnd_6466935] using wordTrace_append hprefix tailTrace_6466935
  have hstable : (prefixWord ++ tailWord_6466935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466935).length < 2 ^ (prefixWord ++ tailWord_6466935).sum := by decide
  have hdescent : baseEnd_6466935 < baseStart_6466935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466955 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 4]
def baseStart_6466955 : Nat := 118140960795 + 6466955 * 2 ^ 59
def prefixEnd_6466955 : Nat := 4983230072969 + 3 ^ 40 * 6466955 * 2
def baseEnd_6466955 : Nat := 3320656285996850742521521

theorem tailTrace_6466955 : CollatzResearch.WordTrace tailWord_6466955 prefixEnd_6466955 3320656285996850742521521 := by
  unfold tailWord_6466955
  simp only [CollatzResearch.WordTrace]
  refine ⟨235869226286333977827922319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157246150857555985218614879 235869226286333977827922319)
  ·
    refine ⟨353803839429500966741883479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235869226286333977827922319 353803839429500966741883479)
    ·
      refine ⟨530705759144251450112825219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353803839429500966741883479 530705759144251450112825219)
      ·
        refine ⟨796058638716377175169237829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530705759144251450112825219 796058638716377175169237829)
        ·
          refine ⟨149260994759320720344232093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 796058638716377175169237829 149260994759320720344232093)
          ·
            refine ⟨55972873034745270129087035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149260994759320720344232093 55972873034745270129087035)
            ·
              refine ⟨83959309552117905193630553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55972873034745270129087035 83959309552117905193630553)
              ·
                refine ⟨62969482164088428895222915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83959309552117905193630553 62969482164088428895222915)
                ·
                  refine ⟨94454223246132643342834373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62969482164088428895222915 94454223246132643342834373)
                  ·
                    refine ⟨17710166858649870626781445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94454223246132643342834373 17710166858649870626781445)
                    ·
                      refine ⟨3320656285996850742521521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17710166858649870626781445 3320656285996850742521521)
                      ·
                        rfl

theorem cell23_6466955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 4].length) (baseStart_6466955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466955 prefixEnd_6466955 := by exact prefixLift 6466955
  have htrace : WordTrace (prefixWord ++ tailWord_6466955) baseStart_6466955 baseEnd_6466955 := by
    simpa [prefixWord, tailWord_6466955, baseEnd_6466955] using wordTrace_append hprefix tailTrace_6466955
  have hstable : (prefixWord ++ tailWord_6466955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466955).length < 2 ^ (prefixWord ++ tailWord_6466955).sum := by decide
  have hdescent : baseEnd_6466955 < baseStart_6466955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466989 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_6466989 : Nat := 118140960795 + 6466989 * 2 ^ 59
def prefixEnd_6466989 : Nat := 4983230072969 + 3 ^ 40 * 6466989 * 2
def baseEnd_6466989 : Nat := 3320673744339103609496365

theorem tailTrace_6466989 : CollatzResearch.WordTrace tailWord_6466989 prefixEnd_6466989 3320673744339103609496365 := by
  unfold tailWord_6466989
  simp only [CollatzResearch.WordTrace]
  refine ⟨235870466368210801634660021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157246977578807201089773347 235870466368210801634660021)
  ·
    refine ⟨22112856222019762653249377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235870466368210801634660021 22112856222019762653249377)
    ·
      refine ⟨16584642166514821989937033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22112856222019762653249377 16584642166514821989937033)
      ·
        refine ⟨12438481624886116492452775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16584642166514821989937033 12438481624886116492452775)
        ·
          refine ⟨18657722437329174738679163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12438481624886116492452775 18657722437329174738679163)
          ·
            refine ⟨27986583655993762108018745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18657722437329174738679163 27986583655993762108018745)
            ·
              refine ⟨20989937741995321581014059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27986583655993762108018745 20989937741995321581014059)
              ·
                refine ⟨31484906612992982371521089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20989937741995321581014059 31484906612992982371521089)
                ·
                  refine ⟨23613679959744736778640817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31484906612992982371521089 23613679959744736778640817)
                  ·
                    refine ⟨17710259969808552583980613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23613679959744736778640817 17710259969808552583980613)
                    ·
                      refine ⟨3320673744339103609496365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17710259969808552583980613 3320673744339103609496365)
                      ·
                        rfl

theorem cell23_6466989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_6466989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466989 prefixEnd_6466989 := by exact prefixLift 6466989
  have htrace : WordTrace (prefixWord ++ tailWord_6466989) baseStart_6466989 baseEnd_6466989 := by
    simpa [prefixWord, tailWord_6466989, baseEnd_6466989] using wordTrace_append hprefix tailTrace_6466989
  have hstable : (prefixWord ++ tailWord_6466989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466989).length < 2 ^ (prefixWord ++ tailWord_6466989).sum := by decide
  have hdescent : baseEnd_6466989 < baseStart_6466989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6466993 : List Nat := [1, 2, 2, 4, 1, 1, 5, 1, 2, 2, 2]
def baseStart_6466993 : Nat := 118140960795 + 6466993 * 2 ^ 59
def prefixEnd_6466993 : Nat := 4983230072969 + 3 ^ 40 * 6466993 * 2
def baseEnd_6466993 : Nat := 3320675798261721593846347

theorem tailTrace_6466993 : CollatzResearch.WordTrace tailWord_6466993 prefixEnd_6466993 3320675798261721593846347 := by
  unfold tailWord_6466993
  simp only [CollatzResearch.WordTrace]
  refine ⟨235870612260196310317805633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157247074840130873545203755 235870612260196310317805633)
  ·
    refine ⟨176902959195147232738354225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235870612260196310317805633 176902959195147232738354225)
    ·
      refine ⟨132677219396360424553765669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176902959195147232738354225 132677219396360424553765669)
      ·
        refine ⟨24876978636817579603831063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132677219396360424553765669 24876978636817579603831063)
        ·
          refine ⟨37315467955226369405746595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24876978636817579603831063 37315467955226369405746595)
          ·
            refine ⟨55973201932839554108619893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37315467955226369405746595 55973201932839554108619893)
            ·
              refine ⟨5247487681203708197683115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55973201932839554108619893 5247487681203708197683115)
              ·
                refine ⟨7871231521805562296524673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5247487681203708197683115 7871231521805562296524673)
                ·
                  refine ⟨5903423641354171722393505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7871231521805562296524673 5903423641354171722393505)
                  ·
                    refine ⟨4427567731015628791795129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5903423641354171722393505 4427567731015628791795129)
                    ·
                      refine ⟨3320675798261721593846347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427567731015628791795129 3320675798261721593846347)
                      ·
                        rfl

theorem cell23_6466993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_6466993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6466993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6466993 prefixEnd_6466993 := by exact prefixLift 6466993
  have htrace : WordTrace (prefixWord ++ tailWord_6466993) baseStart_6466993 baseEnd_6466993 := by
    simpa [prefixWord, tailWord_6466993, baseEnd_6466993] using wordTrace_append hprefix tailTrace_6466993
  have hstable : (prefixWord ++ tailWord_6466993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6466993).length < 2 ^ (prefixWord ++ tailWord_6466993).sum := by decide
  have hdescent : baseEnd_6466993 < baseStart_6466993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6466993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467032 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 4, 1, 4]
def baseStart_6467032 : Nat := 118140960795 + 6467032 * 2 ^ 59
def prefixEnd_6467032 : Nat := 4983230072969 + 3 ^ 40 * 6467032 * 2
def baseEnd_6467032 : Nat := 3320695824007246941258667

theorem tailTrace_6467032 : CollatzResearch.WordTrace tailWord_6467032 prefixEnd_6467032 3320695824007246941258667 := by
  unfold tailWord_6467032
  simp only [CollatzResearch.WordTrace]
  refine ⟨117936017353527509989237675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157248023138036679985650233 117936017353527509989237675)
  ·
    refine ⟨176904026030291264983856513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117936017353527509989237675 176904026030291264983856513)
    ·
      refine ⟨132678019522718448737892385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176904026030291264983856513 132678019522718448737892385)
      ·
        refine ⟨99508514642038836553419289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132678019522718448737892385 99508514642038836553419289)
        ·
          refine ⟨74631385981529127415064467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99508514642038836553419289 74631385981529127415064467)
          ·
            refine ⟨111947078972293691122596701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74631385981529127415064467 111947078972293691122596701)
            ·
              refine ⟨41980154614610134170973763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111947078972293691122596701 41980154614610134170973763)
              ·
                refine ⟨62970231921915201256460645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41980154614610134170973763 62970231921915201256460645)
                ·
                  refine ⟨11806918485359100235586371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62970231921915201256460645 11806918485359100235586371)
                  ·
                    refine ⟨17710377728038650353379557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11806918485359100235586371 17710377728038650353379557)
                    ·
                      refine ⟨3320695824007246941258667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17710377728038650353379557 3320695824007246941258667)
                      ·
                        rfl

theorem cell23_6467032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_6467032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467032 prefixEnd_6467032 := by exact prefixLift 6467032
  have htrace : WordTrace (prefixWord ++ tailWord_6467032) baseStart_6467032 baseEnd_6467032 := by
    simpa [prefixWord, tailWord_6467032, baseEnd_6467032] using wordTrace_append hprefix tailTrace_6467032
  have hstable : (prefixWord ++ tailWord_6467032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467032).length < 2 ^ (prefixWord ++ tailWord_6467032).sum := by decide
  have hdescent : baseEnd_6467032 < baseStart_6467032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467035 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 5]
def baseStart_6467035 : Nat := 118140960795 + 6467035 * 2 ^ 59
def prefixEnd_6467035 : Nat := 4983230072969 + 3 ^ 40 * 6467035 * 2
def baseEnd_6467035 : Nat := 3320697364449210429521153

theorem tailTrace_6467035 : CollatzResearch.WordTrace tailWord_6467035 prefixEnd_6467035 3320697364449210429521153 := by
  unfold tailWord_6467035
  simp only [CollatzResearch.WordTrace]
  refine ⟨235872144126044151490834559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157248096084029434327223039 235872144126044151490834559)
  ·
    refine ⟨353808216189066227236251839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235872144126044151490834559 353808216189066227236251839)
    ·
      refine ⟨530712324283599340854377759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353808216189066227236251839 530712324283599340854377759)
      ·
        refine ⟨796068486425399011281566639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530712324283599340854377759 796068486425399011281566639)
        ·
          refine ⟨1194102729638098516922349959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796068486425399011281566639 1194102729638098516922349959)
          ·
            refine ⟨1791154094457147775383524939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194102729638098516922349959 1791154094457147775383524939)
            ·
              refine ⟨2686731141685721663075287409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791154094457147775383524939 2686731141685721663075287409)
              ·
                refine ⟨2015048356264291247306465557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2686731141685721663075287409 2015048356264291247306465557)
                ·
                  refine ⟨94455391699888652217490573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2015048356264291247306465557 94455391699888652217490573)
                  ·
                    refine ⟨35420771887458244581558965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94455391699888652217490573 35420771887458244581558965)
                    ·
                      refine ⟨3320697364449210429521153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35420771887458244581558965 3320697364449210429521153)
                      ·
                        rfl

theorem cell23_6467035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 5].length) (baseStart_6467035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467035 prefixEnd_6467035 := by exact prefixLift 6467035
  have htrace : WordTrace (prefixWord ++ tailWord_6467035) baseStart_6467035 baseEnd_6467035 := by
    simpa [prefixWord, tailWord_6467035, baseEnd_6467035] using wordTrace_append hprefix tailTrace_6467035
  have hstable : (prefixWord ++ tailWord_6467035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467035).length < 2 ^ (prefixWord ++ tailWord_6467035).sum := by decide
  have hdescent : baseEnd_6467035 < baseStart_6467035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467052 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 3]
def baseStart_6467052 : Nat := 118140960795 + 6467052 * 2 ^ 59
def prefixEnd_6467052 : Nat := 4983230072969 + 3 ^ 40 * 6467052 * 2
def baseEnd_6467052 : Nat := 3320706093620336863008575

theorem tailTrace_6467052 : CollatzResearch.WordTrace tailWord_6467052 prefixEnd_6467052 3320706093620336863008575 := by
  unfold tailWord_6467052
  simp only [CollatzResearch.WordTrace]
  refine ⟨117936382083491281697101705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157248509444655042262802273 117936382083491281697101705)
  ·
    refine ⟨88452286562618461272826279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117936382083491281697101705 88452286562618461272826279)
    ·
      refine ⟨132678429843927691909239419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88452286562618461272826279 132678429843927691909239419)
      ·
        refine ⟨199017644765891537863859129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132678429843927691909239419 199017644765891537863859129)
        ·
          refine ⟨149263233574418653397894347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199017644765891537863859129 149263233574418653397894347)
          ·
            refine ⟨223894850361627980096841521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149263233574418653397894347 223894850361627980096841521)
            ·
              refine ⟨167921137771220985072631141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223894850361627980096841521 167921137771220985072631141)
              ·
                refine ⟨31485213332103934701118339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167921137771220985072631141 31485213332103934701118339)
                ·
                  refine ⟨47227819998155902051677509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31485213332103934701118339 47227819998155902051677509)
                  ·
                    refine ⟨8855216249654231634689533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47227819998155902051677509 8855216249654231634689533)
                    ·
                      refine ⟨3320706093620336863008575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8855216249654231634689533 3320706093620336863008575)
                      ·
                        rfl

theorem cell23_6467052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_6467052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467052 prefixEnd_6467052 := by exact prefixLift 6467052
  have htrace : WordTrace (prefixWord ++ tailWord_6467052) baseStart_6467052 baseEnd_6467052 := by
    simpa [prefixWord, tailWord_6467052, baseEnd_6467052] using wordTrace_append hprefix tailTrace_6467052
  have hstable : (prefixWord ++ tailWord_6467052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467052).length < 2 ^ (prefixWord ++ tailWord_6467052).sum := by decide
  have hdescent : baseEnd_6467052 < baseStart_6467052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467069 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_6467069 : Nat := 118140960795 + 6467069 * 2 ^ 59
def prefixEnd_6467069 : Nat := 4983230072969 + 3 ^ 40 * 6467069 * 2
def baseEnd_6467069 : Nat := 3320714822791463296495997

theorem tailTrace_6467069 : CollatzResearch.WordTrace tailWord_6467069 prefixEnd_6467069 3320714822791463296495997 := by
  unfold tailWord_6467069
  simp only [CollatzResearch.WordTrace]
  refine ⟨235873384207920975297572261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157248922805280650198381507 235873384207920975297572261)
  ·
    refine ⟨44226259538985182868294799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235873384207920975297572261 44226259538985182868294799)
    ·
      refine ⟨66339389308477774302442199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44226259538985182868294799 66339389308477774302442199)
      ·
        refine ⟨99509083962716661453663299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66339389308477774302442199 99509083962716661453663299)
        ·
          refine ⟨149263625944074992180494949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99509083962716661453663299 149263625944074992180494949)
          ·
            refine ⟨27986929864514061033842803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149263625944074992180494949 27986929864514061033842803)
            ·
              refine ⟨41980394796771091550764205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27986929864514061033842803 41980394796771091550764205)
              ·
                refine ⟨15742648048789159331536577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41980394796771091550764205 15742648048789159331536577)
                ·
                  refine ⟨11806986036591869498652433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15742648048789159331536577 11806986036591869498652433)
                  ·
                    refine ⟨8855239527443902123989325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11806986036591869498652433 8855239527443902123989325)
                    ·
                      refine ⟨3320714822791463296495997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8855239527443902123989325 3320714822791463296495997)
                      ·
                        rfl

theorem cell23_6467069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_6467069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467069 prefixEnd_6467069 := by exact prefixLift 6467069
  have htrace : WordTrace (prefixWord ++ tailWord_6467069) baseStart_6467069 baseEnd_6467069 := by
    simpa [prefixWord, tailWord_6467069, baseEnd_6467069] using wordTrace_append hprefix tailTrace_6467069
  have hstable : (prefixWord ++ tailWord_6467069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467069).length < 2 ^ (prefixWord ++ tailWord_6467069).sum := by decide
  have hdescent : baseEnd_6467069 < baseStart_6467069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467093 : List Nat := [1, 3, 2, 1, 3, 2, 4, 2, 1, 4]
def baseStart_6467093 : Nat := 118140960795 + 6467093 * 2 ^ 59
def prefixEnd_6467093 : Nat := 4983230072969 + 3 ^ 40 * 6467093 * 2
def baseEnd_6467093 : Nat := 1106909048775723734198629

theorem tailTrace_6467093 : CollatzResearch.WordTrace tailWord_6467093 prefixEnd_6467093 1106909048775723734198629 := by
  unfold tailWord_6467093
  simp only [CollatzResearch.WordTrace]
  refine ⟨235874259559834027396445933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157249506373222684930963955 235874259559834027396445933)
  ·
    refine ⟨88452847334937760273667225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235874259559834027396445933 88452847334937760273667225)
    ·
      refine ⟨66339635501203320205250419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88452847334937760273667225 66339635501203320205250419)
      ·
        refine ⟨99509453251804980307875629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66339635501203320205250419 99509453251804980307875629)
        ·
          refine ⟨37316044969426867615453361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99509453251804980307875629 37316044969426867615453361)
          ·
            refine ⟨27987033727070150711590021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37316044969426867615453361 27987033727070150711590021)
            ·
              refine ⟨5247568823825653258423129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27987033727070150711590021 5247568823825653258423129)
              ·
                refine ⟨3935676617869239943817347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5247568823825653258423129 3935676617869239943817347)
                ·
                  refine ⟨5903514926803859915726021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3935676617869239943817347 5903514926803859915726021)
                  ·
                    refine ⟨1106909048775723734198629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5903514926803859915726021 1106909048775723734198629)
                    ·
                      rfl

theorem cell23_6467093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_6467093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467093 prefixEnd_6467093 := by exact prefixLift 6467093
  have htrace : WordTrace (prefixWord ++ tailWord_6467093) baseStart_6467093 baseEnd_6467093 := by
    simpa [prefixWord, tailWord_6467093, baseEnd_6467093] using wordTrace_append hprefix tailTrace_6467093
  have hstable : (prefixWord ++ tailWord_6467093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467093).length < 2 ^ (prefixWord ++ tailWord_6467093).sum := by decide
  have hdescent : baseEnd_6467093 < baseStart_6467093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467109 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 1, 5, 2]
def baseStart_6467109 : Nat := 118140960795 + 6467109 * 2 ^ 59
def prefixEnd_6467109 : Nat := 4983230072969 + 3 ^ 40 * 6467109 * 2
def baseEnd_6467109 : Nat := 3320735362017643139995813

theorem tailTrace_6467109 : CollatzResearch.WordTrace tailWord_6467109 prefixEnd_6467109 3320735362017643139995813 := by
  unfold tailWord_6467109
  simp only [CollatzResearch.WordTrace]
  refine ⟨235874843127776062129028381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157249895418517374752685587 235874843127776062129028381)
  ·
    refine ⟨88453066172916023298385643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235874843127776062129028381 88453066172916023298385643)
    ·
      refine ⟨132679599259374034947578465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88453066172916023298385643 132679599259374034947578465)
      ·
        refine ⟨99509699444530526210683849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132679599259374034947578465 99509699444530526210683849)
        ·
          refine ⟨74632274583397894658012887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99509699444530526210683849 74632274583397894658012887)
          ·
            refine ⟨111948411875096841987019331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74632274583397894658012887 111948411875096841987019331)
            ·
              refine ⟨167922617812645262980528997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111948411875096841987019331 167922617812645262980528997)
              ·
                refine ⟨31485490839870986808849187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167922617812645262980528997 31485490839870986808849187)
                ·
                  refine ⟨47228236259806480213273781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31485490839870986808849187 47228236259806480213273781)
                  ·
                    refine ⟨4427647149356857519994417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47228236259806480213273781 4427647149356857519994417)
                    ·
                      refine ⟨3320735362017643139995813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427647149356857519994417 3320735362017643139995813)
                      ·
                        rfl

theorem cell23_6467109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_6467109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467109 prefixEnd_6467109 := by exact prefixLift 6467109
  have htrace : WordTrace (prefixWord ++ tailWord_6467109) baseStart_6467109 baseEnd_6467109 := by
    simpa [prefixWord, tailWord_6467109, baseEnd_6467109] using wordTrace_append hprefix tailTrace_6467109
  have hstable : (prefixWord ++ tailWord_6467109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467109).length < 2 ^ (prefixWord ++ tailWord_6467109).sum := by decide
  have hdescent : baseEnd_6467109 < baseStart_6467109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467152 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 6]
def baseStart_6467152 : Nat := 118140960795 + 6467152 * 2 ^ 59
def prefixEnd_6467152 : Nat := 4983230072969 + 3 ^ 40 * 6467152 * 2
def baseEnd_6467152 : Nat := 3320757441685786471758115

theorem tailTrace_6467152 : CollatzResearch.WordTrace tailWord_6467152 prefixEnd_6467152 3320757441685786471758115 := by
  unfold tailWord_6467152
  simp only [CollatzResearch.WordTrace]
  refine ⟨117938205733310140236421855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157250940977746853648562473 117938205733310140236421855)
  ·
    refine ⟨176907308599965210354632783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117938205733310140236421855 176907308599965210354632783)
    ·
      refine ⟨265360962899947815531949175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176907308599965210354632783 265360962899947815531949175)
      ·
        refine ⟨398041444349921723297923763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265360962899947815531949175 398041444349921723297923763)
        ·
          refine ⟨597062166524882584946885645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398041444349921723297923763 597062166524882584946885645)
          ·
            refine ⟨223898312446830969355082117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 597062166524882584946885645 223898312446830969355082117)
            ·
              refine ⟨41980933583780806754077897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223898312446830969355082117 41980933583780806754077897)
              ·
                refine ⟨31485700187835605065558423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41980933583780806754077897 31485700187835605065558423)
                ·
                  refine ⟨47228550281753407598337635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31485700187835605065558423 47228550281753407598337635)
                  ·
                    refine ⟨70842825422630111397506453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47228550281753407598337635 70842825422630111397506453)
                    ·
                      refine ⟨3320757441685786471758115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70842825422630111397506453 3320757441685786471758115)
                      ·
                        rfl

theorem cell23_6467152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_6467152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467152 prefixEnd_6467152 := by exact prefixLift 6467152
  have htrace : WordTrace (prefixWord ++ tailWord_6467152) baseStart_6467152 baseEnd_6467152 := by
    simpa [prefixWord, tailWord_6467152, baseEnd_6467152] using wordTrace_append hprefix tailTrace_6467152
  have hstable : (prefixWord ++ tailWord_6467152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467152).length < 2 ^ (prefixWord ++ tailWord_6467152).sum := by decide
  have hdescent : baseEnd_6467152 < baseStart_6467152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467159 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 5]
def baseStart_6467159 : Nat := 118140960795 + 6467159 * 2 ^ 59
def prefixEnd_6467159 : Nat := 4983230072969 + 3 ^ 40 * 6467159 * 2
def baseEnd_6467159 : Nat := 3320761036050367944370583

theorem tailTrace_6467159 : CollatzResearch.WordTrace tailWord_6467159 prefixEnd_6467159 3320761036050367944370583 := by
  unfold tailWord_6467159
  simp only [CollatzResearch.WordTrace]
  refine ⟨235876666777594920668348531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157251111185063280445565687 235876666777594920668348531)
  ·
    refine ⟨353815000166392381002522797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235876666777594920668348531 353815000166392381002522797)
    ·
      refine ⟨132680625062397142875946049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353815000166392381002522797 132680625062397142875946049)
      ·
        refine ⟨99510468796797857156959537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132680625062397142875946049 99510468796797857156959537)
        ·
          refine ⟨74632851597598392867719653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99510468796797857156959537 74632851597598392867719653)
          ·
            refine ⟨13993659674549698662697435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74632851597598392867719653 13993659674549698662697435)
            ·
              refine ⟨20990489511824547994046153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13993659674549698662697435 20990489511824547994046153)
              ·
                refine ⟨15742867133868410995534615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20990489511824547994046153 15742867133868410995534615)
                ·
                  refine ⟨23614300700802616493301923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15742867133868410995534615 23614300700802616493301923)
                  ·
                    refine ⟨35421451051203924739952885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23614300700802616493301923 35421451051203924739952885)
                    ·
                      refine ⟨3320761036050367944370583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35421451051203924739952885 3320761036050367944370583)
                      ·
                        rfl

theorem cell23_6467159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_6467159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467159 prefixEnd_6467159 := by exact prefixLift 6467159
  have htrace : WordTrace (prefixWord ++ tailWord_6467159) baseStart_6467159 baseEnd_6467159 := by
    simpa [prefixWord, tailWord_6467159, baseEnd_6467159] using wordTrace_append hprefix tailTrace_6467159
  have hstable : (prefixWord ++ tailWord_6467159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467159).length < 2 ^ (prefixWord ++ tailWord_6467159).sum := by decide
  have hdescent : baseEnd_6467159 < baseStart_6467159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467173 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 3, 2, 2]
def baseStart_6467173 : Nat := 118140960795 + 6467173 * 2 ^ 59
def prefixEnd_6467173 : Nat := 4983230072969 + 3 ^ 40 * 6467173 * 2
def baseEnd_6467173 : Nat := 3320768224779530889595519

theorem tailTrace_6467173 : CollatzResearch.WordTrace tailWord_6467173 prefixEnd_6467173 3320768224779530889595519 := by
  unfold tailWord_6467173
  simp only [CollatzResearch.WordTrace]
  refine ⟨235877177399544201059358173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157251451599696134039572115 235877177399544201059358173)
  ·
    refine ⟨88453941524829075397259315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235877177399544201059358173 88453941524829075397259315)
    ·
      refine ⟨132680912287243613095888973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88453941524829075397259315 132680912287243613095888973)
      ·
        refine ⟨49755342107716354910958365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132680912287243613095888973 49755342107716354910958365)
        ·
          refine ⟨18658253290393633091609387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49755342107716354910958365 18658253290393633091609387)
          ·
            refine ⟨27987379935590449637414081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18658253290393633091609387 27987379935590449637414081)
            ·
              refine ⟨20990534951692837228060561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27987379935590449637414081 20990534951692837228060561)
              ·
                refine ⟨15742901213769627921045421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20990534951692837228060561 15742901213769627921045421)
                ·
                  refine ⟨5903587955163610470392033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15742901213769627921045421 5903587955163610470392033)
                  ·
                    refine ⟨4427690966372707852794025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5903587955163610470392033 4427690966372707852794025)
                    ·
                      refine ⟨3320768224779530889595519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427690966372707852794025 3320768224779530889595519)
                      ·
                        rfl

theorem cell23_6467173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_6467173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467173 prefixEnd_6467173 := by exact prefixLift 6467173
  have htrace : WordTrace (prefixWord ++ tailWord_6467173) baseStart_6467173 baseEnd_6467173 := by
    simpa [prefixWord, tailWord_6467173, baseEnd_6467173] using wordTrace_append hprefix tailTrace_6467173
  have hstable : (prefixWord ++ tailWord_6467173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467173).length < 2 ^ (prefixWord ++ tailWord_6467173).sum := by decide
  have hdescent : baseEnd_6467173 < baseStart_6467173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467199 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 1, 9, 2]
def baseStart_6467199 : Nat := 118140960795 + 6467199 * 2 ^ 59
def prefixEnd_6467199 : Nat := 4983230072969 + 3 ^ 40 * 6467199 * 2
def baseEnd_6467199 : Nat := 3320781575276547787870399

theorem tailTrace_6467199 : CollatzResearch.WordTrace tailWord_6467199 prefixEnd_6467199 3320781575276547787870399 := by
  unfold tailWord_6467199
  simp only [CollatzResearch.WordTrace]
  refine ⟨235878125697450007499804651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157252083798300004999869767 235878125697450007499804651)
  ·
    refine ⟨353817188546175011249706977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235878125697450007499804651 353817188546175011249706977)
    ·
      refine ⟨265362891409631258437280233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353817188546175011249706977 265362891409631258437280233)
      ·
        refine ⟨199022168557223443827960175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265362891409631258437280233 199022168557223443827960175)
        ·
          refine ⟨298533252835835165741940263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199022168557223443827960175 298533252835835165741940263)
          ·
            refine ⟨447799879253752748612910395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298533252835835165741940263 447799879253752748612910395)
            ·
              refine ⟨671699818880629122919365593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447799879253752748612910395 671699818880629122919365593)
              ·
                refine ⟨503774864160471842189524195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671699818880629122919365593 503774864160471842189524195)
                ·
                  refine ⟨755662296240707763284286293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503774864160471842189524195 755662296240707763284286293)
                  ·
                    refine ⟨4427708767035397050493865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 755662296240707763284286293 4427708767035397050493865)
                    ·
                      refine ⟨3320781575276547787870399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427708767035397050493865 3320781575276547787870399)
                      ·
                        rfl

theorem cell23_6467199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 9, 2].length) (baseStart_6467199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467199 prefixEnd_6467199 := by exact prefixLift 6467199
  have htrace : WordTrace (prefixWord ++ tailWord_6467199) baseStart_6467199 baseEnd_6467199 := by
    simpa [prefixWord, tailWord_6467199, baseEnd_6467199] using wordTrace_append hprefix tailTrace_6467199
  have hstable : (prefixWord ++ tailWord_6467199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467199).length < 2 ^ (prefixWord ++ tailWord_6467199).sum := by decide
  have hdescent : baseEnd_6467199 < baseStart_6467199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467207 : List Nat := [1, 1, 4, 2, 1, 4, 3, 2, 1, 2, 2]
def baseStart_6467207 : Nat := 118140960795 + 6467207 * 2 ^ 59
def prefixEnd_6467207 : Nat := 4983230072969 + 3 ^ 40 * 6467207 * 2
def baseEnd_6467207 : Nat := 3320785683121783756570363

theorem tailTrace_6467207 : CollatzResearch.WordTrace tailWord_6467207 prefixEnd_6467207 3320785683121783756570363 := by
  unfold tailWord_6467207
  simp only [CollatzResearch.WordTrace]
  refine ⟨235878417481421024866095875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157252278320947349910730583 235878417481421024866095875)
  ·
    refine ⟨353817626222131537299143813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235878417481421024866095875 353817626222131537299143813)
    ·
      refine ⟨66340804916649663243589465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353817626222131537299143813 66340804916649663243589465)
      ·
        refine ⟨49755603687487247432692099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66340804916649663243589465 49755603687487247432692099)
        ·
          refine ⟨74633405531230871149038149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49755603687487247432692099 74633405531230871149038149)
          ·
            refine ⟨13993763537105788340444653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74633405531230871149038149 13993763537105788340444653)
            ·
              refine ⟨5247661326414670627666745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13993763537105788340444653 5247661326414670627666745)
              ·
                refine ⟨3935745994811002970750059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5247661326414670627666745 3935745994811002970750059)
                ·
                  refine ⟨5903618992216504456125089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3935745994811002970750059 5903618992216504456125089)
                  ·
                    refine ⟨4427714244162378342093817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5903618992216504456125089 4427714244162378342093817)
                    ·
                      refine ⟨3320785683121783756570363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427714244162378342093817 3320785683121783756570363)
                      ·
                        rfl

theorem cell23_6467207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_6467207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467207 prefixEnd_6467207 := by exact prefixLift 6467207
  have htrace : WordTrace (prefixWord ++ tailWord_6467207) baseStart_6467207 baseEnd_6467207 := by
    simpa [prefixWord, tailWord_6467207, baseEnd_6467207] using wordTrace_append hprefix tailTrace_6467207
  have hstable : (prefixWord ++ tailWord_6467207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467207).length < 2 ^ (prefixWord ++ tailWord_6467207).sum := by decide
  have hdescent : baseEnd_6467207 < baseStart_6467207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467223 : List Nat := [1, 1, 3, 3, 2, 3, 1, 3, 2, 1, 3]
def baseStart_6467223 : Nat := 118140960795 + 6467223 * 2 ^ 59
def prefixEnd_6467223 : Nat := 4983230072969 + 3 ^ 40 * 6467223 * 2
def baseEnd_6467223 : Nat := 3320793898812255693970289

theorem tailTrace_6467223 : CollatzResearch.WordTrace tailWord_6467223 prefixEnd_6467223 3320793898812255693970289 := by
  unfold tailWord_6467223
  simp only [CollatzResearch.WordTrace]
  refine ⟨235879001049363059598678323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157252667366242039732452215 235879001049363059598678323)
  ·
    refine ⟨353818501574044589398017485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235879001049363059598678323 353818501574044589398017485)
    ·
      refine ⟨132681938090266721024256557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353818501574044589398017485 132681938090266721024256557)
      ·
        refine ⟨49755726783850020384096209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132681938090266721024256557 49755726783850020384096209)
        ·
          refine ⟨37316795087887515288072157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49755726783850020384096209 37316795087887515288072157)
          ·
            refine ⟨13993798157957818233027059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37316795087887515288072157 13993798157957818233027059)
            ·
              refine ⟨20990697236936727349540589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13993798157957818233027059 20990697236936727349540589)
              ·
                refine ⟨7871511463851272756077721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20990697236936727349540589 7871511463851272756077721)
                ·
                  refine ⟨5903633597888454567058291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7871511463851272756077721 5903633597888454567058291)
                  ·
                    refine ⟨8855450396832681850587437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5903633597888454567058291 8855450396832681850587437)
                    ·
                      refine ⟨3320793898812255693970289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8855450396832681850587437 3320793898812255693970289)
                      ·
                        rfl

theorem cell23_6467223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_6467223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467223 prefixEnd_6467223 := by exact prefixLift 6467223
  have htrace : WordTrace (prefixWord ++ tailWord_6467223) baseStart_6467223 baseEnd_6467223 := by
    simpa [prefixWord, tailWord_6467223, baseEnd_6467223] using wordTrace_append hprefix tailTrace_6467223
  have hstable : (prefixWord ++ tailWord_6467223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467223).length < 2 ^ (prefixWord ++ tailWord_6467223).sum := by decide
  have hdescent : baseEnd_6467223 < baseStart_6467223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467233 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 3, 3, 2]
def baseStart_6467233 : Nat := 118140960795 + 6467233 * 2 ^ 59
def prefixEnd_6467233 : Nat := 4983230072969 + 3 ^ 40 * 6467233 * 2
def baseEnd_6467233 : Nat := 3320799033618800654845243

theorem tailTrace_6467233 : CollatzResearch.WordTrace tailWord_6467233 prefixEnd_6467233 3320799033618800654845243 := by
  unfold tailWord_6467233
  simp only [CollatzResearch.WordTrace]
  refine ⟨235879365779326831306542353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157252910519551220871028235 235879365779326831306542353)
  ·
    refine ⟨176909524334495123479906765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235879365779326831306542353 176909524334495123479906765)
    ·
      refine ⟨66341071625435671304965037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176909524334495123479906765 66341071625435671304965037)
      ·
        refine ⟨24877901859538376739361889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66341071625435671304965037 24877901859538376739361889)
        ·
          refine ⟨18658426394653782554521417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24877901859538376739361889 18658426394653782554521417)
          ·
            refine ⟨13993819795990336915891063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18658426394653782554521417 13993819795990336915891063)
            ·
              refine ⟨20990729693985505373836595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13993819795990336915891063 20990729693985505373836595)
              ·
                refine ⟨31486094540978258060754893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20990729693985505373836595 31486094540978258060754893)
                ·
                  refine ⟨11807285452866846772783085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31486094540978258060754893 11807285452866846772783085)
                  ·
                    refine ⟨4427732044825067539793657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11807285452866846772783085 4427732044825067539793657)
                    ·
                      refine ⟨3320799033618800654845243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427732044825067539793657 3320799033618800654845243)
                      ·
                        rfl

theorem cell23_6467233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_6467233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467233 prefixEnd_6467233 := by exact prefixLift 6467233
  have htrace : WordTrace (prefixWord ++ tailWord_6467233) baseStart_6467233 baseEnd_6467233 := by
    simpa [prefixWord, tailWord_6467233, baseEnd_6467233] using wordTrace_append hprefix tailTrace_6467233
  have hstable : (prefixWord ++ tailWord_6467233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467233).length < 2 ^ (prefixWord ++ tailWord_6467233).sum := by decide
  have hdescent : baseEnd_6467233 < baseStart_6467233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467356 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_6467356 : Nat := 118140960795 + 6467356 * 2 ^ 59
def prefixEnd_6467356 : Nat := 4983230072969 + 3 ^ 40 * 6467356 * 2
def baseEnd_6467356 : Nat := 3320862191739303673607177

theorem tailTrace_6467356 : CollatzResearch.WordTrace tailWord_6467356 prefixEnd_6467356 3320862191739303673607177 := by
  unfold tailWord_6467356
  simp only [CollatzResearch.WordTrace]
  refine ⟨117941925978940611656634961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157255901305254148875513281 117941925978940611656634961)
  ·
    refine ⟨88456444484205458742476221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117941925978940611656634961 88456444484205458742476221)
    ·
      refine ⟨33171166681577047028428583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88456444484205458742476221 33171166681577047028428583)
      ·
        refine ⟨49756750022365570542642875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33171166681577047028428583 49756750022365570542642875)
        ·
          refine ⟨74635125033548355813964313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49756750022365570542642875 74635125033548355813964313)
          ·
            refine ⟨55976343775161266860473235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74635125033548355813964313 55976343775161266860473235)
            ·
              refine ⟨83964515662741900290709853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55976343775161266860473235 83964515662741900290709853)
              ·
                refine ⟨31486693373528212609016195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83964515662741900290709853 31486693373528212609016195)
                ·
                  refine ⟨47230040060292318913524293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31486693373528212609016195 47230040060292318913524293)
                  ·
                    refine ⟨8855632511304809796285805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47230040060292318913524293 8855632511304809796285805)
                    ·
                      refine ⟨3320862191739303673607177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8855632511304809796285805 3320862191739303673607177)
                      ·
                        rfl

theorem cell23_6467356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_6467356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467356 prefixEnd_6467356 := by exact prefixLift 6467356
  have htrace : WordTrace (prefixWord ++ tailWord_6467356) baseStart_6467356 baseEnd_6467356 := by
    simpa [prefixWord, tailWord_6467356, baseEnd_6467356] using wordTrace_append hprefix tailTrace_6467356
  have hstable : (prefixWord ++ tailWord_6467356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467356).length < 2 ^ (prefixWord ++ tailWord_6467356).sum := by decide
  have hdescent : baseEnd_6467356 < baseStart_6467356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467359 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 10]
def baseStart_6467359 : Nat := 118140960795 + 6467359 * 2 ^ 59
def prefixEnd_6467359 : Nat := 4983230072969 + 3 ^ 40 * 6467359 * 2
def baseEnd_6467359 : Nat := 368984859131251906874407

theorem tailTrace_6467359 : CollatzResearch.WordTrace tailWord_6467359 prefixEnd_6467359 368984859131251906874407 := by
  unfold tailWord_6467359
  simp only [CollatzResearch.WordTrace]
  refine ⟨235883961376870354825629131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157255974251246903217086087 235883961376870354825629131)
  ·
    refine ⟨353825942065305532238443697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235883961376870354825629131 353825942065305532238443697)
    ·
      refine ⟨265369456548979149178832773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353825942065305532238443697 265369456548979149178832773)
      ·
        refine ⟨49756773102933590471031145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265369456548979149178832773 49756773102933590471031145)
        ·
          refine ⟨37317579827200192853273359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49756773102933590471031145 37317579827200192853273359)
          ·
            refine ⟨55976369740800289279910039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37317579827200192853273359 55976369740800289279910039)
            ·
              refine ⟨83964554611200433919865059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55976369740800289279910039 83964554611200433919865059)
              ·
                refine ⟨125946831916800650879797589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83964554611200433919865059 125946831916800650879797589)
                ·
                  refine ⟨368984859131251906874407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 125946831916800650879797589 368984859131251906874407)
                  ·
                    rfl

theorem cell23_6467359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 10].length) (baseStart_6467359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467359 prefixEnd_6467359 := by exact prefixLift 6467359
  have htrace : WordTrace (prefixWord ++ tailWord_6467359) baseStart_6467359 baseEnd_6467359 := by
    simpa [prefixWord, tailWord_6467359, baseEnd_6467359] using wordTrace_append hprefix tailTrace_6467359
  have hstable : (prefixWord ++ tailWord_6467359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467359).length < 2 ^ (prefixWord ++ tailWord_6467359).sum := by decide
  have hdescent : baseEnd_6467359 < baseStart_6467359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467380 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_6467380 : Nat := 118140960795 + 6467380 * 2 ^ 59
def prefixEnd_6467380 : Nat := 4983230072969 + 3 ^ 40 * 6467380 * 2
def baseEnd_6467380 : Nat := 1106958171758337193235689

theorem tailTrace_6467380 : CollatzResearch.WordTrace tailWord_6467380 prefixEnd_6467380 1106958171758337193235689 := by
  unfold tailWord_6467380
  simp only [CollatzResearch.WordTrace]
  refine ⟨117942363654897137706071797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157256484873196183608095729 117942363654897137706071797)
  ·
    refine ⟨11057096592646606659944231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117942363654897137706071797 11057096592646606659944231)
    ·
      refine ⟨16585644888969909989916347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11057096592646606659944231 16585644888969909989916347)
      ·
        refine ⟨24878467333454864984874521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16585644888969909989916347 24878467333454864984874521)
        ·
          refine ⟨18658850500091148738655891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24878467333454864984874521 18658850500091148738655891)
          ·
            refine ⟨27988275750136723107983837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18658850500091148738655891 27988275750136723107983837)
            ·
              refine ⟨10495603406301271165493939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27988275750136723107983837 10495603406301271165493939)
              ·
                refine ⟨15743405109451906748240909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10495603406301271165493939 15743405109451906748240909)
                ·
                  refine ⟨5903776916044465030590341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15743405109451906748240909 5903776916044465030590341)
                  ·
                    refine ⟨1106958171758337193235689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5903776916044465030590341 1106958171758337193235689)
                    ·
                      rfl

theorem cell23_6467380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_6467380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467380 prefixEnd_6467380 := by exact prefixLift 6467380
  have htrace : WordTrace (prefixWord ++ tailWord_6467380) baseStart_6467380 baseEnd_6467380 := by
    simpa [prefixWord, tailWord_6467380, baseEnd_6467380] using wordTrace_append hprefix tailTrace_6467380
  have hstable : (prefixWord ++ tailWord_6467380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467380).length < 2 ^ (prefixWord ++ tailWord_6467380).sum := by decide
  have hdescent : baseEnd_6467380 < baseStart_6467380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467460 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_6467460 : Nat := 118140960795 + 6467460 * 2 ^ 59
def prefixEnd_6467460 : Nat := 4983230072969 + 3 ^ 40 * 6467460 * 2
def baseEnd_6467460 : Nat := 3320915593727371266706699

theorem tailTrace_6467460 : CollatzResearch.WordTrace tailWord_6467460 prefixEnd_6467460 3320915593727371266706699 := by
  unfold tailWord_6467460
  simp only [CollatzResearch.WordTrace]
  refine ⟨117943822574752224537527917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157258430099669632716703889 117943822574752224537527917)
  ·
    refine ⟨44228933465532084201572969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117943822574752224537527917 44228933465532084201572969)
    ·
      refine ⟨33171700099149063151179727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44228933465532084201572969 33171700099149063151179727)
      ·
        refine ⟨49757550148723594726769591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33171700099149063151179727 49757550148723594726769591)
        ·
          refine ⟨74636325223085392090154387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49757550148723594726769591 74636325223085392090154387)
          ·
            refine ⟨111954487834628088135231581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74636325223085392090154387 111954487834628088135231581)
            ·
              refine ⟨41982932937985533050711843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111954487834628088135231581 41982932937985533050711843)
              ·
                refine ⟨62974399406978299576067765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41982932937985533050711843 62974399406978299576067765)
                ·
                  refine ⟨5903849944404215585256353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62974399406978299576067765 5903849944404215585256353)
                  ·
                    refine ⟨4427887458303161688942265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5903849944404215585256353 4427887458303161688942265)
                    ·
                      refine ⟨3320915593727371266706699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427887458303161688942265 3320915593727371266706699)
                      ·
                        rfl

theorem cell23_6467460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_6467460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467460 prefixEnd_6467460 := by exact prefixLift 6467460
  have htrace : WordTrace (prefixWord ++ tailWord_6467460) baseStart_6467460 baseEnd_6467460 := by
    simpa [prefixWord, tailWord_6467460, baseEnd_6467460] using wordTrace_append hprefix tailTrace_6467460
  have hstable : (prefixWord ++ tailWord_6467460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467460).length < 2 ^ (prefixWord ++ tailWord_6467460).sum := by decide
  have hdescent : baseEnd_6467460 < baseStart_6467460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467464 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 2, 3, 2]
def baseStart_6467464 : Nat := 118140960795 + 6467464 * 2 ^ 59
def prefixEnd_6467464 : Nat := 4983230072969 + 3 ^ 40 * 6467464 * 2
def baseEnd_6467464 : Nat := 3320917647649989251056681

theorem tailTrace_6467464 : CollatzResearch.WordTrace tailWord_6467464 prefixEnd_6467464 3320917647649989251056681 := by
  unfold tailWord_6467464
  simp only [CollatzResearch.WordTrace]
  refine ⟨117943895520744978879100723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157258527360993305172134297 117943895520744978879100723)
  ·
    refine ⟨176915843281117468318651085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117943895520744978879100723 176915843281117468318651085)
    ·
      refine ⟨66343441230419050619494157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176915843281117468318651085 66343441230419050619494157)
      ·
        refine ⟨24878790461407143982310309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66343441230419050619494157 24878790461407143982310309)
        ·
          refine ⟨4664773211513839496683183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24878790461407143982310309 4664773211513839496683183)
          ·
            refine ⟨6997159817270759245024775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4664773211513839496683183 6997159817270759245024775)
            ·
              refine ⟨10495739725906138867537163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6997159817270759245024775 10495739725906138867537163)
              ·
                refine ⟨15743609588859208301305745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10495739725906138867537163 15743609588859208301305745)
                ·
                  refine ⟨11807707191644406225979309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15743609588859208301305745 11807707191644406225979309)
                  ·
                    refine ⟨4427890196866652334742241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11807707191644406225979309 4427890196866652334742241)
                    ·
                      refine ⟨3320917647649989251056681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427890196866652334742241 3320917647649989251056681)
                      ·
                        rfl

theorem cell23_6467464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_6467464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467464 prefixEnd_6467464 := by exact prefixLift 6467464
  have htrace : WordTrace (prefixWord ++ tailWord_6467464) baseStart_6467464 baseEnd_6467464 := by
    simpa [prefixWord, tailWord_6467464, baseEnd_6467464] using wordTrace_append hprefix tailTrace_6467464
  have hstable : (prefixWord ++ tailWord_6467464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467464).length < 2 ^ (prefixWord ++ tailWord_6467464).sum := by decide
  have hdescent : baseEnd_6467464 < baseStart_6467464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467487 : List Nat := [1, 1, 2, 5, 3, 2, 1, 2, 2, 4]
def baseStart_6467487 : Nat := 118140960795 + 6467487 * 2 ^ 59
def prefixEnd_6467487 : Nat := 4983230072969 + 3 ^ 40 * 6467487 * 2
def baseEnd_6467487 : Nat := 1106976485901680887023025

theorem tailTrace_6467487 : CollatzResearch.WordTrace tailWord_6467487 prefixEnd_6467487 1106976485901680887023025 := by
  unfold tailWord_6467487
  simp only [CollatzResearch.WordTrace]
  refine ⟨235888629920406632686288715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157259086613604421790859143 235888629920406632686288715)
  ·
    refine ⟨353832944880609949029433073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235888629920406632686288715 353832944880609949029433073)
    ·
      refine ⟨265374708660457461772074805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353832944880609949029433073 265374708660457461772074805)
      ·
        refine ⟨24878878936917887041132013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 265374708660457461772074805 24878878936917887041132013)
        ·
          refine ⟨9329579601344207640424505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24878878936917887041132013 9329579601344207640424505)
          ·
            refine ⟨6997184701008155730318379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9329579601344207640424505 6997184701008155730318379)
            ·
              refine ⟨10495777051512233595477569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6997184701008155730318379 10495777051512233595477569)
              ·
                refine ⟨7871832788634175196608177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10495777051512233595477569 7871832788634175196608177)
                ·
                  refine ⟨5903874591475631397456133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7871832788634175196608177 5903874591475631397456133)
                  ·
                    refine ⟨1106976485901680887023025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5903874591475631397456133 1106976485901680887023025)
                    ·
                      rfl

theorem cell23_6467487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 4].length) (baseStart_6467487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467487 prefixEnd_6467487 := by exact prefixLift 6467487
  have htrace : WordTrace (prefixWord ++ tailWord_6467487) baseStart_6467487 baseEnd_6467487 := by
    simpa [prefixWord, tailWord_6467487, baseEnd_6467487] using wordTrace_append hprefix tailTrace_6467487
  have hstable : (prefixWord ++ tailWord_6467487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467487).length < 2 ^ (prefixWord ++ tailWord_6467487).sum := by decide
  have hdescent : baseEnd_6467487 < baseStart_6467487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467506 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_6467506 : Nat := 118140960795 + 6467506 * 2 ^ 59
def prefixEnd_6467506 : Nat := 4983230072969 + 3 ^ 40 * 6467506 * 2
def baseEnd_6467506 : Nat := 3320939213837478086731487

theorem tailTrace_6467506 : CollatzResearch.WordTrace tailWord_6467506 prefixEnd_6467506 3320939213837478086731487 := by
  unfold tailWord_6467506
  simp only [CollatzResearch.WordTrace]
  refine ⟨58972330726834449732807593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157259548604891865954153581 58972330726834449732807593)
  ·
    refine ⟨44229248045125837299605695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58972330726834449732807593 44229248045125837299605695)
    ·
      refine ⟨66343872067688755949408543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44229248045125837299605695 66343872067688755949408543)
      ·
        refine ⟨99515808101533133924112815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66343872067688755949408543 99515808101533133924112815)
        ·
          refine ⟨149273712152299700886169223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99515808101533133924112815 149273712152299700886169223)
          ·
            refine ⟨223910568228449551329253835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149273712152299700886169223 223910568228449551329253835)
            ·
              refine ⟨335865852342674326993880753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223910568228449551329253835 335865852342674326993880753)
              ·
                refine ⟨251899389257005745245410565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335865852342674326993880753 251899389257005745245410565)
                ·
                  refine ⟨47231135485688577233514481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251899389257005745245410565 47231135485688577233514481)
                  ·
                    refine ⟨35423351614266432925135861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47231135485688577233514481 35423351614266432925135861)
                    ·
                      refine ⟨3320939213837478086731487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35423351614266432925135861 3320939213837478086731487)
                      ·
                        rfl

theorem cell23_6467506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_6467506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467506 prefixEnd_6467506 := by exact prefixLift 6467506
  have htrace : WordTrace (prefixWord ++ tailWord_6467506) baseStart_6467506 baseEnd_6467506 := by
    simpa [prefixWord, tailWord_6467506, baseEnd_6467506] using wordTrace_append hprefix tailTrace_6467506
  have hstable : (prefixWord ++ tailWord_6467506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467506).length < 2 ^ (prefixWord ++ tailWord_6467506).sum := by decide
  have hdescent : baseEnd_6467506 < baseStart_6467506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467536 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 5]
def baseStart_6467536 : Nat := 118140960795 + 6467536 * 2 ^ 59
def prefixEnd_6467536 : Nat := 4983230072969 + 3 ^ 40 * 6467536 * 2
def baseEnd_6467536 : Nat := 3320954618257112969356349

theorem tailTrace_6467536 : CollatzResearch.WordTrace tailWord_6467536 prefixEnd_6467536 3320954618257112969356349 := by
  unfold tailWord_6467536
  simp only [CollatzResearch.WordTrace]
  refine ⟨117945208548614557027411231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157260278064819409369881641 117945208548614557027411231)
  ·
    refine ⟨176917812822921835541116847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117945208548614557027411231 176917812822921835541116847)
    ·
      refine ⟨265376719234382753311675271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176917812822921835541116847 265376719234382753311675271)
      ·
        refine ⟨398065078851574129967512907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265376719234382753311675271 398065078851574129967512907)
        ·
          refine ⟨597097618277361194951269361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398065078851574129967512907 597097618277361194951269361)
          ·
            refine ⟨447823213708020896213452021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597097618277361194951269361 447823213708020896213452021)
            ·
              refine ⟨41983426285126959020011127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 447823213708020896213452021 41983426285126959020011127)
              ·
                refine ⟨62975139427690438530016691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41983426285126959020011127 62975139427690438530016691)
                ·
                  refine ⟨94462709141535657795025037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62975139427690438530016691 94462709141535657795025037)
                  ·
                    refine ⟨35423515928075871673134389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94462709141535657795025037 35423515928075871673134389)
                    ·
                      refine ⟨3320954618257112969356349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35423515928075871673134389 3320954618257112969356349)
                      ·
                        rfl

theorem cell23_6467536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_6467536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467536 prefixEnd_6467536 := by exact prefixLift 6467536
  have htrace : WordTrace (prefixWord ++ tailWord_6467536) baseStart_6467536 baseEnd_6467536 := by
    simpa [prefixWord, tailWord_6467536, baseEnd_6467536] using wordTrace_append hprefix tailTrace_6467536
  have hstable : (prefixWord ++ tailWord_6467536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467536).length < 2 ^ (prefixWord ++ tailWord_6467536).sum := by decide
  have hdescent : baseEnd_6467536 < baseStart_6467536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467567 : List Nat := [1, 1, 2, 1, 4, 2, 3, 3, 2, 2, 2]
def baseStart_6467567 : Nat := 118140960795 + 6467567 * 2 ^ 59
def prefixEnd_6467567 : Nat := 4983230072969 + 3 ^ 40 * 6467567 * 2
def baseEnd_6467567 : Nat := 3320970536157402348068707

theorem tailTrace_6467567 : CollatzResearch.WordTrace tailWord_6467567 prefixEnd_6467567 3320970536157402348068707 := by
  unfold tailWord_6467567
  simp only [CollatzResearch.WordTrace]
  refine ⟨235891547760116806349200955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157261031840077870899467303 235891547760116806349200955)
  ·
    refine ⟨353837321640175209523801433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235891547760116806349200955 353837321640175209523801433)
    ·
      refine ⟨265377991230131407142851075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353837321640175209523801433 265377991230131407142851075)
      ·
        refine ⟨398066986845197110714276613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265377991230131407142851075 398066986845197110714276613)
        ·
          refine ⟨74637560033474458258926865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 398066986845197110714276613 74637560033474458258926865)
          ·
            refine ⟨55978170025105843694195149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74637560033474458258926865 55978170025105843694195149)
            ·
              refine ⟨20991813759414691385323181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55978170025105843694195149 20991813759414691385323181)
              ·
                refine ⟨7871930159780509269496193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20991813759414691385323181 7871930159780509269496193)
                ·
                  refine ⟨5903947619835381952122145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7871930159780509269496193 5903947619835381952122145)
                  ·
                    refine ⟨4427960714876536464091609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5903947619835381952122145 4427960714876536464091609)
                    ·
                      refine ⟨3320970536157402348068707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427960714876536464091609 3320970536157402348068707)
                      ·
                        rfl

theorem cell23_6467567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 2, 2].length) (baseStart_6467567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467567 prefixEnd_6467567 := by exact prefixLift 6467567
  have htrace : WordTrace (prefixWord ++ tailWord_6467567) baseStart_6467567 baseEnd_6467567 := by
    simpa [prefixWord, tailWord_6467567, baseEnd_6467567] using wordTrace_append hprefix tailTrace_6467567
  have hstable : (prefixWord ++ tailWord_6467567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467567).length < 2 ^ (prefixWord ++ tailWord_6467567).sum := by decide
  have hdescent : baseEnd_6467567 < baseStart_6467567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467603 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 2, 5]
def baseStart_6467603 : Nat := 118140960795 + 6467603 * 2 ^ 59
def prefixEnd_6467603 : Nat := 4983230072969 + 3 ^ 40 * 6467603 * 2
def baseEnd_6467603 : Nat := 1106996340486988069072847

theorem tailTrace_6467603 : CollatzResearch.WordTrace tailWord_6467603 prefixEnd_6467603 1106996340486988069072847 := by
  unfold tailWord_6467603
  simp only [CollatzResearch.WordTrace]
  refine ⟨235892860787986384497511463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157261907191990922998340975 235892860787986384497511463)
  ·
    refine ⟨353839291181979576746267195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235892860787986384497511463 353839291181979576746267195)
    ·
      refine ⟨530758936772969365119400793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353839291181979576746267195 530758936772969365119400793)
      ·
        refine ⟨398069202579727023839550595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530758936772969365119400793 398069202579727023839550595)
        ·
          refine ⟨597103803869590535759325893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398069202579727023839550595 597103803869590535759325893)
          ·
            refine ⟨111956963225548225454873605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 597103803869590535759325893 111956963225548225454873605)
            ·
              refine ⟨20991930604790292272788801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111956963225548225454873605 20991930604790292272788801)
              ·
                refine ⟨15743947953592719204591601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20991930604790292272788801 15743947953592719204591601)
                ·
                  refine ⟨11807960965194539403443701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15743947953592719204591601 11807960965194539403443701)
                  ·
                    refine ⟨1106996340486988069072847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11807960965194539403443701 1106996340486988069072847)
                    ·
                      rfl

theorem cell23_6467603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 5].length) (baseStart_6467603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467603 prefixEnd_6467603 := by exact prefixLift 6467603
  have htrace : WordTrace (prefixWord ++ tailWord_6467603) baseStart_6467603 baseEnd_6467603 := by
    simpa [prefixWord, tailWord_6467603, baseEnd_6467603] using wordTrace_append hprefix tailTrace_6467603
  have hstable : (prefixWord ++ tailWord_6467603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467603).length < 2 ^ (prefixWord ++ tailWord_6467603).sum := by decide
  have hdescent : baseEnd_6467603 < baseStart_6467603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467607 : List Nat := [1, 1, 3, 5, 2, 1, 1, 4, 5]
def baseStart_6467607 : Nat := 118140960795 + 6467607 * 2 ^ 59
def prefixEnd_6467607 : Nat := 4983230072969 + 3 ^ 40 * 6467607 * 2
def baseEnd_6467607 : Nat := 368999008375953576840947

theorem tailTrace_6467607 : CollatzResearch.WordTrace tailWord_6467607 prefixEnd_6467607 368999008375953576840947 := by
  unfold tailWord_6467607
  simp only [CollatzResearch.WordTrace]
  refine ⟨235893006679971893180657075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157262004453314595453771383 235893006679971893180657075)
  ·
    refine ⟨353839510019957839770985613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235893006679971893180657075 353839510019957839770985613)
    ·
      refine ⟨132689816257484189914119605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353839510019957839770985613 132689816257484189914119605)
      ·
        refine ⟨12439670274139142804448713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132689816257484189914119605 12439670274139142804448713)
        ·
          refine ⟨9329752705604357103336535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12439670274139142804448713 9329752705604357103336535)
          ·
            refine ⟨13994629058406535655004803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9329752705604357103336535 13994629058406535655004803)
            ·
              refine ⟨20991943587609803482507205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13994629058406535655004803 20991943587609803482507205)
              ·
                refine ⟨3935989422676838152970101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20991943587609803482507205 3935989422676838152970101)
                ·
                  refine ⟨368999008375953576840947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3935989422676838152970101 368999008375953576840947)
                  ·
                    rfl

theorem cell23_6467607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 5].length) (baseStart_6467607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467607 prefixEnd_6467607 := by exact prefixLift 6467607
  have htrace : WordTrace (prefixWord ++ tailWord_6467607) baseStart_6467607 baseEnd_6467607 := by
    simpa [prefixWord, tailWord_6467607, baseEnd_6467607] using wordTrace_append hprefix tailTrace_6467607
  have hstable : (prefixWord ++ tailWord_6467607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467607).length < 2 ^ (prefixWord ++ tailWord_6467607).sum := by decide
  have hdescent : baseEnd_6467607 < baseStart_6467607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467610 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2]
def baseStart_6467610 : Nat := 118140960795 + 6467610 * 2 ^ 59
def prefixEnd_6467610 : Nat := 4983230072969 + 3 ^ 40 * 6467610 * 2
def baseEnd_6467610 : Nat := 3320992615825545679831009

theorem tailTrace_6467610 : CollatzResearch.WordTrace tailWord_6467610 prefixEnd_6467610 3320992615825545679831009 := by
  unfold tailWord_6467610
  simp only [CollatzResearch.WordTrace]
  refine ⟨58973279024740256173254071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157262077399307349795344189 58973279024740256173254071)
  ·
    refine ⟨88459918537110384259881107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58973279024740256173254071 88459918537110384259881107)
    ·
      refine ⟨132689877805665576389821661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88459918537110384259881107 132689877805665576389821661)
      ·
        refine ⟨49758704177124591146183123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132689877805665576389821661 49758704177124591146183123)
        ·
          refine ⟨74638056265686886719274685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49758704177124591146183123 74638056265686886719274685)
          ·
            refine ⟨27989271099632582519728007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74638056265686886719274685 27989271099632582519728007)
            ·
              refine ⟨41983906649448873779592011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27989271099632582519728007 41983906649448873779592011)
              ·
                refine ⟨62975859974173310669388017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41983906649448873779592011 62975859974173310669388017)
                ·
                  refine ⟨47231894980629983002041013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62975859974173310669388017 47231894980629983002041013)
                  ·
                    refine ⟨4427990154434060906441345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47231894980629983002041013 4427990154434060906441345)
                    ·
                      refine ⟨3320992615825545679831009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4427990154434060906441345 3320992615825545679831009)
                      ·
                        rfl

theorem cell23_6467610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_6467610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467610 prefixEnd_6467610 := by exact prefixLift 6467610
  have htrace : WordTrace (prefixWord ++ tailWord_6467610) baseStart_6467610 baseEnd_6467610 := by
    simpa [prefixWord, tailWord_6467610, baseEnd_6467610] using wordTrace_append hprefix tailTrace_6467610
  have hstable : (prefixWord ++ tailWord_6467610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467610).length < 2 ^ (prefixWord ++ tailWord_6467610).sum := by decide
  have hdescent : baseEnd_6467610 < baseStart_6467610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467640 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 1, 3, 4]
def baseStart_6467640 : Nat := 118140960795 + 6467640 * 2 ^ 59
def prefixEnd_6467640 : Nat := 4983230072969 + 3 ^ 40 * 6467640 * 2
def baseEnd_6467640 : Nat := 3321008020245180562455871

theorem tailTrace_6467640 : CollatzResearch.WordTrace tailWord_6467640 prefixEnd_6467640 3321008020245180562455871 := by
  unfold tailWord_6467640
  simp only [CollatzResearch.WordTrace]
  refine ⟨117947105144426169908304187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157262806859234893211072249 117947105144426169908304187)
  ·
    refine ⟨176920657716639254862456281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117947105144426169908304187 176920657716639254862456281)
    ·
      refine ⟨132690493287479441146842211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176920657716639254862456281 132690493287479441146842211)
      ·
        refine ⟨199035739931219161720263317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132690493287479441146842211 199035739931219161720263317)
        ·
          refine ⟨9329800309275898205637343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 199035739931219161720263317 9329800309275898205637343)
          ·
            refine ⟨13994700463913847308456015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9329800309275898205637343 13994700463913847308456015)
            ·
              refine ⟨20992050695870770962684023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13994700463913847308456015 20992050695870770962684023)
              ·
                refine ⟨31488076043806156444026035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20992050695870770962684023 31488076043806156444026035)
                ·
                  refine ⟨47232114065709234666039053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31488076043806156444026035 47232114065709234666039053)
                  ·
                    refine ⟨17712042774640962999764645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47232114065709234666039053 17712042774640962999764645)
                    ·
                      refine ⟨3321008020245180562455871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17712042774640962999764645 3321008020245180562455871)
                      ·
                        rfl

theorem cell23_6467640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_6467640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467640 prefixEnd_6467640 := by exact prefixLift 6467640
  have htrace : WordTrace (prefixWord ++ tailWord_6467640) baseStart_6467640 baseEnd_6467640 := by
    simpa [prefixWord, tailWord_6467640, baseEnd_6467640] using wordTrace_append hprefix tailTrace_6467640
  have hstable : (prefixWord ++ tailWord_6467640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467640).length < 2 ^ (prefixWord ++ tailWord_6467640).sum := by decide
  have hdescent : baseEnd_6467640 < baseStart_6467640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467643 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 3]
def baseStart_6467643 : Nat := 118140960795 + 6467643 * 2 ^ 59
def prefixEnd_6467643 : Nat := 4983230072969 + 3 ^ 40 * 6467643 * 2
def baseEnd_6467643 : Nat := 3321009560687144050718357

theorem tailTrace_6467643 : CollatzResearch.WordTrace tailWord_6467643 prefixEnd_6467643 3321009560687144050718357 := by
  unfold tailWord_6467643
  simp only [CollatzResearch.WordTrace]
  refine ⟨235894319707841471328967583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157262879805227647552645055 235894319707841471328967583)
  ·
    refine ⟨353841479561762206993451375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235894319707841471328967583 353841479561762206993451375)
    ·
      refine ⟨530762219342643310490177063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353841479561762206993451375 530762219342643310490177063)
      ·
        refine ⟨796143329013964965735265595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530762219342643310490177063 796143329013964965735265595)
        ·
          refine ⟨1194214993520947448602898393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796143329013964965735265595 1194214993520947448602898393)
          ·
            refine ⟨895661245140710586452173795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1194214993520947448602898393 895661245140710586452173795)
            ·
              refine ⟨1343491867711065879678260693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895661245140710586452173795 1343491867711065879678260693)
              ·
                refine ⟨31488090649478106554959235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1343491867711065879678260693 31488090649478106554959235)
                ·
                  refine ⟨47232135974217159832438853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31488090649478106554959235 47232135974217159832438853)
                  ·
                    refine ⟨8856025495165717468582285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47232135974217159832438853 8856025495165717468582285)
                    ·
                      refine ⟨3321009560687144050718357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8856025495165717468582285 3321009560687144050718357)
                      ·
                        rfl

theorem cell23_6467643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 3].length) (baseStart_6467643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467643 prefixEnd_6467643 := by exact prefixLift 6467643
  have htrace : WordTrace (prefixWord ++ tailWord_6467643) baseStart_6467643 baseEnd_6467643 := by
    simpa [prefixWord, tailWord_6467643, baseEnd_6467643] using wordTrace_append hprefix tailTrace_6467643
  have hstable : (prefixWord ++ tailWord_6467643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467643).length < 2 ^ (prefixWord ++ tailWord_6467643).sum := by decide
  have hdescent : baseEnd_6467643 < baseStart_6467643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467660 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 2, 2, 3]
def baseStart_6467660 : Nat := 118140960795 + 6467660 * 2 ^ 59
def prefixEnd_6467660 : Nat := 4983230072969 + 3 ^ 40 * 6467660 * 2
def baseEnd_6467660 : Nat := 3321018289858270484205779

theorem tailTrace_6467660 : CollatzResearch.WordTrace tailWord_6467660 prefixEnd_6467660 3321018289858270484205779 := by
  unfold tailWord_6467660
  simp only [CollatzResearch.WordTrace]
  refine ⟨117947469874389941616168217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157263293165853255488224289 117947469874389941616168217)
  ·
    refine ⟨88460602405792456212126163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117947469874389941616168217 88460602405792456212126163)
    ·
      refine ⟨132690903608688684318189245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88460602405792456212126163 132690903608688684318189245)
      ·
        refine ⟨49759088853258256619320967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132690903608688684318189245 49759088853258256619320967)
        ·
          refine ⟨74638633279887384928981451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49759088853258256619320967 74638633279887384928981451)
          ·
            refine ⟨111957949919831077393472177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74638633279887384928981451 111957949919831077393472177)
            ·
              refine ⟨83968462439873308045104133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111957949919831077393472177 83968462439873308045104133)
              ·
                refine ⟨15744086707476245258457025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83968462439873308045104133 15744086707476245258457025)
                ·
                  refine ⟨11808065030607183943842769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15744086707476245258457025 11808065030607183943842769)
                  ·
                    refine ⟨8856048772955387957882077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11808065030607183943842769 8856048772955387957882077)
                    ·
                      refine ⟨3321018289858270484205779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8856048772955387957882077 3321018289858270484205779)
                      ·
                        rfl

theorem cell23_6467660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_6467660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467660 prefixEnd_6467660 := by exact prefixLift 6467660
  have htrace : WordTrace (prefixWord ++ tailWord_6467660) baseStart_6467660 baseEnd_6467660 := by
    simpa [prefixWord, tailWord_6467660, baseEnd_6467660] using wordTrace_append hprefix tailTrace_6467660
  have hstable : (prefixWord ++ tailWord_6467660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467660).length < 2 ^ (prefixWord ++ tailWord_6467660).sum := by decide
  have hdescent : baseEnd_6467660 < baseStart_6467660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467677 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_6467677 : Nat := 118140960795 + 6467677 * 2 ^ 59
def prefixEnd_6467677 : Nat := 4983230072969 + 3 ^ 40 * 6467677 * 2
def baseEnd_6467677 : Nat := 3321027019029396917693201

theorem tailTrace_6467677 : CollatzResearch.WordTrace tailWord_6467677 prefixEnd_6467677 3321027019029396917693201 := by
  unfold tailWord_6467677
  simp only [CollatzResearch.WordTrace]
  refine ⟨235895559789718295135705285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157263706526478863423803523 235895559789718295135705285)
  ·
    refine ⟨44230417460572180337944741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235895559789718295135705285 44230417460572180337944741)
    ·
      refine ⟨8293203273857283813364639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44230417460572180337944741 8293203273857283813364639)
      ·
        refine ⟨12439804910785925720046959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8293203273857283813364639 12439804910785925720046959)
        ·
          refine ⟨18659707366178888580070439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12439804910785925720046959 18659707366178888580070439)
          ·
            refine ⟨27989561049268332870105659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18659707366178888580070439 27989561049268332870105659)
            ·
              refine ⟨41984341573902499305158489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27989561049268332870105659 41984341573902499305158489)
              ·
                refine ⟨31488256180426874478868867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41984341573902499305158489 31488256180426874478868867)
                ·
                  refine ⟨47232384270640311718303301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31488256180426874478868867 47232384270640311718303301)
                  ·
                    refine ⟨8856072050745058447181869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47232384270640311718303301 8856072050745058447181869)
                    ·
                      refine ⟨3321027019029396917693201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8856072050745058447181869 3321027019029396917693201)
                      ·
                        rfl

theorem cell23_6467677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_6467677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467677 prefixEnd_6467677 := by exact prefixLift 6467677
  have htrace : WordTrace (prefixWord ++ tailWord_6467677) baseStart_6467677 baseEnd_6467677 := by
    simpa [prefixWord, tailWord_6467677, baseEnd_6467677] using wordTrace_append hprefix tailTrace_6467677
  have hstable : (prefixWord ++ tailWord_6467677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467677).length < 2 ^ (prefixWord ++ tailWord_6467677).sum := by decide
  have hdescent : baseEnd_6467677 < baseStart_6467677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467717 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 4, 3, 2]
def baseStart_6467717 : Nat := 118140960795 + 6467717 * 2 ^ 59
def prefixEnd_6467717 : Nat := 4983230072969 + 3 ^ 40 * 6467717 * 2
def baseEnd_6467717 : Nat := 3321047558255576761193017

theorem tailTrace_6467717 : CollatzResearch.WordTrace tailWord_6467717 prefixEnd_6467717 3321047558255576761193017 := by
  unfold tailWord_6467717
  simp only [CollatzResearch.WordTrace]
  refine ⟨235897018709573381967161405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157264679139715587978107603 235897018709573381967161405)
  ·
    refine ⟨88461382016090018237685527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235897018709573381967161405 88461382016090018237685527)
    ·
      refine ⟨132692073024135027356528291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88461382016090018237685527 132692073024135027356528291)
      ·
        refine ⟨199038109536202541034792437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132692073024135027356528291 199038109536202541034792437)
        ·
          refine ⟨18659822769018988222011791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199038109536202541034792437 18659822769018988222011791)
          ·
            refine ⟨27989734153528482333017687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18659822769018988222011791 27989734153528482333017687)
            ·
              refine ⟨41984601230292723499526531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27989734153528482333017687 41984601230292723499526531)
              ·
                refine ⟨62976901845439085249289797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41984601230292723499526531 62976901845439085249289797)
                ·
                  refine ⟨11808169096019828484241837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62976901845439085249289797 11808169096019828484241837)
                  ·
                    refine ⟨4428063411007435681590689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11808169096019828484241837 4428063411007435681590689)
                    ·
                      refine ⟨3321047558255576761193017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4428063411007435681590689 3321047558255576761193017)
                      ·
                        rfl

theorem cell23_6467717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 3, 2].length) (baseStart_6467717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467717 prefixEnd_6467717 := by exact prefixLift 6467717
  have htrace : WordTrace (prefixWord ++ tailWord_6467717) baseStart_6467717 baseEnd_6467717 := by
    simpa [prefixWord, tailWord_6467717, baseEnd_6467717] using wordTrace_append hprefix tailTrace_6467717
  have hstable : (prefixWord ++ tailWord_6467717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467717).length < 2 ^ (prefixWord ++ tailWord_6467717).sum := by decide
  have hdescent : baseEnd_6467717 < baseStart_6467717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467740 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 1, 6]
def baseStart_6467740 : Nat := 118140960795 + 6467740 * 2 ^ 59
def prefixEnd_6467740 : Nat := 4983230072969 + 3 ^ 40 * 6467740 * 2
def baseEnd_6467740 : Nat := 1107019789436876723735137

theorem tailTrace_6467740 : CollatzResearch.WordTrace tailWord_6467740 prefixEnd_6467740 1107019789436876723735137 := by
  unfold tailWord_6467740
  simp only [CollatzResearch.WordTrace]
  refine ⟨117948928794245028447624337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157265238392326704596832449 117948928794245028447624337)
  ·
    refine ⟨88461696595683771335718253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117948928794245028447624337 88461696595683771335718253)
    ·
      refine ⟨33173136223381414250894345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88461696595683771335718253 33173136223381414250894345)
      ·
        refine ⟨24879852167536060688170759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33173136223381414250894345 24879852167536060688170759)
        ·
          refine ⟨37319778251304091032256139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24879852167536060688170759 37319778251304091032256139)
          ·
            refine ⟨55979667376956136548384209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37319778251304091032256139 55979667376956136548384209)
            ·
              refine ⟨41984750532717102411288157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55979667376956136548384209 41984750532717102411288157)
              ·
                refine ⟨15744281449768913404233059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41984750532717102411288157 15744281449768913404233059)
                ·
                  refine ⟨23616422174653370106349589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15744281449768913404233059 23616422174653370106349589)
                  ·
                    refine ⟨1107019789436876723735137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23616422174653370106349589 1107019789436876723735137)
                    ·
                      rfl

theorem cell23_6467740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_6467740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467740 prefixEnd_6467740 := by exact prefixLift 6467740
  have htrace : WordTrace (prefixWord ++ tailWord_6467740) baseStart_6467740 baseEnd_6467740 := by
    simpa [prefixWord, tailWord_6467740, baseEnd_6467740] using wordTrace_append hprefix tailTrace_6467740
  have hstable : (prefixWord ++ tailWord_6467740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467740).length < 2 ^ (prefixWord ++ tailWord_6467740).sum := by decide
  have hdescent : baseEnd_6467740 < baseStart_6467740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467751 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_6467751 : Nat := 118140960795 + 6467751 * 2 ^ 59
def prefixEnd_6467751 : Nat := 4983230072969 + 3 ^ 40 * 6467751 * 2
def baseEnd_6467751 : Nat := 3321065016597829628167861

theorem tailTrace_6467751 : CollatzResearch.WordTrace tailWord_6467751 prefixEnd_6467751 3321065016597829628167861 := by
  unfold tailWord_6467751
  simp only [CollatzResearch.WordTrace]
  refine ⟨235898258791450205773899107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157265505860966803849266071 235898258791450205773899107)
  ·
    refine ⟨353847388187175308660848661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235898258791450205773899107 353847388187175308660848661)
    ·
      refine ⟨16586596321273842593477281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 353847388187175308660848661 16586596321273842593477281)
      ·
        refine ⟨12439947240955381945107961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16586596321273842593477281 12439947240955381945107961)
        ·
          refine ⟨9329960430716536458830971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12439947240955381945107961 9329960430716536458830971)
          ·
            refine ⟨13994940646074804688246457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9329960430716536458830971 13994940646074804688246457)
            ·
              refine ⟨10496205484556103516184843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13994940646074804688246457 10496205484556103516184843)
              ·
                refine ⟨15744308226834155274277265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10496205484556103516184843 15744308226834155274277265)
                ·
                  refine ⟨11808231170125616455707949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15744308226834155274277265 11808231170125616455707949)
                  ·
                    refine ⟨4428086688797106170890481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11808231170125616455707949 4428086688797106170890481)
                    ·
                      refine ⟨3321065016597829628167861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4428086688797106170890481 3321065016597829628167861)
                      ·
                        rfl

theorem cell23_6467751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_6467751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467751 prefixEnd_6467751 := by exact prefixLift 6467751
  have htrace : WordTrace (prefixWord ++ tailWord_6467751) baseStart_6467751 baseEnd_6467751 := by
    simpa [prefixWord, tailWord_6467751, baseEnd_6467751] using wordTrace_append hprefix tailTrace_6467751
  have hstable : (prefixWord ++ tailWord_6467751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467751).length < 2 ^ (prefixWord ++ tailWord_6467751).sum := by decide
  have hdescent : baseEnd_6467751 < baseStart_6467751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467757 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_6467757 : Nat := 118140960795 + 6467757 * 2 ^ 59
def prefixEnd_6467757 : Nat := 4983230072969 + 3 ^ 40 * 6467757 * 2
def baseEnd_6467757 : Nat := 1107022699160585534897611

theorem tailTrace_6467757 : CollatzResearch.WordTrace tailWord_6467757 prefixEnd_6467757 1107022699160585534897611 := by
  unfold tailWord_6467757
  simp only [CollatzResearch.WordTrace]
  refine ⟨235898477629428468798617525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157265651752952312532411683 235898477629428468798617525)
  ·
    refine ⟨22115482277758918949870393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 235898477629428468798617525 22115482277758918949870393)
    ·
      refine ⟨16586611708319189212402795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22115482277758918949870393 16586611708319189212402795)
      ·
        refine ⟨24879917562478783818604193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16586611708319189212402795 24879917562478783818604193)
        ·
          refine ⟨18659938171859087863953145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24879917562478783818604193 18659938171859087863953145)
          ·
            refine ⟨13994953628894315897964859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18659938171859087863953145 13994953628894315897964859)
            ·
              refine ⟨20992430443341473846947289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13994953628894315897964859 20992430443341473846947289)
              ·
                refine ⟨15744322832506105385210467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20992430443341473846947289 15744322832506105385210467)
                ·
                  refine ⟨23616484248759158077815701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15744322832506105385210467 23616484248759158077815701)
                  ·
                    refine ⟨1107022699160585534897611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23616484248759158077815701 1107022699160585534897611)
                    ·
                      rfl

theorem cell23_6467757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_6467757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467757 prefixEnd_6467757 := by exact prefixLift 6467757
  have htrace : WordTrace (prefixWord ++ tailWord_6467757) baseStart_6467757 baseEnd_6467757 := by
    simpa [prefixWord, tailWord_6467757, baseEnd_6467757] using wordTrace_append hprefix tailTrace_6467757
  have hstable : (prefixWord ++ tailWord_6467757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467757).length < 2 ^ (prefixWord ++ tailWord_6467757).sum := by decide
  have hdescent : baseEnd_6467757 < baseStart_6467757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467767 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 1, 1, 5]
def baseStart_6467767 : Nat := 118140960795 + 6467767 * 2 ^ 59
def prefixEnd_6467767 : Nat := 4983230072969 + 3 ^ 40 * 6467767 * 2
def baseEnd_6467767 : Nat := 3321073232288301565567787

theorem tailTrace_6467767 : CollatzResearch.WordTrace tailWord_6467767 prefixEnd_6467767 3321073232288301565567787 := by
  unfold tailWord_6467767
  simp only [CollatzResearch.WordTrace]
  refine ⟨235898842359392240506481555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157265894906261493670987703 235898842359392240506481555)
  ·
    refine ⟨353848263539088360759722333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235898842359392240506481555 353848263539088360759722333)
    ·
      refine ⟨132693098827158135284895875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353848263539088360759722333 132693098827158135284895875)
      ·
        refine ⟨199039648240737202927343813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132693098827158135284895875 199039648240737202927343813)
        ·
          refine ⟨37319934045138225548876965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199039648240737202927343813 37319934045138225548876965)
          ·
            refine ⟨6997487633463417290414431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37319934045138225548876965 6997487633463417290414431)
            ·
              refine ⟨10496231450195125935621647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6997487633463417290414431 10496231450195125935621647)
              ·
                refine ⟨15744347175292688903432471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10496231450195125935621647 15744347175292688903432471)
                ·
                  refine ⟨23616520762939033355148707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15744347175292688903432471 23616520762939033355148707)
                  ·
                    refine ⟨35424781144408550032723061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23616520762939033355148707 35424781144408550032723061)
                    ·
                      refine ⟨3321073232288301565567787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35424781144408550032723061 3321073232288301565567787)
                      ·
                        rfl

theorem cell23_6467767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_6467767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467767 prefixEnd_6467767 := by exact prefixLift 6467767
  have htrace : WordTrace (prefixWord ++ tailWord_6467767) baseStart_6467767 baseEnd_6467767 := by
    simpa [prefixWord, tailWord_6467767, baseEnd_6467767] using wordTrace_append hprefix tailTrace_6467767
  have hstable : (prefixWord ++ tailWord_6467767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467767).length < 2 ^ (prefixWord ++ tailWord_6467767).sum := by decide
  have hdescent : baseEnd_6467767 < baseStart_6467767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467798 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_6467798 : Nat := 118140960795 + 6467798 * 2 ^ 59
def prefixEnd_6467798 : Nat := 4983230072969 + 3 ^ 40 * 6467798 * 2
def baseEnd_6467798 : Nat := 3321089150188590944280145

theorem tailTrace_6467798 : CollatzResearch.WordTrace tailWord_6467798 prefixEnd_6467798 3321089150188590944280145 := by
  unfold tailWord_6467798
  simp only [CollatzResearch.WordTrace]
  refine ⟨14743748313892495800053753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157266648681519955200573365 14743748313892495800053753)
  ·
    refine ⟨11057811235419371850040315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14743748313892495800053753 11057811235419371850040315)
    ·
      refine ⟨16586716853129057775060473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11057811235419371850040315 16586716853129057775060473)
      ·
        refine ⟨12440037639846793331295355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16586716853129057775060473 12440037639846793331295355)
        ·
          refine ⟨18660056459770189996943033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12440037639846793331295355 18660056459770189996943033)
          ·
            refine ⟨13995042344827642497707275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18660056459770189996943033 13995042344827642497707275)
            ·
              refine ⟨20992563517241463746560913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13995042344827642497707275 20992563517241463746560913)
              ·
                refine ⟨15744422637931097809920685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20992563517241463746560913 15744422637931097809920685)
                ·
                  refine ⟨5904158489224161678720257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15744422637931097809920685 5904158489224161678720257)
                  ·
                    refine ⟨4428118866918121259040193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5904158489224161678720257 4428118866918121259040193)
                    ·
                      refine ⟨3321089150188590944280145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4428118866918121259040193 3321089150188590944280145)
                      ·
                        rfl

theorem cell23_6467798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_6467798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467798 prefixEnd_6467798 := by exact prefixLift 6467798
  have htrace : WordTrace (prefixWord ++ tailWord_6467798) baseStart_6467798 baseEnd_6467798 := by
    simpa [prefixWord, tailWord_6467798, baseEnd_6467798] using wordTrace_append hprefix tailTrace_6467798
  have hstable : (prefixWord ++ tailWord_6467798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467798).length < 2 ^ (prefixWord ++ tailWord_6467798).sum := by decide
  have hdescent : baseEnd_6467798 < baseStart_6467798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467803 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 8]
def baseStart_6467803 : Nat := 118140960795 + 6467803 * 2 ^ 59
def prefixEnd_6467803 : Nat := 4983230072969 + 3 ^ 40 * 6467803 * 2
def baseEnd_6467803 : Nat := 3321091717591863424717621

theorem tailTrace_6467803 : CollatzResearch.WordTrace tailWord_6467803 prefixEnd_6467803 3321091717591863424717621 := by
  unfold tailWord_6467803
  simp only [CollatzResearch.WordTrace]
  refine ⟨235900155387261818654792063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157266770258174545769861375 235900155387261818654792063)
  ·
    refine ⟨353850233080892727982188095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235900155387261818654792063 353850233080892727982188095)
    ·
      refine ⟨530775349621339091973282143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353850233080892727982188095 530775349621339091973282143)
      ·
        refine ⟨796163024432008637959923215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530775349621339091973282143 796163024432008637959923215)
        ·
          refine ⟨1194244536648012956939884823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796163024432008637959923215 1194244536648012956939884823)
          ·
            refine ⟨1791366804972019435409827235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194244536648012956939884823 1791366804972019435409827235)
            ·
              refine ⟨2687050207458029153114740853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791366804972019435409827235 2687050207458029153114740853)
              ·
                refine ⟨251910956949190233104506955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2687050207458029153114740853 251910956949190233104506955)
                ·
                  refine ⟨377866435423785349656760433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251910956949190233104506955 377866435423785349656760433)
                  ·
                    refine ⟨283399826567839012242570325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 377866435423785349656760433 283399826567839012242570325)
                    ·
                      refine ⟨3321091717591863424717621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 283399826567839012242570325 3321091717591863424717621)
                      ·
                        rfl

theorem cell23_6467803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_6467803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467803 prefixEnd_6467803 := by exact prefixLift 6467803
  have htrace : WordTrace (prefixWord ++ tailWord_6467803) baseStart_6467803 baseEnd_6467803 := by
    simpa [prefixWord, tailWord_6467803, baseEnd_6467803] using wordTrace_append hprefix tailTrace_6467803
  have hstable : (prefixWord ++ tailWord_6467803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467803).length < 2 ^ (prefixWord ++ tailWord_6467803).sum := by decide
  have hdescent : baseEnd_6467803 < baseStart_6467803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467837 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 3, 4, 2]
def baseStart_6467837 : Nat := 118140960795 + 6467837 * 2 ^ 59
def prefixEnd_6467837 : Nat := 4983230072969 + 3 ^ 40 * 6467837 * 2
def baseEnd_6467837 : Nat := 3321109175934116291692465

theorem tailTrace_6467837 : CollatzResearch.WordTrace tailWord_6467837 prefixEnd_6467837 3321109175934116291692465 := by
  unfold tailWord_6467837
  simp only [CollatzResearch.WordTrace]
  refine ⟨235901395469138642461529765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157267596979425761641019843 235901395469138642461529765)
  ·
    refine ⟨44231511650463495461536831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235901395469138642461529765 44231511650463495461536831)
    ·
      refine ⟨66347267475695243192305247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44231511650463495461536831 66347267475695243192305247)
      ·
        refine ⟨99520901213542864788457871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66347267475695243192305247 99520901213542864788457871)
        ·
          refine ⟨149281351820314297182686807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99520901213542864788457871 149281351820314297182686807)
          ·
            refine ⟨223922027730471445774030211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149281351820314297182686807 223922027730471445774030211)
            ·
              refine ⟨335883041595707168661045317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223922027730471445774030211 335883041595707168661045317)
              ·
                refine ⟨62978070299195094123945997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335883041595707168661045317 62978070299195094123945997)
                ·
                  refine ⟨23616776362198160296479749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62978070299195094123945997 23616776362198160296479749)
                  ·
                    refine ⟨4428145567912155055589953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23616776362198160296479749 4428145567912155055589953)
                    ·
                      refine ⟨3321109175934116291692465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4428145567912155055589953 3321109175934116291692465)
                      ·
                        rfl

theorem cell23_6467837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_6467837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467837 prefixEnd_6467837 := by exact prefixLift 6467837
  have htrace : WordTrace (prefixWord ++ tailWord_6467837) baseStart_6467837 baseEnd_6467837 := by
    simpa [prefixWord, tailWord_6467837, baseEnd_6467837] using wordTrace_append hprefix tailTrace_6467837
  have hstable : (prefixWord ++ tailWord_6467837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467837).length < 2 ^ (prefixWord ++ tailWord_6467837).sum := by decide
  have hdescent : baseEnd_6467837 < baseStart_6467837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467840 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 3]
def baseStart_6467840 : Nat := 118140960795 + 6467840 * 2 ^ 59
def prefixEnd_6467840 : Nat := 4983230072969 + 3 ^ 40 * 6467840 * 2
def baseEnd_6467840 : Nat := 3321110716376079779954951

theorem tailTrace_6467840 : CollatzResearch.WordTrace tailWord_6467840 prefixEnd_6467840 3321110716376079779954951 := by
  unfold tailWord_6467840
  simp only [CollatzResearch.WordTrace]
  refine ⟨117950752444063886986944487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157267669925418515982592649 117950752444063886986944487)
  ·
    refine ⟨176926128666095830480416731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117950752444063886986944487 176926128666095830480416731)
    ·
      refine ⟨265389192999143745720625097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176926128666095830480416731 265389192999143745720625097)
      ·
        refine ⟨199041894749357809290468823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265389192999143745720625097 199041894749357809290468823)
        ·
          refine ⟨298562842124036713935703235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199041894749357809290468823 298562842124036713935703235)
          ·
            refine ⟨447844263186055070903554853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298562842124036713935703235 447844263186055070903554853)
            ·
              refine ⟨83970799347385325794416535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 447844263186055070903554853 83970799347385325794416535)
              ·
                refine ⟨125956199021077988691624803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83970799347385325794416535 125956199021077988691624803)
                ·
                  refine ⟨188934298531616983037437205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125956199021077988691624803 188934298531616983037437205)
                  ·
                    refine ⟨8856295243669546079879869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 188934298531616983037437205 8856295243669546079879869)
                    ·
                      refine ⟨3321110716376079779954951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8856295243669546079879869 3321110716376079779954951)
                      ·
                        rfl

theorem cell23_6467840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_6467840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467840 prefixEnd_6467840 := by exact prefixLift 6467840
  have htrace : WordTrace (prefixWord ++ tailWord_6467840) baseStart_6467840 baseEnd_6467840 := by
    simpa [prefixWord, tailWord_6467840, baseEnd_6467840] using wordTrace_append hprefix tailTrace_6467840
  have hstable : (prefixWord ++ tailWord_6467840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467840).length < 2 ^ (prefixWord ++ tailWord_6467840).sum := by decide
  have hdescent : baseEnd_6467840 < baseStart_6467840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467924 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_6467924 : Nat := 118140960795 + 6467924 * 2 ^ 59
def prefixEnd_6467924 : Nat := 4983230072969 + 3 ^ 40 * 6467924 * 2
def baseEnd_6467924 : Nat := 1107051282917019150434855

theorem tailTrace_6467924 : CollatzResearch.WordTrace tailWord_6467924 prefixEnd_6467924 1107051282917019150434855 := by
  unfold tailWord_6467924
  simp only [CollatzResearch.WordTrace]
  refine ⟨117952284309911728159973413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157269712413215637546631217 117952284309911728159973413)
  ·
    refine ⟨22116053308108449029995015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117952284309911728159973413 22116053308108449029995015)
    ·
      refine ⟨33174079962162673544992523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22116053308108449029995015 33174079962162673544992523)
      ·
        refine ⟨49761119943244010317488785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33174079962162673544992523 49761119943244010317488785)
        ·
          refine ⟨37320839957433007738116589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49761119943244010317488785 37320839957433007738116589)
          ·
            refine ⟨13995314984037377901793721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37320839957433007738116589 13995314984037377901793721)
            ·
              refine ⟨10496486238028033426345291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13995314984037377901793721 10496486238028033426345291)
              ·
                refine ⟨15744729357042050139517937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10496486238028033426345291 15744729357042050139517937)
                ·
                  refine ⟨11808547017781537604638453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15744729357042050139517937 11808547017781537604638453)
                  ·
                    refine ⟨1107051282917019150434855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11808547017781537604638453 1107051282917019150434855)
                    ·
                      rfl

theorem cell23_6467924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_6467924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467924 prefixEnd_6467924 := by exact prefixLift 6467924
  have htrace : WordTrace (prefixWord ++ tailWord_6467924) baseStart_6467924 baseEnd_6467924 := by
    simpa [prefixWord, tailWord_6467924, baseEnd_6467924] using wordTrace_append hprefix tailTrace_6467924
  have hstable : (prefixWord ++ tailWord_6467924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467924).length < 2 ^ (prefixWord ++ tailWord_6467924).sum := by decide
  have hdescent : baseEnd_6467924 < baseStart_6467924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467944 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_6467944 : Nat := 118140960795 + 6467944 * 2 ^ 59
def prefixEnd_6467944 : Nat := 4983230072969 + 3 ^ 40 * 6467944 * 2
def baseEnd_6467944 : Nat := 3321164118364147373054473

theorem tailTrace_6467944 : CollatzResearch.WordTrace tailWord_6467944 prefixEnd_6467944 3321164118364147373054473 := by
  unfold tailWord_6467944
  simp only [CollatzResearch.WordTrace]
  refine ⟨117952649039875499867837443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157270198719833999823783257 117952649039875499867837443)
  ·
    refine ⟨176928973559813249801756165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117952649039875499867837443 176928973559813249801756165)
    ·
      refine ⟨33174182542464984337829281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176928973559813249801756165 33174182542464984337829281)
      ·
        refine ⟨24880636906848738253371961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33174182542464984337829281 24880636906848738253371961)
        ·
          refine ⟨18660477680136553690028971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24880636906848738253371961 18660477680136553690028971)
          ·
            refine ⟨27990716520204830535043457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18660477680136553690028971 27990716520204830535043457)
            ·
              refine ⟨20993037390153622901282593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27990716520204830535043457 20993037390153622901282593)
              ·
                refine ⟨15744778042615217175961945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20993037390153622901282593 15744778042615217175961945)
                ·
                  refine ⟨11808583531961412881971459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15744778042615217175961945 11808583531961412881971459)
                  ·
                    refine ⟨17712875297942119322957189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11808583531961412881971459 17712875297942119322957189)
                    ·
                      refine ⟨3321164118364147373054473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17712875297942119322957189 3321164118364147373054473)
                      ·
                        rfl

theorem cell23_6467944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_6467944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467944 prefixEnd_6467944 := by exact prefixLift 6467944
  have htrace : WordTrace (prefixWord ++ tailWord_6467944) baseStart_6467944 baseEnd_6467944 := by
    simpa [prefixWord, tailWord_6467944, baseEnd_6467944] using wordTrace_append hprefix tailTrace_6467944
  have hstable : (prefixWord ++ tailWord_6467944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467944).length < 2 ^ (prefixWord ++ tailWord_6467944).sum := by decide
  have hdescent : baseEnd_6467944 < baseStart_6467944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6467978 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 2, 1, 4]
def baseStart_6467978 : Nat := 118140960795 + 6467978 * 2 ^ 59
def prefixEnd_6467978 : Nat := 4983230072969 + 3 ^ 40 * 6467978 * 2
def baseEnd_6467978 : Nat := 3321181576706400240029317

theorem tailTrace_6467978 : CollatzResearch.WordTrace tailWord_6467978 prefixEnd_6467978 3321181576706400240029317 := by
  unfold tailWord_6467978
  simp only [CollatzResearch.WordTrace]
  refine ⟨58976634540406955885603147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157271025441085215694941725 58976634540406955885603147)
  ·
    refine ⟨88464951810610433828404721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58976634540406955885603147 88464951810610433828404721)
    ·
      refine ⟨66348713857957825371303541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88464951810610433828404721 66348713857957825371303541)
      ·
        refine ⟨6220191924183546128559707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66348713857957825371303541 6220191924183546128559707)
        ·
          refine ⟨9330287886275319192839561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6220191924183546128559707 9330287886275319192839561)
          ·
            refine ⟨6997715914706489394629671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9330287886275319192839561 6997715914706489394629671)
            ·
              refine ⟨10496573872059734091944507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6997715914706489394629671 10496573872059734091944507)
              ·
                refine ⟨15744860808089601137916761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10496573872059734091944507 15744860808089601137916761)
                ·
                  refine ⟨11808645606067200853437571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15744860808089601137916761 11808645606067200853437571)
                  ·
                    refine ⟨17712968409100801280156357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11808645606067200853437571 17712968409100801280156357)
                    ·
                      refine ⟨3321181576706400240029317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17712968409100801280156357 3321181576706400240029317)
                      ·
                        rfl

theorem cell23_6467978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_6467978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6467978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6467978 prefixEnd_6467978 := by exact prefixLift 6467978
  have htrace : WordTrace (prefixWord ++ tailWord_6467978) baseStart_6467978 baseEnd_6467978 := by
    simpa [prefixWord, tailWord_6467978, baseEnd_6467978] using wordTrace_append hprefix tailTrace_6467978
  have hstable : (prefixWord ++ tailWord_6467978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6467978).length < 2 ^ (prefixWord ++ tailWord_6467978).sum := by decide
  have hdescent : baseEnd_6467978 < baseStart_6467978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6467978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468037 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 4, 6, 3]
def baseStart_6468037 : Nat := 118140960795 + 6468037 * 2 ^ 59
def prefixEnd_6468037 : Nat := 4983230072969 + 3 ^ 40 * 6468037 * 2
def baseEnd_6468037 : Nat := 3321211872065015509191545

theorem tailTrace_6468037 : CollatzResearch.WordTrace tailWord_6468037 prefixEnd_6468037 3321211872065015509191545 := by
  unfold tailWord_6468037
  simp only [CollatzResearch.WordTrace]
  refine ⟨235908690068414076618810365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157272460045609384412540243 235908690068414076618810365)
  ·
    refine ⟨88465758775655278732053887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235908690068414076618810365 88465758775655278732053887)
    ·
      refine ⟨132698638163482918098080831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88465758775655278732053887 132698638163482918098080831)
      ·
        refine ⟨199047957245224377147121247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132698638163482918098080831 199047957245224377147121247)
        ·
          refine ⟨298571935867836565720681871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199047957245224377147121247 298571935867836565720681871)
          ·
            refine ⟨447857903801754848581022807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298571935867836565720681871 447857903801754848581022807)
            ·
              refine ⟨671786855702632272871534211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447857903801754848581022807 671786855702632272871534211)
              ·
                refine ⟨1007680283553948409307301317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671786855702632272871534211 1007680283553948409307301317)
                ·
                  refine ⟨188940053166365326745118997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1007680283553948409307301317 188940053166365326745118997)
                  ·
                    refine ⟨8856564992173374691177453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 188940053166365326745118997 8856564992173374691177453)
                    ·
                      refine ⟨3321211872065015509191545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8856564992173374691177453 3321211872065015509191545)
                      ·
                        rfl

theorem cell23_6468037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_6468037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468037 prefixEnd_6468037 := by exact prefixLift 6468037
  have htrace : WordTrace (prefixWord ++ tailWord_6468037) baseStart_6468037 baseEnd_6468037 := by
    simpa [prefixWord, tailWord_6468037, baseEnd_6468037] using wordTrace_append hprefix tailTrace_6468037
  have hstable : (prefixWord ++ tailWord_6468037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468037).length < 2 ^ (prefixWord ++ tailWord_6468037).sum := by decide
  have hdescent : baseEnd_6468037 < baseStart_6468037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468047 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 4]
def baseStart_6468047 : Nat := 118140960795 + 6468047 * 2 ^ 59
def prefixEnd_6468047 : Nat := 4983230072969 + 3 ^ 40 * 6468047 * 2
def baseEnd_6468047 : Nat := 3321217006871560470066499

theorem tailTrace_6468047 : CollatzResearch.WordTrace tailWord_6468047 prefixEnd_6468047 3321217006871560470066499 := by
  unfold tailWord_6468047
  simp only [CollatzResearch.WordTrace]
  refine ⟨235909054798377848326674395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157272703198918565551116263 235909054798377848326674395)
  ·
    refine ⟨353863582197566772490011593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235909054798377848326674395 353863582197566772490011593)
    ·
      refine ⟨265397686648175079367508695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353863582197566772490011593 265397686648175079367508695)
      ·
        refine ⟨398096529972262619051263043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265397686648175079367508695 398096529972262619051263043)
        ·
          refine ⟨597144794958393928576894565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398096529972262619051263043 597144794958393928576894565)
          ·
            refine ⟨111964649054698861608167731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 597144794958393928576894565 111964649054698861608167731)
            ·
              refine ⟨167946973582048292412251597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111964649054698861608167731 167946973582048292412251597)
              ·
                refine ⟨62980115093268109654594349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167946973582048292412251597 62980115093268109654594349)
                ·
                  refine ⟨23617543159975541120472881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62980115093268109654594349 23617543159975541120472881)
                  ·
                    refine ⟨17713157369981655840354661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23617543159975541120472881 17713157369981655840354661)
                    ·
                      refine ⟨3321217006871560470066499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17713157369981655840354661 3321217006871560470066499)
                      ·
                        rfl

theorem cell23_6468047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_6468047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468047 prefixEnd_6468047 := by exact prefixLift 6468047
  have htrace : WordTrace (prefixWord ++ tailWord_6468047) baseStart_6468047 baseEnd_6468047 := by
    simpa [prefixWord, tailWord_6468047, baseEnd_6468047] using wordTrace_append hprefix tailTrace_6468047
  have hstable : (prefixWord ++ tailWord_6468047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468047).length < 2 ^ (prefixWord ++ tailWord_6468047).sum := by decide
  have hdescent : baseEnd_6468047 < baseStart_6468047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468061 : List Nat := [1, 4, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_6468061 : Nat := 118140960795 + 6468061 * 2 ^ 59
def prefixEnd_6468061 : Nat := 4983230072969 + 3 ^ 40 * 6468061 * 2
def baseEnd_6468061 : Nat := 1107074731866907805097145

theorem tailTrace_6468061 : CollatzResearch.WordTrace tailWord_6468061 prefixEnd_6468061 1107074731866907805097145 := by
  unfold tailWord_6468061
  simp only [CollatzResearch.WordTrace]
  refine ⟨235909565420327128717684037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157273043613551419145122691 235909565420327128717684037)
  ·
    refine ⟨44233043516311336634565757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235909565420327128717684037 44233043516311336634565757)
    ·
      refine ⟨16587391318616751237962159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44233043516311336634565757 16587391318616751237962159)
      ·
        refine ⟨24881086977925126856943239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16587391318616751237962159 24881086977925126856943239)
        ·
          refine ⟨37321630466887690285414859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24881086977925126856943239 37321630466887690285414859)
          ·
            refine ⟨55982445700331535428122289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37321630466887690285414859 55982445700331535428122289)
            ·
              refine ⟨41986834275248651571091717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55982445700331535428122289 41986834275248651571091717)
              ·
                refine ⟨7872531426609122169579697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41986834275248651571091717 7872531426609122169579697)
                ·
                  refine ⟨5904398569956841627184773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7872531426609122169579697 5904398569956841627184773)
                  ·
                    refine ⟨1107074731866907805097145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5904398569956841627184773 1107074731866907805097145)
                    ·
                      rfl

theorem cell23_6468061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_6468061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468061 prefixEnd_6468061 := by exact prefixLift 6468061
  have htrace : WordTrace (prefixWord ++ tailWord_6468061) baseStart_6468061 baseEnd_6468061 := by
    simpa [prefixWord, tailWord_6468061, baseEnd_6468061] using wordTrace_append hprefix tailTrace_6468061
  have hstable : (prefixWord ++ tailWord_6468061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468061).length < 2 ^ (prefixWord ++ tailWord_6468061).sum := by decide
  have hdescent : baseEnd_6468061 < baseStart_6468061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468074 : List Nat := [3, 1, 3, 1, 3, 2, 2, 8]
def baseStart_6468074 : Nat := 118140960795 + 6468074 * 2 ^ 59
def prefixEnd_6468074 : Nat := 4983230072969 + 3 ^ 40 * 6468074 * 2
def baseEnd_6468074 : Nat := 123008550772193772756625

theorem tailTrace_6468074 : CollatzResearch.WordTrace tailWord_6468074 prefixEnd_6468074 123008550772193772756625 := by
  unfold tailWord_6468074
  simp only [CollatzResearch.WordTrace]
  refine ⟨58977509892320007984476819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157273359712853354625271517 58977509892320007984476819)
  ·
    refine ⟨88466264838480011976715229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58977509892320007984476819 88466264838480011976715229)
    ·
      refine ⟨33174849314430004491268211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88466264838480011976715229 33174849314430004491268211)
      ·
        refine ⟨49762273971645006736902317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33174849314430004491268211 49762273971645006736902317)
        ·
          refine ⟨18660852739366877526338369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49762273971645006736902317 18660852739366877526338369)
          ·
            refine ⟨13995639554525158144753777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18660852739366877526338369 13995639554525158144753777)
            ·
              refine ⟨10496729665893868608565333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13995639554525158144753777 10496729665893868608565333)
              ·
                refine ⟨123008550772193772756625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10496729665893868608565333 123008550772193772756625)
                ·
                  rfl

theorem cell23_6468074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 8].length) (baseStart_6468074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468074 prefixEnd_6468074 := by exact prefixLift 6468074
  have htrace : WordTrace (prefixWord ++ tailWord_6468074) baseStart_6468074 baseEnd_6468074 := by
    simpa [prefixWord, tailWord_6468074, baseEnd_6468074] using wordTrace_append hprefix tailTrace_6468074
  have hstable : (prefixWord ++ tailWord_6468074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468074).length < 2 ^ (prefixWord ++ tailWord_6468074).sum := by decide
  have hdescent : baseEnd_6468074 < baseStart_6468074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468078 : List Nat := [4, 1, 2, 1, 2, 2, 4, 1, 2, 4]
def baseStart_6468078 : Nat := 118140960795 + 6468078 * 2 ^ 59
def prefixEnd_6468078 : Nat := 4983230072969 + 3 ^ 40 * 6468078 * 2
def baseEnd_6468078 : Nat := 1107077641590616616259619

theorem tailTrace_6468078 : CollatzResearch.WordTrace tailWord_6468078 prefixEnd_6468078 1107077641590616616259619 := by
  unfold tailWord_6468078
  simp only [CollatzResearch.WordTrace]
  refine ⟨29488773182658192577631611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157273456974177027080701925 29488773182658192577631611)
  ·
    refine ⟨44233159773987288866447417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29488773182658192577631611 44233159773987288866447417)
    ·
      refine ⟨33174869830490466649835563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44233159773987288866447417 33174869830490466649835563)
      ·
        refine ⟨49762304745735699974753345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33174869830490466649835563 49762304745735699974753345)
        ·
          refine ⟨37321728559301774981065009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49762304745735699974753345 37321728559301774981065009)
          ·
            refine ⟨27991296419476331235798757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37321728559301774981065009 27991296419476331235798757)
            ·
              refine ⟨5248368078651812106712267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27991296419476331235798757 5248368078651812106712267)
              ·
                refine ⟨7872552117977718160068401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5248368078651812106712267 7872552117977718160068401)
                ·
                  refine ⟨5904414088483288620051301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7872552117977718160068401 5904414088483288620051301)
                  ·
                    refine ⟨1107077641590616616259619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5904414088483288620051301 1107077641590616616259619)
                    ·
                      rfl

theorem cell23_6468078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_6468078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468078 prefixEnd_6468078 := by exact prefixLift 6468078
  have htrace : WordTrace (prefixWord ++ tailWord_6468078) baseStart_6468078 baseEnd_6468078 := by
    simpa [prefixWord, tailWord_6468078, baseEnd_6468078] using wordTrace_append hprefix tailTrace_6468078
  have hstable : (prefixWord ++ tailWord_6468078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468078).length < 2 ^ (prefixWord ++ tailWord_6468078).sum := by decide
  have hdescent : baseEnd_6468078 < baseStart_6468078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468085 : List Nat := [1, 3, 5, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_6468085 : Nat := 118140960795 + 6468085 * 2 ^ 59
def prefixEnd_6468085 : Nat := 4983230072969 + 3 ^ 40 * 6468085 * 2
def baseEnd_6468085 : Nat := 3321236519136431321391325

theorem tailTrace_6468085 : CollatzResearch.WordTrace tailWord_6468085 prefixEnd_6468085 3321236519136431321391325 := by
  unfold tailWord_6468085
  simp only [CollatzResearch.WordTrace]
  refine ⟨235910440772240180816557709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157273627181493453877705139 235910440772240180816557709)
  ·
    refine ⟨88466415289590067806209141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235910440772240180816557709 88466415289590067806209141)
    ·
      refine ⟨8293726433399068856832107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88466415289590067806209141 8293726433399068856832107)
      ·
        refine ⟨12440589650098603285248161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8293726433399068856832107 12440589650098603285248161)
        ·
          refine ⟨9330442237573952463936121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12440589650098603285248161 9330442237573952463936121)
          ·
            refine ⟨6997831678180464347952091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9330442237573952463936121 6997831678180464347952091)
            ·
              refine ⟨10496747517270696521928137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6997831678180464347952091 10496747517270696521928137)
              ·
                refine ⟨7872560637953022391446103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10496747517270696521928137 7872560637953022391446103)
                ·
                  refine ⟨11808840956929533587169155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7872560637953022391446103 11808840956929533587169155)
                  ·
                    refine ⟨17713261435394300380753733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11808840956929533587169155 17713261435394300380753733)
                    ·
                      refine ⟨3321236519136431321391325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17713261435394300380753733 3321236519136431321391325)
                      ·
                        rfl

theorem cell23_6468085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_6468085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468085 prefixEnd_6468085 := by exact prefixLift 6468085
  have htrace : WordTrace (prefixWord ++ tailWord_6468085) baseStart_6468085 baseEnd_6468085 := by
    simpa [prefixWord, tailWord_6468085, baseEnd_6468085] using wordTrace_append hprefix tailTrace_6468085
  have hstable : (prefixWord ++ tailWord_6468085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468085).length < 2 ^ (prefixWord ++ tailWord_6468085).sum := by decide
  have hdescent : baseEnd_6468085 < baseStart_6468085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468098 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_6468098 : Nat := 118140960795 + 6468098 * 2 ^ 59
def prefixEnd_6468098 : Nat := 4983230072969 + 3 ^ 40 * 6468098 * 2
def baseEnd_6468098 : Nat := 3321243194384939770528765

theorem tailTrace_6468098 : CollatzResearch.WordTrace tailWord_6468098 prefixEnd_6468098 3321243194384939770528765 := by
  unfold tailWord_6468098
  simp only [CollatzResearch.WordTrace]
  refine ⟨58977728730298271009195237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157273943280795389357853965 58977728730298271009195237)
  ·
    refine ⟨11058324136930925814224107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58977728730298271009195237 11058324136930925814224107)
    ·
      refine ⟨16587486205396388721336161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11058324136930925814224107 16587486205396388721336161)
      ·
        refine ⟨12440614654047291541002121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16587486205396388721336161 12440614654047291541002121)
        ·
          refine ⟨9330460990535468655751591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12440614654047291541002121 9330460990535468655751591)
          ·
            refine ⟨13995691485803202983627387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9330460990535468655751591 13995691485803202983627387)
            ·
              refine ⟨20993537228704804475441081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13995691485803202983627387 20993537228704804475441081)
              ·
                refine ⟨15745152921528603356580811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20993537228704804475441081 15745152921528603356580811)
                ·
                  refine ⟨23617729382292905034871217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15745152921528603356580811 23617729382292905034871217)
                  ·
                    refine ⟨17713297036719678776153413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23617729382292905034871217 17713297036719678776153413)
                    ·
                      refine ⟨3321243194384939770528765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17713297036719678776153413 3321243194384939770528765)
                      ·
                        rfl

theorem cell23_6468098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_6468098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468098 prefixEnd_6468098 := by exact prefixLift 6468098
  have htrace : WordTrace (prefixWord ++ tailWord_6468098) baseStart_6468098 baseEnd_6468098 := by
    simpa [prefixWord, tailWord_6468098, baseEnd_6468098] using wordTrace_append hprefix tailTrace_6468098
  have hstable : (prefixWord ++ tailWord_6468098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468098).length < 2 ^ (prefixWord ++ tailWord_6468098).sum := by decide
  have hdescent : baseEnd_6468098 < baseStart_6468098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468124 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_6468124 : Nat := 118140960795 + 6468124 * 2 ^ 59
def prefixEnd_6468124 : Nat := 4983230072969 + 3 ^ 40 * 6468124 * 2
def baseEnd_6468124 : Nat := 3321256544881956668803645

theorem tailTrace_6468124 : CollatzResearch.WordTrace tailWord_6468124 prefixEnd_6468124 3321256544881956668803645 := by
  unfold tailWord_6468124
  simp only [CollatzResearch.WordTrace]
  refine ⟨117955931609549445238613713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157274575479399260318151617 117955931609549445238613713)
  ·
    refine ⟨88466948707162083928960285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117955931609549445238613713 88466948707162083928960285)
    ·
      refine ⟨33175105765185781473360107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88466948707162083928960285 33175105765185781473360107)
      ·
        refine ⟨49762658647778672210040161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33175105765185781473360107 49762658647778672210040161)
        ·
          refine ⟨37321993985834004157530121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49762658647778672210040161 37321993985834004157530121)
          ·
            refine ⟨27991495489375503118147591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37321993985834004157530121 27991495489375503118147591)
            ·
              refine ⟨41987243234063254677221387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27991495489375503118147591 41987243234063254677221387)
              ·
                refine ⟨62980864851094882015832081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41987243234063254677221387 62980864851094882015832081)
                ·
                  refine ⟨47235648638321161511874061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62980864851094882015832081 47235648638321161511874061)
                  ·
                    refine ⟨17713368239370435566952773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47235648638321161511874061 17713368239370435566952773)
                    ·
                      refine ⟨3321256544881956668803645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17713368239370435566952773 3321256544881956668803645)
                      ·
                        rfl

theorem cell23_6468124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_6468124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468124 prefixEnd_6468124 := by exact prefixLift 6468124
  have htrace : WordTrace (prefixWord ++ tailWord_6468124) baseStart_6468124 baseEnd_6468124 := by
    simpa [prefixWord, tailWord_6468124, baseEnd_6468124] using wordTrace_append hprefix tailTrace_6468124
  have hstable : (prefixWord ++ tailWord_6468124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468124).length < 2 ^ (prefixWord ++ tailWord_6468124).sum := by decide
  have hdescent : baseEnd_6468124 < baseStart_6468124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468135 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_6468135 : Nat := 118140960795 + 6468135 * 2 ^ 59
def prefixEnd_6468135 : Nat := 4983230072969 + 3 ^ 40 * 6468135 * 2
def baseEnd_6468135 : Nat := 3321262193169156125766095

theorem tailTrace_6468135 : CollatzResearch.WordTrace tailWord_6468135 prefixEnd_6468135 3321262193169156125766095 := by
  unfold tailWord_6468135
  simp only [CollatzResearch.WordTrace]
  refine ⟨235912264422059039355877859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157274842948039359570585239 235912264422059039355877859)
  ·
    refine ⟨353868396633088559033816789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235912264422059039355877859 353868396633088559033816789)
    ·
      refine ⟨8293790546088013102355081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 353868396633088559033816789 8293790546088013102355081)
      ·
        refine ⟨6220342909566009826766311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8293790546088013102355081 6220342909566009826766311)
        ·
          refine ⟨9330514364349014740149467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6220342909566009826766311 9330514364349014740149467)
          ·
            refine ⟨13995771546523522110224201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9330514364349014740149467 13995771546523522110224201)
            ·
              refine ⟨10496828659892641582668151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13995771546523522110224201 10496828659892641582668151)
              ·
                refine ⟨15745242989838962374002227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10496828659892641582668151 15745242989838962374002227)
                ·
                  refine ⟨23617864484758443561003341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15745242989838962374002227 23617864484758443561003341)
                  ·
                    refine ⟨8856699181784416335376253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23617864484758443561003341 8856699181784416335376253)
                    ·
                      refine ⟨3321262193169156125766095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8856699181784416335376253 3321262193169156125766095)
                      ·
                        rfl

theorem cell23_6468135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_6468135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468135 prefixEnd_6468135 := by exact prefixLift 6468135
  have htrace : WordTrace (prefixWord ++ tailWord_6468135) baseStart_6468135 baseEnd_6468135 := by
    simpa [prefixWord, tailWord_6468135, baseEnd_6468135] using wordTrace_append hprefix tailTrace_6468135
  have hstable : (prefixWord ++ tailWord_6468135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468135).length < 2 ^ (prefixWord ++ tailWord_6468135).sum := by decide
  have hdescent : baseEnd_6468135 < baseStart_6468135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468181 : List Nat := [1, 3, 2, 2, 1, 1, 4, 4, 5]
def baseStart_6468181 : Nat := 118140960795 + 6468181 * 2 ^ 59
def prefixEnd_6468181 : Nat := 4983230072969 + 3 ^ 40 * 6468181 * 2
def baseEnd_6468181 : Nat := 369031757031029216198987

theorem tailTrace_6468181 : CollatzResearch.WordTrace tailWord_6468181 prefixEnd_6468181 369031757031029216198987 := by
  unfold tailWord_6468181
  simp only [CollatzResearch.WordTrace]
  refine ⟨235913942179892389212052397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157275961453261592808034931 235913942179892389212052397)
  ·
    refine ⟨88467728317459645954519649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235913942179892389212052397 88467728317459645954519649)
    ·
      refine ⟨66350796238094734465889737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88467728317459645954519649 66350796238094734465889737)
      ·
        refine ⟨49763097178571050849417303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66350796238094734465889737 49763097178571050849417303)
        ·
          refine ⟨74644645767856576274125955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49763097178571050849417303 74644645767856576274125955)
          ·
            refine ⟨111966968651784864411188933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74644645767856576274125955 111966968651784864411188933)
            ·
              refine ⟨20993806622209662077097925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111966968651784864411188933 20993806622209662077097925)
              ·
                refine ⟨3936338741664311639455861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20993806622209662077097925 3936338741664311639455861)
                ·
                  refine ⟨369031757031029216198987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3936338741664311639455861 369031757031029216198987)
                  ·
                    rfl

theorem cell23_6468181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 5].length) (baseStart_6468181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468181 prefixEnd_6468181 := by exact prefixLift 6468181
  have htrace : WordTrace (prefixWord ++ tailWord_6468181) baseStart_6468181 baseEnd_6468181 := by
    simpa [prefixWord, tailWord_6468181, baseEnd_6468181] using wordTrace_append hprefix tailTrace_6468181
  have hstable : (prefixWord ++ tailWord_6468181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468181).length < 2 ^ (prefixWord ++ tailWord_6468181).sum := by decide
  have hdescent : baseEnd_6468181 < baseStart_6468181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468231 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_6468231 : Nat := 118140960795 + 6468231 * 2 ^ 59
def prefixEnd_6468231 : Nat := 4983230072969 + 3 ^ 40 * 6468231 * 2
def baseEnd_6468231 : Nat := 3321311487311987750165653

theorem tailTrace_6468231 : CollatzResearch.WordTrace tailWord_6468231 prefixEnd_6468231 3321311487311987750165653 := by
  unfold tailWord_6468231
  simp only [CollatzResearch.WordTrace]
  refine ⟨235915765829711247751372547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157277177219807498500915031 235915765829711247751372547)
  ·
    refine ⟨353873648744566871627058821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235915765829711247751372547 353873648744566871627058821)
    ·
      refine ⟨66351309139606288430073529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353873648744566871627058821 66351309139606288430073529)
      ·
        refine ⟨49763481854704716322555147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66351309139606288430073529 49763481854704716322555147)
        ·
          refine ⟨74645222782057074483832721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49763481854704716322555147 74645222782057074483832721)
          ·
            refine ⟨55983917086542805862874541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74645222782057074483832721 55983917086542805862874541)
            ·
              refine ⟨20993968907453552198577953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55983917086542805862874541 20993968907453552198577953)
              ·
                refine ⟨15745476680590164148933465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20993968907453552198577953 15745476680590164148933465)
                ·
                  refine ⟨11809107510442623111700099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15745476680590164148933465 11809107510442623111700099)
                  ·
                    refine ⟨17713661265663934667550149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11809107510442623111700099 17713661265663934667550149)
                    ·
                      refine ⟨3321311487311987750165653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17713661265663934667550149 3321311487311987750165653)
                      ·
                        rfl

theorem cell23_6468231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_6468231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468231 prefixEnd_6468231 := by exact prefixLift 6468231
  have htrace : WordTrace (prefixWord ++ tailWord_6468231) baseStart_6468231 baseEnd_6468231 := by
    simpa [prefixWord, tailWord_6468231, baseEnd_6468231] using wordTrace_append hprefix tailTrace_6468231
  have hstable : (prefixWord ++ tailWord_6468231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468231).length < 2 ^ (prefixWord ++ tailWord_6468231).sum := by decide
  have hdescent : baseEnd_6468231 < baseStart_6468231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468274 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_6468274 : Nat := 118140960795 + 6468274 * 2 ^ 59
def prefixEnd_6468274 : Nat := 4983230072969 + 3 ^ 40 * 6468274 * 2
def baseEnd_6468274 : Nat := 3321333566980131081927955

theorem tailTrace_6468274 : CollatzResearch.WordTrace tailWord_6468274 prefixEnd_6468274 3321333566980131081927955 := by
  unfold tailWord_6468274
  simp only [CollatzResearch.WordTrace]
  refine ⟨58979333542138866523796969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157278222779036977396791917 58979333542138866523796969)
  ·
    refine ⟨44234500156604149892847727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58979333542138866523796969 44234500156604149892847727)
    ·
      refine ⟨66351750234906224839271591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44234500156604149892847727 66351750234906224839271591)
      ·
        refine ⟨99527625352359337258907387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66351750234906224839271591 99527625352359337258907387)
        ·
          refine ⟨149291438028539005888361081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99527625352359337258907387 149291438028539005888361081)
          ·
            refine ⟨111968578521404254416270811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149291438028539005888361081 111968578521404254416270811)
            ·
              refine ⟨167952867782106381624406217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111968578521404254416270811 167952867782106381624406217)
              ·
                refine ⟨125964650836579786218304663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167952867782106381624406217 125964650836579786218304663)
                ·
                  refine ⟨188946976254869679327456995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125964650836579786218304663 188946976254869679327456995)
                  ·
                    refine ⟨283420464382304518991185493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188946976254869679327456995 283420464382304518991185493)
                    ·
                      refine ⟨3321333566980131081927955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 283420464382304518991185493 3321333566980131081927955)
                      ·
                        rfl

theorem cell23_6468274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_6468274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468274 prefixEnd_6468274 := by exact prefixLift 6468274
  have htrace : WordTrace (prefixWord ++ tailWord_6468274) baseStart_6468274 baseEnd_6468274 := by
    simpa [prefixWord, tailWord_6468274, baseEnd_6468274] using wordTrace_append hprefix tailTrace_6468274
  have hstable : (prefixWord ++ tailWord_6468274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468274).length < 2 ^ (prefixWord ++ tailWord_6468274).sum := by decide
  have hdescent : baseEnd_6468274 < baseStart_6468274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468292 : List Nat := [2, 3, 3, 1, 1, 2, 4, 2, 1, 4]
def baseStart_6468292 : Nat := 118140960795 + 6468292 * 2 ^ 59
def prefixEnd_6468292 : Nat := 4983230072969 + 3 ^ 40 * 6468292 * 2
def baseEnd_6468292 : Nat := 1107114269877304003834291

theorem tailTrace_6468292 : CollatzResearch.WordTrace tailWord_6468292 prefixEnd_6468292 1107114269877304003834291 := by
  unfold tailWord_6468292
  simp only [CollatzResearch.WordTrace]
  refine ⟨117958995341245127584671565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157278660454993503446228753 117958995341245127584671565)
  ·
    refine ⟨44234623252966922844251837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117958995341245127584671565 44234623252966922844251837)
    ·
      refine ⟨16587983719862596066594439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44234623252966922844251837 16587983719862596066594439)
      ·
        refine ⟨24881975579793894099891659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16587983719862596066594439 24881975579793894099891659)
        ·
          refine ⟨37322963369690841149837489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24881975579793894099891659 37322963369690841149837489)
          ·
            refine ⟨27992222527268130862378117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37322963369690841149837489 27992222527268130862378117)
            ·
              refine ⟨5248541723862774536695897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27992222527268130862378117 5248541723862774536695897)
              ·
                refine ⟨3936406292897080902521923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5248541723862774536695897 3936406292897080902521923)
                ·
                  refine ⟨5904609439345621353782885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3936406292897080902521923 5904609439345621353782885)
                  ·
                    refine ⟨1107114269877304003834291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5904609439345621353782885 1107114269877304003834291)
                    ·
                      rfl

theorem cell23_6468292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_6468292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468292 prefixEnd_6468292 := by exact prefixLift 6468292
  have htrace : WordTrace (prefixWord ++ tailWord_6468292) baseStart_6468292 baseEnd_6468292 := by
    simpa [prefixWord, tailWord_6468292, baseEnd_6468292] using wordTrace_append hprefix tailTrace_6468292
  have hstable : (prefixWord ++ tailWord_6468292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468292).length < 2 ^ (prefixWord ++ tailWord_6468292).sum := by decide
  have hdescent : baseEnd_6468292 < baseStart_6468292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468325 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 2, 3, 2]
def baseStart_6468325 : Nat := 118140960795 + 6468325 * 2 ^ 59
def prefixEnd_6468325 : Nat := 4983230072969 + 3 ^ 40 * 6468325 * 2
def baseEnd_6468325 : Nat := 3321359754493510382390221

theorem tailTrace_6468325 : CollatzResearch.WordTrace tailWord_6468325 prefixEnd_6468325 3321359754493510382390221 := by
  unfold tailWord_6468325
  simp only [CollatzResearch.WordTrace]
  refine ⟨235919194291370701805294429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157279462860913801203529619 235919194291370701805294429)
  ·
    refine ⟨88469697859264013176985411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235919194291370701805294429 88469697859264013176985411)
    ·
      refine ⟨132704546788896019765478117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88469697859264013176985411 132704546788896019765478117)
      ·
        refine ⟨24882102522918003706027147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132704546788896019765478117 24882102522918003706027147)
        ·
          refine ⟨37323153784377005559040721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24882102522918003706027147 37323153784377005559040721)
          ·
            refine ⟨27992365338282754169280541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37323153784377005559040721 27992365338282754169280541)
            ·
              refine ⟨10497137001856032813480203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27992365338282754169280541 10497137001856032813480203)
              ·
                refine ⟨15745705502784049220220305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10497137001856032813480203 15745705502784049220220305)
                ·
                  refine ⟨11809279127088036915165229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15745705502784049220220305 11809279127088036915165229)
                  ·
                    refine ⟨4428479672658013843186961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11809279127088036915165229 4428479672658013843186961)
                    ·
                      refine ⟨3321359754493510382390221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4428479672658013843186961 3321359754493510382390221)
                      ·
                        rfl

theorem cell23_6468325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_6468325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468325 prefixEnd_6468325 := by exact prefixLift 6468325
  have htrace : WordTrace (prefixWord ++ tailWord_6468325) baseStart_6468325 baseEnd_6468325 := by
    simpa [prefixWord, tailWord_6468325, baseEnd_6468325] using wordTrace_append hprefix tailTrace_6468325
  have hstable : (prefixWord ++ tailWord_6468325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468325).length < 2 ^ (prefixWord ++ tailWord_6468325).sum := by decide
  have hdescent : baseEnd_6468325 < baseStart_6468325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468331 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 4, 4]
def baseStart_6468331 : Nat := 118140960795 + 6468331 * 2 ^ 59
def prefixEnd_6468331 : Nat := 4983230072969 + 3 ^ 40 * 6468331 * 2
def baseEnd_6468331 : Nat := 1107120945125812452971731

theorem tailTrace_6468331 : CollatzResearch.WordTrace tailWord_6468331 prefixEnd_6468331 1107120945125812452971731 := by
  unfold tailWord_6468331
  simp only [CollatzResearch.WordTrace]
  refine ⟨235919413129348964830012847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157279608752899309886675231 235919413129348964830012847)
  ·
    refine ⟨353879119694023447245019271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235919413129348964830012847 353879119694023447245019271)
    ·
      refine ⟨530818679541035170867528907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353879119694023447245019271 530818679541035170867528907)
      ·
        refine ⟨796228019311552756301293361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530818679541035170867528907 796228019311552756301293361)
        ·
          refine ⟨597171014483664567225970021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 796228019311552756301293361 597171014483664567225970021)
          ·
            refine ⟨111969565215687106354869379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 597171014483664567225970021 111969565215687106354869379)
            ·
              refine ⟨167954347823530659532304069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111969565215687106354869379 167954347823530659532304069)
              ·
                refine ⟨31491440216911998662307013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167954347823530659532304069 31491440216911998662307013)
                ·
                  refine ⟨5904645040670999749182565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31491440216911998662307013 5904645040670999749182565)
                  ·
                    refine ⟨1107120945125812452971731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5904645040670999749182565 1107120945125812452971731)
                    ·
                      rfl

theorem cell23_6468331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 4].length) (baseStart_6468331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468331 prefixEnd_6468331 := by exact prefixLift 6468331
  have htrace : WordTrace (prefixWord ++ tailWord_6468331) baseStart_6468331 baseEnd_6468331 := by
    simpa [prefixWord, tailWord_6468331, baseEnd_6468331] using wordTrace_append hprefix tailTrace_6468331
  have hstable : (prefixWord ++ tailWord_6468331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468331).length < 2 ^ (prefixWord ++ tailWord_6468331).sum := by decide
  have hdescent : baseEnd_6468331 < baseStart_6468331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468335 : List Nat := [1, 1, 2, 1, 5, 4, 2, 1, 1, 5]
def baseStart_6468335 : Nat := 118140960795 + 6468335 * 2 ^ 59
def prefixEnd_6468335 : Nat := 4983230072969 + 3 ^ 40 * 6468335 * 2
def baseEnd_6468335 : Nat := 1107121629766685114421725

theorem tailTrace_6468335 : CollatzResearch.WordTrace tailWord_6468335 prefixEnd_6468335 1107121629766685114421725 := by
  unfold tailWord_6468335
  simp only [CollatzResearch.WordTrace]
  refine ⟨235919559021334473513158459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157279706014222982342105639 235919559021334473513158459)
  ·
    refine ⟨353879338532001710269737689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235919559021334473513158459 353879338532001710269737689)
    ·
      refine ⟨265409503899001282702303267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353879338532001710269737689 265409503899001282702303267)
      ·
        refine ⟨398114255848501924053454901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265409503899001282702303267 398114255848501924053454901)
        ·
          refine ⟨37323211485797055380011397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 398114255848501924053454901 37323211485797055380011397)
          ·
            refine ⟨6998102153586947883752137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37323211485797055380011397 6998102153586947883752137)
            ·
              refine ⟨5248576615190210912814103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6998102153586947883752137 5248576615190210912814103)
              ·
                refine ⟨7872864922785316369221155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5248576615190210912814103 7872864922785316369221155)
                ·
                  refine ⟨11809297384177974553831733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7872864922785316369221155 11809297384177974553831733)
                  ·
                    refine ⟨1107121629766685114421725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11809297384177974553831733 1107121629766685114421725)
                    ·
                      rfl

theorem cell23_6468335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 1, 5].length) (baseStart_6468335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468335 prefixEnd_6468335 := by exact prefixLift 6468335
  have htrace : WordTrace (prefixWord ++ tailWord_6468335) baseStart_6468335 baseEnd_6468335 := by
    simpa [prefixWord, tailWord_6468335, baseEnd_6468335] using wordTrace_append hprefix tailTrace_6468335
  have hstable : (prefixWord ++ tailWord_6468335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468335).length < 2 ^ (prefixWord ++ tailWord_6468335).sum := by decide
  have hdescent : baseEnd_6468335 < baseStart_6468335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468344 : List Nat := [2, 1, 2, 1, 1, 2, 14]
def baseStart_6468344 : Nat := 118140960795 + 6468344 * 2 ^ 59
def prefixEnd_6468344 : Nat := 4983230072969 + 3 ^ 40 * 6468344 * 2
def baseEnd_6468344 : Nat := 41004561859579577877193

theorem tailTrace_6468344 : CollatzResearch.WordTrace tailWord_6468344 prefixEnd_6468344 41004561859579577877193 := by
  unfold tailWord_6468344
  simp only [CollatzResearch.WordTrace]
  refine ⟨117959943639150934025118043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157279924852201245366824057 117959943639150934025118043)
  ·
    refine ⟨176939915458726401037677065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117959943639150934025118043 176939915458726401037677065)
    ·
      refine ⟨132704936594044800778257799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176939915458726401037677065 132704936594044800778257799)
      ·
        refine ⟨199057404891067201167386699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132704936594044800778257799 199057404891067201167386699)
        ·
          refine ⟨298586107336600801751080049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199057404891067201167386699 298586107336600801751080049)
          ·
            refine ⟨223939580502450601313310037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298586107336600801751080049 223939580502450601313310037)
            ·
              refine ⟨41004561859579577877193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 223939580502450601313310037 41004561859579577877193)
              ·
                rfl

theorem cell23_6468344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 14].length) (baseStart_6468344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468344 prefixEnd_6468344 := by exact prefixLift 6468344
  have htrace : WordTrace (prefixWord ++ tailWord_6468344) baseStart_6468344 baseEnd_6468344 := by
    simpa [prefixWord, tailWord_6468344, baseEnd_6468344] using wordTrace_append hprefix tailTrace_6468344
  have hstable : (prefixWord ++ tailWord_6468344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468344).length < 2 ^ (prefixWord ++ tailWord_6468344).sum := by decide
  have hdescent : baseEnd_6468344 < baseStart_6468344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468348 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 4, 4]
def baseStart_6468348 : Nat := 118140960795 + 6468348 * 2 ^ 59
def prefixEnd_6468348 : Nat := 4983230072969 + 3 ^ 40 * 6468348 * 2
def baseEnd_6468348 : Nat := 1107123854849521264134205

theorem tailTrace_6468348 : CollatzResearch.WordTrace tailWord_6468348 prefixEnd_6468348 1107123854849521264134205 := by
  unfold tailWord_6468348
  simp only [CollatzResearch.WordTrace]
  refine ⟨117960016585143688366690849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157280022113524917822254465 117960016585143688366690849)
  ·
    refine ⟨88470012438857766275018137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117960016585143688366690849 88470012438857766275018137)
    ·
      refine ⟨66352509329143324706263603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88470012438857766275018137 66352509329143324706263603)
      ·
        refine ⟨99528763993714987059395405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66352509329143324706263603 99528763993714987059395405)
        ·
          refine ⟨37323286497643120147273277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99528763993714987059395405 37323286497643120147273277)
          ·
            refine ⟨13996232436616170055227479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37323286497643120147273277 13996232436616170055227479)
            ·
              refine ⟨20994348654924255082841219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13996232436616170055227479 20994348654924255082841219)
              ·
                refine ⟨31491522982386382624261829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20994348654924255082841219 31491522982386382624261829)
                ·
                  refine ⟨5904660559197446742049093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31491522982386382624261829 5904660559197446742049093)
                  ·
                    refine ⟨1107123854849521264134205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5904660559197446742049093 1107123854849521264134205)
                    ·
                      rfl

theorem cell23_6468348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_6468348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468348 prefixEnd_6468348 := by exact prefixLift 6468348
  have htrace : WordTrace (prefixWord ++ tailWord_6468348) baseStart_6468348 baseEnd_6468348 := by
    simpa [prefixWord, tailWord_6468348, baseEnd_6468348] using wordTrace_append hprefix tailTrace_6468348
  have hstable : (prefixWord ++ tailWord_6468348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468348).length < 2 ^ (prefixWord ++ tailWord_6468348).sum := by decide
  have hdescent : baseEnd_6468348 < baseStart_6468348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468401 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_6468401 : Nat := 118140960795 + 6468401 * 2 ^ 59
def prefixEnd_6468401 : Nat := 4983230072969 + 3 ^ 40 * 6468401 * 2
def baseEnd_6468401 : Nat := 3321398779023252085039871

theorem tailTrace_6468401 : CollatzResearch.WordTrace tailWord_6468401 prefixEnd_6468401 3321398779023252085039871 := by
  unfold tailWord_6468401
  simp only [CollatzResearch.WordTrace]
  refine ⟨235921966239095366785061057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157281310826063577856707371 235921966239095366785061057)
  ·
    refine ⟨176941474679321525088795793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235921966239095366785061057 176941474679321525088795793)
    ·
      refine ⟨132706106009491143816596845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176941474679321525088795793 132706106009491143816596845)
      ·
        refine ⟨49764789753559178931223817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132706106009491143816596845 49764789753559178931223817)
        ·
          refine ⟨37323592315169384198417863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49764789753559178931223817 37323592315169384198417863)
          ·
            refine ⟨55985388472754076297626795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37323592315169384198417863 55985388472754076297626795)
            ·
              refine ⟨83978082709131114446440193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55985388472754076297626795 83978082709131114446440193)
              ·
                refine ⟨62983562031848335834830145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83978082709131114446440193 62983562031848335834830145)
                ·
                  refine ⟨47237671523886251876122609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62983562031848335834830145 47237671523886251876122609)
                  ·
                    refine ⟨35428253642914688907091957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47237671523886251876122609 35428253642914688907091957)
                    ·
                      refine ⟨3321398779023252085039871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35428253642914688907091957 3321398779023252085039871)
                      ·
                        rfl

theorem cell23_6468401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_6468401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468401 prefixEnd_6468401 := by exact prefixLift 6468401
  have htrace : WordTrace (prefixWord ++ tailWord_6468401) baseStart_6468401 baseEnd_6468401 := by
    simpa [prefixWord, tailWord_6468401, baseEnd_6468401] using wordTrace_append hprefix tailTrace_6468401
  have hstable : (prefixWord ++ tailWord_6468401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468401).length < 2 ^ (prefixWord ++ tailWord_6468401).sum := by decide
  have hdescent : baseEnd_6468401 < baseStart_6468401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468405 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_6468405 : Nat := 118140960795 + 6468405 * 2 ^ 59
def prefixEnd_6468405 : Nat := 4983230072969 + 3 ^ 40 * 6468405 * 2
def baseEnd_6468405 : Nat := 3321400832945870069389853

theorem tailTrace_6468405 : CollatzResearch.WordTrace tailWord_6468405 prefixEnd_6468405 3321400832945870069389853 := by
  unfold tailWord_6468405
  simp only [CollatzResearch.WordTrace]
  refine ⟨235922112131080875468206669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157281408087387250312137779 235922112131080875468206669)
  ·
    refine ⟨88470792049155328300577501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235922112131080875468206669 88470792049155328300577501)
    ·
      refine ⟨33176547018433248112716563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88470792049155328300577501 33176547018433248112716563)
      ·
        refine ⟨49764820527649872169074845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33176547018433248112716563 49764820527649872169074845)
        ·
          refine ⟨18661807697868702063403067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49764820527649872169074845 18661807697868702063403067)
          ·
            refine ⟨27992711546803053095104601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18661807697868702063403067 27992711546803053095104601)
            ·
              refine ⟨20994533660102289821328451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27992711546803053095104601 20994533660102289821328451)
              ·
                refine ⟨31491800490153434731992677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20994533660102289821328451 31491800490153434731992677)
                ·
                  refine ⟨5904712591903769012248627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31491800490153434731992677 5904712591903769012248627)
                  ·
                    refine ⟨8857068887855653518372941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5904712591903769012248627 8857068887855653518372941)
                    ·
                      refine ⟨3321400832945870069389853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8857068887855653518372941 3321400832945870069389853)
                      ·
                        rfl

theorem cell23_6468405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_6468405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468405 prefixEnd_6468405 := by exact prefixLift 6468405
  have htrace : WordTrace (prefixWord ++ tailWord_6468405) baseStart_6468405 baseEnd_6468405 := by
    simpa [prefixWord, tailWord_6468405, baseEnd_6468405] using wordTrace_append hprefix tailTrace_6468405
  have hstable : (prefixWord ++ tailWord_6468405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468405).length < 2 ^ (prefixWord ++ tailWord_6468405).sum := by decide
  have hdescent : baseEnd_6468405 < baseStart_6468405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468406 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_6468406 : Nat := 118140960795 + 6468406 * 2 ^ 59
def prefixEnd_6468406 : Nat := 4983230072969 + 3 ^ 40 * 6468406 * 2
def baseEnd_6468406 : Nat := 3321401346426524565477349

theorem tailTrace_6468406 : CollatzResearch.WordTrace tailWord_6468406 prefixEnd_6468406 3321401346426524565477349 := by
  unfold tailWord_6468406
  simp only [CollatzResearch.WordTrace]
  refine ⟨14745134287754828289937067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157281432402718168425995381 14745134287754828289937067)
  ·
    refine ⟨22117701431632242434905601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14745134287754828289937067 22117701431632242434905601)
    ·
      refine ⟨16588276073724181826179201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22117701431632242434905601 16588276073724181826179201)
      ·
        refine ⟨12441207055293136369634401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16588276073724181826179201 12441207055293136369634401)
        ·
          refine ⟨9330905291469852277225801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12441207055293136369634401 9330905291469852277225801)
          ·
            refine ⟨6998178968602389207919351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9330905291469852277225801 6998178968602389207919351)
            ·
              refine ⟨10497268452903583811879027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6998178968602389207919351 10497268452903583811879027)
              ·
                refine ⟨15745902679355375717818541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10497268452903583811879027 15745902679355375717818541)
                ·
                  refine ⟨5904713504758265894181953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15745902679355375717818541 5904713504758265894181953)
                  ·
                    refine ⟨4428535128568699420636465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5904713504758265894181953 4428535128568699420636465)
                    ·
                      refine ⟨3321401346426524565477349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4428535128568699420636465 3321401346426524565477349)
                      ·
                        rfl

theorem cell23_6468406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_6468406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468406 prefixEnd_6468406 := by exact prefixLift 6468406
  have htrace : WordTrace (prefixWord ++ tailWord_6468406) baseStart_6468406 baseEnd_6468406 := by
    simpa [prefixWord, tailWord_6468406, baseEnd_6468406] using wordTrace_append hprefix tailTrace_6468406
  have hstable : (prefixWord ++ tailWord_6468406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468406).length < 2 ^ (prefixWord ++ tailWord_6468406).sum := by decide
  have hdescent : baseEnd_6468406 < baseStart_6468406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468491 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 7]
def baseStart_6468491 : Nat := 118140960795 + 6468491 * 2 ^ 59
def prefixEnd_6468491 : Nat := 4983230072969 + 3 ^ 40 * 6468491 * 2
def baseEnd_6468491 : Nat := 3321444992282156732914457

theorem tailTrace_6468491 : CollatzResearch.WordTrace tailWord_6468491 prefixEnd_6468491 3321444992282156732914457 := by
  unfold tailWord_6468491
  simp only [CollatzResearch.WordTrace]
  refine ⟨235925248808769312155837327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157283499205846208103891551 235925248808769312155837327)
  ·
    refine ⟨353887873213153968233755991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235925248808769312155837327 353887873213153968233755991)
    ·
      refine ⟨530831809819730952350633987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353887873213153968233755991 530831809819730952350633987)
      ·
        refine ⟨796247714729596428525950981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530831809819730952350633987 796247714729596428525950981)
        ·
          refine ⟨149296446511799330348615809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 796247714729596428525950981 149296446511799330348615809)
          ·
            refine ⟨111972334883849497761461857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149296446511799330348615809 111972334883849497761461857)
            ·
              refine ⟨83979251162887123321096393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111972334883849497761461857 83979251162887123321096393)
              ·
                refine ⟨62984438372165342490822295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83979251162887123321096393 62984438372165342490822295)
                ·
                  refine ⟨94476657558248013736233443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62984438372165342490822295 94476657558248013736233443)
                  ·
                    refine ⟨141714986337372020604350165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94476657558248013736233443 141714986337372020604350165)
                    ·
                      refine ⟨3321444992282156732914457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141714986337372020604350165 3321444992282156732914457)
                      ·
                        rfl

theorem cell23_6468491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 7].length) (baseStart_6468491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468491 prefixEnd_6468491 := by exact prefixLift 6468491
  have htrace : WordTrace (prefixWord ++ tailWord_6468491) baseStart_6468491 baseEnd_6468491 := by
    simpa [prefixWord, tailWord_6468491, baseEnd_6468491] using wordTrace_append hprefix tailTrace_6468491
  have hstable : (prefixWord ++ tailWord_6468491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468491).length < 2 ^ (prefixWord ++ tailWord_6468491).sum := by decide
  have hdescent : baseEnd_6468491 < baseStart_6468491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468535 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 2, 4, 2]
def baseStart_6468535 : Nat := 118140960795 + 6468535 * 2 ^ 59
def prefixEnd_6468535 : Nat := 4983230072969 + 3 ^ 40 * 6468535 * 2
def baseEnd_6468535 : Nat := 3321467585430954560764255

theorem tailTrace_6468535 : CollatzResearch.WordTrace tailWord_6468535 prefixEnd_6468535 3321467585430954560764255 := by
  unfold tailWord_6468535
  simp only [CollatzResearch.WordTrace]
  refine ⟨235926853620609907670439059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157284569080406605113626039 235926853620609907670439059)
  ·
    refine ⟨353890280430914861505658589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235926853620609907670439059 353890280430914861505658589)
    ·
      refine ⟨132708855161593073064621971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353890280430914861505658589 132708855161593073064621971)
      ·
        refine ⟨199063282742389609596932957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132708855161593073064621971 199063282742389609596932957)
        ·
          refine ⟨74648731028396103598849859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199063282742389609596932957 74648731028396103598849859)
          ·
            refine ⟨111973096542594155398274789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74648731028396103598849859 111973096542594155398274789)
            ·
              refine ⟨20994955601736404137176523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111973096542594155398274789 20994955601736404137176523)
              ·
                refine ⟨31492433402604606205764785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20994955601736404137176523 31492433402604606205764785)
                ·
                  refine ⟨23619325051953454654323589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31492433402604606205764785 23619325051953454654323589)
                  ·
                    refine ⟨4428623447241272747685673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23619325051953454654323589 4428623447241272747685673)
                    ·
                      refine ⟨3321467585430954560764255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4428623447241272747685673 3321467585430954560764255)
                      ·
                        rfl

theorem cell23_6468535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 4, 2].length) (baseStart_6468535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468535 prefixEnd_6468535 := by exact prefixLift 6468535
  have htrace : WordTrace (prefixWord ++ tailWord_6468535) baseStart_6468535 baseEnd_6468535 := by
    simpa [prefixWord, tailWord_6468535, baseEnd_6468535] using wordTrace_append hprefix tailTrace_6468535
  have hstable : (prefixWord ++ tailWord_6468535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468535).length < 2 ^ (prefixWord ++ tailWord_6468535).sum := by decide
  have hdescent : baseEnd_6468535 < baseStart_6468535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468538 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3]
def baseStart_6468538 : Nat := 118140960795 + 6468538 * 2 ^ 59
def prefixEnd_6468538 : Nat := 4983230072969 + 3 ^ 40 * 6468538 * 2
def baseEnd_6468538 : Nat := 3321469125872918049026741

theorem tailTrace_6468538 : CollatzResearch.WordTrace tailWord_6468538 prefixEnd_6468538 3321469125872918049026741 := by
  unfold tailWord_6468538
  simp only [CollatzResearch.WordTrace]
  refine ⟨58981740759899759795699567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157284642026399359455198845 58981740759899759795699567)
  ·
    refine ⟨88472611139849639693549351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58981740759899759795699567 88472611139849639693549351)
    ·
      refine ⟨132708916709774459540324027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88472611139849639693549351 132708916709774459540324027)
      ·
        refine ⟨199063375064661689310486041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132708916709774459540324027 199063375064661689310486041)
        ·
          refine ⟨149297531298496266982864531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199063375064661689310486041 149297531298496266982864531)
          ·
            refine ⟨223946296947744400474296797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149297531298496266982864531 223946296947744400474296797)
            ·
              refine ⟨83979861355404150177861299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223946296947744400474296797 83979861355404150177861299)
              ·
                refine ⟨125969792033106225266791949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83979861355404150177861299 125969792033106225266791949)
                ·
                  refine ⟨47238672012414834475046981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125969792033106225266791949 47238672012414834475046981)
                  ·
                    refine ⟨8857251002327781464071309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47238672012414834475046981 8857251002327781464071309)
                    ·
                      refine ⟨3321469125872918049026741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8857251002327781464071309 3321469125872918049026741)
                      ·
                        rfl

theorem cell23_6468538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_6468538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468538 prefixEnd_6468538 := by exact prefixLift 6468538
  have htrace : WordTrace (prefixWord ++ tailWord_6468538) baseStart_6468538 baseEnd_6468538 := by
    simpa [prefixWord, tailWord_6468538, baseEnd_6468538] using wordTrace_append hprefix tailTrace_6468538
  have hstable : (prefixWord ++ tailWord_6468538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468538).length < 2 ^ (prefixWord ++ tailWord_6468538).sum := by decide
  have hdescent : baseEnd_6468538 < baseStart_6468538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468558 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 8]
def baseStart_6468558 : Nat := 118140960795 + 6468558 * 2 ^ 59
def prefixEnd_6468558 : Nat := 4983230072969 + 3 ^ 40 * 6468558 * 2
def baseEnd_6468558 : Nat := 369053266165111996752961

theorem tailTrace_6468558 : CollatzResearch.WordTrace tailWord_6468558 prefixEnd_6468558 369053266165111996752961 := by
  unfold tailWord_6468558
  simp only [CollatzResearch.WordTrace]
  refine ⟨29490961562440822824815791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157285128333017721732350885 29490961562440822824815791)
  ·
    refine ⟨44236442343661234237223687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29490961562440822824815791 44236442343661234237223687)
    ·
      refine ⟨66354663515491851355835531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44236442343661234237223687 66354663515491851355835531)
      ·
        refine ⟨99531995273237777033753297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66354663515491851355835531 99531995273237777033753297)
        ·
          refine ⟨74648996454928332775314973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99531995273237777033753297 74648996454928332775314973)
          ·
            refine ⟨27993373670598124790743115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74648996454928332775314973 27993373670598124790743115)
            ·
              refine ⟨41990060505897187186114673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27993373670598124790743115 41990060505897187186114673)
              ·
                refine ⟨31492545379422890389586005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41990060505897187186114673 31492545379422890389586005)
                ·
                  refine ⟨369053266165111996752961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31492545379422890389586005 369053266165111996752961)
                  ·
                    rfl

theorem cell23_6468558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_6468558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468558 prefixEnd_6468558 := by exact prefixLift 6468558
  have htrace : WordTrace (prefixWord ++ tailWord_6468558) baseStart_6468558 baseEnd_6468558 := by
    simpa [prefixWord, tailWord_6468558, baseEnd_6468558] using wordTrace_append hprefix tailTrace_6468558
  have hstable : (prefixWord ++ tailWord_6468558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468558).length < 2 ^ (prefixWord ++ tailWord_6468558).sum := by decide
  have hdescent : baseEnd_6468558 < baseStart_6468558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468579 : List Nat := [1, 1, 1, 6, 1, 1, 5, 2, 1, 4]
def baseStart_6468579 : Nat := 118140960795 + 6468579 * 2 ^ 59
def prefixEnd_6468579 : Nat := 4983230072969 + 3 ^ 40 * 6468579 * 2
def baseEnd_6468579 : Nat := 1107163392859917462871351

theorem tailTrace_6468579 : CollatzResearch.WordTrace tailWord_6468579 prefixEnd_6468579 1107163392859917462871351 := by
  unfold tailWord_6468579
  simp only [CollatzResearch.WordTrace]
  refine ⟨235928458432450503185040791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157285638954967002123360527 235928458432450503185040791)
  ·
    refine ⟨353892687648675754777561187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235928458432450503185040791 353892687648675754777561187)
    ·
      refine ⟨530839031473013632166341781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353892687648675754777561187 530839031473013632166341781)
      ·
        refine ⟨24883079600297514007797271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 530839031473013632166341781 24883079600297514007797271)
        ·
          refine ⟨37324619400446271011695907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24883079600297514007797271 37324619400446271011695907)
          ·
            refine ⟨55986929100669406517543861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37324619400446271011695907 55986929100669406517543861)
            ·
              refine ⟨5248774603187756861019737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55986929100669406517543861 5248774603187756861019737)
              ·
                refine ⟨3936580952390817645764803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5248774603187756861019737 3936580952390817645764803)
                ·
                  refine ⟨5904871428586226468647205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3936580952390817645764803 5904871428586226468647205)
                  ·
                    refine ⟨1107163392859917462871351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5904871428586226468647205 1107163392859917462871351)
                    ·
                      rfl

theorem cell23_6468579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 1, 4].length) (baseStart_6468579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468579 prefixEnd_6468579 := by exact prefixLift 6468579
  have htrace : WordTrace (prefixWord ++ tailWord_6468579) baseStart_6468579 baseEnd_6468579 := by
    simpa [prefixWord, tailWord_6468579, baseEnd_6468579] using wordTrace_append hprefix tailTrace_6468579
  have hstable : (prefixWord ++ tailWord_6468579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468579).length < 2 ^ (prefixWord ++ tailWord_6468579).sum := by decide
  have hdescent : baseEnd_6468579 < baseStart_6468579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468625 : List Nat := [1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 4]
def baseStart_6468625 : Nat := 118140960795 + 6468625 * 2 ^ 59
def prefixEnd_6468625 : Nat := 4983230072969 + 3 ^ 40 * 6468625 * 2
def baseEnd_6468625 : Nat := 3321513798689859208638841

theorem tailTrace_6468625 : CollatzResearch.WordTrace tailWord_6468625 prefixEnd_6468625 3321513798689859208638841 := by
  unfold tailWord_6468625
  simp only [CollatzResearch.WordTrace]
  refine ⟨235930136190283853041215329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157286757460189235360810219 235930136190283853041215329)
  ·
    refine ⟨176947602142712889780911497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235930136190283853041215329 176947602142712889780911497)
    ·
      refine ⟨132710701607034667335683623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176947602142712889780911497 132710701607034667335683623)
      ·
        refine ⟨199066052410552001003525435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132710701607034667335683623 199066052410552001003525435)
        ·
          refine ⟨298599078615828001505288153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199066052410552001003525435 298599078615828001505288153)
          ·
            refine ⟨223949308961871001128966115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298599078615828001505288153 223949308961871001128966115)
            ·
              refine ⟨335923963442806501693449173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223949308961871001128966115 335923963442806501693449173)
              ·
                refine ⟨7873217893190777383440215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 335923963442806501693449173 7873217893190777383440215)
                ·
                  refine ⟨11809826839786166075160323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7873217893190777383440215 11809826839786166075160323)
                  ·
                    refine ⟨17714740259679249112740485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11809826839786166075160323 17714740259679249112740485)
                    ·
                      refine ⟨3321513798689859208638841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17714740259679249112740485 3321513798689859208638841)
                      ·
                        rfl

theorem cell23_6468625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_6468625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468625 prefixEnd_6468625 := by exact prefixLift 6468625
  have htrace : WordTrace (prefixWord ++ tailWord_6468625) baseStart_6468625 baseEnd_6468625 := by
    simpa [prefixWord, tailWord_6468625, baseEnd_6468625] using wordTrace_append hprefix tailTrace_6468625
  have hstable : (prefixWord ++ tailWord_6468625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468625).length < 2 ^ (prefixWord ++ tailWord_6468625).sum := by decide
  have hdescent : baseEnd_6468625 < baseStart_6468625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468626 : List Nat := [3, 2, 5, 1, 1, 1, 2, 2, 6]
def baseStart_6468626 : Nat := 118140960795 + 6468626 * 2 ^ 59
def prefixEnd_6468626 : Nat := 4983230072969 + 3 ^ 40 * 6468626 * 2
def baseEnd_6468626 : Nat := 369057145796723744969593

theorem tailTrace_6468626 : CollatzResearch.WordTrace tailWord_6468626 prefixEnd_6468626 369057145796723744969593 := by
  unfold tailWord_6468626
  simp only [CollatzResearch.WordTrace]
  refine ⟨58982543165820057553000433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157286781775520153474667821 58982543165820057553000433)
  ·
    refine ⟨44236907374365043164750325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58982543165820057553000433 44236907374365043164750325)
    ·
      refine ⟨4147210066346722796695343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44236907374365043164750325 4147210066346722796695343)
      ·
        refine ⟨6220815099520084195043015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4147210066346722796695343 6220815099520084195043015)
        ·
          refine ⟨9331222649280126292564523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6220815099520084195043015 9331222649280126292564523)
          ·
            refine ⟨13996833973920189438846785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9331222649280126292564523 13996833973920189438846785)
            ·
              refine ⟨10497625480440142079135089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13996833973920189438846785 10497625480440142079135089)
              ·
                refine ⟨7873219110330106559351317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10497625480440142079135089 7873219110330106559351317)
                ·
                  refine ⟨369057145796723744969593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7873219110330106559351317 369057145796723744969593)
                  ·
                    rfl

theorem cell23_6468626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_6468626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468626 prefixEnd_6468626 := by exact prefixLift 6468626
  have htrace : WordTrace (prefixWord ++ tailWord_6468626) baseStart_6468626 baseEnd_6468626 := by
    simpa [prefixWord, tailWord_6468626, baseEnd_6468626] using wordTrace_append hprefix tailTrace_6468626
  have hstable : (prefixWord ++ tailWord_6468626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468626).length < 2 ^ (prefixWord ++ tailWord_6468626).sum := by decide
  have hdescent : baseEnd_6468626 < baseStart_6468626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468636 : List Nat := [2, 2, 3, 1, 4, 1, 1, 4, 1, 1, 3]
def baseStart_6468636 : Nat := 118140960795 + 6468636 * 2 ^ 59
def prefixEnd_6468636 : Nat := 4983230072969 + 3 ^ 40 * 6468636 * 2
def baseEnd_6468636 : Nat := 3321519446977058665601291

theorem tailTrace_6468636 : CollatzResearch.WordTrace tailWord_6468636 prefixEnd_6468636 3321519446977058665601291 := by
  unfold tailWord_6468636
  simp only [CollatzResearch.WordTrace]
  refine ⟨117965268696622000959932881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157287024928829334613243841 117965268696622000959932881)
  ·
    refine ⟨88473951522466500719949661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117965268696622000959932881 88473951522466500719949661)
    ·
      refine ⟨33177731820924937769981123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88473951522466500719949661 33177731820924937769981123)
      ·
        refine ⟨49766597731387406654971685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33177731820924937769981123 49766597731387406654971685)
        ·
          refine ⟨9331237074635138747807191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49766597731387406654971685 9331237074635138747807191)
          ·
            refine ⟨13996855611952708121710787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9331237074635138747807191 13996855611952708121710787)
            ·
              refine ⟨20995283417929062182566181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13996855611952708121710787 20995283417929062182566181)
              ·
                refine ⟨3936615640861699159231159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20995283417929062182566181 3936615640861699159231159)
                ·
                  refine ⟨5904923461292548738846739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3936615640861699159231159 5904923461292548738846739)
                  ·
                    refine ⟨8857385191938823108270109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5904923461292548738846739 8857385191938823108270109)
                    ·
                      refine ⟨3321519446977058665601291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8857385191938823108270109 3321519446977058665601291)
                      ·
                        rfl

theorem cell23_6468636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_6468636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468636 prefixEnd_6468636 := by exact prefixLift 6468636
  have htrace : WordTrace (prefixWord ++ tailWord_6468636) baseStart_6468636 baseEnd_6468636 := by
    simpa [prefixWord, tailWord_6468636, baseEnd_6468636] using wordTrace_append hprefix tailTrace_6468636
  have hstable : (prefixWord ++ tailWord_6468636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468636).length < 2 ^ (prefixWord ++ tailWord_6468636).sum := by decide
  have hdescent : baseEnd_6468636 < baseStart_6468636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468645 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 5, 2, 3]
def baseStart_6468645 : Nat := 118140960795 + 6468645 * 2 ^ 59
def prefixEnd_6468645 : Nat := 4983230072969 + 3 ^ 40 * 6468645 * 2
def baseEnd_6468645 : Nat := 3321524068302949130388749

theorem tailTrace_6468645 : CollatzResearch.WordTrace tailWord_6468645 prefixEnd_6468645 3321524068302949130388749 := by
  unfold tailWord_6468645
  simp only [CollatzResearch.WordTrace]
  refine ⟨235930865650211396456943389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157287243766807597637962259 235930865650211396456943389)
  ·
    refine ⟨88474074618829273671353771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235930865650211396456943389 88474074618829273671353771)
    ·
      refine ⟨132711111928243910507030657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88474074618829273671353771 132711111928243910507030657)
      ·
        refine ⟨99533333946182932880272993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132711111928243910507030657 99533333946182932880272993)
        ·
          refine ⟨74650000459637199660204745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99533333946182932880272993 74650000459637199660204745)
          ·
            refine ⟨55987500344727899745153559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74650000459637199660204745 55987500344727899745153559)
            ·
              refine ⟨83981250517091849617730339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55987500344727899745153559 83981250517091849617730339)
              ·
                refine ⟨125971875775637774426595509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83981250517091849617730339 125971875775637774426595509)
                ·
                  refine ⟨11809863353966041352493329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125971875775637774426595509 11809863353966041352493329)
                  ·
                    refine ⟨8857397515474531014369997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11809863353966041352493329 8857397515474531014369997)
                    ·
                      refine ⟨3321524068302949130388749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8857397515474531014369997 3321524068302949130388749)
                      ·
                        rfl

theorem cell23_6468645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_6468645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468645 prefixEnd_6468645 := by exact prefixLift 6468645
  have htrace : WordTrace (prefixWord ++ tailWord_6468645) baseStart_6468645 baseEnd_6468645 := by
    simpa [prefixWord, tailWord_6468645, baseEnd_6468645] using wordTrace_append hprefix tailTrace_6468645
  have hstable : (prefixWord ++ tailWord_6468645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468645).length < 2 ^ (prefixWord ++ tailWord_6468645).sum := by decide
  have hdescent : baseEnd_6468645 < baseStart_6468645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468675 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 3]
def baseStart_6468675 : Nat := 118140960795 + 6468675 * 2 ^ 59
def prefixEnd_6468675 : Nat := 4983230072969 + 3 ^ 40 * 6468675 * 2
def baseEnd_6468675 : Nat := 3321539472722584013013611

theorem tailTrace_6468675 : CollatzResearch.WordTrace tailWord_6468675 prefixEnd_6468675 3321539472722584013013611 := by
  unfold tailWord_6468675
  simp only [CollatzResearch.WordTrace]
  refine ⟨235931959840102711580535479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157287973226735141053690319 235931959840102711580535479)
  ·
    refine ⟨353897939760154067370803219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235931959840102711580535479 353897939760154067370803219)
    ·
      refine ⟨530846909640231101056204829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353897939760154067370803219 530846909640231101056204829)
      ·
        refine ⟨199067591115086662896076811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 530846909640231101056204829 199067591115086662896076811)
        ·
          refine ⟨298601386672629994344115217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199067591115086662896076811 298601386672629994344115217)
          ·
            refine ⟨223951040004472495758086413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298601386672629994344115217 223951040004472495758086413)
            ·
              refine ⟨83981640001677185909282405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223951040004472495758086413 83981640001677185909282405)
              ·
                refine ⟨15746557500314472357990451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83981640001677185909282405 15746557500314472357990451)
                ·
                  refine ⟨23619836250471708536985677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15746557500314472357990451 23619836250471708536985677)
                  ·
                    refine ⟨8857438593926890701369629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23619836250471708536985677 8857438593926890701369629)
                    ·
                      refine ⟨3321539472722584013013611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8857438593926890701369629 3321539472722584013013611)
                      ·
                        rfl

theorem cell23_6468675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_6468675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468675 prefixEnd_6468675 := by exact prefixLift 6468675
  have htrace : WordTrace (prefixWord ++ tailWord_6468675) baseStart_6468675 baseEnd_6468675 := by
    simpa [prefixWord, tailWord_6468675, baseEnd_6468675] using wordTrace_append hprefix tailTrace_6468675
  have hstable : (prefixWord ++ tailWord_6468675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468675).length < 2 ^ (prefixWord ++ tailWord_6468675).sum := by decide
  have hdescent : baseEnd_6468675 < baseStart_6468675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468679 : List Nat := [1, 1, 4, 1, 3, 2, 4, 1, 1, 2, 3]
def baseStart_6468679 : Nat := 118140960795 + 6468679 * 2 ^ 59
def prefixEnd_6468679 : Nat := 4983230072969 + 3 ^ 40 * 6468679 * 2
def baseEnd_6468679 : Nat := 3321541526645201997363593

theorem tailTrace_6468679 : CollatzResearch.WordTrace tailWord_6468679 prefixEnd_6468679 3321541526645201997363593 := by
  unfold tailWord_6468679
  simp only [CollatzResearch.WordTrace]
  refine ⟨235932105732088220263681091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157288070488058813509120727 235932105732088220263681091)
  ·
    refine ⟨353898158598132330395521637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235932105732088220263681091 353898158598132330395521637)
    ·
      refine ⟨66355904737149811949160307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353898158598132330395521637 66355904737149811949160307)
      ·
        refine ⟨99533857105724717923740461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66355904737149811949160307 99533857105724717923740461)
        ·
          refine ⟨37325196414646769221402673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99533857105724717923740461 37325196414646769221402673)
          ·
            refine ⟨27993897310985076916052005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37325196414646769221402673 27993897310985076916052005)
            ·
              refine ⟨5248855745809701921759751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27993897310985076916052005 5248855745809701921759751)
              ·
                refine ⟨7873283618714552882639627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5248855745809701921759751 7873283618714552882639627)
                ·
                  refine ⟨11809925428071829323959441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7873283618714552882639627 11809925428071829323959441)
                  ·
                    refine ⟨8857444071053871992969581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11809925428071829323959441 8857444071053871992969581)
                    ·
                      refine ⟨3321541526645201997363593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8857444071053871992969581 3321541526645201997363593)
                      ·
                        rfl

theorem cell23_6468679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 1, 2, 3].length) (baseStart_6468679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468679 prefixEnd_6468679 := by exact prefixLift 6468679
  have htrace : WordTrace (prefixWord ++ tailWord_6468679) baseStart_6468679 baseEnd_6468679 := by
    simpa [prefixWord, tailWord_6468679, baseEnd_6468679] using wordTrace_append hprefix tailTrace_6468679
  have hstable : (prefixWord ++ tailWord_6468679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468679).length < 2 ^ (prefixWord ++ tailWord_6468679).sum := by decide
  have hdescent : baseEnd_6468679 < baseStart_6468679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468719 : List Nat := [1, 1, 2, 1, 3, 3, 4, 2, 1, 3, 2]
def baseStart_6468719 : Nat := 118140960795 + 6468719 * 2 ^ 59
def prefixEnd_6468719 : Nat := 4983230072969 + 3 ^ 40 * 6468719 * 2
def baseEnd_6468719 : Nat := 3321562065871381840863409

theorem tailTrace_6468719 : CollatzResearch.WordTrace tailWord_6468719 prefixEnd_6468719 3321562065871381840863409 := by
  unfold tailWord_6468719
  simp only [CollatzResearch.WordTrace]
  refine ⟨235933564651943307095137211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157289043101295538063424807 235933564651943307095137211)
  ·
    refine ⟨353900346977914960642705817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235933564651943307095137211 353900346977914960642705817)
    ·
      refine ⟨265425260233436220482029363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353900346977914960642705817 265425260233436220482029363)
      ·
        refine ⟨398137890350154330723044045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265425260233436220482029363 398137890350154330723044045)
        ·
          refine ⟨149301708881307874021141517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398137890350154330723044045 149301708881307874021141517)
          ·
            refine ⟨55988140830490452757928069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149301708881307874021141517 55988140830490452757928069)
            ·
              refine ⟨10497776405716959892111513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55988140830490452757928069 10497776405716959892111513)
              ·
                refine ⟨7873332304287719919083635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10497776405716959892111513 7873332304287719919083635)
                ·
                  refine ⟨11809998456431579878625453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7873332304287719919083635 11809998456431579878625453)
                  ·
                    refine ⟨4428749421161842454484545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11809998456431579878625453 4428749421161842454484545)
                    ·
                      refine ⟨3321562065871381840863409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4428749421161842454484545 3321562065871381840863409)
                      ·
                        rfl

theorem cell23_6468719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 3, 2].length) (baseStart_6468719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468719 prefixEnd_6468719 := by exact prefixLift 6468719
  have htrace : WordTrace (prefixWord ++ tailWord_6468719) baseStart_6468719 baseEnd_6468719 := by
    simpa [prefixWord, tailWord_6468719, baseEnd_6468719] using wordTrace_append hprefix tailTrace_6468719
  have hstable : (prefixWord ++ tailWord_6468719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468719).length < 2 ^ (prefixWord ++ tailWord_6468719).sum := by decide
  have hdescent : baseEnd_6468719 < baseStart_6468719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468732 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 3, 4, 2]
def baseStart_6468732 : Nat := 118140960795 + 6468732 * 2 ^ 59
def prefixEnd_6468732 : Nat := 4983230072969 + 3 ^ 40 * 6468732 * 2
def baseEnd_6468732 : Nat := 3321568741119890290000849

theorem tailTrace_6468732 : CollatzResearch.WordTrace tailWord_6468732 prefixEnd_6468732 3321568741119890290000849 := by
  unfold tailWord_6468732
  simp only [CollatzResearch.WordTrace]
  refine ⟨117967019400448105157680225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157289359200597473543573633 117967019400448105157680225)
  ·
    refine ⟨88475264550336078868260169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117967019400448105157680225 88475264550336078868260169)
    ·
      refine ⟨66356448412752059151195127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88475264550336078868260169 66356448412752059151195127)
      ·
        refine ⟨99534672619128088726792691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66356448412752059151195127 99534672619128088726792691)
        ·
          refine ⟨149302008928692133090189037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99534672619128088726792691 149302008928692133090189037)
          ·
            refine ⟨55988253348259549908820889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149302008928692133090189037 55988253348259549908820889)
            ·
              refine ⟨41991190011194662431615667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55988253348259549908820889 41991190011194662431615667)
              ·
                refine ⟨62986785016791993647423501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41991190011194662431615667 62986785016791993647423501)
                ·
                  refine ⟨23620044381296997617783813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62986785016791993647423501 23620044381296997617783813)
                  ·
                    refine ⟨4428758321493187053334465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23620044381296997617783813 4428758321493187053334465)
                    ·
                      refine ⟨3321568741119890290000849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4428758321493187053334465 3321568741119890290000849)
                      ·
                        rfl

theorem cell23_6468732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_6468732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468732 prefixEnd_6468732 := by exact prefixLift 6468732
  have htrace : WordTrace (prefixWord ++ tailWord_6468732) baseStart_6468732 baseEnd_6468732 := by
    simpa [prefixWord, tailWord_6468732, baseEnd_6468732] using wordTrace_append hprefix tailTrace_6468732
  have hstable : (prefixWord ++ tailWord_6468732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468732).length < 2 ^ (prefixWord ++ tailWord_6468732).sum := by decide
  have hdescent : baseEnd_6468732 < baseStart_6468732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468755 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 7]
def baseStart_6468755 : Nat := 118140960795 + 6468755 * 2 ^ 59
def prefixEnd_6468755 : Nat := 4983230072969 + 3 ^ 40 * 6468755 * 2
def baseEnd_6468755 : Nat := 369064505686104855557027

theorem tailTrace_6468755 : CollatzResearch.WordTrace tailWord_6468755 prefixEnd_6468755 369064505686104855557027 := by
  unfold tailWord_6468755
  simp only [CollatzResearch.WordTrace]
  refine ⟨235934877679812885243447719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157289918453208590162298479 235934877679812885243447719)
  ·
    refine ⟨353902316519719327865171579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235934877679812885243447719 353902316519719327865171579)
    ·
      refine ⟨530853474779578991797757369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353902316519719327865171579 530853474779578991797757369)
      ·
        refine ⟨398140106084684243848318027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530853474779578991797757369 398140106084684243848318027)
        ·
          refine ⟨597210159127026365772477041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398140106084684243848318027 597210159127026365772477041)
          ·
            refine ⟨447907619345269774329357781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597210159127026365772477041 447907619345269774329357781)
            ·
              refine ⟨10497834828404760335844323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 447907619345269774329357781 10497834828404760335844323)
              ·
                refine ⟨15746752242607140503766485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10497834828404760335844323 15746752242607140503766485)
                ·
                  refine ⟨369064505686104855557027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15746752242607140503766485 369064505686104855557027)
                  ·
                    rfl

theorem cell23_6468755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 7].length) (baseStart_6468755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468755 prefixEnd_6468755 := by exact prefixLift 6468755
  have htrace : WordTrace (prefixWord ++ tailWord_6468755) baseStart_6468755 baseEnd_6468755 := by
    simpa [prefixWord, tailWord_6468755, baseEnd_6468755] using wordTrace_append hprefix tailTrace_6468755
  have hstable : (prefixWord ++ tailWord_6468755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468755).length < 2 ^ (prefixWord ++ tailWord_6468755).sum := by decide
  have hdescent : baseEnd_6468755 < baseStart_6468755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468770 : List Nat := [3, 3, 1, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_6468770 : Nat := 118140960795 + 6468770 * 2 ^ 59
def prefixEnd_6468770 : Nat := 4983230072969 + 3 ^ 40 * 6468770 * 2
def baseEnd_6468770 : Nat := 3321588253384761141325675

theorem tailTrace_6468770 : CollatzResearch.WordTrace tailWord_6468770 prefixEnd_6468770 3321588253384761141325675 := by
  unfold tailWord_6468770
  simp only [CollatzResearch.WordTrace]
  refine ⟨58983856193689635701310941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157290283183172361870162509 58983856193689635701310941)
  ·
    refine ⟨22118946072633613387991603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58983856193689635701310941 22118946072633613387991603)
    ·
      refine ⟨33178419108950420081987405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22118946072633613387991603 33178419108950420081987405)
      ·
        refine ⟨12441907165856407530745277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33178419108950420081987405 12441907165856407530745277)
        ·
          refine ⟨4665715187196152824029479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12441907165856407530745277 4665715187196152824029479)
          ·
            refine ⟨6998572780794229236044219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4665715187196152824029479 6998572780794229236044219)
            ·
              refine ⟨10497859171191343854066329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6998572780794229236044219 10497859171191343854066329)
              ·
                refine ⟨7873394378393507890549747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10497859171191343854066329 7873394378393507890549747)
                ·
                  refine ⟨11810091567590261835824621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7873394378393507890549747 11810091567590261835824621)
                  ·
                    refine ⟨4428784337846348188434233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11810091567590261835824621 4428784337846348188434233)
                    ·
                      refine ⟨3321588253384761141325675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4428784337846348188434233 3321588253384761141325675)
                      ·
                        rfl

theorem cell23_6468770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_6468770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468770 prefixEnd_6468770 := by exact prefixLift 6468770
  have htrace : WordTrace (prefixWord ++ tailWord_6468770) baseStart_6468770 baseEnd_6468770 := by
    simpa [prefixWord, tailWord_6468770, baseEnd_6468770] using wordTrace_append hprefix tailTrace_6468770
  have hstable : (prefixWord ++ tailWord_6468770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468770).length < 2 ^ (prefixWord ++ tailWord_6468770).sum := by decide
  have hdescent : baseEnd_6468770 < baseStart_6468770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468805 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_6468805 : Nat := 118140960795 + 6468805 * 2 ^ 59
def prefixEnd_6468805 : Nat := 4983230072969 + 3 ^ 40 * 6468805 * 2
def baseEnd_6468805 : Nat := 3321606225207668504388013

theorem tailTrace_6468805 : CollatzResearch.WordTrace tailWord_6468805 prefixEnd_6468805 3321606225207668504388013 := by
  unfold tailWord_6468805
  simp only [CollatzResearch.WordTrace]
  refine ⟨235936701329631743782767869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157291134219754495855178579 235936701329631743782767869)
  ·
    refine ⟨88476262998611903918537951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235936701329631743782767869 88476262998611903918537951)
    ·
      refine ⟨132714394497917855877806927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88476262998611903918537951 132714394497917855877806927)
      ·
        refine ⟨199071591746876783816710391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132714394497917855877806927 199071591746876783816710391)
        ·
          refine ⟨298607387620315175725065587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199071591746876783816710391 298607387620315175725065587)
          ·
            refine ⟨447911081430472763587598381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298607387620315175725065587 447911081430472763587598381)
            ·
              refine ⟨167966655536427286345349393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 447911081430472763587598381 167966655536427286345349393)
              ·
                refine ⟨125974991652320464759012045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167966655536427286345349393 125974991652320464759012045)
                ·
                  refine ⟨47240621869620174284629517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125974991652320464759012045 47240621869620174284629517)
                  ·
                    refine ⟨17715233201107565356736069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47240621869620174284629517 17715233201107565356736069)
                    ·
                      refine ⟨3321606225207668504388013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17715233201107565356736069 3321606225207668504388013)
                      ·
                        rfl

theorem cell23_6468805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_6468805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468805 prefixEnd_6468805 := by exact prefixLift 6468805
  have htrace : WordTrace (prefixWord ++ tailWord_6468805) baseStart_6468805 baseEnd_6468805 := by
    simpa [prefixWord, tailWord_6468805, baseEnd_6468805] using wordTrace_append hprefix tailTrace_6468805
  have hstable : (prefixWord ++ tailWord_6468805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468805).length < 2 ^ (prefixWord ++ tailWord_6468805).sum := by decide
  have hdescent : baseEnd_6468805 < baseStart_6468805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468832 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 5, 4]
def baseStart_6468832 : Nat := 118140960795 + 6468832 * 2 ^ 59
def prefixEnd_6468832 : Nat := 4983230072969 + 3 ^ 40 * 6468832 * 2
def baseEnd_6468832 : Nat := 1107206696395113299583463

theorem tailTrace_6468832 : CollatzResearch.WordTrace tailWord_6468832 prefixEnd_6468832 1107206696395113299583463 := by
  unfold tailWord_6468832
  simp only [CollatzResearch.WordTrace]
  refine ⟨117968843050266963697000375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157291790733689284929333833 117968843050266963697000375)
  ·
    refine ⟨176953264575400445545500563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117968843050266963697000375 176953264575400445545500563)
    ·
      refine ⟨265429896863100668318250845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176953264575400445545500563 265429896863100668318250845)
      ·
        refine ⟨99536211323662750619344067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265429896863100668318250845 99536211323662750619344067)
        ·
          refine ⟨149304316985494125929016101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99536211323662750619344067 149304316985494125929016101)
          ·
            refine ⟨27994559434780148611690519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149304316985494125929016101 27994559434780148611690519)
            ·
              refine ⟨41991839152170222917535779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27994559434780148611690519 41991839152170222917535779)
              ·
                refine ⟨62987758728255334376303669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41991839152170222917535779 62987758728255334376303669)
                ·
                  refine ⟨5905102380773937597778469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62987758728255334376303669 5905102380773937597778469)
                  ·
                    refine ⟨1107206696395113299583463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5905102380773937597778469 1107206696395113299583463)
                    ·
                      rfl

theorem cell23_6468832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 5, 4].length) (baseStart_6468832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468832 prefixEnd_6468832 := by exact prefixLift 6468832
  have htrace : WordTrace (prefixWord ++ tailWord_6468832) baseStart_6468832 baseEnd_6468832 := by
    simpa [prefixWord, tailWord_6468832, baseEnd_6468832] using wordTrace_append hprefix tailTrace_6468832
  have hstable : (prefixWord ++ tailWord_6468832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468832).length < 2 ^ (prefixWord ++ tailWord_6468832).sum := by decide
  have hdescent : baseEnd_6468832 < baseStart_6468832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468839 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_6468839 : Nat := 118140960795 + 6468839 * 2 ^ 59
def prefixEnd_6468839 : Nat := 4983230072969 + 3 ^ 40 * 6468839 * 2
def baseEnd_6468839 : Nat := 3321623683549921371362857

theorem tailTrace_6468839 : CollatzResearch.WordTrace tailWord_6468839 prefixEnd_6468839 3321623683549921371362857 := by
  unfold tailWord_6468839
  simp only [CollatzResearch.WordTrace]
  refine ⟨235937941411508567589505571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157291960941005711726337047 235937941411508567589505571)
  ·
    refine ⟨353906912117262851384258357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235937941411508567589505571 353906912117262851384258357)
    ·
      refine ⟨33178773010993392317274221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 353906912117262851384258357 33178773010993392317274221)
      ·
        refine ⟨12442039879122522118977833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33178773010993392317274221 12442039879122522118977833)
        ·
          refine ⟨9331529909341891589233375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12442039879122522118977833 9331529909341891589233375)
          ·
            refine ⟨13997294864012837383850063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9331529909341891589233375 13997294864012837383850063)
            ·
              refine ⟨20995942296019256075775095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13997294864012837383850063 20995942296019256075775095)
              ·
                refine ⟨31493913444028884113662643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20995942296019256075775095 31493913444028884113662643)
                ·
                  refine ⟨47240870166043326170493965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31493913444028884113662643 47240870166043326170493965)
                  ·
                    refine ⟨17715326312266247313935237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47240870166043326170493965 17715326312266247313935237)
                    ·
                      refine ⟨3321623683549921371362857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17715326312266247313935237 3321623683549921371362857)
                      ·
                        rfl

theorem cell23_6468839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_6468839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468839 prefixEnd_6468839 := by exact prefixLift 6468839
  have htrace : WordTrace (prefixWord ++ tailWord_6468839) baseStart_6468839 baseEnd_6468839 := by
    simpa [prefixWord, tailWord_6468839, baseEnd_6468839] using wordTrace_append hprefix tailTrace_6468839
  have hstable : (prefixWord ++ tailWord_6468839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468839).length < 2 ^ (prefixWord ++ tailWord_6468839).sum := by decide
  have hdescent : baseEnd_6468839 < baseStart_6468839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468892 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 3, 5]
def baseStart_6468892 : Nat := 118140960795 + 6468892 * 2 ^ 59
def prefixEnd_6468892 : Nat := 4983230072969 + 3 ^ 40 * 6468892 * 2
def baseEnd_6468892 : Nat := 1107216966008203221333371

theorem tailTrace_6468892 : CollatzResearch.WordTrace tailWord_6468892 prefixEnd_6468892 1107216966008203221333371 := by
  unfold tailWord_6468892
  simp only [CollatzResearch.WordTrace]
  refine ⟨117969937240158278820592465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157293249653544371760789953 117969937240158278820592465)
  ·
    refine ⟨88477452930118709115444349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117969937240158278820592465 88477452930118709115444349)
    ·
      refine ⟨33179044848794515918291631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88477452930118709115444349 33179044848794515918291631)
      ·
        refine ⟨49768567273191773877437447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33179044848794515918291631 49768567273191773877437447)
        ·
          refine ⟨74652850909787660816156171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49768567273191773877437447 74652850909787660816156171)
          ·
            refine ⟨111979276364681491224234257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74652850909787660816156171 111979276364681491224234257)
            ·
              refine ⟨83984457273511118418175693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111979276364681491224234257 83984457273511118418175693)
              ·
                refine ⟨31494171477566669406815885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83984457273511118418175693 31494171477566669406815885)
                ·
                  refine ⟨11810314304087501027555957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31494171477566669406815885 11810314304087501027555957)
                  ·
                    refine ⟨1107216966008203221333371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11810314304087501027555957 1107216966008203221333371)
                    ·
                      rfl

theorem cell23_6468892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_6468892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468892 prefixEnd_6468892 := by exact prefixLift 6468892
  have htrace : WordTrace (prefixWord ++ tailWord_6468892) baseStart_6468892 baseEnd_6468892 := by
    simpa [prefixWord, tailWord_6468892, baseEnd_6468892] using wordTrace_append hprefix tailTrace_6468892
  have hstable : (prefixWord ++ tailWord_6468892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468892).length < 2 ^ (prefixWord ++ tailWord_6468892).sum := by decide
  have hdescent : baseEnd_6468892 < baseStart_6468892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468899 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 1, 5, 2]
def baseStart_6468899 : Nat := 118140960795 + 6468899 * 2 ^ 59
def prefixEnd_6468899 : Nat := 4983230072969 + 3 ^ 40 * 6468899 * 2
def baseEnd_6468899 : Nat := 3321654492389191136612581

theorem tailTrace_6468899 : CollatzResearch.WordTrace tailWord_6468899 prefixEnd_6468899 3321654492389191136612581 := by
  unfold tailWord_6468899
  simp only [CollatzResearch.WordTrace]
  refine ⟨235940129791291197836689751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157293419860860798557793167 235940129791291197836689751)
  ·
    refine ⟨353910194686936796755034627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235940129791291197836689751 353910194686936796755034627)
    ·
      refine ⟨530865292030405195132551941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353910194686936796755034627 530865292030405195132551941)
      ·
        refine ⟨99537242255700974087353489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 530865292030405195132551941 99537242255700974087353489)
        ·
          refine ⟨74652931691775730565515117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99537242255700974087353489 74652931691775730565515117)
          ·
            refine ⟨27994849384415898962068169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74652931691775730565515117 27994849384415898962068169)
            ·
              refine ⟨20996137038311924221551127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27994849384415898962068169 20996137038311924221551127)
              ·
                refine ⟨31494205557467886332326691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20996137038311924221551127 31494205557467886332326691)
                ·
                  refine ⟨47241308336201829498490037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31494205557467886332326691 47241308336201829498490037)
                  ·
                    refine ⟨4428872656518921515483441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47241308336201829498490037 4428872656518921515483441)
                    ·
                      refine ⟨3321654492389191136612581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4428872656518921515483441 3321654492389191136612581)
                      ·
                        rfl

theorem cell23_6468899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_6468899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468899 prefixEnd_6468899 := by exact prefixLift 6468899
  have htrace : WordTrace (prefixWord ++ tailWord_6468899) baseStart_6468899 baseEnd_6468899 := by
    simpa [prefixWord, tailWord_6468899, baseEnd_6468899] using wordTrace_append hprefix tailTrace_6468899
  have hstable : (prefixWord ++ tailWord_6468899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468899).length < 2 ^ (prefixWord ++ tailWord_6468899).sum := by decide
  have hdescent : baseEnd_6468899 < baseStart_6468899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468942 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_6468942 : Nat := 118140960795 + 6468942 * 2 ^ 59
def prefixEnd_6468942 : Nat := 4983230072969 + 3 ^ 40 * 6468942 * 2
def baseEnd_6468942 : Nat := 3321676572057334468374883

theorem tailTrace_6468942 : CollatzResearch.WordTrace tailWord_6468942 prefixEnd_6468942 3321676572057334468374883 := by
  unfold tailWord_6468942
  simp only [CollatzResearch.WordTrace]
  refine ⟨29492712266266927022563135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157294465420090277453670053 29492712266266927022563135)
  ·
    refine ⟨44239068399400390533844703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29492712266266927022563135 44239068399400390533844703)
    ·
      refine ⟨66358602599100585800767055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44239068399400390533844703 66358602599100585800767055)
      ·
        refine ⟨99537903898650878701150583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66358602599100585800767055 99537903898650878701150583)
        ·
          refine ⟨149306855847976318051725875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99537903898650878701150583 149306855847976318051725875)
          ·
            refine ⟨223960283771964477077588813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149306855847976318051725875 223960283771964477077588813)
            ·
              refine ⟨83985106414486678904095805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223960283771964477077588813 83985106414486678904095805)
              ·
                refine ⟨31494414905432504589035927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83985106414486678904095805 31494414905432504589035927)
                ·
                  refine ⟨47241622358148756883553891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31494414905432504589035927 47241622358148756883553891)
                  ·
                    refine ⟨70862433537223135325330837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47241622358148756883553891 70862433537223135325330837)
                    ·
                      refine ⟨3321676572057334468374883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70862433537223135325330837 3321676572057334468374883)
                      ·
                        rfl

theorem cell23_6468942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_6468942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468942 prefixEnd_6468942 := by exact prefixLift 6468942
  have htrace : WordTrace (prefixWord ++ tailWord_6468942) baseStart_6468942 baseEnd_6468942 := by
    simpa [prefixWord, tailWord_6468942, baseEnd_6468942] using wordTrace_append hprefix tailTrace_6468942
  have hstable : (prefixWord ++ tailWord_6468942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468942).length < 2 ^ (prefixWord ++ tailWord_6468942).sum := by decide
  have hdescent : baseEnd_6468942 < baseStart_6468942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468946 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_6468946 : Nat := 118140960795 + 6468946 * 2 ^ 59
def prefixEnd_6468946 : Nat := 4983230072969 + 3 ^ 40 * 6468946 * 2
def baseEnd_6468946 : Nat := 3321678625979952452724865

theorem tailTrace_6468946 : CollatzResearch.WordTrace tailWord_6468946 prefixEnd_6468946 3321678625979952452724865 := by
  unfold tailWord_6468946
  simp only [CollatzResearch.WordTrace]
  refine ⟨58985461005530231215912673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157294562681413949909100461 58985461005530231215912673)
  ·
    refine ⟨44239095754147673411934505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58985461005530231215912673 44239095754147673411934505)
    ·
      refine ⟨33179321815610755058950879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44239095754147673411934505 33179321815610755058950879)
      ·
        refine ⟨49768982723416132588426319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33179321815610755058950879 49768982723416132588426319)
        ·
          refine ⟨74653474085124198882639479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49768982723416132588426319 74653474085124198882639479)
          ·
            refine ⟨111980211127686298323959219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74653474085124198882639479 111980211127686298323959219)
            ·
              refine ⟨167970316691529447485938829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111980211127686298323959219 167970316691529447485938829)
              ·
                refine ⟨62988868759323542807227061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167970316691529447485938829 62988868759323542807227061)
                ·
                  refine ⟨5905206446186582138177537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62988868759323542807227061 5905206446186582138177537)
                  ·
                    refine ⟨4428904834639936603633153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5905206446186582138177537 4428904834639936603633153)
                    ·
                      refine ⟨3321678625979952452724865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4428904834639936603633153 3321678625979952452724865)
                      ·
                        rfl

theorem cell23_6468946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_6468946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468946 prefixEnd_6468946 := by exact prefixLift 6468946
  have htrace : WordTrace (prefixWord ++ tailWord_6468946) baseStart_6468946 baseEnd_6468946 := by
    simpa [prefixWord, tailWord_6468946, baseEnd_6468946] using wordTrace_append hprefix tailTrace_6468946
  have hstable : (prefixWord ++ tailWord_6468946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468946).length < 2 ^ (prefixWord ++ tailWord_6468946).sum := by decide
  have hdescent : baseEnd_6468946 < baseStart_6468946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468974 : List Nat := [4, 1, 2, 4, 1, 2, 2, 2, 1, 1, 3]
def baseStart_6468974 : Nat := 118140960795 + 6468974 * 2 ^ 59
def prefixEnd_6468974 : Nat := 4983230072969 + 3 ^ 40 * 6468974 * 2
def baseEnd_6468974 : Nat := 3321693003438278343174737

theorem tailTrace_6468974 : CollatzResearch.WordTrace tailWord_6468974 prefixEnd_6468974 3321693003438278343174737 := by
  unfold tailWord_6468974
  simp only [CollatzResearch.WordTrace]
  refine ⟨29492858158252435705708747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157295243510679657097113317 29492858158252435705708747)
  ·
    refine ⟨44239287237378653558563121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29492858158252435705708747 44239287237378653558563121)
    ·
      refine ⟨33179465428033990168922341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44239287237378653558563121 33179465428033990168922341)
      ·
        refine ⟨6221149767756373156672939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33179465428033990168922341 6221149767756373156672939)
        ·
          refine ⟨9331724651634559735009409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6221149767756373156672939 9331724651634559735009409)
          ·
            refine ⟨6998793488725919801257057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9331724651634559735009409 6998793488725919801257057)
            ·
              refine ⟨5249095116544439850942793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6998793488725919801257057 5249095116544439850942793)
              ·
                refine ⟨3936821337408329888207095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5249095116544439850942793 3936821337408329888207095)
                ·
                  refine ⟨5905232006112494832310643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3936821337408329888207095 5905232006112494832310643)
                  ·
                    refine ⟨8857848009168742248465965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5905232006112494832310643 8857848009168742248465965)
                    ·
                      refine ⟨3321693003438278343174737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8857848009168742248465965 3321693003438278343174737)
                      ·
                        rfl

theorem cell23_6468974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_6468974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468974 prefixEnd_6468974 := by exact prefixLift 6468974
  have htrace : WordTrace (prefixWord ++ tailWord_6468974) baseStart_6468974 baseEnd_6468974 := by
    simpa [prefixWord, tailWord_6468974, baseEnd_6468974] using wordTrace_append hprefix tailTrace_6468974
  have hstable : (prefixWord ++ tailWord_6468974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468974).length < 2 ^ (prefixWord ++ tailWord_6468974).sum := by decide
  have hdescent : baseEnd_6468974 < baseStart_6468974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6468996 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_6468996 : Nat := 118140960795 + 6468996 * 2 ^ 59
def prefixEnd_6468996 : Nat := 4983230072969 + 3 ^ 40 * 6468996 * 2
def baseEnd_6468996 : Nat := 3321704300012677257099635

theorem tailTrace_6468996 : CollatzResearch.WordTrace tailWord_6468996 prefixEnd_6468996 3321704300012677257099635 := by
  unfold tailWord_6468996
  simp only [CollatzResearch.WordTrace]
  refine ⟨117971833835969891701485421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157295778447959855601980561 117971833835969891701485421)
  ·
    refine ⟨44239437688488709388057033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117971833835969891701485421 44239437688488709388057033)
    ·
      refine ⟨33179578266366532041042775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44239437688488709388057033 33179578266366532041042775)
      ·
        refine ⟨49769367399549798061564163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33179578266366532041042775 49769367399549798061564163)
        ·
          refine ⟨74654051099324697092346245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49769367399549798061564163 74654051099324697092346245)
          ·
            refine ⟨13997634581123380704814921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74654051099324697092346245 13997634581123380704814921)
            ·
              refine ⟨10498225935842535528611191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13997634581123380704814921 10498225935842535528611191)
              ·
                refine ⟨15747338903763803292916787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10498225935842535528611191 15747338903763803292916787)
                ·
                  refine ⟨23621008355645704939375181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15747338903763803292916787 23621008355645704939375181)
                  ·
                    refine ⟨8857878133367139352265693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23621008355645704939375181 8857878133367139352265693)
                    ·
                      refine ⟨3321704300012677257099635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8857878133367139352265693 3321704300012677257099635)
                      ·
                        rfl

theorem cell23_6468996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_6468996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6468996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6468996 prefixEnd_6468996 := by exact prefixLift 6468996
  have htrace : WordTrace (prefixWord ++ tailWord_6468996) baseStart_6468996 baseEnd_6468996 := by
    simpa [prefixWord, tailWord_6468996, baseEnd_6468996] using wordTrace_append hprefix tailTrace_6468996
  have hstable : (prefixWord ++ tailWord_6468996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6468996).length < 2 ^ (prefixWord ++ tailWord_6468996).sum := by decide
  have hdescent : baseEnd_6468996 < baseStart_6468996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6468996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469023 : List Nat := [1, 1, 2, 5, 1, 3, 1, 3, 1, 3, 2]
def baseStart_6469023 : Nat := 118140960795 + 6469023 * 2 ^ 59
def prefixEnd_6469023 : Nat := 4983230072969 + 3 ^ 40 * 6469023 * 2
def baseEnd_6469023 : Nat := 3321718163990348651462011

theorem tailTrace_6469023 : CollatzResearch.WordTrace tailWord_6469023 prefixEnd_6469023 3321718163990348651462011 := by
  unfold tailWord_6469023
  simp only [CollatzResearch.WordTrace]
  refine ⟨235944652442841967014203723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157296434961894644676135815 235944652442841967014203723)
  ·
    refine ⟨353916978664262950521305585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235944652442841967014203723 353916978664262950521305585)
    ·
      refine ⟨265437733998197212890979189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353916978664262950521305585 265437733998197212890979189)
      ·
        refine ⟨24884787562330988708529299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 265437733998197212890979189 24884787562330988708529299)
        ·
          refine ⟨37327181343496483062793949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24884787562330988708529299 37327181343496483062793949)
          ·
            refine ⟨13997693003811181148547731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37327181343496483062793949 13997693003811181148547731)
            ·
              refine ⟨20996539505716771722821597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13997693003811181148547731 20996539505716771722821597)
              ·
                refine ⟨7873702314643789396058099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20996539505716771722821597 7873702314643789396058099)
                ·
                  refine ⟨11810553471965684094087149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7873702314643789396058099 11810553471965684094087149)
                  ·
                    refine ⟨4428957551987131535282681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11810553471965684094087149 4428957551987131535282681)
                    ·
                      refine ⟨3321718163990348651462011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4428957551987131535282681 3321718163990348651462011)
                      ·
                        rfl

theorem cell23_6469023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_6469023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469023 prefixEnd_6469023 := by exact prefixLift 6469023
  have htrace : WordTrace (prefixWord ++ tailWord_6469023) baseStart_6469023 baseEnd_6469023 := by
    simpa [prefixWord, tailWord_6469023, baseEnd_6469023] using wordTrace_append hprefix tailTrace_6469023
  have hstable : (prefixWord ++ tailWord_6469023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469023).length < 2 ^ (prefixWord ++ tailWord_6469023).sum := by decide
  have hdescent : baseEnd_6469023 < baseStart_6469023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469089 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 4, 5]
def baseStart_6469089 : Nat := 118140960795 + 6469089 * 2 ^ 59
def prefixEnd_6469089 : Nat := 4983230072969 + 3 ^ 40 * 6469089 * 2
def baseEnd_6469089 : Nat := 1107250684571181797745569

theorem tailTrace_6469089 : CollatzResearch.WordTrace tailWord_6469089 prefixEnd_6469089 1107250684571181797745569 := by
  unfold tailWord_6469089
  simp only [CollatzResearch.WordTrace]
  refine ⟨235947059660602860286106321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157298039773735240190737547 235947059660602860286106321)
  ·
    refine ⟨176960294745452145214579741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235947059660602860286106321 176960294745452145214579741)
    ·
      refine ⟨66360110529544554455467403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176960294745452145214579741 66360110529544554455467403)
      ·
        refine ⟨99540165794316831683201105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66360110529544554455467403 99540165794316831683201105)
        ·
          refine ⟨74655124345737623762400829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99540165794316831683201105 74655124345737623762400829)
          ·
            refine ⟨27995671629651608910900311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74655124345737623762400829 27995671629651608910900311)
            ·
              refine ⟨41993507444477413366350467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27995671629651608910900311 41993507444477413366350467)
              ·
                refine ⟨62990261166716120049525701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41993507444477413366350467 62990261166716120049525701)
                ·
                  refine ⟨11810673968759272509286069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62990261166716120049525701 11810673968759272509286069)
                  ·
                    refine ⟨1107250684571181797745569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11810673968759272509286069 1107250684571181797745569)
                    ·
                      rfl

theorem cell23_6469089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_6469089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469089 prefixEnd_6469089 := by exact prefixLift 6469089
  have htrace : WordTrace (prefixWord ++ tailWord_6469089) baseStart_6469089 baseEnd_6469089 := by
    simpa [prefixWord, tailWord_6469089, baseEnd_6469089] using wordTrace_append hprefix tailTrace_6469089
  have hstable : (prefixWord ++ tailWord_6469089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469089).length < 2 ^ (prefixWord ++ tailWord_6469089).sum := by decide
  have hdescent : baseEnd_6469089 < baseStart_6469089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469096 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_6469096 : Nat := 118140960795 + 6469096 * 2 ^ 59
def prefixEnd_6469096 : Nat := 4983230072969 + 3 ^ 40 * 6469096 * 2
def baseEnd_6469096 : Nat := 3321755648078126865849175

theorem tailTrace_6469096 : CollatzResearch.WordTrace tailWord_6469096 prefixEnd_6469096 3321755648078126865849175 := by
  unfold tailWord_6469096
  simp only [CollatzResearch.WordTrace]
  refine ⟨117973657485788750240805571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157298209981051666987740761 117973657485788750240805571)
  ·
    refine ⟨176960486228683125361208357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117973657485788750240805571 176960486228683125361208357)
    ·
      refine ⟨33180091167878086005226567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176960486228683125361208357 33180091167878086005226567)
      ·
        refine ⟨49770136751817129007839851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33180091167878086005226567 49770136751817129007839851)
        ·
          refine ⟨74655205127725693511759777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49770136751817129007839851 74655205127725693511759777)
          ·
            refine ⟨55991403845794270133819833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74655205127725693511759777 55991403845794270133819833)
            ·
              refine ⟨41993552884345702600364875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55991403845794270133819833 41993552884345702600364875)
              ·
                refine ⟨62990329326518553900547313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41993552884345702600364875 62990329326518553900547313)
                ·
                  refine ⟨47242746994888915425410485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62990329326518553900547313 47242746994888915425410485)
                  ·
                    refine ⟨4429007530770835821132233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47242746994888915425410485 4429007530770835821132233)
                    ·
                      refine ⟨3321755648078126865849175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4429007530770835821132233 3321755648078126865849175)
                      ·
                        rfl

theorem cell23_6469096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_6469096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469096 prefixEnd_6469096 := by exact prefixLift 6469096
  have htrace : WordTrace (prefixWord ++ tailWord_6469096) baseStart_6469096 baseEnd_6469096 := by
    simpa [prefixWord, tailWord_6469096, baseEnd_6469096] using wordTrace_append hprefix tailTrace_6469096
  have hstable : (prefixWord ++ tailWord_6469096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469096).length < 2 ^ (prefixWord ++ tailWord_6469096).sum := by decide
  have hdescent : baseEnd_6469096 < baseStart_6469096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469160 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_6469160 : Nat := 118140960795 + 6469160 * 2 ^ 59
def prefixEnd_6469160 : Nat := 4983230072969 + 3 ^ 40 * 6469160 * 2
def baseEnd_6469160 : Nat := 3321788510840014615448881

theorem tailTrace_6469160 : CollatzResearch.WordTrace tailWord_6469160 prefixEnd_6469160 3321788510840014615448881 := by
  unfold tailWord_6469160
  simp only [CollatzResearch.WordTrace]
  refine ⟨117974824621672819705970467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157299766162230426274627289 117974824621672819705970467)
  ·
    refine ⟨176962236932509229558955701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117974824621672819705970467 176962236932509229558955701)
    ·
      refine ⟨16590209712422740271152097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176962236932509229558955701 16590209712422740271152097)
      ·
        refine ⟨12442657284317055203364073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16590209712422740271152097 12442657284317055203364073)
        ·
          refine ⟨9331992963237791402523055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12442657284317055203364073 9331992963237791402523055)
          ·
            refine ⟨13997989444856687103784583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9331992963237791402523055 13997989444856687103784583)
            ·
              refine ⟨20996984167285030655676875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13997989444856687103784583 20996984167285030655676875)
              ·
                refine ⟨31495476250927545983515313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20996984167285030655676875 31495476250927545983515313)
                ·
                  refine ⟨23621607188195659487636485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31495476250927545983515313 23621607188195659487636485)
                  ·
                    refine ⟨4429051347786686153931841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23621607188195659487636485 4429051347786686153931841)
                    ·
                      refine ⟨3321788510840014615448881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4429051347786686153931841 3321788510840014615448881)
                      ·
                        rfl

theorem cell23_6469160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_6469160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469160 prefixEnd_6469160 := by exact prefixLift 6469160
  have htrace : WordTrace (prefixWord ++ tailWord_6469160) baseStart_6469160 baseEnd_6469160 := by
    simpa [prefixWord, tailWord_6469160, baseEnd_6469160] using wordTrace_append hprefix tailTrace_6469160
  have hstable : (prefixWord ++ tailWord_6469160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469160).length < 2 ^ (prefixWord ++ tailWord_6469160).sum := by decide
  have hdescent : baseEnd_6469160 < baseStart_6469160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469180 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 2, 2, 3]
def baseStart_6469180 : Nat := 118140960795 + 6469180 * 2 ^ 59
def prefixEnd_6469180 : Nat := 4983230072969 + 3 ^ 40 * 6469180 * 2
def baseEnd_6469180 : Nat := 3321798780453104537198789

theorem tailTrace_6469180 : CollatzResearch.WordTrace tailWord_6469180 prefixEnd_6469180 3321798780453104537198789 := by
  unfold tailWord_6469180
  simp only [CollatzResearch.WordTrace]
  refine ⟨117975189351636591413834497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157300252468848788551779329 117975189351636591413834497)
  ·
    refine ⟨88481392013727443560375873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117975189351636591413834497 88481392013727443560375873)
    ·
      refine ⟨66361044010295582670281905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88481392013727443560375873 66361044010295582670281905)
      ·
        refine ⟨49770783007721687002711429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66361044010295582670281905 49770783007721687002711429)
        ·
          refine ⟨9332021813947816313008393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49770783007721687002711429 9332021813947816313008393)
          ·
            refine ⟨6999016360460862234756295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9332021813947816313008393 6999016360460862234756295)
            ·
              refine ⟨10498524540691293352134443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6999016360460862234756295 10498524540691293352134443)
              ·
                refine ⟨15747786811036940028201665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10498524540691293352134443 15747786811036940028201665)
                ·
                  refine ⟨11810840108277705021151249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15747786811036940028201665 11810840108277705021151249)
                  ·
                    refine ⟨8858130081208278765863437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11810840108277705021151249 8858130081208278765863437)
                    ·
                      refine ⟨3321798780453104537198789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8858130081208278765863437 3321798780453104537198789)
                      ·
                        rfl

theorem cell23_6469180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_6469180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469180 prefixEnd_6469180 := by exact prefixLift 6469180
  have htrace : WordTrace (prefixWord ++ tailWord_6469180) baseStart_6469180 baseEnd_6469180 := by
    simpa [prefixWord, tailWord_6469180, baseEnd_6469180] using wordTrace_append hprefix tailTrace_6469180
  have hstable : (prefixWord ++ tailWord_6469180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469180).length < 2 ^ (prefixWord ++ tailWord_6469180).sum := by decide
  have hdescent : baseEnd_6469180 < baseStart_6469180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469209 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 3, 6]
def baseStart_6469209 : Nat := 118140960795 + 6469209 * 2 ^ 59
def prefixEnd_6469209 : Nat := 4983230072969 + 3 ^ 40 * 6469209 * 2
def baseEnd_6469209 : Nat := 1107271223797361641245385

theorem tailTrace_6469209 : CollatzResearch.WordTrace tailWord_6469209 prefixEnd_6469209 1107271223797361641245385 := by
  unfold tailWord_6469209
  simp only [CollatzResearch.WordTrace]
  refine ⟨235951436420168120780474681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157300957613445413853649787 235951436420168120780474681)
  ·
    refine ⟨176963577315126090585356011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235951436420168120780474681 176963577315126090585356011)
    ·
      refine ⟨265445365972689135878034017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176963577315126090585356011 265445365972689135878034017)
      ·
        refine ⟨199084024479516851908525513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265445365972689135878034017 199084024479516851908525513)
        ·
          refine ⟨149313018359637638931394135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199084024479516851908525513 149313018359637638931394135)
          ·
            refine ⟨223969527539456458397091203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149313018359637638931394135 223969527539456458397091203)
            ·
              refine ⟨335954291309184687595636805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223969527539456458397091203 335954291309184687595636805)
              ·
                refine ⟨62991429620472128924181901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335954291309184687595636805 62991429620472128924181901)
                ·
                  refine ⟨23621786107677048346568213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62991429620472128924181901 23621786107677048346568213)
                  ·
                    refine ⟨1107271223797361641245385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23621786107677048346568213 1107271223797361641245385)
                    ·
                      rfl

theorem cell23_6469209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_6469209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469209 prefixEnd_6469209 := by exact prefixLift 6469209
  have htrace : WordTrace (prefixWord ++ tailWord_6469209) baseStart_6469209 baseEnd_6469209 := by
    simpa [prefixWord, tailWord_6469209, baseEnd_6469209] using wordTrace_append hprefix tailTrace_6469209
  have hstable : (prefixWord ++ tailWord_6469209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469209).length < 2 ^ (prefixWord ++ tailWord_6469209).sum := by decide
  have hdescent : baseEnd_6469209 < baseStart_6469209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469230 : List Nat := [4, 1, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_6469230 : Nat := 118140960795 + 6469230 * 2 ^ 59
def prefixEnd_6469230 : Nat := 4983230072969 + 3 ^ 40 * 6469230 * 2
def baseEnd_6469230 : Nat := 1107274818161943113857853

theorem tailTrace_6469230 : CollatzResearch.WordTrace tailWord_6469230 prefixEnd_6469230 1107274818161943113857853 := by
  unfold tailWord_6469230
  simp only [CollatzResearch.WordTrace]
  refine ⟨29494025294136505170873643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157301468235394694244659429 29494025294136505170873643)
  ·
    refine ⟨44241037941204757756310465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29494025294136505170873643 44241037941204757756310465)
    ·
      refine ⟨33180778455903568317232849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44241037941204757756310465 33180778455903568317232849)
      ·
        refine ⟨24885583841927676237924637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33180778455903568317232849 24885583841927676237924637)
        ·
          refine ⟨9332093940722878589221739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24885583841927676237924637 9332093940722878589221739)
          ·
            refine ⟨13998140911084317883832609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9332093940722878589221739 13998140911084317883832609)
            ·
              refine ⟨10498605683313238412874457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13998140911084317883832609 10498605683313238412874457)
              ·
                refine ⟨7873954262484928809655843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10498605683313238412874457 7873954262484928809655843)
                ·
                  refine ⟨11810931393727393214483765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7873954262484928809655843 11810931393727393214483765)
                  ·
                    refine ⟨1107274818161943113857853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11810931393727393214483765 1107274818161943113857853)
                    ·
                      rfl

theorem cell23_6469230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_6469230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469230 prefixEnd_6469230 := by exact prefixLift 6469230
  have htrace : WordTrace (prefixWord ++ tailWord_6469230) baseStart_6469230 baseEnd_6469230 := by
    simpa [prefixWord, tailWord_6469230, baseEnd_6469230] using wordTrace_append hprefix tailTrace_6469230
  have hstable : (prefixWord ++ tailWord_6469230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469230).length < 2 ^ (prefixWord ++ tailWord_6469230).sum := by decide
  have hdescent : baseEnd_6469230 < baseStart_6469230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469253 : List Nat := [1, 3, 1, 1, 4, 1, 1, 5, 1, 2, 3]
def baseStart_6469253 : Nat := 118140960795 + 6469253 * 2 ^ 59
def prefixEnd_6469253 : Nat := 4983230072969 + 3 ^ 40 * 6469253 * 2
def baseEnd_6469253 : Nat := 3321836264540882751585953

theorem tailTrace_6469253 : CollatzResearch.WordTrace tailWord_6469253 prefixEnd_6469253 3321836264540882751585953 := by
  unfold tailWord_6469253
  simp only [CollatzResearch.WordTrace]
  refine ⟨235953041232008716295076413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157302027488005810863384275 235953041232008716295076413)
  ·
    refine ⟨88482390462003268610653655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235953041232008716295076413 88482390462003268610653655)
    ·
      refine ⟨132723585693004902915980483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88482390462003268610653655 132723585693004902915980483)
      ·
        refine ⟨199085378539507354373970725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132723585693004902915980483 199085378539507354373970725)
        ·
          refine ⟨37328508476157628945119511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199085378539507354373970725 37328508476157628945119511)
          ·
            refine ⟨55992762714236443417679267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37328508476157628945119511 55992762714236443417679267)
            ·
              refine ⟨83989144071354665126518901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55992762714236443417679267 83989144071354665126518901)
              ·
                refine ⟨7873982256689499855611147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83989144071354665126518901 7873982256689499855611147)
                ·
                  refine ⟨11810973385034249783416721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7873982256689499855611147 11810973385034249783416721)
                  ·
                    refine ⟨8858230038775687337562541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11810973385034249783416721 8858230038775687337562541)
                    ·
                      refine ⟨3321836264540882751585953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8858230038775687337562541 3321836264540882751585953)
                      ·
                        rfl

theorem cell23_6469253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_6469253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469253 prefixEnd_6469253 := by exact prefixLift 6469253
  have htrace : WordTrace (prefixWord ++ tailWord_6469253) baseStart_6469253 baseEnd_6469253 := by
    simpa [prefixWord, tailWord_6469253, baseEnd_6469253] using wordTrace_append hprefix tailTrace_6469253
  have hstable : (prefixWord ++ tailWord_6469253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469253).length < 2 ^ (prefixWord ++ tailWord_6469253).sum := by decide
  have hdescent : baseEnd_6469253 < baseStart_6469253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469318 : List Nat := [6, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_6469318 : Nat := 118140960795 + 6469318 * 2 ^ 59
def prefixEnd_6469318 : Nat := 4983230072969 + 3 ^ 40 * 6469318 * 2
def baseEnd_6469318 : Nat := 3321869640783424997273155

theorem tailTrace_6469318 : CollatzResearch.WordTrace tailWord_6469318 prefixEnd_6469318 3321869640783424997273155 := by
  unfold tailWord_6469318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7373606624274163512381019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157303607984515488264128405 7373606624274163512381019)
  ·
    refine ⟨11060409936411245268571529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7373606624274163512381019 11060409936411245268571529)
    ·
      refine ⟨8295307452308433951428647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11060409936411245268571529 8295307452308433951428647)
      ·
        refine ⟨12442961178462650927142971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8295307452308433951428647 12442961178462650927142971)
        ·
          refine ⟨18664441767693976390714457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12442961178462650927142971 18664441767693976390714457)
          ·
            refine ⟨13998331325770482293035843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18664441767693976390714457 13998331325770482293035843)
            ·
              refine ⟨20997496988655723439553765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13998331325770482293035843 20997496988655723439553765)
              ·
                refine ⟨3937030685372948144916331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20997496988655723439553765 3937030685372948144916331)
                ·
                  refine ⟨5905546028059422217374497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3937030685372948144916331 5905546028059422217374497)
                  ·
                    refine ⟨4429159521044566663030873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5905546028059422217374497 4429159521044566663030873)
                    ·
                      refine ⟨3321869640783424997273155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4429159521044566663030873 3321869640783424997273155)
                      ·
                        rfl

theorem cell23_6469318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_6469318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469318 prefixEnd_6469318 := by exact prefixLift 6469318
  have htrace : WordTrace (prefixWord ++ tailWord_6469318) baseStart_6469318 baseEnd_6469318 := by
    simpa [prefixWord, tailWord_6469318, baseEnd_6469318] using wordTrace_append hprefix tailTrace_6469318
  have hstable : (prefixWord ++ tailWord_6469318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469318).length < 2 ^ (prefixWord ++ tailWord_6469318).sum := by decide
  have hdescent : baseEnd_6469318 < baseStart_6469318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469334 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_6469334 : Nat := 118140960795 + 6469334 * 2 ^ 59
def prefixEnd_6469334 : Nat := 4983230072969 + 3 ^ 40 * 6469334 * 2
def baseEnd_6469334 : Nat := 3321877856473896934673081

theorem tailTrace_6469334 : CollatzResearch.WordTrace tailWord_6469334 prefixEnd_6469334 3321877856473896934673081 := by
  unfold tailWord_6469334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14747249721544704195548441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157303997029810178085850037 14747249721544704195548441)
  ·
    refine ⟨11060437291158528146661331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14747249721544704195548441 11060437291158528146661331)
    ·
      refine ⟨16590655936737792219991997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11060437291158528146661331 16590655936737792219991997)
      ·
        refine ⟨6221495976276672082496999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16590655936737792219991997 6221495976276672082496999)
        ·
          refine ⟨9332243964415008123745499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6221495976276672082496999 9332243964415008123745499)
          ·
            refine ⟨13998365946622512185618249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9332243964415008123745499 13998365946622512185618249)
            ·
              refine ⟨10498774459966884139213687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13998365946622512185618249 10498774459966884139213687)
              ·
                refine ⟨15748161689950326208820531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10498774459966884139213687 15748161689950326208820531)
                ·
                  refine ⟨23622242534925489313230797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15748161689950326208820531 23622242534925489313230797)
                  ·
                    refine ⟨8858340950597058492461549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23622242534925489313230797 8858340950597058492461549)
                    ·
                      refine ⟨3321877856473896934673081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8858340950597058492461549 3321877856473896934673081)
                      ·
                        rfl

theorem cell23_6469334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_6469334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469334 prefixEnd_6469334 := by exact prefixLift 6469334
  have htrace : WordTrace (prefixWord ++ tailWord_6469334) baseStart_6469334 baseEnd_6469334 := by
    simpa [prefixWord, tailWord_6469334, baseEnd_6469334] using wordTrace_append hprefix tailTrace_6469334
  have hstable : (prefixWord ++ tailWord_6469334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469334).length < 2 ^ (prefixWord ++ tailWord_6469334).sum := by decide
  have hdescent : baseEnd_6469334 < baseStart_6469334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469363 : List Nat := [1, 1, 1, 2, 2, 3, 3, 5, 5]
def baseStart_6469363 : Nat := 118140960795 + 6469363 * 2 ^ 59
def prefixEnd_6469363 : Nat := 4983230072969 + 3 ^ 40 * 6469363 * 2
def baseEnd_6469363 : Nat := 369099194156986369023383

theorem tailTrace_6469363 : CollatzResearch.WordTrace tailWord_6469363 prefixEnd_6469363 369099194156986369023383 := by
  unfold tailWord_6469363
  simp only [CollatzResearch.WordTrace]
  refine ⟨235957053261610205081580743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157304702174406803387720495 235957053261610205081580743)
  ·
    refine ⟨353935579892415307622371115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235957053261610205081580743 353935579892415307622371115)
    ·
      refine ⟨530903369838622961433556673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353935579892415307622371115 530903369838622961433556673)
      ·
        refine ⟨398177527378967221075167505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530903369838622961433556673 398177527378967221075167505)
        ·
          refine ⟨298633145534225415806375629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398177527378967221075167505 298633145534225415806375629)
          ·
            refine ⟨111987429575334530927390861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298633145534225415806375629 111987429575334530927390861)
            ·
              refine ⟨41995286090750449097771573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111987429575334530927390861 41995286090750449097771573)
              ·
                refine ⟨3937058071007854602916085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41995286090750449097771573 3937058071007854602916085)
                ·
                  refine ⟨369099194156986369023383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3937058071007854602916085 369099194156986369023383)
                  ·
                    rfl

theorem cell23_6469363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 5].length) (baseStart_6469363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469363 prefixEnd_6469363 := by exact prefixLift 6469363
  have htrace : WordTrace (prefixWord ++ tailWord_6469363) baseStart_6469363 baseEnd_6469363 := by
    simpa [prefixWord, tailWord_6469363, baseEnd_6469363] using wordTrace_append hprefix tailTrace_6469363
  have hstable : (prefixWord ++ tailWord_6469363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469363).length < 2 ^ (prefixWord ++ tailWord_6469363).sum := by decide
  have hdescent : baseEnd_6469363 < baseStart_6469363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469374 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_6469374 : Nat := 118140960795 + 6469374 * 2 ^ 59
def prefixEnd_6469374 : Nat := 4983230072969 + 3 ^ 40 * 6469374 * 2
def baseEnd_6469374 : Nat := 3321898395700076778172897

theorem tailTrace_6469374 : CollatzResearch.WordTrace tailWord_6469374 prefixEnd_6469374 3321898395700076778172897 := by
  unfold tailWord_6469374
  simp only [CollatzResearch.WordTrace]
  refine ⟨29494681808071294245028897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157304969643046902640154117 29494681808071294245028897)
  ·
    refine ⟨22121011356053470683771673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29494681808071294245028897 22121011356053470683771673)
    ·
      refine ⟨16590758517040103012828755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22121011356053470683771673 16590758517040103012828755)
      ·
        refine ⟨24886137775560154519243133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16590758517040103012828755 24886137775560154519243133)
        ·
          refine ⟨9332301665835057944716175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24886137775560154519243133 9332301665835057944716175)
          ·
            refine ⟨13998452498752586917074263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9332301665835057944716175 13998452498752586917074263)
            ·
              refine ⟨20997678748128880375611395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13998452498752586917074263 20997678748128880375611395)
              ·
                refine ⟨31496518122193320563417093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20997678748128880375611395 31496518122193320563417093)
                ·
                  refine ⟨5905597147911247605640705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31496518122193320563417093 5905597147911247605640705)
                  ·
                    refine ⟨4429197860933435704230529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5905597147911247605640705 4429197860933435704230529)
                    ·
                      refine ⟨3321898395700076778172897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4429197860933435704230529 3321898395700076778172897)
                      ·
                        rfl

theorem cell23_6469374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_6469374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469374 prefixEnd_6469374 := by exact prefixLift 6469374
  have htrace : WordTrace (prefixWord ++ tailWord_6469374) baseStart_6469374 baseEnd_6469374 := by
    simpa [prefixWord, tailWord_6469374, baseEnd_6469374] using wordTrace_append hprefix tailTrace_6469374
  have hstable : (prefixWord ++ tailWord_6469374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469374).length < 2 ^ (prefixWord ++ tailWord_6469374).sum := by decide
  have hdescent : baseEnd_6469374 < baseStart_6469374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469380 : List Nat := [2, 3, 2, 2, 1, 2, 2, 4, 5]
def baseStart_6469380 : Nat := 118140960795 + 6469380 * 2 ^ 59
def prefixEnd_6469380 : Nat := 4983230072969 + 3 ^ 40 * 6469380 * 2
def baseEnd_6469380 : Nat := 369100164064889306077541

theorem tailTrace_6469380 : CollatzResearch.WordTrace tailWord_6469380 prefixEnd_6469380 369100164064889306077541 := by
  unfold tailWord_6469380
  simp only [CollatzResearch.WordTrace]
  refine ⟨117978836651274308492474797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157305115535032411323299729 117978836651274308492474797)
  ·
    refine ⟨44242063744227865684678049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117978836651274308492474797 44242063744227865684678049)
    ·
      refine ⟨33181547808170899263508537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44242063744227865684678049 33181547808170899263508537)
      ·
        refine ⟨24886160856128174447631403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33181547808170899263508537 24886160856128174447631403)
        ·
          refine ⟨37329241284192261671447105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24886160856128174447631403 37329241284192261671447105)
          ·
            refine ⟨27996930963144196253585329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37329241284192261671447105 27996930963144196253585329)
            ·
              refine ⟨20997698222358147190188997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27996930963144196253585329 20997698222358147190188997)
              ·
                refine ⟨3937068416692152598160437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20997698222358147190188997 3937068416692152598160437)
                ·
                  refine ⟨369100164064889306077541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3937068416692152598160437 369100164064889306077541)
                  ·
                    rfl

theorem cell23_6469380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_6469380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469380 prefixEnd_6469380 := by exact prefixLift 6469380
  have htrace : WordTrace (prefixWord ++ tailWord_6469380) baseStart_6469380 baseEnd_6469380 := by
    simpa [prefixWord, tailWord_6469380, baseEnd_6469380] using wordTrace_append hprefix tailTrace_6469380
  have hstable : (prefixWord ++ tailWord_6469380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469380).length < 2 ^ (prefixWord ++ tailWord_6469380).sum := by decide
  have hdescent : baseEnd_6469380 < baseStart_6469380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469413 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_6469413 : Nat := 118140960795 + 6469413 * 2 ^ 59
def prefixEnd_6469413 : Nat := 4983230072969 + 3 ^ 40 * 6469413 * 2
def baseEnd_6469413 : Nat := 3321918421445602125585217

theorem tailTrace_6469413 : CollatzResearch.WordTrace tailWord_6469413 prefixEnd_6469413 3321918421445602125585217 := by
  unfold tailWord_6469413
  simp only [CollatzResearch.WordTrace]
  refine ⟨235958876911429063620900893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157305917940952709080600595 235958876911429063620900893)
  ·
    refine ⟨88484578841785898857837835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235958876911429063620900893 88484578841785898857837835)
    ·
      refine ⟨132726868262678848286756753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88484578841785898857837835 132726868262678848286756753)
      ·
        refine ⟨99545151197009136215067565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132726868262678848286756753 99545151197009136215067565)
        ·
          refine ⟨37329431698878426080650337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99545151197009136215067565 37329431698878426080650337)
          ·
            refine ⟨27997073774158819560487753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37329431698878426080650337 27997073774158819560487753)
            ·
              refine ⟨20997805330619114670365815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27997073774158819560487753 20997805330619114670365815)
              ·
                refine ⟨31496707995928672005548723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20997805330619114670365815 31496707995928672005548723)
                ·
                  refine ⟨47245061993893008008323085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31496707995928672005548723 47245061993893008008323085)
                  ·
                    refine ⟨17716898247709878003121157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47245061993893008008323085 17716898247709878003121157)
                    ·
                      refine ⟨3321918421445602125585217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17716898247709878003121157 3321918421445602125585217)
                      ·
                        rfl

theorem cell23_6469413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_6469413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469413 prefixEnd_6469413 := by exact prefixLift 6469413
  have htrace : WordTrace (prefixWord ++ tailWord_6469413) baseStart_6469413 baseEnd_6469413 := by
    simpa [prefixWord, tailWord_6469413, baseEnd_6469413] using wordTrace_append hprefix tailTrace_6469413
  have hstable : (prefixWord ++ tailWord_6469413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469413).length < 2 ^ (prefixWord ++ tailWord_6469413).sum := by decide
  have hdescent : baseEnd_6469413 < baseStart_6469413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469490 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 3, 5, 2]
def baseStart_6469490 : Nat := 118140960795 + 6469490 * 2 ^ 59
def prefixEnd_6469490 : Nat := 4983230072969 + 3 ^ 40 * 6469490 * 2
def baseEnd_6469490 : Nat := 3321957959455998324322363

theorem tailTrace_6469490 : CollatzResearch.WordTrace tailWord_6469490 prefixEnd_6469490 3321957959455998324322363 := by
  unfold tailWord_6469490
  simp only [CollatzResearch.WordTrace]
  refine ⟨58990421333037526442863481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157307790221433403847635949 58990421333037526442863481)
  ·
    refine ⟨44242815999778144832147611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58990421333037526442863481 44242815999778144832147611)
    ·
      refine ⟨66364223999667217248221417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44242815999778144832147611 66364223999667217248221417)
      ·
        refine ⟨49773167999750412936166063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66364223999667217248221417 49773167999750412936166063)
        ·
          refine ⟨74659751999625619404249095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49773167999750412936166063 74659751999625619404249095)
          ·
            refine ⟨111989627999438429106373643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74659751999625619404249095 111989627999438429106373643)
            ·
              refine ⟨167984441999157643659560465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111989627999438429106373643 167984441999157643659560465)
              ·
                refine ⟨125988331499368232744670349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167984441999157643659560465 125988331499368232744670349)
                ·
                  refine ⟨47245624312263087279251381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125988331499368232744670349 47245624312263087279251381)
                  ·
                    refine ⟨4429277279274664432429817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47245624312263087279251381 4429277279274664432429817)
                    ·
                      refine ⟨3321957959455998324322363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4429277279274664432429817 3321957959455998324322363)
                      ·
                        rfl

theorem cell23_6469490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_6469490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469490 prefixEnd_6469490 := by exact prefixLift 6469490
  have htrace : WordTrace (prefixWord ++ tailWord_6469490) baseStart_6469490 baseEnd_6469490 := by
    simpa [prefixWord, tailWord_6469490, baseEnd_6469490] using wordTrace_append hprefix tailTrace_6469490
  have hstable : (prefixWord ++ tailWord_6469490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469490).length < 2 ^ (prefixWord ++ tailWord_6469490).sum := by decide
  have hdescent : baseEnd_6469490 < baseStart_6469490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469514 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 3, 1, 3]
def baseStart_6469514 : Nat := 118140960795 + 6469514 * 2 ^ 59
def prefixEnd_6469514 : Nat := 4983230072969 + 3 ^ 40 * 6469514 * 2
def baseEnd_6469514 : Nat := 3321970282991706230422253

theorem tailTrace_6469514 : CollatzResearch.WordTrace tailWord_6469514 prefixEnd_6469514 3321970282991706230422253 := by
  unfold tailWord_6469514
  simp only [CollatzResearch.WordTrace]
  refine ⟨58990640171015789467581899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157308373789375438580218397 58990640171015789467581899)
  ·
    refine ⟨88485960256523684201372849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58990640171015789467581899 88485960256523684201372849)
    ·
      refine ⟨66364470192392763151029637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88485960256523684201372849 66364470192392763151029637)
      ·
        refine ⟨12443338161073643090818057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66364470192392763151029637 12443338161073643090818057)
        ·
          refine ⟨9332503620805232318113543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12443338161073643090818057 9332503620805232318113543)
          ·
            refine ⟨13998755431207848477170315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9332503620805232318113543 13998755431207848477170315)
            ·
              refine ⟨20998133146811772715755473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13998755431207848477170315 20998133146811772715755473)
              ·
                refine ⟨15748599860108829536816605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20998133146811772715755473 15748599860108829536816605)
                ·
                  refine ⟨5905724947540811076306227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15748599860108829536816605 5905724947540811076306227)
                  ·
                    refine ⟨8858587421311216614459341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5905724947540811076306227 8858587421311216614459341)
                    ·
                      refine ⟨3321970282991706230422253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8858587421311216614459341 3321970282991706230422253)
                      ·
                        rfl

theorem cell23_6469514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_6469514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469514 prefixEnd_6469514 := by exact prefixLift 6469514
  have htrace : WordTrace (prefixWord ++ tailWord_6469514) baseStart_6469514 baseEnd_6469514 := by
    simpa [prefixWord, tailWord_6469514, baseEnd_6469514] using wordTrace_append hprefix tailTrace_6469514
  have hstable : (prefixWord ++ tailWord_6469514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469514).length < 2 ^ (prefixWord ++ tailWord_6469514).sum := by decide
  have hdescent : baseEnd_6469514 < baseStart_6469514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469524 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_6469524 : Nat := 118140960795 + 6469524 * 2 ^ 59
def prefixEnd_6469524 : Nat := 4983230072969 + 3 ^ 40 * 6469524 * 2
def baseEnd_6469524 : Nat := 3321975417798251191297207

theorem tailTrace_6469524 : CollatzResearch.WordTrace tailWord_6469524 prefixEnd_6469524 3321975417798251191297207 := by
  unfold tailWord_6469524
  simp only [CollatzResearch.WordTrace]
  refine ⟨117981462707013464789095813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157308616942684619718794417 117981462707013464789095813)
  ·
    refine ⟨22121524257565024647955465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117981462707013464789095813 22121524257565024647955465)
    ·
      refine ⟨16591143193173768485966599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22121524257565024647955465 16591143193173768485966599)
      ·
        refine ⟨24886714789760652728949899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16591143193173768485966599 24886714789760652728949899)
        ·
          refine ⟨37330072184640979093424849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24886714789760652728949899 37330072184640979093424849)
          ·
            refine ⟨27997554138480734320068637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37330072184640979093424849 27997554138480734320068637)
            ·
              refine ⟨10499082801930275370025739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27997554138480734320068637 10499082801930275370025739)
              ·
                refine ⟨15748624202895413055038609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10499082801930275370025739 15748624202895413055038609)
                ·
                  refine ⟨11811468152171559791278957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15748624202895413055038609 11811468152171559791278957)
                  ·
                    refine ⟨4429300557064334921729609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11811468152171559791278957 4429300557064334921729609)
                    ·
                      refine ⟨3321975417798251191297207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4429300557064334921729609 3321975417798251191297207)
                      ·
                        rfl

theorem cell23_6469524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_6469524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469524 prefixEnd_6469524 := by exact prefixLift 6469524
  have htrace : WordTrace (prefixWord ++ tailWord_6469524) baseStart_6469524 baseEnd_6469524 := by
    simpa [prefixWord, tailWord_6469524, baseEnd_6469524] using wordTrace_append hprefix tailTrace_6469524
  have hstable : (prefixWord ++ tailWord_6469524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469524).length < 2 ^ (prefixWord ++ tailWord_6469524).sum := by decide
  have hdescent : baseEnd_6469524 < baseStart_6469524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469530 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 1, 6]
def baseStart_6469530 : Nat := 118140960795 + 6469530 * 2 ^ 59
def prefixEnd_6469530 : Nat := 4983230072969 + 3 ^ 40 * 6469530 * 2
def baseEnd_6469530 : Nat := 1107326166227392722607393

theorem tailTrace_6469530 : CollatzResearch.WordTrace tailWord_6469530 prefixEnd_6469530 1107326166227392722607393 := by
  unfold tailWord_6469530
  simp only [CollatzResearch.WordTrace]
  refine ⟨58990786063001298150727511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157308762834670128401940029 58990786063001298150727511)
  ·
    refine ⟨88486179094501947226091267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58990786063001298150727511 88486179094501947226091267)
    ·
      refine ⟨132729268641752920839136901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88486179094501947226091267 132729268641752920839136901)
      ·
        refine ⟨24886737870328672657338169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132729268641752920839136901 24886737870328672657338169)
        ·
          refine ⟨18665053402746504493003627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24886737870328672657338169 18665053402746504493003627)
          ·
            refine ⟨27997580104119756739505441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18665053402746504493003627 27997580104119756739505441)
            ·
              refine ⟨20998185078089817554629081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27997580104119756739505441 20998185078089817554629081)
              ·
                refine ⟨15748638808567363165971811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20998185078089817554629081 15748638808567363165971811)
                ·
                  refine ⟨23622958212851044748957717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15748638808567363165971811 23622958212851044748957717)
                  ·
                    refine ⟨1107326166227392722607393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23622958212851044748957717 1107326166227392722607393)
                    ·
                      rfl

theorem cell23_6469530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_6469530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469530 prefixEnd_6469530 := by exact prefixLift 6469530
  have htrace : WordTrace (prefixWord ++ tailWord_6469530) baseStart_6469530 baseEnd_6469530 := by
    simpa [prefixWord, tailWord_6469530, baseEnd_6469530] using wordTrace_append hprefix tailTrace_6469530
  have hstable : (prefixWord ++ tailWord_6469530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469530).length < 2 ^ (prefixWord ++ tailWord_6469530).sum := by decide
  have hdescent : baseEnd_6469530 < baseStart_6469530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469564 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 1, 6]
def baseStart_6469564 : Nat := 118140960795 + 6469564 * 2 ^ 59
def prefixEnd_6469564 : Nat := 4983230072969 + 3 ^ 40 * 6469564 * 2
def baseEnd_6469564 : Nat := 1107331985674810344932341

theorem tailTrace_6469564 : CollatzResearch.WordTrace tailWord_6469564 prefixEnd_6469564 1107331985674810344932341 := by
  unfold tailWord_6469564
  simp only [CollatzResearch.WordTrace]
  refine ⟨117982192166941008204823873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157309589555921344273098497 117982192166941008204823873)
  ·
    refine ⟨88486644125205756153617905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117982192166941008204823873 88486644125205756153617905)
    ·
      refine ⟨66364983093904317115213429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88486644125205756153617905 66364983093904317115213429)
      ·
        refine ⟨6221717165053529729551259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66364983093904317115213429 6221717165053529729551259)
        ·
          refine ⟨9332575747580294594326889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6221717165053529729551259 9332575747580294594326889)
          ·
            refine ⟨6999431810685220945745167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9332575747580294594326889 6999431810685220945745167)
            ·
              refine ⟨10499147716027831418617751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6999431810685220945745167 10499147716027831418617751)
              ·
                refine ⟨15748721574041747127926627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10499147716027831418617751 15748721574041747127926627)
                ·
                  refine ⟨23623082361062620691889941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15748721574041747127926627 23623082361062620691889941)
                  ·
                    refine ⟨1107331985674810344932341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23623082361062620691889941 1107331985674810344932341)
                    ·
                      rfl

theorem cell23_6469564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_6469564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469564 prefixEnd_6469564 := by exact prefixLift 6469564
  have htrace : WordTrace (prefixWord ++ tailWord_6469564) baseStart_6469564 baseEnd_6469564 := by
    simpa [prefixWord, tailWord_6469564, baseEnd_6469564] using wordTrace_append hprefix tailTrace_6469564
  have hstable : (prefixWord ++ tailWord_6469564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469564).length < 2 ^ (prefixWord ++ tailWord_6469564).sum := by decide
  have hdescent : baseEnd_6469564 < baseStart_6469564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469583 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 5]
def baseStart_6469583 : Nat := 118140960795 + 6469583 * 2 ^ 59
def prefixEnd_6469583 : Nat := 4983230072969 + 3 ^ 40 * 6469583 * 2
def baseEnd_6469583 : Nat := 3322005713156866460459435

theorem tailTrace_6469583 : CollatzResearch.WordTrace tailWord_6469583 prefixEnd_6469583 3322005713156866460459435 := by
  unfold tailWord_6469583
  simp only [CollatzResearch.WordTrace]
  refine ⟨235965077320813182654589403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157310051547208788436392935 235965077320813182654589403)
  ·
    refine ⟨353947615981219773981884105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235965077320813182654589403 353947615981219773981884105)
    ·
      refine ⟨265460711985914830486413079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353947615981219773981884105 265460711985914830486413079)
      ·
        refine ⟨398191067978872245729619619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265460711985914830486413079 398191067978872245729619619)
        ·
          refine ⟨597286601968308368594429429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398191067978872245729619619 597286601968308368594429429)
          ·
            refine ⟨55995618934528909555727759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 597286601968308368594429429 55995618934528909555727759)
            ·
              refine ⟨83993428401793364333591639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55995618934528909555727759 83993428401793364333591639)
              ·
                refine ⟨125990142602690046500387459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83993428401793364333591639 125990142602690046500387459)
                ·
                  refine ⟨188985213904035069750581189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125990142602690046500387459 188985213904035069750581189)
                  ·
                    refine ⟨35434727607006575578233973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 188985213904035069750581189 35434727607006575578233973)
                    ·
                      refine ⟨3322005713156866460459435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35434727607006575578233973 3322005713156866460459435)
                      ·
                        rfl

theorem cell23_6469583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_6469583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469583 prefixEnd_6469583 := by exact prefixLift 6469583
  have htrace : WordTrace (prefixWord ++ tailWord_6469583) baseStart_6469583 baseEnd_6469583 := by
    simpa [prefixWord, tailWord_6469583, baseEnd_6469583] using wordTrace_append hprefix tailTrace_6469583
  have hstable : (prefixWord ++ tailWord_6469583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469583).length < 2 ^ (prefixWord ++ tailWord_6469583).sum := by decide
  have hdescent : baseEnd_6469583 < baseStart_6469583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469610 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_6469610 : Nat := 118140960795 + 6469610 * 2 ^ 59
def prefixEnd_6469610 : Nat := 4983230072969 + 3 ^ 40 * 6469610 * 2
def baseEnd_6469610 : Nat := 3322019577134537854821811

theorem tailTrace_6469610 : CollatzResearch.WordTrace tailWord_6469610 prefixEnd_6469610 3322019577134537854821811 := by
  unfold tailWord_6469610
  simp only [CollatzResearch.WordTrace]
  refine ⟨58991515522928841566455571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157310708061143577510548189 58991515522928841566455571)
  ·
    refine ⟨88487273284393262349683357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58991515522928841566455571 88487273284393262349683357)
    ·
      refine ⟨33182727481647473381131259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88487273284393262349683357 33182727481647473381131259)
      ·
        refine ⟨49774091222471210071696889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33182727481647473381131259 49774091222471210071696889)
        ·
          refine ⟨37330568416853407553772667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49774091222471210071696889 37330568416853407553772667)
          ·
            refine ⟨55995852625280111330659001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37330568416853407553772667 55995852625280111330659001)
            ·
              refine ⟨41996889468960083497994251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55995852625280111330659001 41996889468960083497994251)
              ·
                refine ⟨62995334203440125246991377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41996889468960083497994251 62995334203440125246991377)
                ·
                  refine ⟨47246500652580093935243533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62995334203440125246991377 47246500652580093935243533)
                  ·
                    refine ⟨17717437744717535225716325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47246500652580093935243533 17717437744717535225716325)
                    ·
                      refine ⟨3322019577134537854821811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17717437744717535225716325 3322019577134537854821811)
                      ·
                        rfl

theorem cell23_6469610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_6469610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469610 prefixEnd_6469610 := by exact prefixLift 6469610
  have htrace : WordTrace (prefixWord ++ tailWord_6469610) baseStart_6469610 baseEnd_6469610 := by
    simpa [prefixWord, tailWord_6469610, baseEnd_6469610] using wordTrace_append hprefix tailTrace_6469610
  have hstable : (prefixWord ++ tailWord_6469610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469610).length < 2 ^ (prefixWord ++ tailWord_6469610).sum := by decide
  have hdescent : baseEnd_6469610 < baseStart_6469610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469623 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_6469623 : Nat := 118140960795 + 6469623 * 2 ^ 59
def prefixEnd_6469623 : Nat := 4983230072969 + 3 ^ 40 * 6469623 * 2
def baseEnd_6469623 : Nat := 3322026252383046303959251

theorem tailTrace_6469623 : CollatzResearch.WordTrace tailWord_6469623 prefixEnd_6469623 3322026252383046303959251 := by
  unfold tailWord_6469623
  simp only [CollatzResearch.WordTrace]
  refine ⟨235966536240668269486045523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157311024160445512990697015 235966536240668269486045523)
  ·
    refine ⟨353949804361002404229068285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235966536240668269486045523 353949804361002404229068285)
    ·
      refine ⟨132731176635375901585900607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353949804361002404229068285 132731176635375901585900607)
      ·
        refine ⟨199096764953063852378850911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132731176635375901585900607 199096764953063852378850911)
        ·
          refine ⟨298645147429595778568276367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199096764953063852378850911 298645147429595778568276367)
          ·
            refine ⟨447967721144393667852414551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298645147429595778568276367 447967721144393667852414551)
            ·
              refine ⟨671951581716590501778621827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447967721144393667852414551 671951581716590501778621827)
              ·
                refine ⟨1007927372574885752667932741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671951581716590501778621827 1007927372574885752667932741)
                ·
                  refine ⟨188986382357791078625237389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1007927372574885752667932741 188986382357791078625237389)
                  ·
                    refine ⟨70869893384171654484464021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188986382357791078625237389 70869893384171654484464021)
                    ·
                      refine ⟨3322026252383046303959251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70869893384171654484464021 3322026252383046303959251)
                      ·
                        rfl

theorem cell23_6469623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_6469623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469623 prefixEnd_6469623 := by exact prefixLift 6469623
  have htrace : WordTrace (prefixWord ++ tailWord_6469623) baseStart_6469623 baseEnd_6469623 := by
    simpa [prefixWord, tailWord_6469623, baseEnd_6469623] using wordTrace_append hprefix tailTrace_6469623
  have hstable : (prefixWord ++ tailWord_6469623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469623).length < 2 ^ (prefixWord ++ tailWord_6469623).sum := by decide
  have hdescent : baseEnd_6469623 < baseStart_6469623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469661 : List Nat := [1, 4, 2, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_6469661 : Nat := 118140960795 + 6469661 * 2 ^ 59
def prefixEnd_6469661 : Nat := 4983230072969 + 3 ^ 40 * 6469661 * 2
def baseEnd_6469661 : Nat := 3322045764647917155284077

theorem tailTrace_6469661 : CollatzResearch.WordTrace tailWord_6469661 prefixEnd_6469661 3322045764647917155284077 := by
  unfold tailWord_6469661
  simp only [CollatzResearch.WordTrace]
  refine ⟨235967922214530601975928837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157311948143020401317285891 235967922214530601975928837)
  ·
    refine ⟨44243985415224487870486657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235967922214530601975928837 44243985415224487870486657)
    ·
      refine ⟨33182989061418365902864993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44243985415224487870486657 33182989061418365902864993)
      ·
        refine ⟨24887241796063774427148745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33182989061418365902864993 24887241796063774427148745)
        ·
          refine ⟨18665431347047830820361559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24887241796063774427148745 18665431347047830820361559)
          ·
            refine ⟨27998147020571746230542339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18665431347047830820361559 27998147020571746230542339)
            ·
              refine ⟨41997220530857619345813509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27998147020571746230542339 41997220530857619345813509)
              ·
                refine ⟨7874478849535803627340033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41997220530857619345813509 7874478849535803627340033)
                ·
                  refine ⟨5905859137151852720505025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7874478849535803627340033 5905859137151852720505025)
                  ·
                    refine ⟨4429394352863889540378769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5905859137151852720505025 4429394352863889540378769)
                    ·
                      refine ⟨3322045764647917155284077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4429394352863889540378769 3322045764647917155284077)
                      ·
                        rfl

theorem cell23_6469661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_6469661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469661 prefixEnd_6469661 := by exact prefixLift 6469661
  have htrace : WordTrace (prefixWord ++ tailWord_6469661) baseStart_6469661 baseEnd_6469661 := by
    simpa [prefixWord, tailWord_6469661, baseEnd_6469661] using wordTrace_append hprefix tailTrace_6469661
  have hstable : (prefixWord ++ tailWord_6469661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469661).length < 2 ^ (prefixWord ++ tailWord_6469661).sum := by decide
  have hdescent : baseEnd_6469661 < baseStart_6469661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469667 : List Nat := [1, 1, 1, 4, 3, 1, 3, 4, 5]
def baseStart_6469667 : Nat := 118140960795 + 6469667 * 2 ^ 59
def prefixEnd_6469667 : Nat := 4983230072969 + 3 ^ 40 * 6469667 * 2
def baseEnd_6469667 : Nat := 369116538392427125756561

theorem tailTrace_6469667 : CollatzResearch.WordTrace tailWord_6469667 prefixEnd_6469667 369116538392427125756561 := by
  unfold tailWord_6469667
  simp only [CollatzResearch.WordTrace]
  refine ⟨235968141052508865000647255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157312094035005910000431503 235968141052508865000647255)
  ·
    refine ⟨353952211578763297500970883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235968141052508865000647255 353952211578763297500970883)
    ·
      refine ⟨530928317368144946251456325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353952211578763297500970883 530928317368144946251456325)
      ·
        refine ⟨99549059506527177422148061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 530928317368144946251456325 99549059506527177422148061)
        ·
          refine ⟨37330897314947691533305523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99549059506527177422148061 37330897314947691533305523)
          ·
            refine ⟨55996345972421537299958285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37330897314947691533305523 55996345972421537299958285)
            ·
              refine ⟨20998629739658076487484357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55996345972421537299958285 20998629739658076487484357)
              ·
                refine ⟨3937243076185889341403317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20998629739658076487484357 3937243076185889341403317)
                ·
                  refine ⟨369116538392427125756561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3937243076185889341403317 369116538392427125756561)
                  ·
                    rfl

theorem cell23_6469667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 5].length) (baseStart_6469667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469667 prefixEnd_6469667 := by exact prefixLift 6469667
  have htrace : WordTrace (prefixWord ++ tailWord_6469667) baseStart_6469667 baseEnd_6469667 := by
    simpa [prefixWord, tailWord_6469667, baseEnd_6469667] using wordTrace_append hprefix tailTrace_6469667
  have hstable : (prefixWord ++ tailWord_6469667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469667).length < 2 ^ (prefixWord ++ tailWord_6469667).sum := by decide
  have hdescent : baseEnd_6469667 < baseStart_6469667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469684 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 7]
def baseStart_6469684 : Nat := 118140960795 + 6469684 * 2 ^ 59
def prefixEnd_6469684 : Nat := 4983230072969 + 3 ^ 40 * 6469684 * 2
def baseEnd_6469684 : Nat := 369117508300330062810719

theorem tailTrace_6469684 : CollatzResearch.WordTrace tailWord_6469684 prefixEnd_6469684 369117508300330062810719 := by
  unfold tailWord_6469684
  simp only [CollatzResearch.WordTrace]
  refine ⟨117984380546723638452008053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157312507395631517936010737 117984380546723638452008053)
  ·
    refine ⟨11061035676255341104875755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117984380546723638452008053 11061035676255341104875755)
    ·
      refine ⟨16591553514383011657313633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11061035676255341104875755 16591553514383011657313633)
      ·
        refine ⟨12443665135787258742985225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16591553514383011657313633 12443665135787258742985225)
        ·
          refine ⟨9332748851840444057238919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12443665135787258742985225 9332748851840444057238919)
          ·
            refine ⟨13999123277760666085858379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9332748851840444057238919 13999123277760666085858379)
            ·
              refine ⟨20998684916640999128787569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13999123277760666085858379 20998684916640999128787569)
              ·
                refine ⟨15749013687480749346590677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20998684916640999128787569 15749013687480749346590677)
                ·
                  refine ⟨369117508300330062810719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15749013687480749346590677 369117508300330062810719)
                  ·
                    rfl

theorem cell23_6469684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_6469684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469684 prefixEnd_6469684 := by exact prefixLift 6469684
  have htrace : WordTrace (prefixWord ++ tailWord_6469684) baseStart_6469684 baseEnd_6469684 := by
    simpa [prefixWord, tailWord_6469684, baseEnd_6469684] using wordTrace_append hprefix tailTrace_6469684
  have hstable : (prefixWord ++ tailWord_6469684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469684).length < 2 ^ (prefixWord ++ tailWord_6469684).sum := by decide
  have hdescent : baseEnd_6469684 < baseStart_6469684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469697 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 1, 7]
def baseStart_6469697 : Nat := 118140960795 + 6469697 * 2 ^ 59
def prefixEnd_6469697 : Nat := 4983230072969 + 3 ^ 40 * 6469697 * 2
def baseEnd_6469697 : Nat := 1107354749983826338144637

theorem tailTrace_6469697 : CollatzResearch.WordTrace tailWord_6469697 prefixEnd_6469697 1107354749983826338144637 := by
  unfold tailWord_6469697
  simp only [CollatzResearch.WordTrace]
  refine ⟨235969235242400180124239345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157312823494933453416159563 235969235242400180124239345)
  ·
    refine ⟨176976926431800135093179509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235969235242400180124239345 176976926431800135093179509)
    ·
      refine ⟨16591586852981262664985579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176976926431800135093179509 16591586852981262664985579)
      ·
        refine ⟨24887380279471893997478369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16591586852981262664985579 24887380279471893997478369)
        ·
          refine ⟨18665535209603920498108777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24887380279471893997478369 18665535209603920498108777)
          ·
            refine ⟨13999151407202940373581583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18665535209603920498108777 13999151407202940373581583)
            ·
              refine ⟨20998727110804410560372375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13999151407202940373581583 20998727110804410560372375)
              ·
                refine ⟨31498090666206615840558563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20998727110804410560372375 31498090666206615840558563)
                ·
                  refine ⟨47247135999309923760837845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31498090666206615840558563 47247135999309923760837845)
                  ·
                    refine ⟨1107354749983826338144637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47247135999309923760837845 1107354749983826338144637)
                    ·
                      rfl

theorem cell23_6469697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_6469697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469697 prefixEnd_6469697 := by exact prefixLift 6469697
  have htrace : WordTrace (prefixWord ++ tailWord_6469697) baseStart_6469697 baseEnd_6469697 := by
    simpa [prefixWord, tailWord_6469697, baseEnd_6469697] using wordTrace_append hprefix tailTrace_6469697
  have hstable : (prefixWord ++ tailWord_6469697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469697).length < 2 ^ (prefixWord ++ tailWord_6469697).sum := by decide
  have hdescent : baseEnd_6469697 < baseStart_6469697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469777 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 2, 9, 2]
def baseStart_6469777 : Nat := 118140960795 + 6469777 * 2 ^ 59
def prefixEnd_6469777 : Nat := 4983230072969 + 3 ^ 40 * 6469777 * 2
def baseEnd_6469777 : Nat := 3322105328403838701433543

theorem tailTrace_6469777 : CollatzResearch.WordTrace tailWord_6469777 prefixEnd_6469777 3322105328403838701433543 := by
  unfold tailWord_6469777
  simp only [CollatzResearch.WordTrace]
  refine ⟨235972153082110353787151585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157314768721406902524767723 235972153082110353787151585)
  ·
    refine ⟨176979114811582765340363689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235972153082110353787151585 176979114811582765340363689)
    ·
      refine ⟨132734336108687074005272767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176979114811582765340363689 132734336108687074005272767)
      ·
        refine ⟨199101504163030611007909151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132734336108687074005272767 199101504163030611007909151)
        ·
          refine ⟨298652256244545916511863727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199101504163030611007909151 298652256244545916511863727)
          ·
            refine ⟨447978384366818874767795591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298652256244545916511863727 447978384366818874767795591)
            ·
              refine ⟨671967576550228312151693387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447978384366818874767795591 671967576550228312151693387)
              ·
                refine ⟨1007951364825342468227540081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671967576550228312151693387 1007951364825342468227540081)
                ·
                  refine ⟨755963523619006851170655061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1007951364825342468227540081 755963523619006851170655061)
                  ·
                    refine ⟨4429473771205118268578057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 755963523619006851170655061 4429473771205118268578057)
                    ·
                      refine ⟨3322105328403838701433543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4429473771205118268578057 3322105328403838701433543)
                      ·
                        rfl

theorem cell23_6469777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 9, 2].length) (baseStart_6469777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469777 prefixEnd_6469777 := by exact prefixLift 6469777
  have htrace : WordTrace (prefixWord ++ tailWord_6469777) baseStart_6469777 baseEnd_6469777 := by
    simpa [prefixWord, tailWord_6469777, baseEnd_6469777] using wordTrace_append hprefix tailTrace_6469777
  have hstable : (prefixWord ++ tailWord_6469777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469777).length < 2 ^ (prefixWord ++ tailWord_6469777).sum := by decide
  have hdescent : baseEnd_6469777 < baseStart_6469777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469778 : List Nat := [3, 2, 3, 1, 1, 1, 5, 2, 1, 4]
def baseStart_6469778 : Nat := 118140960795 + 6469778 * 2 ^ 59
def prefixEnd_6469778 : Nat := 4983230072969 + 3 ^ 40 * 6469778 * 2
def baseEnd_6469778 : Nat := 1107368613961497732507013

theorem tailTrace_6469778 : CollatzResearch.WordTrace tailWord_6469778 prefixEnd_6469778 1107368613961497732507013 := by
  unfold tailWord_6469778
  simp only [CollatzResearch.WordTrace]
  refine ⟨58993047388776682739484497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157314793036737820638625325 58993047388776682739484497)
  ·
    refine ⟨44244785541582512054613373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58993047388776682739484497 44244785541582512054613373)
    ·
      refine ⟨16591794578093442020480015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44244785541582512054613373 16591794578093442020480015)
      ·
        refine ⟨24887691867140163030720023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16591794578093442020480015 24887691867140163030720023)
        ·
          refine ⟨37331537800710244546080035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24887691867140163030720023 37331537800710244546080035)
          ·
            refine ⟨55997306701065366819120053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37331537800710244546080035 55997306701065366819120053)
            ·
              refine ⟨5249747503224878139292505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55997306701065366819120053 5249747503224878139292505)
              ·
                refine ⟨3937310627418658604469379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5249747503224878139292505 3937310627418658604469379)
                ·
                  refine ⟨5905965941127987906704069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3937310627418658604469379 5905965941127987906704069)
                  ·
                    refine ⟨1107368613961497732507013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5905965941127987906704069 1107368613961497732507013)
                    ·
                      rfl

theorem cell23_6469778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_6469778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469778 prefixEnd_6469778 := by exact prefixLift 6469778
  have htrace : WordTrace (prefixWord ++ tailWord_6469778) baseStart_6469778 baseEnd_6469778 := by
    simpa [prefixWord, tailWord_6469778, baseEnd_6469778] using wordTrace_append hprefix tailTrace_6469778
  have hstable : (prefixWord ++ tailWord_6469778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469778).length < 2 ^ (prefixWord ++ tailWord_6469778).sum := by decide
  have hdescent : baseEnd_6469778 < baseStart_6469778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469791 : List Nat := [1, 1, 2, 6, 1, 3, 2, 1, 6]
def baseStart_6469791 : Nat := 118140960795 + 6469791 * 2 ^ 59
def prefixEnd_6469791 : Nat := 4983230072969 + 3 ^ 40 * 6469791 * 2
def baseEnd_6469791 : Nat := 369123613014777960739831

theorem tailTrace_6469791 : CollatzResearch.WordTrace tailWord_6469791 prefixEnd_6469791 369123613014777960739831 := by
  unfold tailWord_6469791
  simp only [CollatzResearch.WordTrace]
  refine ⟨235972663704059634178161227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157315109136039756118774151 235972663704059634178161227)
  ·
    refine ⟨353958995556089451267241841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235972663704059634178161227 353958995556089451267241841)
    ·
      refine ⟨265469246667067088450431381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353958995556089451267241841 265469246667067088450431381)
      ·
        refine ⟨12443870937518769771113971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 265469246667067088450431381 12443870937518769771113971)
        ·
          refine ⟨18665806406278154656670957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12443870937518769771113971 18665806406278154656670957)
          ·
            refine ⟨6999677402354307996251609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18665806406278154656670957 6999677402354307996251609)
            ·
              refine ⟨5249758051765730997188707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6999677402354307996251609 5249758051765730997188707)
              ·
                refine ⟨7874637077648596495783061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5249758051765730997188707 7874637077648596495783061)
                ·
                  refine ⟨369123613014777960739831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7874637077648596495783061 369123613014777960739831)
                  ·
                    rfl

theorem cell23_6469791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 6].length) (baseStart_6469791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469791 prefixEnd_6469791 := by exact prefixLift 6469791
  have htrace : WordTrace (prefixWord ++ tailWord_6469791) baseStart_6469791 baseEnd_6469791 := by
    simpa [prefixWord, tailWord_6469791, baseEnd_6469791] using wordTrace_append hprefix tailTrace_6469791
  have hstable : (prefixWord ++ tailWord_6469791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469791).length < 2 ^ (prefixWord ++ tailWord_6469791).sum := by decide
  have hdescent : baseEnd_6469791 < baseStart_6469791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469817 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 1, 6]
def baseStart_6469817 : Nat := 118140960795 + 6469817 * 2 ^ 59
def prefixEnd_6469817 : Nat := 4983230072969 + 3 ^ 40 * 6469817 * 2
def baseEnd_6469817 : Nat := 1107375289210006181644453

theorem tailTrace_6469817 : CollatzResearch.WordTrace tailWord_6469817 prefixEnd_6469817 1107375289210006181644453 := by
  unfold tailWord_6469817
  simp only [CollatzResearch.WordTrace]
  refine ⟨235973612001965440618607705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157315741334643627079071803 235973612001965440618607705)
  ·
    refine ⟨176980209001474080463955779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235973612001965440618607705 176980209001474080463955779)
    ·
      refine ⟨265470313502211120695933669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176980209001474080463955779 265470313502211120695933669)
      ·
        refine ⟨49775683781664585130487563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265470313502211120695933669 49775683781664585130487563)
        ·
          refine ⟨74663525672496877695731345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49775683781664585130487563 74663525672496877695731345)
          ·
            refine ⟨55997644254372658271798509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74663525672496877695731345 55997644254372658271798509)
            ·
              refine ⟨20999116595389746851924441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55997644254372658271798509 20999116595389746851924441)
              ·
                refine ⟨15749337446542310138943331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20999116595389746851924441 15749337446542310138943331)
                ·
                  refine ⟨23624006169813465208414997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15749337446542310138943331 23624006169813465208414997)
                  ·
                    refine ⟨1107375289210006181644453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23624006169813465208414997 1107375289210006181644453)
                    ·
                      rfl

theorem cell23_6469817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 6].length) (baseStart_6469817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469817 prefixEnd_6469817 := by exact prefixLift 6469817
  have htrace : WordTrace (prefixWord ++ tailWord_6469817) baseStart_6469817 baseEnd_6469817 := by
    simpa [prefixWord, tailWord_6469817, baseEnd_6469817] using wordTrace_append hprefix tailTrace_6469817
  have hstable : (prefixWord ++ tailWord_6469817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469817).length < 2 ^ (prefixWord ++ tailWord_6469817).sum := by decide
  have hdescent : baseEnd_6469817 < baseStart_6469817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469864 : List Nat := [2, 1, 4, 1, 2, 3, 3, 7]
def baseStart_6469864 : Nat := 118140960795 + 6469864 * 2 ^ 59
def prefixEnd_6469864 : Nat := 4983230072969 + 3 ^ 40 * 6469864 * 2
def baseEnd_6469864 : Nat := 123042592637806661520209

theorem tailTrace_6469864 : CollatzResearch.WordTrace tailWord_6469864 prefixEnd_6469864 123042592637806661520209 := by
  unfold tailWord_6469864
  simp only [CollatzResearch.WordTrace]
  refine ⟨117987663116397583822784323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157316884155196778430379097 117987663116397583822784323)
  ·
    refine ⟨176981494674596375734176485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117987663116397583822784323 176981494674596375734176485)
    ·
      refine ⟨33184030251486820450158091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176981494674596375734176485 33184030251486820450158091)
      ·
        refine ⟨49776045377230230675237137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33184030251486820450158091 49776045377230230675237137)
        ·
          refine ⟨37332034032922673006427853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49776045377230230675237137 37332034032922673006427853)
          ·
            refine ⟨13999512762346002377410445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37332034032922673006427853 13999512762346002377410445)
            ·
              refine ⟨5249817285879750891528917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13999512762346002377410445 5249817285879750891528917)
              ·
                refine ⟨123042592637806661520209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5249817285879750891528917 123042592637806661520209)
                ·
                  rfl

theorem cell23_6469864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 7].length) (baseStart_6469864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469864 prefixEnd_6469864 := by exact prefixLift 6469864
  have htrace : WordTrace (prefixWord ++ tailWord_6469864) baseStart_6469864 baseEnd_6469864 := by
    simpa [prefixWord, tailWord_6469864, baseEnd_6469864] using wordTrace_append hprefix tailTrace_6469864
  have hstable : (prefixWord ++ tailWord_6469864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469864).length < 2 ^ (prefixWord ++ tailWord_6469864).sum := by decide
  have hdescent : baseEnd_6469864 < baseStart_6469864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469878 : List Nat := [5, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_6469878 : Nat := 118140960795 + 6469878 * 2 ^ 59
def prefixEnd_6469878 : Nat := 4983230072969 + 3 ^ 40 * 6469878 * 2
def baseEnd_6469878 : Nat := 3322157189949942806270579

theorem tailTrace_6469878 : CollatzResearch.WordTrace tailWord_6469878 prefixEnd_6469878 3322157189949942806270579 := by
  unfold tailWord_6469878
  simp only [CollatzResearch.WordTrace]
  refine ⟨14748489803421528002286143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157317224569829632024385525 14748489803421528002286143)
  ·
    refine ⟨22122734705132292003429215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14748489803421528002286143 22122734705132292003429215)
    ·
      refine ⟨33184102057698438005143823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22122734705132292003429215 33184102057698438005143823)
      ·
        refine ⟨49776153086547657007715735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33184102057698438005143823 49776153086547657007715735)
        ·
          refine ⟨74664229629821485511573603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49776153086547657007715735 74664229629821485511573603)
          ·
            refine ⟨111996344444732228267360405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74664229629821485511573603 111996344444732228267360405)
            ·
              refine ⟨5249828645846823200032519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111996344444732228267360405 5249828645846823200032519)
              ·
                refine ⟨7874742968770234800048779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5249828645846823200032519 7874742968770234800048779)
                ·
                  refine ⟨11812114453155352200073169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7874742968770234800048779 11812114453155352200073169)
                  ·
                    refine ⟨8859085839866514150054877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11812114453155352200073169 8859085839866514150054877)
                    ·
                      refine ⟨3322157189949942806270579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8859085839866514150054877 3322157189949942806270579)
                      ·
                        rfl

theorem cell23_6469878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_6469878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469878 prefixEnd_6469878 := by exact prefixLift 6469878
  have htrace : WordTrace (prefixWord ++ tailWord_6469878) baseStart_6469878 baseEnd_6469878 := by
    simpa [prefixWord, tailWord_6469878, baseEnd_6469878] using wordTrace_append hprefix tailTrace_6469878
  have hstable : (prefixWord ++ tailWord_6469878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469878).length < 2 ^ (prefixWord ++ tailWord_6469878).sum := by decide
  have hdescent : baseEnd_6469878 < baseStart_6469878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469948 : List Nat := [2, 2, 2, 2, 1, 2, 2, 4, 2, 2, 2]
def baseStart_6469948 : Nat := 118140960795 + 6469948 * 2 ^ 59
def prefixEnd_6469948 : Nat := 4983230072969 + 3 ^ 40 * 6469948 * 2
def baseEnd_6469948 : Nat := 3322193133595757532395257

theorem tailTrace_6469948 : CollatzResearch.WordTrace tailWord_6469948 prefixEnd_6469948 3322193133595757532395257 := by
  unfold tailWord_6469948
  simp only [CollatzResearch.WordTrace]
  refine ⟨117989194982245424995813249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157318926642993899994417665 117989194982245424995813249)
  ·
    refine ⟨88491896236684068746859937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117989194982245424995813249 88491896236684068746859937)
    ·
      refine ⟨66368922177513051560144953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88491896236684068746859937 66368922177513051560144953)
      ·
        refine ⟨49776691633134788670108715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66368922177513051560144953 49776691633134788670108715)
        ·
          refine ⟨74665037449702183005163073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49776691633134788670108715 74665037449702183005163073)
          ·
            refine ⟨55998778087276637253872305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74665037449702183005163073 55998778087276637253872305)
            ·
              refine ⟨41999083565457477940404229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55998778087276637253872305 41999083565457477940404229)
              ·
                refine ⟨7874828168523277113825793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41999083565457477940404229 7874828168523277113825793)
                ·
                  refine ⟨5906121126392457835369345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7874828168523277113825793 5906121126392457835369345)
                  ·
                    refine ⟨4429590844794343376527009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5906121126392457835369345 4429590844794343376527009)
                    ·
                      refine ⟨3322193133595757532395257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4429590844794343376527009 3322193133595757532395257)
                      ·
                        rfl

theorem cell23_6469948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_6469948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469948 prefixEnd_6469948 := by exact prefixLift 6469948
  have htrace : WordTrace (prefixWord ++ tailWord_6469948) baseStart_6469948 baseEnd_6469948 := by
    simpa [prefixWord, tailWord_6469948, baseEnd_6469948] using wordTrace_append hprefix tailTrace_6469948
  have hstable : (prefixWord ++ tailWord_6469948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469948).length < 2 ^ (prefixWord ++ tailWord_6469948).sum := by decide
  have hdescent : baseEnd_6469948 < baseStart_6469948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469964 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 1, 5, 3]
def baseStart_6469964 : Nat := 118140960795 + 6469964 * 2 ^ 59
def prefixEnd_6469964 : Nat := 4983230072969 + 3 ^ 40 * 6469964 * 2
def baseEnd_6469964 : Nat := 3322201349286229469795183

theorem tailTrace_6469964 : CollatzResearch.WordTrace tailWord_6469964 prefixEnd_6469964 3322201349286229469795183 := by
  unfold tailWord_6469964
  simp only [CollatzResearch.WordTrace]
  refine ⟨117989486766216442362104473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157319315688288589816139297 117989486766216442362104473)
  ·
    refine ⟨88492115074662331771578355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117989486766216442362104473 88492115074662331771578355)
    ·
      refine ⟨132738172611993497657367533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88492115074662331771578355 132738172611993497657367533)
      ·
        refine ⟨49776814729497561621512825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132738172611993497657367533 49776814729497561621512825)
        ·
          refine ⟨37332611047123171216134619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49776814729497561621512825 37332611047123171216134619)
          ·
            refine ⟨55998916570684756824201929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37332611047123171216134619 55998916570684756824201929)
            ·
              refine ⟨41999187428013567618151447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55998916570684756824201929 41999187428013567618151447)
              ·
                refine ⟨62998781142020351427227171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41999187428013567618151447 62998781142020351427227171)
                ·
                  refine ⟨94498171713030527140840757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62998781142020351427227171 94498171713030527140840757)
                  ·
                    refine ⟨8859203598096611919453821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94498171713030527140840757 8859203598096611919453821)
                    ·
                      refine ⟨3322201349286229469795183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8859203598096611919453821 3322201349286229469795183)
                      ·
                        rfl

theorem cell23_6469964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_6469964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469964 prefixEnd_6469964 := by exact prefixLift 6469964
  have htrace : WordTrace (prefixWord ++ tailWord_6469964) baseStart_6469964 baseEnd_6469964 := by
    simpa [prefixWord, tailWord_6469964, baseEnd_6469964] using wordTrace_append hprefix tailTrace_6469964
  have hstable : (prefixWord ++ tailWord_6469964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469964).length < 2 ^ (prefixWord ++ tailWord_6469964).sum := by decide
  have hdescent : baseEnd_6469964 < baseStart_6469964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469967 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 1, 7]
def baseStart_6469967 : Nat := 118140960795 + 6469967 * 2 ^ 59
def prefixEnd_6469967 : Nat := 4983230072969 + 3 ^ 40 * 6469967 * 2
def baseEnd_6469967 : Nat := 1107400963242730986019223

theorem tailTrace_6469967 : CollatzResearch.WordTrace tailWord_6469967 prefixEnd_6469967 1107400963242730986019223 := by
  unfold tailWord_6469967
  simp only [CollatzResearch.WordTrace]
  refine ⟨235979082951422016236568155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157319388634281344157712103 235979082951422016236568155)
  ·
    refine ⟨353968624427133024354852233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235979082951422016236568155 353968624427133024354852233)
    ·
      refine ⟨265476468320349768266139175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353968624427133024354852233 265476468320349768266139175)
      ·
        refine ⟨398214702480524652399208763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265476468320349768266139175 398214702480524652399208763)
        ·
          refine ⟨597322053720786978598813145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398214702480524652399208763 597322053720786978598813145)
          ·
            refine ⟨447991540290590233949109859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597322053720786978598813145 447991540290590233949109859)
            ·
              refine ⟨671987310435885350923664789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447991540290590233949109859 671987310435885350923664789)
              ·
                refine ⟨31499405176682125824546787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 671987310435885350923664789 31499405176682125824546787)
                ·
                  refine ⟨47249107765023188736820181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31499405176682125824546787 47249107765023188736820181)
                  ·
                    refine ⟨1107400963242730986019223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47249107765023188736820181 1107400963242730986019223)
                    ·
                      rfl

theorem cell23_6469967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 7].length) (baseStart_6469967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469967 prefixEnd_6469967 := by exact prefixLift 6469967
  have htrace : WordTrace (prefixWord ++ tailWord_6469967) baseStart_6469967 baseEnd_6469967 := by
    simpa [prefixWord, tailWord_6469967, baseEnd_6469967] using wordTrace_append hprefix tailTrace_6469967
  have hstable : (prefixWord ++ tailWord_6469967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469967).length < 2 ^ (prefixWord ++ tailWord_6469967).sum := by decide
  have hdescent : baseEnd_6469967 < baseStart_6469967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6469977 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 7]
def baseStart_6469977 : Nat := 118140960795 + 6469977 * 2 ^ 59
def prefixEnd_6469977 : Nat := 4983230072969 + 3 ^ 40 * 6469977 * 2
def baseEnd_6469977 : Nat := 3322208024534737918932623

theorem tailTrace_6469977 : CollatzResearch.WordTrace tailWord_6469977 prefixEnd_6469977 3322208024534737918932623 := by
  unfold tailWord_6469977
  simp only [CollatzResearch.WordTrace]
  refine ⟨235979447681385787944432185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157319631787590525296288123 235979447681385787944432185)
  ·
    refine ⟨176984585761039340958324139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235979447681385787944432185 176984585761039340958324139)
    ·
      refine ⟨265476878641559011437486209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176984585761039340958324139 265476878641559011437486209)
      ·
        refine ⟨199107658981169258578114657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265476878641559011437486209 199107658981169258578114657)
        ·
          refine ⟨149330744235876943933585993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199107658981169258578114657 149330744235876943933585993)
          ·
            refine ⟨111998058176907707950189495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149330744235876943933585993 111998058176907707950189495)
            ·
              refine ⟨167997087265361561925284243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111998058176907707950189495 167997087265361561925284243)
              ·
                refine ⟨251995630898042342887926365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167997087265361561925284243 251995630898042342887926365)
                ·
                  refine ⟨94498361586765878582972387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251995630898042342887926365 94498361586765878582972387)
                  ·
                    refine ⟨141747542380148817874458581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94498361586765878582972387 141747542380148817874458581)
                    ·
                      refine ⟨3322208024534737918932623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 141747542380148817874458581 3322208024534737918932623)
                      ·
                        rfl

theorem cell23_6469977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_6469977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6469977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6469977 prefixEnd_6469977 := by exact prefixLift 6469977
  have htrace : WordTrace (prefixWord ++ tailWord_6469977) baseStart_6469977 baseEnd_6469977 := by
    simpa [prefixWord, tailWord_6469977, baseEnd_6469977] using wordTrace_append hprefix tailTrace_6469977
  have hstable : (prefixWord ++ tailWord_6469977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6469977).length < 2 ^ (prefixWord ++ tailWord_6469977).sum := by decide
  have hdescent : baseEnd_6469977 < baseStart_6469977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6469977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470005 : List Nat := [1, 3, 4, 1, 2, 3, 2, 2, 5]
def baseStart_6470005 : Nat := 118140960795 + 6470005 * 2 ^ 59
def prefixEnd_6470005 : Nat := 4983230072969 + 3 ^ 40 * 6470005 * 2
def baseEnd_6470005 : Nat := 369135822443673756598055

theorem tailTrace_6470005 : CollatzResearch.WordTrace tailWord_6470005 prefixEnd_6470005 369135822443673756598055 := by
  unfold tailWord_6470005
  simp only [CollatzResearch.WordTrace]
  refine ⟨235980468925284348726451469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157320312616856232484300979 235980468925284348726451469)
  ·
    refine ⟨88492675846981630772419301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235980468925284348726451469 88492675846981630772419301)
    ·
      refine ⟨16592376721309055769828619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88492675846981630772419301 16592376721309055769828619)
      ·
        refine ⟨24888565081963583654742929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16592376721309055769828619 24888565081963583654742929)
        ·
          refine ⟨18666423811472687741057197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24888565081963583654742929 18666423811472687741057197)
          ·
            refine ⟨6999908929302257902896449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18666423811472687741057197 6999908929302257902896449)
            ·
              refine ⟨5249931696976693427172337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6999908929302257902896449 5249931696976693427172337)
              ·
                refine ⟨3937448772732520070379253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5249931696976693427172337 3937448772732520070379253)
                ·
                  refine ⟨369135822443673756598055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3937448772732520070379253 369135822443673756598055)
                  ·
                    rfl

theorem cell23_6470005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2, 5].length) (baseStart_6470005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470005 prefixEnd_6470005 := by exact prefixLift 6470005
  have htrace : WordTrace (prefixWord ++ tailWord_6470005) baseStart_6470005 baseEnd_6470005 := by
    simpa [prefixWord, tailWord_6470005, baseEnd_6470005] using wordTrace_append hprefix tailTrace_6470005
  have hstable : (prefixWord ++ tailWord_6470005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470005).length < 2 ^ (prefixWord ++ tailWord_6470005).sum := by decide
  have hdescent : baseEnd_6470005 < baseStart_6470005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470048 : List Nat := [2, 1, 1, 4, 1, 3, 1, 5, 1, 4]
def baseStart_6470048 : Nat := 118140960795 + 6470048 * 2 ^ 59
def prefixEnd_6470048 : Nat := 4983230072969 + 3 ^ 40 * 6470048 * 2
def baseEnd_6470048 : Nat := 1107414827220402380381599

theorem tailTrace_6470048 : CollatzResearch.WordTrace tailWord_6470048 prefixEnd_6470048 1107414827220402380381599 := by
  unfold tailWord_6470048
  simp only [CollatzResearch.WordTrace]
  refine ⟨117991018632064283535133399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157321358176085711380177865 117991018632064283535133399)
  ·
    refine ⟨176986527948096425302700099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117991018632064283535133399 176986527948096425302700099)
    ·
      refine ⟨265479791922144637954050149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176986527948096425302700099 265479791922144637954050149)
      ·
        refine ⟨49777460985402119616384403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265479791922144637954050149 49777460985402119616384403)
        ·
          refine ⟨74666191478103179424576605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49777460985402119616384403 74666191478103179424576605)
          ·
            refine ⟨27999821804288692284216227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74666191478103179424576605 27999821804288692284216227)
            ·
              refine ⟨41999732706433038426324341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27999821804288692284216227 41999732706433038426324341)
              ·
                refine ⟨3937474941228097352467907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41999732706433038426324341 3937474941228097352467907)
                ·
                  refine ⟨5906212411842146028701861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3937474941228097352467907 5906212411842146028701861)
                  ·
                    refine ⟨1107414827220402380381599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5906212411842146028701861 1107414827220402380381599)
                    ·
                      rfl

theorem cell23_6470048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 1, 4].length) (baseStart_6470048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470048 prefixEnd_6470048 := by exact prefixLift 6470048
  have htrace : WordTrace (prefixWord ++ tailWord_6470048) baseStart_6470048 baseEnd_6470048 := by
    simpa [prefixWord, tailWord_6470048, baseEnd_6470048] using wordTrace_append hprefix tailTrace_6470048
  have hstable : (prefixWord ++ tailWord_6470048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470048).length < 2 ^ (prefixWord ++ tailWord_6470048).sum := by decide
  have hdescent : baseEnd_6470048 < baseStart_6470048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470074 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 5, 5]
def baseStart_6470074 : Nat := 118140960795 + 6470074 * 2 ^ 59
def prefixEnd_6470074 : Nat := 4983230072969 + 3 ^ 40 * 6470074 * 2
def baseEnd_6470074 : Nat := 1107419277386074679806559

theorem tailTrace_6470074 : CollatzResearch.WordTrace tailWord_6470074 prefixEnd_6470074 1107419277386074679806559 := by
  unfold tailWord_6470074
  simp only [CollatzResearch.WordTrace]
  refine ⟨58995746390508593377678319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157321990374689582340475517 58995746390508593377678319)
  ·
    refine ⟨88493619585762890066517479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58995746390508593377678319 88493619585762890066517479)
    ·
      refine ⟨132740429378644335099776219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88493619585762890066517479 132740429378644335099776219)
      ·
        refine ⟨199110644067966502649664329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132740429378644335099776219 199110644067966502649664329)
        ·
          refine ⟨149332983050974876987248247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199110644067966502649664329 149332983050974876987248247)
          ·
            refine ⟨223999474576462315480872371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149332983050974876987248247 223999474576462315480872371)
            ·
              refine ⟨335999211864693473221308557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223999474576462315480872371 335999211864693473221308557)
              ·
                refine ⟨125999704449260052457990709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335999211864693473221308557 125999704449260052457990709)
                ·
                  refine ⟨11812472292118129917936629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125999704449260052457990709 11812472292118129917936629)
                  ·
                    refine ⟨1107419277386074679806559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11812472292118129917936629 1107419277386074679806559)
                    ·
                      rfl

theorem cell23_6470074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_6470074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470074 prefixEnd_6470074 := by exact prefixLift 6470074
  have htrace : WordTrace (prefixWord ++ tailWord_6470074) baseStart_6470074 baseEnd_6470074 := by
    simpa [prefixWord, tailWord_6470074, baseEnd_6470074] using wordTrace_append hprefix tailTrace_6470074
  have hstable : (prefixWord ++ tailWord_6470074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470074).length < 2 ^ (prefixWord ++ tailWord_6470074).sum := by decide
  have hdescent : baseEnd_6470074 < baseStart_6470074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470088 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 3, 1, 3]
def baseStart_6470088 : Nat := 118140960795 + 6470088 * 2 ^ 59
def prefixEnd_6470088 : Nat := 4983230072969 + 3 ^ 40 * 6470088 * 2
def baseEnd_6470088 : Nat := 3322265020887386984644613

theorem tailTrace_6470088 : CollatzResearch.WordTrace tailWord_6470088 prefixEnd_6470088 3322265020887386984644613 := by
  unfold tailWord_6470088
  simp only [CollatzResearch.WordTrace]
  refine ⟨117991748091991826950861459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157322330789322435934481945 117991748091991826950861459)
  ·
    refine ⟨176987622137987740426292189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117991748091991826950861459 176987622137987740426292189)
    ·
      refine ⟨66370358301745402659859571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176987622137987740426292189 66370358301745402659859571)
      ·
        refine ⟨99555537452618103989789357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66370358301745402659859571 99555537452618103989789357)
        ·
          refine ⟨37333326544731788996171009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99555537452618103989789357 37333326544731788996171009)
          ·
            refine ⟨27999994908548841747128257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37333326544731788996171009 27999994908548841747128257)
            ·
              refine ⟨20999996181411631310346193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27999994908548841747128257 20999996181411631310346193)
              ·
                refine ⟨15749997136058723482759645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20999996181411631310346193 15749997136058723482759645)
                ·
                  refine ⟨5906248926022021306034867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15749997136058723482759645 5906248926022021306034867)
                  ·
                    refine ⟨8859373389033031959052301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5906248926022021306034867 8859373389033031959052301)
                    ·
                      refine ⟨3322265020887386984644613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8859373389033031959052301 3322265020887386984644613)
                      ·
                        rfl

theorem cell23_6470088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_6470088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470088 prefixEnd_6470088 := by exact prefixLift 6470088
  have htrace : WordTrace (prefixWord ++ tailWord_6470088) baseStart_6470088 baseEnd_6470088 := by
    simpa [prefixWord, tailWord_6470088, baseEnd_6470088] using wordTrace_append hprefix tailTrace_6470088
  have hstable : (prefixWord ++ tailWord_6470088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470088).length < 2 ^ (prefixWord ++ tailWord_6470088).sum := by decide
  have hdescent : baseEnd_6470088 < baseStart_6470088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470104 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 3, 6]
def baseStart_6470104 : Nat := 118140960795 + 6470104 * 2 ^ 59
def prefixEnd_6470104 : Nat := 4983230072969 + 3 ^ 40 * 6470104 * 2
def baseEnd_6470104 : Nat := 1107424412192619640681513

theorem tailTrace_6470104 : CollatzResearch.WordTrace tailWord_6470104 prefixEnd_6470104 1107424412192619640681513 := by
  unfold tailWord_6470104
  simp only [CollatzResearch.WordTrace]
  refine ⟨117992039875962844317152683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157322719834617125756203577 117992039875962844317152683)
  ·
    refine ⟨176988059813944266475729025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117992039875962844317152683 176988059813944266475729025)
    ·
      refine ⟨132741044860458199856796769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176988059813944266475729025 132741044860458199856796769)
      ·
        refine ⟨99555783645343649892597577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132741044860458199856796769 99555783645343649892597577)
        ·
          refine ⟨74666837734007737419448183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99555783645343649892597577 74666837734007737419448183)
          ·
            refine ⟨112000256601011606129172275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74666837734007737419448183 112000256601011606129172275)
            ·
              refine ⟨168000384901517409193758413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112000256601011606129172275 168000384901517409193758413)
              ·
                refine ⟨63000144338069028447659405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168000384901517409193758413 63000144338069028447659405)
                ·
                  refine ⟨23625054126775885667872277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63000144338069028447659405 23625054126775885667872277)
                  ·
                    refine ⟨1107424412192619640681513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23625054126775885667872277 1107424412192619640681513)
                    ·
                      rfl

theorem cell23_6470104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_6470104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470104 prefixEnd_6470104 := by exact prefixLift 6470104
  have htrace : WordTrace (prefixWord ++ tailWord_6470104) baseStart_6470104 baseEnd_6470104 := by
    simpa [prefixWord, tailWord_6470104, baseEnd_6470104] using wordTrace_append hprefix tailTrace_6470104
  have hstable : (prefixWord ++ tailWord_6470104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470104).length < 2 ^ (prefixWord ++ tailWord_6470104).sum := by decide
  have hdescent : baseEnd_6470104 < baseStart_6470104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470115 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 2, 3, 2]
def baseStart_6470115 : Nat := 118140960795 + 6470115 * 2 ^ 59
def prefixEnd_6470115 : Nat := 4983230072969 + 3 ^ 40 * 6470115 * 2
def baseEnd_6470115 : Nat := 3322278884865058379006989

theorem tailTrace_6470115 : CollatzResearch.WordTrace tailWord_6470115 prefixEnd_6470115 3322278884865058379006989 := by
  unfold tailWord_6470115
  simp only [CollatzResearch.WordTrace]
  refine ⟨235984480954885837512955799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157322987303257225008637199 235984480954885837512955799)
  ·
    refine ⟨353976721432328756269433699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235984480954885837512955799 353976721432328756269433699)
    ·
      refine ⟨530965082148493134404150549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353976721432328756269433699 530965082148493134404150549)
      ·
        refine ⟨24888988225710615675194557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 530965082148493134404150549 24888988225710615675194557)
        ·
          refine ⟨9333370584641480878197959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24888988225710615675194557 9333370584641480878197959)
          ·
            refine ⟨14000055876962221317296939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9333370584641480878197959 14000055876962221317296939)
            ·
              refine ⟨21000083815443331975945409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14000055876962221317296939 21000083815443331975945409)
              ·
                refine ⟨15750062861582498981959057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21000083815443331975945409 15750062861582498981959057)
                ·
                  refine ⟨11812547146186874236469293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15750062861582498981959057 11812547146186874236469293)
                  ·
                    refine ⟨4429705179820077838675985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11812547146186874236469293 4429705179820077838675985)
                    ·
                      refine ⟨3322278884865058379006989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4429705179820077838675985 3322278884865058379006989)
                      ·
                        rfl

theorem cell23_6470115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_6470115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470115 prefixEnd_6470115 := by exact prefixLift 6470115
  have htrace : WordTrace (prefixWord ++ tailWord_6470115) baseStart_6470115 baseEnd_6470115 := by
    simpa [prefixWord, tailWord_6470115, baseEnd_6470115] using wordTrace_append hprefix tailTrace_6470115
  have hstable : (prefixWord ++ tailWord_6470115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470115).length < 2 ^ (prefixWord ++ tailWord_6470115).sum := by decide
  have hdescent : baseEnd_6470115 < baseStart_6470115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470124 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_6470124 : Nat := 118140960795 + 6470124 * 2 ^ 59
def prefixEnd_6470124 : Nat := 4983230072969 + 3 ^ 40 * 6470124 * 2
def baseEnd_6470124 : Nat := 3322283506190948843794447

theorem tailTrace_6470124 : CollatzResearch.WordTrace tailWord_6470124 prefixEnd_6470124 3322283506190948843794447 := by
  unfold tailWord_6470124
  simp only [CollatzResearch.WordTrace]
  refine ⟨117992404605926616025016713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157323206141235488033355617 117992404605926616025016713)
  ·
    refine ⟨88494303454444962018762535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117992404605926616025016713 88494303454444962018762535)
    ·
      refine ⟨132741455181667443028143803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88494303454444962018762535 132741455181667443028143803)
      ·
        refine ⟨199112182772501164542215705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132741455181667443028143803 199112182772501164542215705)
        ·
          refine ⟨149334137079375873406661779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199112182772501164542215705 149334137079375873406661779)
          ·
            refine ⟨224001205619063810109992669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149334137079375873406661779 224001205619063810109992669)
            ·
              refine ⟨84000452107148928791247251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224001205619063810109992669 84000452107148928791247251)
              ·
                refine ⟨126000678160723393186870877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84000452107148928791247251 126000678160723393186870877)
                ·
                  refine ⟨47250254310271272445076579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126000678160723393186870877 47250254310271272445076579)
                  ·
                    refine ⟨70875381465406908667614869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47250254310271272445076579 70875381465406908667614869)
                    ·
                      refine ⟨3322283506190948843794447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70875381465406908667614869 3322283506190948843794447)
                      ·
                        rfl

theorem cell23_6470124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_6470124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470124 prefixEnd_6470124 := by exact prefixLift 6470124
  have htrace : WordTrace (prefixWord ++ tailWord_6470124) baseStart_6470124 baseEnd_6470124 := by
    simpa [prefixWord, tailWord_6470124, baseEnd_6470124] using wordTrace_append hprefix tailTrace_6470124
  have hstable : (prefixWord ++ tailWord_6470124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470124).length < 2 ^ (prefixWord ++ tailWord_6470124).sum := by decide
  have hdescent : baseEnd_6470124 < baseStart_6470124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470131 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 3]
def baseStart_6470131 : Nat := 118140960795 + 6470131 * 2 ^ 59
def prefixEnd_6470131 : Nat := 4983230072969 + 3 ^ 40 * 6470131 * 2
def baseEnd_6470131 : Nat := 3322287100555530316406915

theorem tailTrace_6470131 : CollatzResearch.WordTrace tailWord_6470131 prefixEnd_6470131 3322287100555530316406915 := by
  unfold tailWord_6470131
  simp only [CollatzResearch.WordTrace]
  refine ⟨235985064522827872245538247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157323376348551914830358831 235985064522827872245538247)
  ·
    refine ⟨353977596784241808368307371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235985064522827872245538247 353977596784241808368307371)
    ·
      refine ⟨530966395176362712552461057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353977596784241808368307371 530966395176362712552461057)
      ·
        refine ⟨398224796382272034414345793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 530966395176362712552461057 398224796382272034414345793)
        ·
          refine ⟨298668597286704025810759345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398224796382272034414345793 298668597286704025810759345)
          ·
            refine ⟨224001447965028019358069509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298668597286704025810759345 224001447965028019358069509)
            ·
              refine ⟨42000271493442753629638033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224001447965028019358069509 42000271493442753629638033)
              ·
                refine ⟨31500203620082065222228525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42000271493442753629638033 31500203620082065222228525)
                ·
                  refine ⟨11812576357530774458335697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31500203620082065222228525 11812576357530774458335697)
                  ·
                    refine ⟨8859432268148080843751773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11812576357530774458335697 8859432268148080843751773)
                    ·
                      refine ⟨3322287100555530316406915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8859432268148080843751773 3322287100555530316406915)
                      ·
                        rfl

theorem cell23_6470131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 3].length) (baseStart_6470131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470131 prefixEnd_6470131 := by exact prefixLift 6470131
  have htrace : WordTrace (prefixWord ++ tailWord_6470131) baseStart_6470131 baseEnd_6470131 := by
    simpa [prefixWord, tailWord_6470131, baseEnd_6470131] using wordTrace_append hprefix tailTrace_6470131
  have hstable : (prefixWord ++ tailWord_6470131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470131).length < 2 ^ (prefixWord ++ tailWord_6470131).sum := by decide
  have hdescent : baseEnd_6470131 < baseStart_6470131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470141 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_6470141 : Nat := 118140960795 + 6470141 * 2 ^ 59
def prefixEnd_6470141 : Nat := 4983230072969 + 3 ^ 40 * 6470141 * 2
def baseEnd_6470141 : Nat := 3322292235362075277281869

theorem tailTrace_6470141 : CollatzResearch.WordTrace tailWord_6470141 prefixEnd_6470141 3322292235362075277281869 := by
  unfold tailWord_6470141
  simp only [CollatzResearch.WordTrace]
  refine ⟨235985429252791643953402277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157323619501861095968934851 235985429252791643953402277)
  ·
    refine ⟨44247267984898433241262927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235985429252791643953402277 44247267984898433241262927)
    ·
      refine ⟨66370901977347649861894391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44247267984898433241262927 66370901977347649861894391)
      ·
        refine ⟨99556352966021474792841587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66370901977347649861894391 99556352966021474792841587)
        ·
          refine ⟨149334529449032212189262381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99556352966021474792841587 149334529449032212189262381)
          ·
            refine ⟨56000448543387079570973393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149334529449032212189262381 56000448543387079570973393)
            ·
              refine ⟨42000336407540309678230045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56000448543387079570973393 42000336407540309678230045)
              ·
                refine ⟨15750126152827616129336267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42000336407540309678230045 15750126152827616129336267)
                ·
                  refine ⟨23625189229241424194004401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15750126152827616129336267 23625189229241424194004401)
                  ·
                    refine ⟨17718891921931068145503301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23625189229241424194004401 17718891921931068145503301)
                    ·
                      refine ⟨3322292235362075277281869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17718891921931068145503301 3322292235362075277281869)
                      ·
                        rfl

theorem cell23_6470141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_6470141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470141 prefixEnd_6470141 := by exact prefixLift 6470141
  have htrace : WordTrace (prefixWord ++ tailWord_6470141) baseStart_6470141 baseEnd_6470141 := by
    simpa [prefixWord, tailWord_6470141, baseEnd_6470141] using wordTrace_append hprefix tailTrace_6470141
  have hstable : (prefixWord ++ tailWord_6470141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470141).length < 2 ^ (prefixWord ++ tailWord_6470141).sum := by decide
  have hdescent : baseEnd_6470141 < baseStart_6470141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470145 : List Nat := [1, 2, 4, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_6470145 : Nat := 118140960795 + 6470145 * 2 ^ 59
def prefixEnd_6470145 : Nat := 4983230072969 + 3 ^ 40 * 6470145 * 2
def baseEnd_6470145 : Nat := 3322294289284693261631851

theorem tailTrace_6470145 : CollatzResearch.WordTrace tailWord_6470145 prefixEnd_6470145 3322294289284693261631851 := by
  unfold tailWord_6470145
  simp only [CollatzResearch.WordTrace]
  refine ⟨235985575144777152636547889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157323716763184768424365259 235985575144777152636547889)
  ·
    refine ⟨176989181358582864477410917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235985575144777152636547889 176989181358582864477410917)
    ·
      refine ⟨33185471504734287089514547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176989181358582864477410917 33185471504734287089514547)
      ·
        refine ⟨49778207257101430634271821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33185471504734287089514547 49778207257101430634271821)
        ·
          refine ⟨18666827721413036487851933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49778207257101430634271821 18666827721413036487851933)
          ·
            refine ⟨7000060395529888682944475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18666827721413036487851933 7000060395529888682944475)
            ·
              refine ⟨10500090593294833024416713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7000060395529888682944475 10500090593294833024416713)
              ·
                refine ⟨7875067944971124768312535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10500090593294833024416713 7875067944971124768312535)
                ·
                  refine ⟨11812601917456687152468803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7875067944971124768312535 11812601917456687152468803)
                  ·
                    refine ⟨17718902876185030728703205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11812601917456687152468803 17718902876185030728703205)
                    ·
                      refine ⟨3322294289284693261631851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17718902876185030728703205 3322294289284693261631851)
                      ·
                        rfl

theorem cell23_6470145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_6470145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470145 prefixEnd_6470145 := by exact prefixLift 6470145
  have htrace : WordTrace (prefixWord ++ tailWord_6470145) baseStart_6470145 baseEnd_6470145 := by
    simpa [prefixWord, tailWord_6470145, baseEnd_6470145] using wordTrace_append hprefix tailTrace_6470145
  have hstable : (prefixWord ++ tailWord_6470145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470145).length < 2 ^ (prefixWord ++ tailWord_6470145).sum := by decide
  have hdescent : baseEnd_6470145 < baseStart_6470145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470158 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_6470158 : Nat := 118140960795 + 6470158 * 2 ^ 59
def prefixEnd_6470158 : Nat := 4983230072969 + 3 ^ 40 * 6470158 * 2
def baseEnd_6470158 : Nat := 3322300964533201710769291

theorem tailTrace_6470158 : CollatzResearch.WordTrace tailWord_6470158 prefixEnd_6470158 3322300964533201710769291 := by
  unfold tailWord_6470158
  simp only [CollatzResearch.WordTrace]
  refine ⟨29498256161716256982096391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157324032862486703904514085 29498256161716256982096391)
  ·
    refine ⟨44247384242574385473144587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29498256161716256982096391 44247384242574385473144587)
    ·
      refine ⟨66371076363861578209716881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44247384242574385473144587 66371076363861578209716881)
      ·
        refine ⟨49778307272896183657287661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66371076363861578209716881 49778307272896183657287661)
        ·
          refine ⟨18666865227336068871482873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49778307272896183657287661 18666865227336068871482873)
          ·
            refine ⟨14000148920502051653612155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18666865227336068871482873 14000148920502051653612155)
            ·
              refine ⟨21000223380753077480418233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14000148920502051653612155 21000223380753077480418233)
              ·
                refine ⟨15750167535564808110313675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21000223380753077480418233 15750167535564808110313675)
                ·
                  refine ⟨23625251303347212165470513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15750167535564808110313675 23625251303347212165470513)
                  ·
                    refine ⟨17718938477510409124102885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23625251303347212165470513 17718938477510409124102885)
                    ·
                      refine ⟨3322300964533201710769291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17718938477510409124102885 3322300964533201710769291)
                      ·
                        rfl

theorem cell23_6470158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_6470158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470158 prefixEnd_6470158 := by exact prefixLift 6470158
  have htrace : WordTrace (prefixWord ++ tailWord_6470158) baseStart_6470158 baseEnd_6470158 := by
    simpa [prefixWord, tailWord_6470158, baseEnd_6470158] using wordTrace_append hprefix tailTrace_6470158
  have hstable : (prefixWord ++ tailWord_6470158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470158).length < 2 ^ (prefixWord ++ tailWord_6470158).sum := by decide
  have hdescent : baseEnd_6470158 < baseStart_6470158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470165 : List Nat := [1, 3, 2, 1, 3, 1, 5, 1, 1, 2, 3]
def baseStart_6470165 : Nat := 118140960795 + 6470165 * 2 ^ 59
def prefixEnd_6470165 : Nat := 4983230072969 + 3 ^ 40 * 6470165 * 2
def baseEnd_6470165 : Nat := 3322304558897783183381759

theorem tailTrace_6470165 : CollatzResearch.WordTrace tailWord_6470165 prefixEnd_6470165 3322304558897783183381759 := by
  unfold tailWord_6470165
  simp only [CollatzResearch.WordTrace]
  refine ⟨235986304604704696052275949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157324203069803130701517299 235986304604704696052275949)
  ·
    refine ⟨88494864226764261019603481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235986304604704696052275949 88494864226764261019603481)
    ·
      refine ⟨66371148170073195764702611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88494864226764261019603481 66371148170073195764702611)
      ·
        refine ⟨99556722255109793647053917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66371148170073195764702611 99556722255109793647053917)
        ·
          refine ⟨37333770845666172617645219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99556722255109793647053917 37333770845666172617645219)
          ·
            refine ⟨56000656268499258926467829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37333770845666172617645219 56000656268499258926467829)
            ·
              refine ⟨5250061525171805524356359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56000656268499258926467829 5250061525171805524356359)
              ·
                refine ⟨7875092287757708286534539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5250061525171805524356359 7875092287757708286534539)
                ·
                  refine ⟨11812638431636562429801809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7875092287757708286534539 11812638431636562429801809)
                  ·
                    refine ⟨8859478823727421822351357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11812638431636562429801809 8859478823727421822351357)
                    ·
                      refine ⟨3322304558897783183381759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8859478823727421822351357 3322304558897783183381759)
                      ·
                        rfl

theorem cell23_6470165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_6470165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470165 prefixEnd_6470165 := by exact prefixLift 6470165
  have htrace : WordTrace (prefixWord ++ tailWord_6470165) baseStart_6470165 baseEnd_6470165 := by
    simpa [prefixWord, tailWord_6470165, baseEnd_6470165] using wordTrace_append hprefix tailTrace_6470165
  have hstable : (prefixWord ++ tailWord_6470165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470165).length < 2 ^ (prefixWord ++ tailWord_6470165).sum := by decide
  have hdescent : baseEnd_6470165 < baseStart_6470165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470179 : List Nat := [1, 1, 1, 4, 4, 1, 4, 2, 1, 2, 2]
def baseStart_6470179 : Nat := 118140960795 + 6470179 * 2 ^ 59
def prefixEnd_6470179 : Nat := 4983230072969 + 3 ^ 40 * 6470179 * 2
def baseEnd_6470179 : Nat := 3322311747626946128606695

theorem tailTrace_6470179 : CollatzResearch.WordTrace tailWord_6470179 prefixEnd_6470179 3322311747626946128606695 := by
  unfold tailWord_6470179
  simp only [CollatzResearch.WordTrace]
  refine ⟨235986815226653976443285591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157324543484435984295523727 235986815226653976443285591)
  ·
    refine ⟨353980222839980964664928387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235986815226653976443285591 353980222839980964664928387)
    ·
      refine ⟨530970334259971446997392581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353980222839980964664928387 530970334259971446997392581)
      ·
        refine ⟨99556937673744646312011109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 530970334259971446997392581 99556937673744646312011109)
        ·
          refine ⟨18666925813827121183502083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99556937673744646312011109 18666925813827121183502083)
          ·
            refine ⟨28000388720740681775253125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18666925813827121183502083 28000388720740681775253125)
            ·
              refine ⟨5250072885138877832859961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28000388720740681775253125 5250072885138877832859961)
              ·
                refine ⟨3937554663854158374644971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5250072885138877832859961 3937554663854158374644971)
                ·
                  refine ⟨5906331995781237561967457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3937554663854158374644971 5906331995781237561967457)
                  ·
                    refine ⟨4429748996835928171475593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5906331995781237561967457 4429748996835928171475593)
                    ·
                      refine ⟨3322311747626946128606695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4429748996835928171475593 3322311747626946128606695)
                      ·
                        rfl

theorem cell23_6470179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_6470179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470179 prefixEnd_6470179 := by exact prefixLift 6470179
  have htrace : WordTrace (prefixWord ++ tailWord_6470179) baseStart_6470179 baseEnd_6470179 := by
    simpa [prefixWord, tailWord_6470179, baseEnd_6470179] using wordTrace_append hprefix tailTrace_6470179
  have hstable : (prefixWord ++ tailWord_6470179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470179).length < 2 ^ (prefixWord ++ tailWord_6470179).sum := by decide
  have hdescent : baseEnd_6470179 < baseStart_6470179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470201 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 2, 3, 4]
def baseStart_6470201 : Nat := 118140960795 + 6470201 * 2 ^ 59
def prefixEnd_6470201 : Nat := 4983230072969 + 3 ^ 40 * 6470201 * 2
def baseEnd_6470201 : Nat := 3322323044201345042531593

theorem tailTrace_6470201 : CollatzResearch.WordTrace tailWord_6470201 prefixEnd_6470201 3322323044201345042531593 := by
  unfold tailWord_6470201
  simp only [CollatzResearch.WordTrace]
  refine ⟨235987617632574274200586457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157325078421716182800390971 235987617632574274200586457)
  ·
    refine ⟨176990713224430705650439843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235987617632574274200586457 176990713224430705650439843)
    ·
      refine ⟨265486069836646058475659765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176990713224430705650439843 265486069836646058475659765)
      ·
        refine ⟨24889319047185567982093103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 265486069836646058475659765 24889319047185567982093103)
        ·
          refine ⟨37333978570778351973139655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24889319047185567982093103 37333978570778351973139655)
          ·
            refine ⟨56000967856167527959709483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37333978570778351973139655 56000967856167527959709483)
            ·
              refine ⟨84001451784251291939564225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56000967856167527959709483 84001451784251291939564225)
              ·
                refine ⟨63001088838188468954673169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84001451784251291939564225 63001088838188468954673169)
                ·
                  refine ⟨47250816628641351716004877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63001088838188468954673169 47250816628641351716004877)
                  ·
                    refine ⟨17719056235740506893501829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47250816628641351716004877 17719056235740506893501829)
                    ·
                      refine ⟨3322323044201345042531593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17719056235740506893501829 3322323044201345042531593)
                      ·
                        rfl

theorem cell23_6470201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_6470201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470201 prefixEnd_6470201 := by exact prefixLift 6470201
  have htrace : WordTrace (prefixWord ++ tailWord_6470201) baseStart_6470201 baseEnd_6470201 := by
    simpa [prefixWord, tailWord_6470201, baseEnd_6470201] using wordTrace_append hprefix tailTrace_6470201
  have hstable : (prefixWord ++ tailWord_6470201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470201).length < 2 ^ (prefixWord ++ tailWord_6470201).sum := by decide
  have hdescent : baseEnd_6470201 < baseStart_6470201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470205 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 3, 3, 2]
def baseStart_6470205 : Nat := 118140960795 + 6470205 * 2 ^ 59
def prefixEnd_6470205 : Nat := 4983230072969 + 3 ^ 40 * 6470205 * 2
def baseEnd_6470205 : Nat := 3322325098123963026881575

theorem tailTrace_6470205 : CollatzResearch.WordTrace tailWord_6470205 prefixEnd_6470205 3322325098123963026881575 := by
  unfold tailWord_6470205
  simp only [CollatzResearch.WordTrace]
  refine ⟨235987763524559782883732069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157325175683039855255821379 235987763524559782883732069)
  ·
    refine ⟨44247705660854959290699763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235987763524559782883732069 44247705660854959290699763)
    ·
      refine ⟨66371558491282438936049645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44247705660854959290699763 66371558491282438936049645)
      ·
        refine ⟨24889334434230914601018617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66371558491282438936049645 24889334434230914601018617)
        ·
          refine ⟨18667000825673185950763963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24889334434230914601018617 18667000825673185950763963)
          ·
            refine ⟨28000501238509778926145945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18667000825673185950763963 28000501238509778926145945)
            ·
              refine ⟨21000375928882334194609459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28000501238509778926145945 21000375928882334194609459)
              ·
                refine ⟨31500563893323501291914189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21000375928882334194609459 31500563893323501291914189)
                ·
                  refine ⟨11812711459996312984467821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31500563893323501291914189 11812711459996312984467821)
                  ·
                    refine ⟨4429766797498617369175433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11812711459996312984467821 4429766797498617369175433)
                    ·
                      refine ⟨3322325098123963026881575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4429766797498617369175433 3322325098123963026881575)
                      ·
                        rfl

theorem cell23_6470205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_6470205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470205 prefixEnd_6470205 := by exact prefixLift 6470205
  have htrace : WordTrace (prefixWord ++ tailWord_6470205) baseStart_6470205 baseEnd_6470205 := by
    simpa [prefixWord, tailWord_6470205, baseEnd_6470205] using wordTrace_append hprefix tailTrace_6470205
  have hstable : (prefixWord ++ tailWord_6470205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470205).length < 2 ^ (prefixWord ++ tailWord_6470205).sum := by decide
  have hdescent : baseEnd_6470205 < baseStart_6470205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470222 : List Nat := [4, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2]
def baseStart_6470222 : Nat := 118140960795 + 6470222 * 2 ^ 59
def prefixEnd_6470222 : Nat := 4983230072969 + 3 ^ 40 * 6470222 * 2
def baseEnd_6470222 : Nat := 3322333827295089460368997

theorem tailTrace_6470222 : CollatzResearch.WordTrace tailWord_6470222 prefixEnd_6470222 3322333827295089460368997 := by
  unfold tailWord_6470222
  simp only [CollatzResearch.WordTrace]
  refine ⟨29498547945687274348387615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157325589043665463191400613 29498547945687274348387615)
  ·
    refine ⟨44247821918530911522581423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29498547945687274348387615 44247821918530911522581423)
    ·
      refine ⟨66371732877796367283872135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44247821918530911522581423 66371732877796367283872135)
      ·
        refine ⟨99557599316694550925808203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66371732877796367283872135 99557599316694550925808203)
        ·
          refine ⟨149336398975041826388712305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99557599316694550925808203 149336398975041826388712305)
          ·
            refine ⟨112002299231281369791534229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149336398975041826388712305 112002299231281369791534229)
            ·
              refine ⟨5250107776466314208978167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112002299231281369791534229 5250107776466314208978167)
              ·
                refine ⟨7875161664699471313467251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5250107776466314208978167 7875161664699471313467251)
                ·
                  refine ⟨11812742497049206970200877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7875161664699471313467251 11812742497049206970200877)
                  ·
                    refine ⟨4429778436393452613825329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11812742497049206970200877 4429778436393452613825329)
                    ·
                      refine ⟨3322333827295089460368997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4429778436393452613825329 3322333827295089460368997)
                      ·
                        rfl

theorem cell23_6470222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_6470222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470222 prefixEnd_6470222 := by exact prefixLift 6470222
  have htrace : WordTrace (prefixWord ++ tailWord_6470222) baseStart_6470222 baseEnd_6470222 := by
    simpa [prefixWord, tailWord_6470222, baseEnd_6470222] using wordTrace_append hprefix tailTrace_6470222
  have hstable : (prefixWord ++ tailWord_6470222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470222).length < 2 ^ (prefixWord ++ tailWord_6470222).sum := by decide
  have hdescent : baseEnd_6470222 < baseStart_6470222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470231 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_6470231 : Nat := 118140960795 + 6470231 * 2 ^ 59
def prefixEnd_6470231 : Nat := 4983230072969 + 3 ^ 40 * 6470231 * 2
def baseEnd_6470231 : Nat := 3322338448620979925156455

theorem tailTrace_6470231 : CollatzResearch.WordTrace tailWord_6470231 prefixEnd_6470231 3322338448620979925156455 := by
  unfold tailWord_6470231
  simp only [CollatzResearch.WordTrace]
  refine ⟨235988711822465589324178547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157325807881643726216119031 235988711822465589324178547)
  ·
    refine ⟨353983067733698383986267821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235988711822465589324178547 353983067733698383986267821)
    ·
      refine ⟨132743650400136893994850433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 353983067733698383986267821 132743650400136893994850433)
      ·
        refine ⟨99557737800102670496137825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132743650400136893994850433 99557737800102670496137825)
        ·
          refine ⟨74668303350077002872103369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99557737800102670496137825 74668303350077002872103369)
          ·
            refine ⟨56001227512557752154077527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74668303350077002872103369 56001227512557752154077527)
            ·
              refine ⟨84001841268836628231116291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56001227512557752154077527 84001841268836628231116291)
              ·
                refine ⟨126002761903254942346674437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84001841268836628231116291 126002761903254942346674437)
                ·
                  refine ⟨23625517856860301690001457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126002761903254942346674437 23625517856860301690001457)
                  ·
                    refine ⟨17719138392645226267501093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23625517856860301690001457 17719138392645226267501093)
                    ·
                      refine ⟨3322338448620979925156455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17719138392645226267501093 3322338448620979925156455)
                      ·
                        rfl

theorem cell23_6470231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_6470231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470231 prefixEnd_6470231 := by exact prefixLift 6470231
  have htrace : WordTrace (prefixWord ++ tailWord_6470231) baseStart_6470231 baseEnd_6470231 := by
    simpa [prefixWord, tailWord_6470231, baseEnd_6470231] using wordTrace_append hprefix tailTrace_6470231
  have hstable : (prefixWord ++ tailWord_6470231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470231).length < 2 ^ (prefixWord ++ tailWord_6470231).sum := by decide
  have hdescent : baseEnd_6470231 < baseStart_6470231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470241 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 7]
def baseStart_6470241 : Nat := 118140960795 + 6470241 * 2 ^ 59
def prefixEnd_6470241 : Nat := 4983230072969 + 3 ^ 40 * 6470241 * 2
def baseEnd_6470241 : Nat := 369149287047502765114601

theorem tailTrace_6470241 : CollatzResearch.WordTrace tailWord_6470241 prefixEnd_6470241 369149287047502765114601 := by
  unfold tailWord_6470241
  simp only [CollatzResearch.WordTrace]
  refine ⟨235989076552429361032042577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157326051034952907354695051 235989076552429361032042577)
  ·
    refine ⟨176991807414322020774031933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235989076552429361032042577 176991807414322020774031933)
    ·
      refine ⟨66371927780370757790261975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176991807414322020774031933 66371927780370757790261975)
      ·
        refine ⟨99557891670556136685392963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66371927780370757790261975 99557891670556136685392963)
        ·
          refine ⟨149336837505834205028089445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99557891670556136685392963 149336837505834205028089445)
          ·
            refine ⟨28000657032343913442766771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149336837505834205028089445 28000657032343913442766771)
            ·
              refine ⟨42000985548515870164150157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28000657032343913442766771 42000985548515870164150157)
              ·
                refine ⟨15750369580693451311556309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42000985548515870164150157 15750369580693451311556309)
                ·
                  refine ⟨369149287047502765114601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15750369580693451311556309 369149287047502765114601)
                  ·
                    rfl

theorem cell23_6470241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 7].length) (baseStart_6470241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470241 prefixEnd_6470241 := by exact prefixLift 6470241
  have htrace : WordTrace (prefixWord ++ tailWord_6470241) baseStart_6470241 baseEnd_6470241 := by
    simpa [prefixWord, tailWord_6470241, baseEnd_6470241] using wordTrace_append hprefix tailTrace_6470241
  have hstable : (prefixWord ++ tailWord_6470241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470241).length < 2 ^ (prefixWord ++ tailWord_6470241).sum := by decide
  have hdescent : baseEnd_6470241 < baseStart_6470241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470251 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 3]
def baseStart_6470251 : Nat := 118140960795 + 6470251 * 2 ^ 59
def prefixEnd_6470251 : Nat := 4983230072969 + 3 ^ 40 * 6470251 * 2
def baseEnd_6470251 : Nat := 3322348718234069846906363

theorem tailTrace_6470251 : CollatzResearch.WordTrace tailWord_6470251 prefixEnd_6470251 3322348718234069846906363 := by
  unfold tailWord_6470251
  simp only [CollatzResearch.WordTrace]
  refine ⟨235989441282393132739906607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157326294188262088493271071 235989441282393132739906607)
  ·
    refine ⟨353984161923589699109859911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235989441282393132739906607 353984161923589699109859911)
    ·
      refine ⟨530976242885384548664789867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353984161923589699109859911 530976242885384548664789867)
      ·
        refine ⟨796464364328076822997184801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530976242885384548664789867 796464364328076822997184801)
        ·
          refine ⟨597348273246057617247888601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 796464364328076822997184801 597348273246057617247888601)
          ·
            refine ⟨448011204934543212935916451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597348273246057617247888601 448011204934543212935916451)
            ·
              refine ⟨672016807401814819403874677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448011204934543212935916451 672016807401814819403874677)
              ·
                refine ⟨63001575693920139319113251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 672016807401814819403874677 63001575693920139319113251)
                ·
                  refine ⟨94502363540880208978669877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63001575693920139319113251 94502363540880208978669877)
                  ·
                    refine ⟨8859596581957519591750301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94502363540880208978669877 8859596581957519591750301)
                    ·
                      refine ⟨3322348718234069846906363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8859596581957519591750301 3322348718234069846906363)
                      ·
                        rfl

theorem cell23_6470251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 3].length) (baseStart_6470251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470251 prefixEnd_6470251 := by exact prefixLift 6470251
  have htrace : WordTrace (prefixWord ++ tailWord_6470251) baseStart_6470251 baseEnd_6470251 := by
    simpa [prefixWord, tailWord_6470251, baseEnd_6470251] using wordTrace_append hprefix tailTrace_6470251
  have hstable : (prefixWord ++ tailWord_6470251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470251).length < 2 ^ (prefixWord ++ tailWord_6470251).sum := by decide
  have hdescent : baseEnd_6470251 < baseStart_6470251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470281 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 1, 2, 5]
def baseStart_6470281 : Nat := 118140960795 + 6470281 * 2 ^ 59
def prefixEnd_6470281 : Nat := 4983230072969 + 3 ^ 40 * 6470281 * 2
def baseEnd_6470281 : Nat := 3322364122653704729531225

theorem tailTrace_6470281 : CollatzResearch.WordTrace tailWord_6470281 prefixEnd_6470281 3322364122653704729531225 := by
  unfold tailWord_6470281
  simp only [CollatzResearch.WordTrace]
  refine ⟨235990535472284447863498697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157327023648189631908999131 235990535472284447863498697)
  ·
    refine ⟨176992901604213335897624023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235990535472284447863498697 176992901604213335897624023)
    ·
      refine ⟨265489352406320003846436035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176992901604213335897624023 265489352406320003846436035)
      ·
        refine ⟨398234028609480005769654053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265489352406320003846436035 398234028609480005769654053)
        ·
          refine ⟨74668880364277501081810135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 398234028609480005769654053 74668880364277501081810135)
          ·
            refine ⟨112003320546416251622715203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74668880364277501081810135 112003320546416251622715203)
            ·
              refine ⟨168004980819624377434072805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112003320546416251622715203 168004980819624377434072805)
              ·
                refine ⟨31500933903679570768888651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168004980819624377434072805 31500933903679570768888651)
                ·
                  refine ⟨47251400855519356153332977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31500933903679570768888651 47251400855519356153332977)
                  ·
                    refine ⟨35438550641639517114999733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47251400855519356153332977 35438550641639517114999733)
                    ·
                      refine ⟨3322364122653704729531225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35438550641639517114999733 3322364122653704729531225)
                      ·
                        rfl

theorem cell23_6470281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_6470281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470281 prefixEnd_6470281 := by exact prefixLift 6470281
  have htrace : WordTrace (prefixWord ++ tailWord_6470281) baseStart_6470281 baseEnd_6470281 := by
    simpa [prefixWord, tailWord_6470281, baseEnd_6470281] using wordTrace_append hprefix tailTrace_6470281
  have hstable : (prefixWord ++ tailWord_6470281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470281).length < 2 ^ (prefixWord ++ tailWord_6470281).sum := by decide
  have hdescent : baseEnd_6470281 < baseStart_6470281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470308 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_6470308 : Nat := 118140960795 + 6470308 * 2 ^ 59
def prefixEnd_6470308 : Nat := 4983230072969 + 3 ^ 40 * 6470308 * 2
def baseEnd_6470308 : Nat := 3322377986631376123893601

theorem tailTrace_6470308 : CollatzResearch.WordTrace tailWord_6470308 prefixEnd_6470308 3322377986631376123893601 := by
  unfold tailWord_6470308
  simp only [CollatzResearch.WordTrace]
  refine ⟨117995760121593315737365789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157327680162124420983154385 117995760121593315737365789)
  ·
    refine ⟨44248410045597493401512171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117995760121593315737365789 44248410045597493401512171)
    ·
      refine ⟨66372615068396240102268257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44248410045597493401512171 66372615068396240102268257)
      ·
        refine ⟨49779461301297180076701193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66372615068396240102268257 49779461301297180076701193)
        ·
          refine ⟨37334595975972885057525895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49779461301297180076701193 37334595975972885057525895)
          ·
            refine ⟨56001893963959327586288843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37334595975972885057525895 56001893963959327586288843)
            ·
              refine ⟨84002840945938991379433265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56001893963959327586288843 84002840945938991379433265)
              ·
                refine ⟨63002130709454243534574949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84002840945938991379433265 63002130709454243534574949)
                ·
                  refine ⟨11812899508022670662732803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63002130709454243534574949 11812899508022670662732803)
                  ·
                    refine ⟨17719349262034005994099205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11812899508022670662732803 17719349262034005994099205)
                    ·
                      refine ⟨3322377986631376123893601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17719349262034005994099205 3322377986631376123893601)
                      ·
                        rfl

theorem cell23_6470308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_6470308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470308 prefixEnd_6470308 := by exact prefixLift 6470308
  have htrace : WordTrace (prefixWord ++ tailWord_6470308) baseStart_6470308 baseEnd_6470308 := by
    simpa [prefixWord, tailWord_6470308, baseEnd_6470308] using wordTrace_append hprefix tailTrace_6470308
  have hstable : (prefixWord ++ tailWord_6470308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470308).length < 2 ^ (prefixWord ++ tailWord_6470308).sum := by decide
  have hdescent : baseEnd_6470308 < baseStart_6470308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470325 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_6470325 : Nat := 118140960795 + 6470325 * 2 ^ 59
def prefixEnd_6470325 : Nat := 4983230072969 + 3 ^ 40 * 6470325 * 2
def baseEnd_6470325 : Nat := 3322386715802502557381023

theorem tailTrace_6470325 : CollatzResearch.WordTrace tailWord_6470325 prefixEnd_6470325 3322386715802502557381023 := by
  unfold tailWord_6470325
  simp only [CollatzResearch.WordTrace]
  refine ⟨235992140284125043378100429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157328093522750028918733619 235992140284125043378100429)
  ·
    refine ⟨88497052606546891266787661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 235992140284125043378100429 88497052606546891266787661)
    ·
      refine ⟨33186394727455084225045373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88497052606546891266787661 33186394727455084225045373)
      ·
        refine ⟨12444898022795656584392015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33186394727455084225045373 12444898022795656584392015)
        ·
          refine ⟨18667347034193484876588023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12444898022795656584392015 18667347034193484876588023)
          ·
            refine ⟨28001020551290227314882035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18667347034193484876588023 28001020551290227314882035)
            ·
              refine ⟨42001530826935340972323053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28001020551290227314882035 42001530826935340972323053)
              ·
                refine ⟨15750574060100752864621145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42001530826935340972323053 15750574060100752864621145)
                ·
                  refine ⟨11812930545075564648465859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15750574060100752864621145 11812930545075564648465859)
                  ·
                    refine ⟨17719395817613346972698789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11812930545075564648465859 17719395817613346972698789)
                    ·
                      refine ⟨3322386715802502557381023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17719395817613346972698789 3322386715802502557381023)
                      ·
                        rfl

theorem cell23_6470325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_6470325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470325 prefixEnd_6470325 := by exact prefixLift 6470325
  have htrace : WordTrace (prefixWord ++ tailWord_6470325) baseStart_6470325 baseEnd_6470325 := by
    simpa [prefixWord, tailWord_6470325, baseEnd_6470325] using wordTrace_append hprefix tailTrace_6470325
  have hstable : (prefixWord ++ tailWord_6470325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470325).length < 2 ^ (prefixWord ++ tailWord_6470325).sum := by decide
  have hdescent : baseEnd_6470325 < baseStart_6470325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470385 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 1, 5, 2]
def baseStart_6470385 : Nat := 118140960795 + 6470385 * 2 ^ 59
def prefixEnd_6470385 : Nat := 4983230072969 + 3 ^ 40 * 6470385 * 2
def baseEnd_6470385 : Nat := 3322417524641772322630747

theorem tailTrace_6470385 : CollatzResearch.WordTrace tailWord_6470385 prefixEnd_6470385 3322417524641772322630747 := by
  unfold tailWord_6470385
  simp only [CollatzResearch.WordTrace]
  refine ⟨235994328663907673625284609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157329552442605115750189739 235994328663907673625284609)
  ·
    refine ⟨176995746497930755218963457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235994328663907673625284609 176995746497930755218963457)
    ·
      refine ⟨132746809873448066414222593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176995746497930755218963457 132746809873448066414222593)
      ·
        refine ⟨99560107405086049810666945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132746809873448066414222593 99560107405086049810666945)
        ·
          refine ⟨74670080553814537358000209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99560107405086049810666945 74670080553814537358000209)
          ·
            refine ⟨56002560415360903018500157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74670080553814537358000209 56002560415360903018500157)
            ·
              refine ⟨21000960155760338631937559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56002560415360903018500157 21000960155760338631937559)
              ·
                refine ⟨31501440233640507947906339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21000960155760338631937559 31501440233640507947906339)
                ·
                  refine ⟨47252160350460761921859509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31501440233640507947906339 47252160350460761921859509)
                  ·
                    refine ⟨4429890032855696430174329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47252160350460761921859509 4429890032855696430174329)
                    ·
                      refine ⟨3322417524641772322630747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4429890032855696430174329 3322417524641772322630747)
                      ·
                        rfl

theorem cell23_6470385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_6470385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470385 prefixEnd_6470385 := by exact prefixLift 6470385
  have htrace : WordTrace (prefixWord ++ tailWord_6470385) baseStart_6470385 baseEnd_6470385 := by
    simpa [prefixWord, tailWord_6470385, baseEnd_6470385] using wordTrace_append hprefix tailTrace_6470385
  have hstable : (prefixWord ++ tailWord_6470385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470385).length < 2 ^ (prefixWord ++ tailWord_6470385).sum := by decide
  have hdescent : baseEnd_6470385 < baseStart_6470385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470429 : List Nat := [1, 4, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_6470429 : Nat := 118140960795 + 6470429 * 2 ^ 59
def prefixEnd_6470429 : Nat := 4983230072969 + 3 ^ 40 * 6470429 * 2
def baseEnd_6470429 : Nat := 1107480039263523383493515

theorem tailTrace_6470429 : CollatzResearch.WordTrace tailWord_6470429 prefixEnd_6470429 1107480039263523383493515 := by
  unfold tailWord_6470429
  simp only [CollatzResearch.WordTrace]
  refine ⟨235995933475748269139886341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157330622317165512759924227 235995933475748269139886341)
  ·
    refine ⟨44249237526702800463728689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235995933475748269139886341 44249237526702800463728689)
    ·
      refine ⟨33186928145027100347796517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44249237526702800463728689 33186928145027100347796517)
      ·
        refine ⟨6222549027192581315211847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33186928145027100347796517 6222549027192581315211847)
        ·
          refine ⟨9333823540788871972817771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6222549027192581315211847 9333823540788871972817771)
          ·
            refine ⟨14000735311183307959226657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9333823540788871972817771 14000735311183307959226657)
            ·
              refine ⟨10500551483387480969419993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14000735311183307959226657 10500551483387480969419993)
              ·
                refine ⟨7875413612540610727064995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10500551483387480969419993 7875413612540610727064995)
                ·
                  refine ⟨11813120418810916090597493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7875413612540610727064995 11813120418810916090597493)
                  ·
                    refine ⟨1107480039263523383493515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11813120418810916090597493 1107480039263523383493515)
                    ·
                      rfl

theorem cell23_6470429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_6470429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470429 prefixEnd_6470429 := by exact prefixLift 6470429
  have htrace : WordTrace (prefixWord ++ tailWord_6470429) baseStart_6470429 baseEnd_6470429 := by
    simpa [prefixWord, tailWord_6470429, baseEnd_6470429] using wordTrace_append hprefix tailTrace_6470429
  have hstable : (prefixWord ++ tailWord_6470429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470429).length < 2 ^ (prefixWord ++ tailWord_6470429).sum := by decide
  have hdescent : baseEnd_6470429 < baseStart_6470429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470432 : List Nat := [2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 4]
def baseStart_6470432 : Nat := 118140960795 + 6470432 * 2 ^ 59
def prefixEnd_6470432 : Nat := 4983230072969 + 3 ^ 40 * 6470432 * 2
def baseEnd_6470432 : Nat := 3322441658232533638743031

theorem tailTrace_6470432 : CollatzResearch.WordTrace tailWord_6470432 prefixEnd_6470432 3322441658232533638743031 := by
  unfold tailWord_6470432
  simp only [CollatzResearch.WordTrace]
  refine ⟨117998021447368700326122775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157330695263158267101497033 117998021447368700326122775)
  ·
    refine ⟨176997032171053050489184163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117998021447368700326122775 176997032171053050489184163)
    ·
      refine ⟨265495548256579575733776245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176997032171053050489184163 265495548256579575733776245)
      ·
        refine ⟨24890207649054335225041523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 265495548256579575733776245 24890207649054335225041523)
        ·
          refine ⟨37335311473581502837562285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24890207649054335225041523 37335311473581502837562285)
          ·
            refine ⟨14000741802593063564085857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37335311473581502837562285 14000741802593063564085857)
            ·
              refine ⟨10500556351944797673064393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14000741802593063564085857 10500556351944797673064393)
              ·
                refine ⟨7875417263958598254798295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10500556351944797673064393 7875417263958598254798295)
                ·
                  refine ⟨11813125895937897382197443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7875417263958598254798295 11813125895937897382197443)
                  ·
                    refine ⟨17719688843906846073296165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11813125895937897382197443 17719688843906846073296165)
                    ·
                      refine ⟨3322441658232533638743031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17719688843906846073296165 3322441658232533638743031)
                      ·
                        rfl

theorem cell23_6470432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_6470432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470432 prefixEnd_6470432 := by exact prefixLift 6470432
  have htrace : WordTrace (prefixWord ++ tailWord_6470432) baseStart_6470432 baseEnd_6470432 := by
    simpa [prefixWord, tailWord_6470432, baseEnd_6470432] using wordTrace_append hprefix tailTrace_6470432
  have hstable : (prefixWord ++ tailWord_6470432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470432).length < 2 ^ (prefixWord ++ tailWord_6470432).sum := by decide
  have hdescent : baseEnd_6470432 < baseStart_6470432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470525 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_6470525 : Nat := 118140960795 + 6470525 * 2 ^ 59
def prefixEnd_6470525 : Nat := 4983230072969 + 3 ^ 40 * 6470525 * 2
def baseEnd_6470525 : Nat := 3322489411933401774880103

theorem tailTrace_6470525 : CollatzResearch.WordTrace tailWord_6470525 prefixEnd_6470525 3322489411933401774880103 := by
  unfold tailWord_6470525
  simp only [CollatzResearch.WordTrace]
  refine ⟨235999434883400477535381029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157332956588933651690254019 235999434883400477535381029)
  ·
    refine ⟨44249894040637589537883943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235999434883400477535381029 44249894040637589537883943)
    ·
      refine ⟨66374841060956384306825915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44249894040637589537883943 66374841060956384306825915)
      ·
        refine ⟨99562261591434576460238873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66374841060956384306825915 99562261591434576460238873)
        ·
          refine ⟨74671696193575932345179155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99562261591434576460238873 74671696193575932345179155)
          ·
            refine ⟨112007544290363898517768733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74671696193575932345179155 112007544290363898517768733)
            ·
              refine ⟨42002829108886461944163275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112007544290363898517768733 42002829108886461944163275)
              ·
                refine ⟨63004243663329692916244913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42002829108886461944163275 63004243663329692916244913)
                ·
                  refine ⟨47253182747497269687183685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63004243663329692916244913 47253182747497269687183685)
                  ·
                    refine ⟨8859971765155738066346941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47253182747497269687183685 8859971765155738066346941)
                    ·
                      refine ⟨3322489411933401774880103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8859971765155738066346941 3322489411933401774880103)
                      ·
                        rfl

theorem cell23_6470525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_6470525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470525 prefixEnd_6470525 := by exact prefixLift 6470525
  have htrace : WordTrace (prefixWord ++ tailWord_6470525) baseStart_6470525 baseEnd_6470525 := by
    simpa [prefixWord, tailWord_6470525, baseEnd_6470525] using wordTrace_append hprefix tailTrace_6470525
  have hstable : (prefixWord ++ tailWord_6470525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470525).length < 2 ^ (prefixWord ++ tailWord_6470525).sum := by decide
  have hdescent : baseEnd_6470525 < baseStart_6470525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470535 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_6470535 : Nat := 118140960795 + 6470535 * 2 ^ 59
def prefixEnd_6470535 : Nat := 4983230072969 + 3 ^ 40 * 6470535 * 2
def baseEnd_6470535 : Nat := 3322494546739946735755057

theorem tailTrace_6470535 : CollatzResearch.WordTrace tailWord_6470535 prefixEnd_6470535 3322494546739946735755057 := by
  unfold tailWord_6470535
  simp only [CollatzResearch.WordTrace]
  refine ⟨235999799613364249243245059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157333199742242832828830039 235999799613364249243245059)
  ·
    refine ⟨353999699420046373864867589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235999799613364249243245059 353999699420046373864867589)
    ·
      refine ⟨66374943641258695099662673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353999699420046373864867589 66374943641258695099662673)
      ·
        refine ⟨49781207730944021324747005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66374943641258695099662673 49781207730944021324747005)
        ·
          refine ⟨18667952899104007996780127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49781207730944021324747005 18667952899104007996780127)
          ·
            refine ⟨28001929348656011995170191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18667952899104007996780127 28001929348656011995170191)
            ·
              refine ⟨42002894022984017992755287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28001929348656011995170191 42002894022984017992755287)
              ·
                refine ⟨63004341034476026989132931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42002894022984017992755287 63004341034476026989132931)
                ·
                  refine ⟨94506511551714040483699397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63004341034476026989132931 94506511551714040483699397)
                  ·
                    refine ⟨17719970915946382590693637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94506511551714040483699397 17719970915946382590693637)
                    ·
                      refine ⟨3322494546739946735755057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17719970915946382590693637 3322494546739946735755057)
                      ·
                        rfl

theorem cell23_6470535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_6470535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470535 prefixEnd_6470535 := by exact prefixLift 6470535
  have htrace : WordTrace (prefixWord ++ tailWord_6470535) baseStart_6470535 baseEnd_6470535 := by
    simpa [prefixWord, tailWord_6470535, baseEnd_6470535] using wordTrace_append hprefix tailTrace_6470535
  have hstable : (prefixWord ++ tailWord_6470535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470535).length < 2 ^ (prefixWord ++ tailWord_6470535).sum := by decide
  have hdescent : baseEnd_6470535 < baseStart_6470535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470539 : List Nat := [1, 1, 1, 1, 4, 2, 4, 3, 2, 2, 2]
def baseStart_6470539 : Nat := 118140960795 + 6470539 * 2 ^ 59
def prefixEnd_6470539 : Nat := 4983230072969 + 3 ^ 40 * 6470539 * 2
def baseEnd_6470539 : Nat := 3322496600662564720105039

theorem tailTrace_6470539 : CollatzResearch.WordTrace tailWord_6470539 prefixEnd_6470539 3322496600662564720105039 := by
  unfold tailWord_6470539
  simp only [CollatzResearch.WordTrace]
  refine ⟨235999945505349757926390671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157333297003566505284260447 235999945505349757926390671)
  ·
    refine ⟨353999918258024636889586007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235999945505349757926390671 353999918258024636889586007)
    ·
      refine ⟨530999877387036955334379011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353999918258024636889586007 530999877387036955334379011)
      ·
        refine ⟨796499816080555433001568517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530999877387036955334379011 796499816080555433001568517)
        ·
          refine ⟨149343715515104143687794097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 796499816080555433001568517 149343715515104143687794097)
          ·
            refine ⟨112007786636328107765845573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149343715515104143687794097 112007786636328107765845573)
            ·
              refine ⟨21001459994311520206096045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112007786636328107765845573 21001459994311520206096045)
              ·
                refine ⟨7875547497866820077286017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21001459994311520206096045 7875547497866820077286017)
                ·
                  refine ⟨5906660623400115057964513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7875547497866820077286017 5906660623400115057964513)
                  ·
                    refine ⟨4429995467550086293473385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5906660623400115057964513 4429995467550086293473385)
                    ·
                      refine ⟨3322496600662564720105039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4429995467550086293473385 3322496600662564720105039)
                      ·
                        rfl

theorem cell23_6470539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 2, 2].length) (baseStart_6470539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470539 prefixEnd_6470539 := by exact prefixLift 6470539
  have htrace : WordTrace (prefixWord ++ tailWord_6470539) baseStart_6470539 baseEnd_6470539 := by
    simpa [prefixWord, tailWord_6470539, baseEnd_6470539] using wordTrace_append hprefix tailTrace_6470539
  have hstable : (prefixWord ++ tailWord_6470539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470539).length < 2 ^ (prefixWord ++ tailWord_6470539).sum := by decide
  have hdescent : baseEnd_6470539 < baseStart_6470539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470573 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_6470573 : Nat := 118140960795 + 6470573 * 2 ^ 59
def prefixEnd_6470573 : Nat := 4983230072969 + 3 ^ 40 * 6470573 * 2
def baseEnd_6470573 : Nat := 3322514059004817587079883

theorem tailTrace_6470573 : CollatzResearch.WordTrace tailWord_6470573 prefixEnd_6470573 3322514059004817587079883 := by
  unfold tailWord_6470573
  simp only [CollatzResearch.WordTrace]
  refine ⟨236001185587226581733128373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157334123724817721155418915 236001185587226581733128373)
  ·
    refine ⟨22125111148802492037480785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236001185587226581733128373 22125111148802492037480785)
    ·
      refine ⟨16593833361601869028110589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22125111148802492037480785 16593833361601869028110589)
      ·
        refine ⟨6222687510600700885541471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16593833361601869028110589 6222687510600700885541471)
        ·
          refine ⟨9334031265901051328312207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6222687510600700885541471 9334031265901051328312207)
          ·
            refine ⟨14001046898851576992468311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9334031265901051328312207 14001046898851576992468311)
            ·
              refine ⟨21001570348277365488702467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14001046898851576992468311 21001570348277365488702467)
              ·
                refine ⟨31502355522416048233053701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21001570348277365488702467 31502355522416048233053701)
                ·
                  refine ⟨5906691660453009043697569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31502355522416048233053701 5906691660453009043697569)
                  ·
                    refine ⟨4430018745339756782773177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5906691660453009043697569 4430018745339756782773177)
                    ·
                      refine ⟨3322514059004817587079883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4430018745339756782773177 3322514059004817587079883)
                      ·
                        rfl

theorem cell23_6470573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_6470573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470573 prefixEnd_6470573 := by exact prefixLift 6470573
  have htrace : WordTrace (prefixWord ++ tailWord_6470573) baseStart_6470573 baseEnd_6470573 := by
    simpa [prefixWord, tailWord_6470573, baseEnd_6470573] using wordTrace_append hprefix tailTrace_6470573
  have hstable : (prefixWord ++ tailWord_6470573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470573).length < 2 ^ (prefixWord ++ tailWord_6470573).sum := by decide
  have hdescent : baseEnd_6470573 < baseStart_6470573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470595 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 4]
def baseStart_6470595 : Nat := 118140960795 + 6470595 * 2 ^ 59
def prefixEnd_6470595 : Nat := 4983230072969 + 3 ^ 40 * 6470595 * 2
def baseEnd_6470595 : Nat := 3322525355579216501004781

theorem tailTrace_6470595 : CollatzResearch.WordTrace tailWord_6470595 prefixEnd_6470595 3322525355579216501004781 := by
  unfold tailWord_6470595
  simp only [CollatzResearch.WordTrace]
  refine ⟨236001987993146879490429239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157334658662097919660286159 236001987993146879490429239)
  ·
    refine ⟨354002981989720319235643859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236001987993146879490429239 354002981989720319235643859)
    ·
      refine ⟨531004472984580478853465789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354002981989720319235643859 531004472984580478853465789)
      ·
        refine ⟨199126677369217679570049671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 531004472984580478853465789 199126677369217679570049671)
        ·
          refine ⟨298690016053826519355074507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199126677369217679570049671 298690016053826519355074507)
          ·
            refine ⟨448035024080739779032611761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298690016053826519355074507 448035024080739779032611761)
            ·
              refine ⟨336026268060554834274458821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448035024080739779032611761 336026268060554834274458821)
              ·
                refine ⟨63004925261354031426461029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336026268060554834274458821 63004925261354031426461029)
                ·
                  refine ⟨11813423486503880892461443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63004925261354031426461029 11813423486503880892461443)
                  ·
                    refine ⟨17720135229755821338692165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11813423486503880892461443 17720135229755821338692165)
                    ·
                      refine ⟨3322525355579216501004781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17720135229755821338692165 3322525355579216501004781)
                      ·
                        rfl

theorem cell23_6470595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_6470595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470595 prefixEnd_6470595 := by exact prefixLift 6470595
  have htrace : WordTrace (prefixWord ++ tailWord_6470595) baseStart_6470595 baseEnd_6470595 := by
    simpa [prefixWord, tailWord_6470595, baseEnd_6470595] using wordTrace_append hprefix tailTrace_6470595
  have hstable : (prefixWord ++ tailWord_6470595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470595).length < 2 ^ (prefixWord ++ tailWord_6470595).sum := by decide
  have hdescent : baseEnd_6470595 < baseStart_6470595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470612 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_6470612 : Nat := 118140960795 + 6470612 * 2 ^ 59
def prefixEnd_6470612 : Nat := 4983230072969 + 3 ^ 40 * 6470612 * 2
def baseEnd_6470612 : Nat := 3322534084750342934492203

theorem tailTrace_6470612 : CollatzResearch.WordTrace tailWord_6470612 prefixEnd_6470612 3322534084750342934492203 := by
  unfold tailWord_6470612
  simp only [CollatzResearch.WordTrace]
  refine ⟨118001304017042645696899045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157335072022723527595865393 118001304017042645696899045)
  ·
    refine ⟨22125244503195496068168571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118001304017042645696899045 22125244503195496068168571)
    ·
      refine ⟨33187866754793244102252857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22125244503195496068168571 33187866754793244102252857)
      ·
        refine ⟨24890900066094933076689643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33187866754793244102252857 24890900066094933076689643)
        ·
          refine ⟨37336350099142399615034465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24890900066094933076689643 37336350099142399615034465)
          ·
            refine ⟨28002262574356799711275849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37336350099142399615034465 28002262574356799711275849)
            ·
              refine ⟨21001696930767599783456887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28002262574356799711275849 21001696930767599783456887)
              ·
                refine ⟨31502545396151399675185331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21001696930767599783456887 31502545396151399675185331)
                ·
                  refine ⟨47253818094227099512777997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31502545396151399675185331 47253818094227099512777997)
                  ·
                    refine ⟨17720181785335162317291749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47253818094227099512777997 17720181785335162317291749)
                    ·
                      refine ⟨3322534084750342934492203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17720181785335162317291749 3322534084750342934492203)
                      ·
                        rfl

theorem cell23_6470612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_6470612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470612 prefixEnd_6470612 := by exact prefixLift 6470612
  have htrace : WordTrace (prefixWord ++ tailWord_6470612) baseStart_6470612 baseEnd_6470612 := by
    simpa [prefixWord, tailWord_6470612, baseEnd_6470612] using wordTrace_append hprefix tailTrace_6470612
  have hstable : (prefixWord ++ tailWord_6470612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470612).length < 2 ^ (prefixWord ++ tailWord_6470612).sum := by decide
  have hdescent : baseEnd_6470612 < baseStart_6470612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470632 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_6470632 : Nat := 118140960795 + 6470632 * 2 ^ 59
def prefixEnd_6470632 : Nat := 4983230072969 + 3 ^ 40 * 6470632 * 2
def baseEnd_6470632 : Nat := 3322544354363432856242111

theorem tailTrace_6470632 : CollatzResearch.WordTrace tailWord_6470632 prefixEnd_6470632 3322544354363432856242111 := by
  unfold tailWord_6470632
  simp only [CollatzResearch.WordTrace]
  refine ⟨118001668747006417404763075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157335558329341889873017433 118001668747006417404763075)
  ·
    refine ⟨177002503120509626107144613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118001668747006417404763075 177002503120509626107144613)
    ·
      refine ⟨33187969335095554895089615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177002503120509626107144613 33187969335095554895089615)
      ·
        refine ⟨49781954002643332342634423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33187969335095554895089615 49781954002643332342634423)
        ·
          refine ⟨74672931003964998513951635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49781954002643332342634423 74672931003964998513951635)
          ·
            refine ⟨112009396505947497770927453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74672931003964998513951635 112009396505947497770927453)
            ·
              refine ⟨42003523689730311664097795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112009396505947497770927453 42003523689730311664097795)
              ·
                refine ⟨63005285534595467496146693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42003523689730311664097795 63005285534595467496146693)
                ·
                  refine ⟨11813491037736650155527505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63005285534595467496146693 11813491037736650155527505)
                  ·
                    refine ⟨8860118278302487616645629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11813491037736650155527505 8860118278302487616645629)
                    ·
                      refine ⟨3322544354363432856242111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8860118278302487616645629 3322544354363432856242111)
                      ·
                        rfl

theorem cell23_6470632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_6470632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470632 prefixEnd_6470632 := by exact prefixLift 6470632
  have htrace : WordTrace (prefixWord ++ tailWord_6470632) baseStart_6470632 baseEnd_6470632 := by
    simpa [prefixWord, tailWord_6470632, baseEnd_6470632] using wordTrace_append hprefix tailTrace_6470632
  have hstable : (prefixWord ++ tailWord_6470632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470632).length < 2 ^ (prefixWord ++ tailWord_6470632).sum := by decide
  have hdescent : baseEnd_6470632 < baseStart_6470632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470639 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 3, 4]
def baseStart_6470639 : Nat := 118140960795 + 6470639 * 2 ^ 59
def prefixEnd_6470639 : Nat := 4983230072969 + 3 ^ 40 * 6470639 * 2
def baseEnd_6470639 : Nat := 1107515982909338109618193

theorem tailTrace_6470639 : CollatzResearch.WordTrace tailWord_6470639 prefixEnd_6470639 1107515982909338109618193 := by
  unfold tailWord_6470639
  simp only [CollatzResearch.WordTrace]
  refine ⟨236003592804987475005030971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157335728536658316670020647 236003592804987475005030971)
  ·
    refine ⟨354005389207481212507546457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236003592804987475005030971 354005389207481212507546457)
    ·
      refine ⟨265504041905610909380659843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354005389207481212507546457 265504041905610909380659843)
      ·
        refine ⟨398256062858416364070989765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265504041905610909380659843 398256062858416364070989765)
        ·
          refine ⟨74673011785953068263310581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 398256062858416364070989765 74673011785953068263310581)
          ·
            refine ⟨7000594854933100149685367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74673011785953068263310581 7000594854933100149685367)
            ·
              refine ⟨10500892282399650224528051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7000594854933100149685367 10500892282399650224528051)
              ·
                refine ⟨15751338423599475336792077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10500892282399650224528051 15751338423599475336792077)
                ·
                  refine ⟨5906751908849803251297029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15751338423599475336792077 5906751908849803251297029)
                  ·
                    refine ⟨1107515982909338109618193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5906751908849803251297029 1107515982909338109618193)
                    ·
                      rfl

theorem cell23_6470639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 4].length) (baseStart_6470639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470639 prefixEnd_6470639 := by exact prefixLift 6470639
  have htrace : WordTrace (prefixWord ++ tailWord_6470639) baseStart_6470639 baseEnd_6470639 := by
    simpa [prefixWord, tailWord_6470639, baseEnd_6470639] using wordTrace_append hprefix tailTrace_6470639
  have hstable : (prefixWord ++ tailWord_6470639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470639).length < 2 ^ (prefixWord ++ tailWord_6470639).sum := by decide
  have hdescent : baseEnd_6470639 < baseStart_6470639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470652 : List Nat := [2, 2, 2, 1, 2, 4, 1, 3, 6]
def baseStart_6470652 : Nat := 118140960795 + 6470652 * 2 ^ 59
def prefixEnd_6470652 : Nat := 4983230072969 + 3 ^ 40 * 6470652 * 2
def baseEnd_6470652 : Nat := 369172735997391419776891

theorem tailTrace_6470652 : CollatzResearch.WordTrace tailWord_6470652 prefixEnd_6470652 369172735997391419776891 := by
  unfold tailWord_6470652
  simp only [CollatzResearch.WordTrace]
  refine ⟨118002033476970189112627105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157336044635960252150169473 118002033476970189112627105)
  ·
    refine ⟨88501525107727641834470329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118002033476970189112627105 88501525107727641834470329)
    ·
      refine ⟨66376143830795731375852747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88501525107727641834470329 66376143830795731375852747)
      ·
        refine ⟨99564215746193597063779121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66376143830795731375852747 99564215746193597063779121)
        ·
          refine ⟨74673161809645197797834341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99564215746193597063779121 74673161809645197797834341)
          ·
            refine ⟨14001217839308474587093939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74673161809645197797834341 14001217839308474587093939)
            ·
              refine ⟨21001826758962711880640909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14001217839308474587093939 21001826758962711880640909)
              ·
                refine ⟨7875685034611016955240341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21001826758962711880640909 7875685034611016955240341)
                ·
                  refine ⟨369172735997391419776891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7875685034611016955240341 369172735997391419776891)
                  ·
                    rfl

theorem cell23_6470652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 6].length) (baseStart_6470652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470652 prefixEnd_6470652 := by exact prefixLift 6470652
  have htrace : WordTrace (prefixWord ++ tailWord_6470652) baseStart_6470652 baseEnd_6470652 := by
    simpa [prefixWord, tailWord_6470652, baseEnd_6470652] using wordTrace_append hprefix tailTrace_6470652
  have hstable : (prefixWord ++ tailWord_6470652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470652).length < 2 ^ (prefixWord ++ tailWord_6470652).sum := by decide
  have hdescent : baseEnd_6470652 < baseStart_6470652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470712 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 1, 6]
def baseStart_6470712 : Nat := 118140960795 + 6470712 * 2 ^ 59
def prefixEnd_6470712 : Nat := 4983230072969 + 3 ^ 40 * 6470712 * 2
def baseEnd_6470712 : Nat := 1107528477605264181080581

theorem tailTrace_6470712 : CollatzResearch.WordTrace tailWord_6470712 prefixEnd_6470712 1107528477605264181080581 := by
  unfold tailWord_6470712
  simp only [CollatzResearch.WordTrace]
  refine ⟨118003127666861504236219195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157337503555815338981625593 118003127666861504236219195)
  ·
    refine ⟨177004691500292256354328793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118003127666861504236219195 177004691500292256354328793)
    ·
      refine ⟨132753518625219192265746595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177004691500292256354328793 132753518625219192265746595)
      ·
        refine ⟨199130277937828788398619893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132753518625219192265746595 199130277937828788398619893)
        ·
          refine ⟨18668463556671448912370615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199130277937828788398619893 18668463556671448912370615)
          ·
            refine ⟨28002695335007173368555923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18668463556671448912370615 28002695335007173368555923)
            ·
              refine ⟨42004043002510760052833885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28002695335007173368555923 42004043002510760052833885)
              ·
                refine ⟨15751516125941535019812707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42004043002510760052833885 15751516125941535019812707)
                ·
                  refine ⟨23627274188912302529719061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15751516125941535019812707 23627274188912302529719061)
                  ·
                    refine ⟨1107528477605264181080581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23627274188912302529719061 1107528477605264181080581)
                    ·
                      rfl

theorem cell23_6470712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_6470712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470712 prefixEnd_6470712 := by exact prefixLift 6470712
  have htrace : WordTrace (prefixWord ++ tailWord_6470712) baseStart_6470712 baseEnd_6470712 := by
    simpa [prefixWord, tailWord_6470712, baseEnd_6470712] using wordTrace_append hprefix tailTrace_6470712
  have hstable : (prefixWord ++ tailWord_6470712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470712).length < 2 ^ (prefixWord ++ tailWord_6470712).sum := by decide
  have hdescent : baseEnd_6470712 < baseStart_6470712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470725 : List Nat := [1, 3, 1, 1, 1, 3, 2, 11]
def baseStart_6470725 : Nat := 118140960795 + 6470725 * 2 ^ 59
def prefixEnd_6470725 : Nat := 4983230072969 + 3 ^ 40 * 6470725 * 2
def baseEnd_6470725 : Nat := 123058966965344481199229

theorem tailTrace_6470725 : CollatzResearch.WordTrace tailWord_6470725 prefixEnd_6470725 123058966965344481199229 := by
  unfold tailWord_6470725
  simp only [CollatzResearch.WordTrace]
  refine ⟨236006729482675911692661629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157337819655117274461774419 236006729482675911692661629)
  ·
    refine ⟨88502523556003466884748111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236006729482675911692661629 88502523556003466884748111)
    ·
      refine ⟨132753785334005200327122167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88502523556003466884748111 132753785334005200327122167)
      ·
        refine ⟨199130678001007800490683251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132753785334005200327122167 199130678001007800490683251)
        ·
          refine ⟨298696017001511700736024877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199130678001007800490683251 298696017001511700736024877)
          ·
            refine ⟨112011006375566887776009329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298696017001511700736024877 112011006375566887776009329)
            ·
              refine ⟨84008254781675165832006997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112011006375566887776009329 84008254781675165832006997)
              ·
                refine ⟨123058966965344481199229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 84008254781675165832006997 123058966965344481199229)
                ·
                  rfl

theorem cell23_6470725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 11].length) (baseStart_6470725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470725 prefixEnd_6470725 := by exact prefixLift 6470725
  have htrace : WordTrace (prefixWord ++ tailWord_6470725) baseStart_6470725 baseEnd_6470725 := by
    simpa [prefixWord, tailWord_6470725, baseEnd_6470725] using wordTrace_append hprefix tailTrace_6470725
  have hstable : (prefixWord ++ tailWord_6470725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470725).length < 2 ^ (prefixWord ++ tailWord_6470725).sum := by decide
  have hdescent : baseEnd_6470725 < baseStart_6470725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470733 : List Nat := [1, 6, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_6470733 : Nat := 118140960795 + 6470733 * 2 ^ 59
def prefixEnd_6470733 : Nat := 4983230072969 + 3 ^ 40 * 6470733 * 2
def baseEnd_6470733 : Nat := 1107532071969845653693049

theorem tailTrace_6470733 : CollatzResearch.WordTrace tailWord_6470733 prefixEnd_6470733 1107532071969845653693049 := by
  unfold tailWord_6470733
  simp only [CollatzResearch.WordTrace]
  refine ⟨236007021266646929058952853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157338014177764619372635235 236007021266646929058952853)
  ·
    refine ⟨11062829121874074799638415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 236007021266646929058952853 11062829121874074799638415)
    ·
      refine ⟨16594243682811112199457623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11062829121874074799638415 16594243682811112199457623)
      ·
        refine ⟨24891365524216668299186435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16594243682811112199457623 24891365524216668299186435)
        ·
          refine ⟨37337048286325002448779653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24891365524216668299186435 37337048286325002448779653)
          ·
            refine ⟨7000696553685937959146185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37337048286325002448779653 7000696553685937959146185)
            ·
              refine ⟨5250522415264453469359639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7000696553685937959146185 5250522415264453469359639)
              ·
                refine ⟨7875783622896680204039459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5250522415264453469359639 7875783622896680204039459)
                ·
                  refine ⟨11813675434345020306059189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7875783622896680204039459 11813675434345020306059189)
                  ·
                    refine ⟨1107532071969845653693049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11813675434345020306059189 1107532071969845653693049)
                    ·
                      rfl

theorem cell23_6470733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_6470733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470733 prefixEnd_6470733 := by exact prefixLift 6470733
  have htrace : WordTrace (prefixWord ++ tailWord_6470733) baseStart_6470733 baseEnd_6470733 := by
    simpa [prefixWord, tailWord_6470733, baseEnd_6470733] using wordTrace_append hprefix tailTrace_6470733
  have hstable : (prefixWord ++ tailWord_6470733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470733).length < 2 ^ (prefixWord ++ tailWord_6470733).sum := by decide
  have hdescent : baseEnd_6470733 < baseStart_6470733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470753 : List Nat := [1, 2, 3, 1, 1, 2, 4, 4, 1, 2, 2]
def baseStart_6470753 : Nat := 118140960795 + 6470753 * 2 ^ 59
def prefixEnd_6470753 : Nat := 4983230072969 + 3 ^ 40 * 6470753 * 2
def baseEnd_6470753 : Nat := 3322606485522626882829055

theorem tailTrace_6470753 : CollatzResearch.WordTrace tailWord_6470753 prefixEnd_6470753 3322606485522626882829055 := by
  unfold tailWord_6470753
  simp only [CollatzResearch.WordTrace]
  refine ⟨236007750726574472474680913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157338500484382981649787275 236007750726574472474680913)
  ·
    refine ⟨177005813044930854356010685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236007750726574472474680913 177005813044930854356010685)
    ·
      refine ⟨66377179891849070383504007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177005813044930854356010685 66377179891849070383504007)
      ·
        refine ⟨99565769837773605575256011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66377179891849070383504007 99565769837773605575256011)
        ·
          refine ⟨149348654756660408362884017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99565769837773605575256011 149348654756660408362884017)
          ·
            refine ⟨112011491067495306272163013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149348654756660408362884017 112011491067495306272163013)
            ·
              refine ⟨21002154575155369926030565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112011491067495306272163013 21002154575155369926030565)
              ·
                refine ⟨3937903982841631861130731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21002154575155369926030565 3937903982841631861130731)
                ·
                  refine ⟨5906855974262447791696097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3937903982841631861130731 5906855974262447791696097)
                  ·
                    refine ⟨4430141980696835843772073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5906855974262447791696097 4430141980696835843772073)
                    ·
                      refine ⟨3322606485522626882829055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4430141980696835843772073 3322606485522626882829055)
                      ·
                        rfl

theorem cell23_6470753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_6470753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470753 prefixEnd_6470753 := by exact prefixLift 6470753
  have htrace : WordTrace (prefixWord ++ tailWord_6470753) baseStart_6470753 baseEnd_6470753 := by
    simpa [prefixWord, tailWord_6470753, baseEnd_6470753] using wordTrace_append hprefix tailTrace_6470753
  have hstable : (prefixWord ++ tailWord_6470753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470753).length < 2 ^ (prefixWord ++ tailWord_6470753).sum := by decide
  have hdescent : baseEnd_6470753 < baseStart_6470753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470766 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_6470766 : Nat := 118140960795 + 6470766 * 2 ^ 59
def prefixEnd_6470766 : Nat := 4983230072969 + 3 ^ 40 * 6470766 * 2
def baseEnd_6470766 : Nat := 3322613160771135331966495

theorem tailTrace_6470766 : CollatzResearch.WordTrace tailWord_6470766 prefixEnd_6470766 3322613160771135331966495 := by
  unfold tailWord_6470766
  simp only [CollatzResearch.WordTrace]
  refine ⟨29501028109440921961863019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157338816583684917129936101 29501028109440921961863019)
  ·
    refine ⟨44251542164161382942794529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29501028109440921961863019 44251542164161382942794529)
    ·
      refine ⟨33188656623121037207095897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44251542164161382942794529 33188656623121037207095897)
      ·
        refine ⟨24891492467340777905321923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33188656623121037207095897 24891492467340777905321923)
        ·
          refine ⟨37337238701011166857982885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24891492467340777905321923 37337238701011166857982885)
          ·
            refine ⟨7000732256439593785871791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37337238701011166857982885 7000732256439593785871791)
            ·
              refine ⟨10501098384659390678807687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7000732256439593785871791 10501098384659390678807687)
              ·
                refine ⟨15751647576989086018211531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10501098384659390678807687 15751647576989086018211531)
                ·
                  refine ⟨23627471365483629027317297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15751647576989086018211531 23627471365483629027317297)
                  ·
                    refine ⟨17720603524112721770487973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23627471365483629027317297 17720603524112721770487973)
                    ·
                      refine ⟨3322613160771135331966495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17720603524112721770487973 3322613160771135331966495)
                      ·
                        rfl

theorem cell23_6470766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_6470766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470766 prefixEnd_6470766 := by exact prefixLift 6470766
  have htrace : WordTrace (prefixWord ++ tailWord_6470766) baseStart_6470766 baseEnd_6470766 := by
    simpa [prefixWord, tailWord_6470766, baseEnd_6470766] using wordTrace_append hprefix tailTrace_6470766
  have hstable : (prefixWord ++ tailWord_6470766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470766).length < 2 ^ (prefixWord ++ tailWord_6470766).sum := by decide
  have hdescent : baseEnd_6470766 < baseStart_6470766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470779 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 3, 3, 2]
def baseStart_6470779 : Nat := 118140960795 + 6470779 * 2 ^ 59
def prefixEnd_6470779 : Nat := 4983230072969 + 3 ^ 40 * 6470779 * 2
def baseEnd_6470779 : Nat := 3322619836019643781103935

theorem tailTrace_6470779 : CollatzResearch.WordTrace tailWord_6470779 prefixEnd_6470779 3322619836019643781103935 := by
  unfold tailWord_6470779
  simp only [CollatzResearch.WordTrace]
  refine ⟨236008699024480278915127391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157339132682986852610084927 236008699024480278915127391)
  ·
    refine ⟨354013048536720418372691087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236008699024480278915127391 354013048536720418372691087)
    ·
      refine ⟨531019572805080627559036631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354013048536720418372691087 531019572805080627559036631)
      ·
        refine ⟨796529359207620941338554947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531019572805080627559036631 796529359207620941338554947)
        ·
          refine ⟨1194794038811431412007832421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796529359207620941338554947 1194794038811431412007832421)
          ·
            refine ⟨224023882277143389751468579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1194794038811431412007832421 224023882277143389751468579)
            ·
              refine ⟨336035823415715084627202869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224023882277143389751468579 336035823415715084627202869)
              ·
                refine ⟨31503358445223289183800269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 336035823415715084627202869 31503358445223289183800269)
                ·
                  refine ⟨11813759416958733443925101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31503358445223289183800269 11813759416958733443925101)
                  ·
                    refine ⟨4430159781359525041471913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11813759416958733443925101 4430159781359525041471913)
                    ·
                      refine ⟨3322619836019643781103935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4430159781359525041471913 3322619836019643781103935)
                      ·
                        rfl

theorem cell23_6470779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 3, 2].length) (baseStart_6470779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470779 prefixEnd_6470779 := by exact prefixLift 6470779
  have htrace : WordTrace (prefixWord ++ tailWord_6470779) baseStart_6470779 baseEnd_6470779 := by
    simpa [prefixWord, tailWord_6470779, baseEnd_6470779] using wordTrace_append hprefix tailTrace_6470779
  have hstable : (prefixWord ++ tailWord_6470779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470779).length < 2 ^ (prefixWord ++ tailWord_6470779).sum := by decide
  have hdescent : baseEnd_6470779 < baseStart_6470779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470820 : List Nat := [2, 3, 1, 2, 3, 3, 2, 1, 2, 1, 3]
def baseStart_6470820 : Nat := 118140960795 + 6470820 * 2 ^ 59
def prefixEnd_6470820 : Nat := 4983230072969 + 3 ^ 40 * 6470820 * 2
def baseEnd_6470820 : Nat := 3322640888726478120691247

theorem tailTrace_6470820 : CollatzResearch.WordTrace tailWord_6470820 prefixEnd_6470820 3322640888726478120691247 := by
  unfold tailWord_6470820
  simp only [CollatzResearch.WordTrace]
  refine ⟨118005097208665871458684957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157340129611554495278246609 118005097208665871458684957)
  ·
    refine ⟨44251911453249701797006859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118005097208665871458684957 44251911453249701797006859)
    ·
      refine ⟨66377867179874552695510289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44251911453249701797006859 66377867179874552695510289)
      ·
        refine ⟨49783400384905914521632717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66377867179874552695510289 49783400384905914521632717)
        ·
          refine ⟨18668775144339717945612269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49783400384905914521632717 18668775144339717945612269)
          ·
            refine ⟨7000790679127394229604601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18668775144339717945612269 7000790679127394229604601)
            ·
              refine ⟨5250593009345545672203451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7000790679127394229604601 5250593009345545672203451)
              ·
                refine ⟨7875889514018318508305177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5250593009345545672203451 7875889514018318508305177)
                ·
                  refine ⟨5906917135513738881228883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7875889514018318508305177 5906917135513738881228883)
                  ·
                    refine ⟨8860375703270608321843325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5906917135513738881228883 8860375703270608321843325)
                    ·
                      refine ⟨3322640888726478120691247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8860375703270608321843325 3322640888726478120691247)
                      ·
                        rfl

theorem cell23_6470820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_6470820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470820 prefixEnd_6470820 := by exact prefixLift 6470820
  have htrace : WordTrace (prefixWord ++ tailWord_6470820) baseStart_6470820 baseEnd_6470820 := by
    simpa [prefixWord, tailWord_6470820, baseEnd_6470820] using wordTrace_append hprefix tailTrace_6470820
  have hstable : (prefixWord ++ tailWord_6470820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470820).length < 2 ^ (prefixWord ++ tailWord_6470820).sum := by decide
  have hdescent : baseEnd_6470820 < baseStart_6470820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470854 : List Nat := [6, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_6470854 : Nat := 118140960795 + 6470854 * 2 ^ 59
def prefixEnd_6470854 : Nat := 4983230072969 + 3 ^ 40 * 6470854 * 2
def baseEnd_6470854 : Nat := 3322658347068730987666091

theorem tailTrace_6470854 : CollatzResearch.WordTrace tailWord_6470854 prefixEnd_6470854 3322658347068730987666091 := by
  unfold tailWord_6470854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7375357328100267710128363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157340956332805711149405077 7375357328100267710128363)
  ·
    refine ⟨11063035992150401565192545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7375357328100267710128363 11063035992150401565192545)
    ·
      refine ⟨8297276994112801173894409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11063035992150401565192545 8297276994112801173894409)
      ·
        refine ⟨6222957745584600880420807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8297276994112801173894409 6222957745584600880420807)
        ·
          refine ⟨9334436618376901320631211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6222957745584600880420807 9334436618376901320631211)
          ·
            refine ⟨14001654927565351980946817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9334436618376901320631211 14001654927565351980946817)
            ·
              refine ⟨10501241195674013985710113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14001654927565351980946817 10501241195674013985710113)
              ·
                refine ⟨7875930896755510489282585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10501241195674013985710113 7875930896755510489282585)
                ·
                  refine ⟨5906948172566632866961939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7875930896755510489282585 5906948172566632866961939)
                  ·
                    refine ⟨8860422258849949300442909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5906948172566632866961939 8860422258849949300442909)
                    ·
                      refine ⟨3322658347068730987666091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8860422258849949300442909 3322658347068730987666091)
                      ·
                        rfl

theorem cell23_6470854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_6470854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470854 prefixEnd_6470854 := by exact prefixLift 6470854
  have htrace : WordTrace (prefixWord ++ tailWord_6470854) baseStart_6470854 baseEnd_6470854 := by
    simpa [prefixWord, tailWord_6470854, baseEnd_6470854] using wordTrace_append hprefix tailTrace_6470854
  have hstable : (prefixWord ++ tailWord_6470854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470854).length < 2 ^ (prefixWord ++ tailWord_6470854).sum := by decide
  have hdescent : baseEnd_6470854 < baseStart_6470854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470866 : List Nat := [3, 2, 2, 2, 1, 1, 3, 4, 5]
def baseStart_6470866 : Nat := 118140960795 + 6470866 * 2 ^ 59
def prefixEnd_6470866 : Nat := 4983230072969 + 3 ^ 40 * 6470866 * 2
def baseEnd_6470866 : Nat := 369184945426287215635115

theorem tailTrace_6470866 : CollatzResearch.WordTrace tailWord_6470866 prefixEnd_6470866 369184945426287215635115 := by
  unfold tailWord_6470866
  simp only [CollatzResearch.WordTrace]
  refine ⟨59002968043791273193386113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157341248116776728515696301 59002968043791273193386113)
  ·
    refine ⟨44252226032843454895039585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59002968043791273193386113 44252226032843454895039585)
    ·
      refine ⟨33189169524632591171279689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44252226032843454895039585 33189169524632591171279689)
      ·
        refine ⟨24891877143474443378459767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33189169524632591171279689 24891877143474443378459767)
        ·
          refine ⟨37337815715211665067689651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24891877143474443378459767 37337815715211665067689651)
          ·
            refine ⟨56006723572817497601534477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37337815715211665067689651 56006723572817497601534477)
            ·
              refine ⟨21002521339806561600575429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56006723572817497601534477 21002521339806561600575429)
              ·
                refine ⟨3937972751213730300107893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21002521339806561600575429 3937972751213730300107893)
                ·
                  refine ⟨369184945426287215635115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3937972751213730300107893 369184945426287215635115)
                  ·
                    rfl

theorem cell23_6470866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_6470866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470866 prefixEnd_6470866 := by exact prefixLift 6470866
  have htrace : WordTrace (prefixWord ++ tailWord_6470866) baseStart_6470866 baseEnd_6470866 := by
    simpa [prefixWord, tailWord_6470866, baseEnd_6470866] using wordTrace_append hprefix tailTrace_6470866
  have hstable : (prefixWord ++ tailWord_6470866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470866).length < 2 ^ (prefixWord ++ tailWord_6470866).sum := by decide
  have hdescent : baseEnd_6470866 < baseStart_6470866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470899 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 4]
def baseStart_6470899 : Nat := 118140960795 + 6470899 * 2 ^ 59
def prefixEnd_6470899 : Nat := 4983230072969 + 3 ^ 40 * 6470899 * 2
def baseEnd_6470899 : Nat := 3322681453698183311603383

theorem tailTrace_6470899 : CollatzResearch.WordTrace tailWord_6470899 prefixEnd_6470899 3322681453698183311603383 := by
  unfold tailWord_6470899
  simp only [CollatzResearch.WordTrace]
  refine ⟨236013075784045539409495751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157342050522697026272997167 236013075784045539409495751)
  ·
    refine ⟨354019613676068309114243627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236013075784045539409495751 354019613676068309114243627)
    ·
      refine ⟨531029420514102463671365441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354019613676068309114243627 531029420514102463671365441)
      ·
        refine ⟨398272065385576847753524081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531029420514102463671365441 398272065385576847753524081)
        ·
          refine ⟨298704049039182635815143061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398272065385576847753524081 298704049039182635815143061)
          ·
            refine ⟨14001752298711686053834831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 298704049039182635815143061 14001752298711686053834831)
            ·
              refine ⟨21002628448067529080752247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14001752298711686053834831 21002628448067529080752247)
              ·
                refine ⟨31503942672101293621128371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21002628448067529080752247 31503942672101293621128371)
                ·
                  refine ⟨47255914008151940431692557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31503942672101293621128371 47255914008151940431692557)
                  ·
                    refine ⟨17720967753056977661884709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47255914008151940431692557 17720967753056977661884709)
                    ·
                      refine ⟨3322681453698183311603383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17720967753056977661884709 3322681453698183311603383)
                      ·
                        rfl

theorem cell23_6470899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_6470899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470899 prefixEnd_6470899 := by exact prefixLift 6470899
  have htrace : WordTrace (prefixWord ++ tailWord_6470899) baseStart_6470899 baseEnd_6470899 := by
    simpa [prefixWord, tailWord_6470899, baseEnd_6470899] using wordTrace_append hprefix tailTrace_6470899
  have hstable : (prefixWord ++ tailWord_6470899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470899).length < 2 ^ (prefixWord ++ tailWord_6470899).sum := by decide
  have hdescent : baseEnd_6470899 < baseStart_6470899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470926 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_6470926 : Nat := 118140960795 + 6470926 * 2 ^ 59
def prefixEnd_6470926 : Nat := 4983230072969 + 3 ^ 40 * 6470926 * 2
def baseEnd_6470926 : Nat := 1107565105891951568655253

theorem tailTrace_6470926 : CollatzResearch.WordTrace tailWord_6470926 prefixEnd_6470926 1107565105891951568655253 := by
  unfold tailWord_6470926
  simp only [CollatzResearch.WordTrace]
  refine ⟨29501757569368465377591079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157342707036631815347152421 29501757569368465377591079)
  ·
    refine ⟨44252636354052698066386619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29501757569368465377591079 44252636354052698066386619)
    ·
      refine ⟨66378954531079047099579929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44252636354052698066386619 66378954531079047099579929)
      ·
        refine ⟨49784215898309285324684947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66378954531079047099579929 49784215898309285324684947)
        ·
          refine ⟨74676323847463927987027421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49784215898309285324684947 74676323847463927987027421)
          ·
            refine ⟨28003621442798972995135283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74676323847463927987027421 28003621442798972995135283)
            ·
              refine ⟨42005432164198459492702925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28003621442798972995135283 42005432164198459492702925)
              ·
                refine ⟨15752037061574422309763597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42005432164198459492702925 15752037061574422309763597)
                ·
                  refine ⟨5907013898090408366161349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15752037061574422309763597 5907013898090408366161349)
                  ·
                    refine ⟨1107565105891951568655253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5907013898090408366161349 1107565105891951568655253)
                    ·
                      rfl

theorem cell23_6470926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_6470926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470926 prefixEnd_6470926 := by exact prefixLift 6470926
  have htrace : WordTrace (prefixWord ++ tailWord_6470926) baseStart_6470926 baseEnd_6470926 := by
    simpa [prefixWord, tailWord_6470926, baseEnd_6470926] using wordTrace_append hprefix tailTrace_6470926
  have hstable : (prefixWord ++ tailWord_6470926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470926).length < 2 ^ (prefixWord ++ tailWord_6470926).sum := by decide
  have hdescent : baseEnd_6470926 < baseStart_6470926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470977 : List Nat := [1, 2, 5, 2, 1, 2, 3, 2, 1, 4]
def baseStart_6470977 : Nat := 118140960795 + 6470977 * 2 ^ 59
def prefixEnd_6470977 : Nat := 4983230072969 + 3 ^ 40 * 6470977 * 2
def baseEnd_6470977 : Nat := 1107573835063078002142675

theorem tailTrace_6470977 : CollatzResearch.WordTrace tailWord_6470977 prefixEnd_6470977 1107573835063078002142675 := by
  unfold tailWord_6470977
  simp only [CollatzResearch.WordTrace]
  refine ⟨236015920677762958730835185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157343947118508639153890123 236015920677762958730835185)
  ·
    refine ⟨177011940508322219048126389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236015920677762958730835185 177011940508322219048126389)
    ·
      refine ⟨16594869422655208035761849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177011940508322219048126389 16594869422655208035761849)
      ·
        refine ⟨12446152066991406026821387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16594869422655208035761849 12446152066991406026821387)
        ·
          refine ⟨18669228100487109040232081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12446152066991406026821387 18669228100487109040232081)
          ·
            refine ⟨14001921075365331780174061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18669228100487109040232081 14001921075365331780174061)
            ·
              refine ⟨5250720403261999417565273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14001921075365331780174061 5250720403261999417565273)
              ·
                refine ⟨3938040302446499563173955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5250720403261999417565273 3938040302446499563173955)
                ·
                  refine ⟨5907060453669749344760933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3938040302446499563173955 5907060453669749344760933)
                  ·
                    refine ⟨1107573835063078002142675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5907060453669749344760933 1107573835063078002142675)
                    ·
                      rfl

theorem cell23_6470977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_6470977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470977 prefixEnd_6470977 := by exact prefixLift 6470977
  have htrace : WordTrace (prefixWord ++ tailWord_6470977) baseStart_6470977 baseEnd_6470977 := by
    simpa [prefixWord, tailWord_6470977, baseEnd_6470977] using wordTrace_append hprefix tailTrace_6470977
  have hstable : (prefixWord ++ tailWord_6470977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470977).length < 2 ^ (prefixWord ++ tailWord_6470977).sum := by decide
  have hdescent : baseEnd_6470977 < baseStart_6470977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6470983 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 3, 1, 3]
def baseStart_6470983 : Nat := 118140960795 + 6470983 * 2 ^ 59
def prefixEnd_6470983 : Nat := 4983230072969 + 3 ^ 40 * 6470983 * 2
def baseEnd_6470983 : Nat := 3322724586073160982952997

theorem tailTrace_6470983 : CollatzResearch.WordTrace tailWord_6470983 prefixEnd_6470983 3322724586073160982952997 := by
  unfold tailWord_6470983
  simp only [CollatzResearch.WordTrace]
  refine ⟨236016139515741221755553603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157344093010494147837035735 236016139515741221755553603)
  ·
    refine ⟨354024209273611832633330405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236016139515741221755553603 354024209273611832633330405)
    ·
      refine ⟨66379539238802218618749451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 354024209273611832633330405 66379539238802218618749451)
      ·
        refine ⟨99569308858203327928124177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66379539238802218618749451 99569308858203327928124177)
        ·
          refine ⟨74676981643652495946093133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99569308858203327928124177 74676981643652495946093133)
          ·
            refine ⟨28003868116369685979784925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74676981643652495946093133 28003868116369685979784925)
            ·
              refine ⟨10501450543638632242419347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28003868116369685979784925 10501450543638632242419347)
              ·
                refine ⟨15752175815457948363629021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10501450543638632242419347 15752175815457948363629021)
                ·
                  refine ⟨5907065930796730636360883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15752175815457948363629021 5907065930796730636360883)
                  ·
                    refine ⟨8860598896195095954541325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5907065930796730636360883 8860598896195095954541325)
                    ·
                      refine ⟨3322724586073160982952997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8860598896195095954541325 3322724586073160982952997)
                      ·
                        rfl

theorem cell23_6470983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_6470983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6470983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6470983 prefixEnd_6470983 := by exact prefixLift 6470983
  have htrace : WordTrace (prefixWord ++ tailWord_6470983) baseStart_6470983 baseEnd_6470983 := by
    simpa [prefixWord, tailWord_6470983, baseEnd_6470983] using wordTrace_append hprefix tailTrace_6470983
  have hstable : (prefixWord ++ tailWord_6470983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6470983).length < 2 ^ (prefixWord ++ tailWord_6470983).sum := by decide
  have hdescent : baseEnd_6470983 < baseStart_6470983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6470983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471009 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_6471009 : Nat := 118140960795 + 6471009 * 2 ^ 59
def prefixEnd_6471009 : Nat := 4983230072969 + 3 ^ 40 * 6471009 * 2
def baseEnd_6471009 : Nat := 3322737936570177881227877

theorem tailTrace_6471009 : CollatzResearch.WordTrace tailWord_6471009 prefixEnd_6471009 3322737936570177881227877 := by
  unfold tailWord_6471009
  simp only [CollatzResearch.WordTrace]
  refine ⟨236017087813647028196000081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157344725209098018797333387 236017087813647028196000081)
  ·
    refine ⟨177012815860235271147000061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236017087813647028196000081 177012815860235271147000061)
    ·
      refine ⟨66379805947588226680125023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177012815860235271147000061 66379805947588226680125023)
      ·
        refine ⟨99569708921382340020187535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66379805947588226680125023 99569708921382340020187535)
        ·
          refine ⟨149354563382073510030281303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99569708921382340020187535 149354563382073510030281303)
          ·
            refine ⟨224031845073110265045421955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149354563382073510030281303 224031845073110265045421955)
            ·
              refine ⟨336047767609665397568132933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224031845073110265045421955 336047767609665397568132933)
              ·
                refine ⟨63008956426812262044024925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336047767609665397568132933 63008956426812262044024925)
                ·
                  refine ⟨23628358660054598266509347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63008956426812262044024925 23628358660054598266509347)
                  ·
                    refine ⟨35442537990081897399764021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23628358660054598266509347 35442537990081897399764021)
                    ·
                      refine ⟨3322737936570177881227877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35442537990081897399764021 3322737936570177881227877)
                      ·
                        rfl

theorem cell23_6471009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_6471009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471009 prefixEnd_6471009 := by exact prefixLift 6471009
  have htrace : WordTrace (prefixWord ++ tailWord_6471009) baseStart_6471009 baseEnd_6471009 := by
    simpa [prefixWord, tailWord_6471009, baseEnd_6471009] using wordTrace_append hprefix tailTrace_6471009
  have hstable : (prefixWord ++ tailWord_6471009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471009).length < 2 ^ (prefixWord ++ tailWord_6471009).sum := by decide
  have hdescent : baseEnd_6471009 < baseStart_6471009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471010 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_6471010 : Nat := 118140960795 + 6471010 * 2 ^ 59
def prefixEnd_6471010 : Nat := 4983230072969 + 3 ^ 40 * 6471010 * 2
def baseEnd_6471010 : Nat := 3322738450050832377315373

theorem tailTrace_6471010 : CollatzResearch.WordTrace tailWord_6471010 prefixEnd_6471010 3322738450050832377315373 := by
  unfold tailWord_6471010
  simp only [CollatzResearch.WordTrace]
  refine ⟨59004281071660851341696621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157344749524428936911190989 59004281071660851341696621)
  ·
    refine ⟨22126605401872819253136233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59004281071660851341696621 22126605401872819253136233)
    ·
      refine ⟨16594954051404614439852175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22126605401872819253136233 16594954051404614439852175)
      ·
        refine ⟨24892431077106921659778263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16594954051404614439852175 24892431077106921659778263)
        ·
          refine ⟨37338646615660382489667395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24892431077106921659778263 37338646615660382489667395)
          ·
            refine ⟨56007969923490573734501093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37338646615660382489667395 56007969923490573734501093)
            ·
              refine ⟨10501494360654482575218955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56007969923490573734501093 10501494360654482575218955)
              ·
                refine ⟨15752241540981723862828433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10501494360654482575218955 15752241540981723862828433)
                ·
                  refine ⟨11814181155736292897121325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15752241540981723862828433 11814181155736292897121325)
                  ·
                    refine ⟨4430317933401109836420497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11814181155736292897121325 4430317933401109836420497)
                    ·
                      refine ⟨3322738450050832377315373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4430317933401109836420497 3322738450050832377315373)
                      ·
                        rfl

theorem cell23_6471010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_6471010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471010 prefixEnd_6471010 := by exact prefixLift 6471010
  have htrace : WordTrace (prefixWord ++ tailWord_6471010) baseStart_6471010 baseEnd_6471010 := by
    simpa [prefixWord, tailWord_6471010, baseEnd_6471010] using wordTrace_append hprefix tailTrace_6471010
  have hstable : (prefixWord ++ tailWord_6471010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471010).length < 2 ^ (prefixWord ++ tailWord_6471010).sum := by decide
  have hdescent : baseEnd_6471010 < baseStart_6471010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471023 : List Nat := [1, 1, 2, 1, 3, 1, 7, 1, 1, 1, 4]
def baseStart_6471023 : Nat := 118140960795 + 6471023 * 2 ^ 59
def prefixEnd_6471023 : Nat := 4983230072969 + 3 ^ 40 * 6471023 * 2
def baseEnd_6471023 : Nat := 3322745125299340826452813

theorem tailTrace_6471023 : CollatzResearch.WordTrace tailWord_6471023 prefixEnd_6471023 3322745125299340826452813 := by
  unfold tailWord_6471023
  simp only [CollatzResearch.WordTrace]
  refine ⟨236017598435596308587009723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157345065623730872391339815 236017598435596308587009723)
  ·
    refine ⟨354026397653394462880514585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236017598435596308587009723 354026397653394462880514585)
    ·
      refine ⟨265519798240045847160385939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 354026397653394462880514585 265519798240045847160385939)
      ·
        refine ⟨398279697360068770740578909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265519798240045847160385939 398279697360068770740578909)
        ·
          refine ⟨149354886510025789027717091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398279697360068770740578909 149354886510025789027717091)
          ·
            refine ⟨224032329765038683541575637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149354886510025789027717091 224032329765038683541575637)
            ·
              refine ⟨5250757728868094145505679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 224032329765038683541575637 5250757728868094145505679)
              ·
                refine ⟨7876136593302141218258519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5250757728868094145505679 7876136593302141218258519)
                ·
                  refine ⟨11814204889953211827387779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7876136593302141218258519 11814204889953211827387779)
                  ·
                    refine ⟨17721307334929817741081669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11814204889953211827387779 17721307334929817741081669)
                    ·
                      refine ⟨3322745125299340826452813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17721307334929817741081669 3322745125299340826452813)
                      ·
                        rfl

theorem cell23_6471023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 1, 1, 4].length) (baseStart_6471023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471023 prefixEnd_6471023 := by exact prefixLift 6471023
  have htrace : WordTrace (prefixWord ++ tailWord_6471023) baseStart_6471023 baseEnd_6471023 := by
    simpa [prefixWord, tailWord_6471023, baseEnd_6471023] using wordTrace_append hprefix tailTrace_6471023
  have hstable : (prefixWord ++ tailWord_6471023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471023).length < 2 ^ (prefixWord ++ tailWord_6471023).sum := by decide
  have hdescent : baseEnd_6471023 < baseStart_6471023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471029 : List Nat := [1, 3, 4, 1, 14]
def baseStart_6471029 : Nat := 118140960795 + 6471029 * 2 ^ 59
def prefixEnd_6471029 : Nat := 4983230072969 + 3 ^ 40 * 6471029 * 2
def baseEnd_6471029 : Nat := 4557953643598446917665

theorem tailTrace_6471029 : CollatzResearch.WordTrace tailWord_6471029 prefixEnd_6471029 4557953643598446917665 := by
  unfold tailWord_6471029
  simp only [CollatzResearch.WordTrace]
  refine ⟨236017817273574571611728141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157345211515716381074485427 236017817273574571611728141)
  ·
    refine ⟨88506681477590464354398053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236017817273574571611728141 88506681477590464354398053)
    ·
      refine ⟨16595002777048212066449635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88506681477590464354398053 16595002777048212066449635)
      ·
        refine ⟨24892504165572318099674453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16595002777048212066449635 24892504165572318099674453)
        ·
          refine ⟨4557953643598446917665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 24892504165572318099674453 4557953643598446917665)
          ·
            rfl

theorem cell23_6471029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 14].length) (baseStart_6471029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471029 prefixEnd_6471029 := by exact prefixLift 6471029
  have htrace : WordTrace (prefixWord ++ tailWord_6471029) baseStart_6471029 baseEnd_6471029 := by
    simpa [prefixWord, tailWord_6471029, baseEnd_6471029] using wordTrace_append hprefix tailTrace_6471029
  have hstable : (prefixWord ++ tailWord_6471029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471029).length < 2 ^ (prefixWord ++ tailWord_6471029).sum := by decide
  have hdescent : baseEnd_6471029 < baseStart_6471029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471074 : List Nat := [3, 3, 1, 2, 1, 3, 2, 3, 1, 2, 2]
def baseStart_6471074 : Nat := 118140960795 + 6471074 * 2 ^ 59
def prefixEnd_6471074 : Nat := 4983230072969 + 3 ^ 40 * 6471074 * 2
def baseEnd_6471074 : Nat := 3322771312812720126915079

theorem tailTrace_6471074 : CollatzResearch.WordTrace tailWord_6471074 prefixEnd_6471074 3322771312812720126915079 := by
  unfold tailWord_6471074
  simp only [CollatzResearch.WordTrace]
  refine ⟨59004864639602886074279069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157346305705607696198077517 59004864639602886074279069)
  ·
    refine ⟨22126824239851082277854651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59004864639602886074279069 22126824239851082277854651)
    ·
      refine ⟨33190236359776623416781977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22126824239851082277854651 33190236359776623416781977)
      ·
        refine ⟨24892677269832467562586483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33190236359776623416781977 24892677269832467562586483)
        ·
          refine ⟨37339015904748701343879725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24892677269832467562586483 37339015904748701343879725)
          ·
            refine ⟨14002130964280763003954897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37339015904748701343879725 14002130964280763003954897)
            ·
              refine ⟨10501598223210572252966173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14002130964280763003954897 10501598223210572252966173)
              ·
                refine ⟨3938099333703964594862315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10501598223210572252966173 3938099333703964594862315)
                ·
                  refine ⟨5907149000555946892293473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3938099333703964594862315 5907149000555946892293473)
                  ·
                    refine ⟨4430361750416960169220105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5907149000555946892293473 4430361750416960169220105)
                    ·
                      refine ⟨3322771312812720126915079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4430361750416960169220105 3322771312812720126915079)
                      ·
                        rfl

theorem cell23_6471074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_6471074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471074 prefixEnd_6471074 := by exact prefixLift 6471074
  have htrace : WordTrace (prefixWord ++ tailWord_6471074) baseStart_6471074 baseEnd_6471074 := by
    simpa [prefixWord, tailWord_6471074, baseEnd_6471074] using wordTrace_append hprefix tailTrace_6471074
  have hstable : (prefixWord ++ tailWord_6471074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471074).length < 2 ^ (prefixWord ++ tailWord_6471074).sum := by decide
  have hdescent : baseEnd_6471074 < baseStart_6471074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471109 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_6471109 : Nat := 118140960795 + 6471109 * 2 ^ 59
def prefixEnd_6471109 : Nat := 4983230072969 + 3 ^ 40 * 6471109 * 2
def baseEnd_6471109 : Nat := 3322789284635627489977417

theorem tailTrace_6471109 : CollatzResearch.WordTrace tailWord_6471109 prefixEnd_6471109 3322789284635627489977417 := by
  unfold tailWord_6471109
  simp only [CollatzResearch.WordTrace]
  refine ⟨236020735113284745274640381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157347156742189830183093587 236020735113284745274640381)
  ·
    refine ⟨88507775667481779477990143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236020735113284745274640381 88507775667481779477990143)
    ·
      refine ⟨132761663501222669216985215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88507775667481779477990143 132761663501222669216985215)
      ·
        refine ⟨199142495251834003825477823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132761663501222669216985215 199142495251834003825477823)
        ·
          refine ⟨298713742877751005738216735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199142495251834003825477823 298713742877751005738216735)
          ·
            refine ⟨448070614316626508607325103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298713742877751005738216735 448070614316626508607325103)
            ·
              refine ⟨672105921474939762910987655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448070614316626508607325103 672105921474939762910987655)
              ·
                refine ⟨1008158882212409644366481483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672105921474939762910987655 1008158882212409644366481483)
                ·
                  refine ⟨1512238323318614466549722225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008158882212409644366481483 1512238323318614466549722225)
                  ·
                    refine ⟨1134178742488960849912291669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1512238323318614466549722225 1134178742488960849912291669)
                    ·
                      refine ⟨3322789284635627489977417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1134178742488960849912291669 3322789284635627489977417)
                      ·
                        rfl

theorem cell23_6471109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_6471109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471109 prefixEnd_6471109 := by exact prefixLift 6471109
  have htrace : WordTrace (prefixWord ++ tailWord_6471109) baseStart_6471109 baseEnd_6471109 := by
    simpa [prefixWord, tailWord_6471109, baseEnd_6471109] using wordTrace_append hprefix tailTrace_6471109
  have hstable : (prefixWord ++ tailWord_6471109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471109).length < 2 ^ (prefixWord ++ tailWord_6471109).sum := by decide
  have hdescent : baseEnd_6471109 < baseStart_6471109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471130 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2]
def baseStart_6471130 : Nat := 118140960795 + 6471130 * 2 ^ 59
def prefixEnd_6471130 : Nat := 4983230072969 + 3 ^ 40 * 6471130 * 2
def baseEnd_6471130 : Nat := 3322800067729371907814821

theorem tailTrace_6471130 : CollatzResearch.WordTrace tailWord_6471130 prefixEnd_6471130 3322800067729371907814821 := by
  unfold tailWord_6471130
  simp only [CollatzResearch.WordTrace]
  refine ⟨59005375261552166465288711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157347667364139110574103229 59005375261552166465288711)
  ·
    refine ⟨88508062892328249697933067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59005375261552166465288711 88508062892328249697933067)
    ·
      refine ⟨132762094338492374546899601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88508062892328249697933067 132762094338492374546899601)
      ·
        refine ⟨99571570753869280910174701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132762094338492374546899601 99571570753869280910174701)
        ·
          refine ⟨37339339032700980341315513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99571570753869280910174701 37339339032700980341315513)
          ·
            refine ⟨28004504274525735255986635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37339339032700980341315513 28004504274525735255986635)
            ·
              refine ⟨42006756411788602883979953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28004504274525735255986635 42006756411788602883979953)
              ·
                refine ⟨31505067308841452162984965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42006756411788602883979953 31505067308841452162984965)
                ·
                  refine ⟨5907200120407772280559681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31505067308841452162984965 5907200120407772280559681)
                  ·
                    refine ⟨4430400090305829210419761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5907200120407772280559681 4430400090305829210419761)
                    ·
                      refine ⟨3322800067729371907814821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4430400090305829210419761 3322800067729371907814821)
                      ·
                        rfl

theorem cell23_6471130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_6471130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471130 prefixEnd_6471130 := by exact prefixLift 6471130
  have htrace : WordTrace (prefixWord ++ tailWord_6471130) baseStart_6471130 baseEnd_6471130 := by
    simpa [prefixWord, tailWord_6471130, baseEnd_6471130] using wordTrace_append hprefix tailTrace_6471130
  have hstable : (prefixWord ++ tailWord_6471130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471130).length < 2 ^ (prefixWord ++ tailWord_6471130).sum := by decide
  have hdescent : baseEnd_6471130 < baseStart_6471130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471133 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_6471133 : Nat := 118140960795 + 6471133 * 2 ^ 59
def prefixEnd_6471133 : Nat := 4983230072969 + 3 ^ 40 * 6471133 * 2
def baseEnd_6471133 : Nat := 3322801608171335396077307

theorem tailTrace_6471133 : CollatzResearch.WordTrace tailWord_6471133 prefixEnd_6471133 3322801608171335396077307 := by
  unfold tailWord_6471133
  simp only [CollatzResearch.WordTrace]
  refine ⟨236021610465197797373514053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157347740310131864915676035 236021610465197797373514053)
  ·
    refine ⟨44254051962224587007533885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236021610465197797373514053 44254051962224587007533885)
    ·
      refine ⟨16595269485834220127825207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44254051962224587007533885 16595269485834220127825207)
      ·
        refine ⟨24892904228751330191737811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16595269485834220127825207 24892904228751330191737811)
        ·
          refine ⟨37339356343126995287606717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24892904228751330191737811 37339356343126995287606717)
          ·
            refine ⟨14002258628672623232852519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37339356343126995287606717 14002258628672623232852519)
            ·
              refine ⟨21003387943008934849278779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14002258628672623232852519 21003387943008934849278779)
              ·
                refine ⟨31505081914513402273918169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21003387943008934849278779 31505081914513402273918169)
                ·
                  refine ⟨23628811435885051705438627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31505081914513402273918169 23628811435885051705438627)
                  ·
                    refine ⟨35443217153827577558157941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23628811435885051705438627 35443217153827577558157941)
                    ·
                      refine ⟨3322801608171335396077307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35443217153827577558157941 3322801608171335396077307)
                      ·
                        rfl

theorem cell23_6471133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_6471133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471133 prefixEnd_6471133 := by exact prefixLift 6471133
  have htrace : WordTrace (prefixWord ++ tailWord_6471133) baseStart_6471133 baseEnd_6471133 := by
    simpa [prefixWord, tailWord_6471133, baseEnd_6471133] using wordTrace_append hprefix tailTrace_6471133
  have hstable : (prefixWord ++ tailWord_6471133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471133).length < 2 ^ (prefixWord ++ tailWord_6471133).sum := by decide
  have hdescent : baseEnd_6471133 < baseStart_6471133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471153 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 7]
def baseStart_6471153 : Nat := 118140960795 + 6471153 * 2 ^ 59
def prefixEnd_6471153 : Nat := 4983230072969 + 3 ^ 40 * 6471153 * 2
def baseEnd_6471153 : Nat := 369201319753825035314135

theorem tailTrace_6471153 : CollatzResearch.WordTrace tailWord_6471153 prefixEnd_6471153 369201319753825035314135 := by
  unfold tailWord_6471153
  simp only [CollatzResearch.WordTrace]
  refine ⟨236022339925125340789242113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157348226616750227192828075 236022339925125340789242113)
  ·
    refine ⟨177016754943844005591931585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236022339925125340789242113 177016754943844005591931585)
    ·
      refine ⟨132762566207883004193948689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177016754943844005591931585 132762566207883004193948689)
      ·
        refine ⟨99571924655912253145461517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132762566207883004193948689 99571924655912253145461517)
        ·
          refine ⟨37339471745967094929548069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99571924655912253145461517 37339471745967094929548069)
          ·
            refine ⟨7001150952368830299290263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37339471745967094929548069 7001150952368830299290263)
            ·
              refine ⟨10501726428553245448935395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7001150952368830299290263 10501726428553245448935395)
              ·
                refine ⟨15752589642829868173403093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10501726428553245448935395 15752589642829868173403093)
                ·
                  refine ⟨369201319753825035314135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15752589642829868173403093 369201319753825035314135)
                  ·
                    rfl

theorem cell23_6471153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 7].length) (baseStart_6471153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471153 prefixEnd_6471153 := by exact prefixLift 6471153
  have htrace : WordTrace (prefixWord ++ tailWord_6471153) baseStart_6471153 baseEnd_6471153 := by
    simpa [prefixWord, tailWord_6471153, baseEnd_6471153] using wordTrace_append hprefix tailTrace_6471153
  have hstable : (prefixWord ++ tailWord_6471153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471153).length < 2 ^ (prefixWord ++ tailWord_6471153).sum := by decide
  have hdescent : baseEnd_6471153 < baseStart_6471153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6471216 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 4]
def baseStart_6471216 : Nat := 118140960795 + 6471216 * 2 ^ 59
def prefixEnd_6471216 : Nat := 4983230072969 + 3 ^ 40 * 6471216 * 2
def baseEnd_6471216 : Nat := 3322844227065658571339425

theorem tailTrace_6471216 : CollatzResearch.WordTrace tailWord_6471216 prefixEnd_6471216 3322844227065658571339425 := by
  unfold tailWord_6471216
  simp only [CollatzResearch.WordTrace]
  refine ⟨118012318861948551274392751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157349758482598068365857001 118012318861948551274392751)
  ·
    refine ⟨177018478292922826911589127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118012318861948551274392751 177018478292922826911589127)
    ·
      refine ⟨265527717439384240367383691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177018478292922826911589127 265527717439384240367383691)
      ·
        refine ⟨398291576159076360551075537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265527717439384240367383691 398291576159076360551075537)
        ·
          refine ⟨298718682119307270413306653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398291576159076360551075537 298718682119307270413306653)
          ·
            refine ⟨112019505794740226404989995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298718682119307270413306653 112019505794740226404989995)
            ·
              refine ⟨168029258692110339607484993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112019505794740226404989995 168029258692110339607484993)
              ·
                refine ⟨126021944019082754705613745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168029258692110339607484993 126021944019082754705613745)
                ·
                  refine ⟨94516458014312066029210309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126021944019082754705613745 94516458014312066029210309)
                  ·
                    refine ⟨17721835877683512380476933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94516458014312066029210309 17721835877683512380476933)
                    ·
                      refine ⟨3322844227065658571339425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17721835877683512380476933 3322844227065658571339425)
                      ·
                        rfl

theorem cell23_6471216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_6471216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6471216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6471216 prefixEnd_6471216 := by exact prefixLift 6471216
  have htrace : WordTrace (prefixWord ++ tailWord_6471216) baseStart_6471216 baseEnd_6471216 := by
    simpa [prefixWord, tailWord_6471216, baseEnd_6471216] using wordTrace_append hprefix tailTrace_6471216
  have hstable : (prefixWord ++ tailWord_6471216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6471216).length < 2 ^ (prefixWord ++ tailWord_6471216).sum := by decide
  have hdescent : baseEnd_6471216 < baseStart_6471216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6471216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
