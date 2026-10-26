import V185TrunkScan22Chunk123

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1109213 : List Nat := [1, 4, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1109213 : Nat := 118140960795 + 1109213 * 2 ^ 59
def prefixEnd_1109213 : Nat := 4983230072969 + 3 ^ 40 * 1109213 * 2
def baseEnd_1109213 : Nat := 379706278143782621824219

theorem tailTrace_1109213 : CollatzResearch.WordTrace tailWord_1109213 prefixEnd_1109213 379706278143782621824219 := by
  unfold tailWord_1109213
  simp only [CollatzResearch.WordTrace]
  refine ⟨40456321730518214343540293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26970881153678809562360195 40456321730518214343540293)
  ·
    refine ⟨7585560324472165189413805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40456321730518214343540293 7585560324472165189413805)
    ·
      refine ⟨2844585121677061946030177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7585560324472165189413805 2844585121677061946030177)
      ·
        refine ⟨2133438841257796459522633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2844585121677061946030177 2133438841257796459522633)
        ·
          refine ⟨1600079130943347344641975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2133438841257796459522633 1600079130943347344641975)
          ·
            refine ⟨2400118696415021016962963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600079130943347344641975 2400118696415021016962963)
            ·
              refine ⟨3600178044622531525444445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400118696415021016962963 3600178044622531525444445)
              ·
                refine ⟨1350066766733449322041667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3600178044622531525444445 1350066766733449322041667)
                ·
                  refine ⟨2025100150100173983062501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350066766733449322041667 2025100150100173983062501)
                  ·
                    refine ⟨379706278143782621824219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2025100150100173983062501 379706278143782621824219)
                    ·
                      rfl

theorem cell22_1109213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1109213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109213 prefixEnd_1109213 := by exact prefixLift 1109213
  have htrace : WordTrace (prefixWord ++ tailWord_1109213) baseStart_1109213 baseEnd_1109213 := by
    simpa [prefixWord, tailWord_1109213, baseEnd_1109213] using wordTrace_append hprefix tailTrace_1109213
  have hstable : (prefixWord ++ tailWord_1109213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109213).length < 2 ^ (prefixWord ++ tailWord_1109213).sum := by decide
  have hdescent : baseEnd_1109213 < baseStart_1109213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109224 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1109224 : Nat := 118140960795 + 1109224 * 2 ^ 59
def prefixEnd_1109224 : Nat := 4983230072969 + 3 ^ 40 * 1109224 * 2
def baseEnd_1109224 : Nat := 379710043668582259799185

theorem tailTrace_1109224 : CollatzResearch.WordTrace tailWord_1109224 prefixEnd_1109224 379710043668582259799185 := by
  unfold tailWord_1109224
  simp only [CollatzResearch.WordTrace]
  refine ⟨20228361466739181611095363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26971148622318908814793817 20228361466739181611095363)
  ·
    refine ⟨30342542200108772416643045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20228361466739181611095363 30342542200108772416643045)
    ·
      refine ⟨5689226662520394828120571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30342542200108772416643045 5689226662520394828120571)
      ·
        refine ⟨8533839993780592242180857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5689226662520394828120571 8533839993780592242180857)
        ·
          refine ⟨6400379995335444181635643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8533839993780592242180857 6400379995335444181635643)
          ·
            refine ⟨9600569993003166272453465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6400379995335444181635643 9600569993003166272453465)
            ·
              refine ⟨7200427494752374704340099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9600569993003166272453465 7200427494752374704340099)
              ·
                refine ⟨10800641242128562056510149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7200427494752374704340099 10800641242128562056510149)
                ·
                  refine ⟨2025120232899105385595653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10800641242128562056510149 2025120232899105385595653)
                  ·
                    refine ⟨379710043668582259799185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2025120232899105385595653 379710043668582259799185)
                    ·
                      rfl

theorem cell22_1109224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1109224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109224 prefixEnd_1109224 := by exact prefixLift 1109224
  have htrace : WordTrace (prefixWord ++ tailWord_1109224) baseStart_1109224 baseEnd_1109224 := by
    simpa [prefixWord, tailWord_1109224, baseEnd_1109224] using wordTrace_append hprefix tailTrace_1109224
  have hstable : (prefixWord ++ tailWord_1109224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109224).length < 2 ^ (prefixWord ++ tailWord_1109224).sum := by decide
  have hdescent : baseEnd_1109224 < baseStart_1109224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109226 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 4, 3]
def baseStart_1109226 : Nat := 118140960795 + 1109226 * 2 ^ 59
def prefixEnd_1109226 : Nat := 4983230072969 + 3 ^ 40 * 1109226 * 2
def baseEnd_1109226 : Nat := 379710728309454921249179

theorem tailTrace_1109226 : CollatzResearch.WordTrace tailWord_1109226 prefixEnd_1109226 379710728309454921249179 := by
  unfold tailWord_1109226
  simp only [CollatzResearch.WordTrace]
  refine ⟨10114198969867779390940883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26971197252980745042509021 10114198969867779390940883)
  ·
    refine ⟨15171298454801669086411325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10114198969867779390940883 15171298454801669086411325)
    ·
      refine ⟨5689236920550625907404247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15171298454801669086411325 5689236920550625907404247)
      ·
        refine ⟨8533855380825938861106371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5689236920550625907404247 8533855380825938861106371)
        ·
          refine ⟨12800783071238908291659557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8533855380825938861106371 12800783071238908291659557)
          ·
            refine ⟨2400146825857295304686167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12800783071238908291659557 2400146825857295304686167)
            ·
              refine ⟨3600220238785942957029251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400146825857295304686167 3600220238785942957029251)
              ·
                refine ⟨5400330358178914435543877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3600220238785942957029251 5400330358178914435543877)
                ·
                  refine ⟨1012561942158546456664477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5400330358178914435543877 1012561942158546456664477)
                  ·
                    refine ⟨379710728309454921249179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1012561942158546456664477 379710728309454921249179)
                    ·
                      rfl

theorem cell22_1109226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_1109226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109226 prefixEnd_1109226 := by exact prefixLift 1109226
  have htrace : WordTrace (prefixWord ++ tailWord_1109226) baseStart_1109226 baseEnd_1109226 := by
    simpa [prefixWord, tailWord_1109226, baseEnd_1109226] using wordTrace_append hprefix tailTrace_1109226
  have hstable : (prefixWord ++ tailWord_1109226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109226).length < 2 ^ (prefixWord ++ tailWord_1109226).sum := by decide
  have hdescent : baseEnd_1109226 < baseStart_1109226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109284 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 7]
def baseStart_1109284 : Nat := 118140960795 + 1109284 * 2 ^ 59
def prefixEnd_1109284 : Nat := 4983230072969 + 3 ^ 40 * 1109284 * 2
def baseEnd_1109284 : Nat := 126576860964920701099667

theorem tailTrace_1109284 : CollatzResearch.WordTrace tailWord_1109284 prefixEnd_1109284 126576860964920701099667 := by
  unfold tailWord_1109284
  simp only [CollatzResearch.WordTrace]
  refine ⟨20229455656630496734687453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26972607542173995646249937 20229455656630496734687453)
  ·
    refine ⟨7586045871236436275507795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20229455656630496734687453 7586045871236436275507795)
    ·
      refine ⟨11379068806854654413261693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7586045871236436275507795 11379068806854654413261693)
      ·
        refine ⟨4267150802570495404973135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11379068806854654413261693 4267150802570495404973135)
        ·
          refine ⟨6400726203855743107459703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4267150802570495404973135 6400726203855743107459703)
          ·
            refine ⟨9601089305783614661189555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6400726203855743107459703 9601089305783614661189555)
            ·
              refine ⟨14401633958675421991784333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9601089305783614661189555 14401633958675421991784333)
              ·
                refine ⟨5400612734503283246919125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14401633958675421991784333 5400612734503283246919125)
                ·
                  refine ⟨126576860964920701099667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5400612734503283246919125 126576860964920701099667)
                  ·
                    rfl

theorem cell22_1109284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_1109284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109284 prefixEnd_1109284 := by exact prefixLift 1109284
  have htrace : WordTrace (prefixWord ++ tailWord_1109284) baseStart_1109284 baseEnd_1109284 := by
    simpa [prefixWord, tailWord_1109284, baseEnd_1109284] using wordTrace_append hprefix tailTrace_1109284
  have hstable : (prefixWord ++ tailWord_1109284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109284).length < 2 ^ (prefixWord ++ tailWord_1109284).sum := by decide
  have hdescent : baseEnd_1109284 < baseStart_1109284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109288 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1109288 : Nat := 118140960795 + 1109288 * 2 ^ 59
def prefixEnd_1109288 : Nat := 4983230072969 + 3 ^ 40 * 1109288 * 2
def baseEnd_1109288 : Nat := 379731952176507426198989

theorem tailTrace_1109288 : CollatzResearch.WordTrace tailWord_1109288 prefixEnd_1109288 379731952176507426198989 := by
  unfold tailWord_1109288
  simp only [CollatzResearch.WordTrace]
  refine ⟨20229528602623251076260259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26972704803497668101680345 20229528602623251076260259)
  ·
    refine ⟨30344292903934876614390389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20229528602623251076260259 30344292903934876614390389)
    ·
      refine ⟨2844777459743894682599099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30344292903934876614390389 2844777459743894682599099)
      ·
        refine ⟨4267166189615842023898649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2844777459743894682599099 4267166189615842023898649)
        ·
          refine ⟨3200374642211881517923987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4267166189615842023898649 3200374642211881517923987)
          ·
            refine ⟨4800561963317822276885981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3200374642211881517923987 4800561963317822276885981)
            ·
              refine ⟨1800210736244183353832243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4800561963317822276885981 1800210736244183353832243)
              ·
                refine ⟨2700316104366275030748365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1800210736244183353832243 2700316104366275030748365)
                ·
                  refine ⟨1012618539137353136530637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2700316104366275030748365 1012618539137353136530637)
                  ·
                    refine ⟨379731952176507426198989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1012618539137353136530637 379731952176507426198989)
                    ·
                      rfl

theorem cell22_1109288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1109288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109288 prefixEnd_1109288 := by exact prefixLift 1109288
  have htrace : WordTrace (prefixWord ++ tailWord_1109288) baseStart_1109288 baseEnd_1109288 := by
    simpa [prefixWord, tailWord_1109288, baseEnd_1109288] using wordTrace_append hprefix tailTrace_1109288
  have hstable : (prefixWord ++ tailWord_1109288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109288).length < 2 ^ (prefixWord ++ tailWord_1109288).sum := by decide
  have hdescent : baseEnd_1109288 < baseStart_1109288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109301 : List Nat := [1, 3, 3, 1, 2, 3, 1, 3, 5]
def baseStart_1109301 : Nat := 118140960795 + 1109301 * 2 ^ 59
def prefixEnd_1109301 : Nat := 4983230072969 + 3 ^ 40 * 1109301 * 2
def baseEnd_1109301 : Nat := 126578800780726575207983

theorem tailTrace_1109301 : CollatzResearch.WordTrace tailWord_1109301 prefixEnd_1109301 126578800780726575207983 := by
  unfold tailWord_1109301
  simp only [CollatzResearch.WordTrace]
  refine ⟨40459531354199405372743757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26973020902799603581829171 40459531354199405372743757)
  ·
    refine ⟨15172324257824777014778909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40459531354199405372743757 15172324257824777014778909)
    ·
      refine ⟨5689621596684291380542091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15172324257824777014778909 5689621596684291380542091)
      ·
        refine ⟨8534432395026437070813137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5689621596684291380542091 8534432395026437070813137)
        ·
          refine ⟨6400824296269827803109853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8534432395026437070813137 6400824296269827803109853)
          ·
            refine ⟨2400309111101185426166195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6400824296269827803109853 2400309111101185426166195)
            ·
              refine ⟨3600463666651778139249293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400309111101185426166195 3600463666651778139249293)
              ·
                refine ⟨1350173874994416802218485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3600463666651778139249293 1350173874994416802218485)
                ·
                  refine ⟨126578800780726575207983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1350173874994416802218485 126578800780726575207983)
                  ·
                    rfl

theorem cell22_1109301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_1109301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109301 prefixEnd_1109301 := by exact prefixLift 1109301
  have htrace : WordTrace (prefixWord ++ tailWord_1109301) baseStart_1109301 baseEnd_1109301 := by
    simpa [prefixWord, tailWord_1109301, baseEnd_1109301] using wordTrace_append hprefix tailTrace_1109301
  have hstable : (prefixWord ++ tailWord_1109301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109301).length < 2 ^ (prefixWord ++ tailWord_1109301).sum := by decide
  have hdescent : baseEnd_1109301 < baseStart_1109301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109346 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 6]
def baseStart_1109346 : Nat := 118140960795 + 1109346 * 2 ^ 59
def prefixEnd_1109346 : Nat := 4983230072969 + 3 ^ 40 * 1109346 * 2
def baseEnd_1109346 : Nat := 126583935587271536082937

theorem tailTrace_1109346 : CollatzResearch.WordTrace tailWord_1109346 prefixEnd_1109346 126583935587271536082937 := by
  unfold tailWord_1109346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10115293159759094514532973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26974115092690918705421261 10115293159759094514532973)
  ·
    refine ⟨3793234934909660442949865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10115293159759094514532973 3793234934909660442949865)
    ·
      refine ⟨2844926201182245332212399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3793234934909660442949865 2844926201182245332212399)
      ·
        refine ⟨4267389301773367998318599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2844926201182245332212399 4267389301773367998318599)
        ·
          refine ⟨6401083952660051997477899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4267389301773367998318599 6401083952660051997477899)
          ·
            refine ⟨9601625928990077996216849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6401083952660051997477899 9601625928990077996216849)
            ·
              refine ⟨7201219446742558497162637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9601625928990077996216849 7201219446742558497162637)
              ·
                refine ⟨2700457292528459436435989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7201219446742558497162637 2700457292528459436435989)
                ·
                  refine ⟨126583935587271536082937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2700457292528459436435989 126583935587271536082937)
                  ·
                    rfl

theorem cell22_1109346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_1109346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109346 prefixEnd_1109346 := by exact prefixLift 1109346
  have htrace : WordTrace (prefixWord ++ tailWord_1109346) baseStart_1109346 baseEnd_1109346 := by
    simpa [prefixWord, tailWord_1109346, baseEnd_1109346] using wordTrace_append hprefix tailTrace_1109346
  have hstable : (prefixWord ++ tailWord_1109346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109346).length < 2 ^ (prefixWord ++ tailWord_1109346).sum := by decide
  have hdescent : baseEnd_1109346 < baseStart_1109346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109359 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 1, 6]
def baseStart_1109359 : Nat := 118140960795 + 1109359 * 2 ^ 59
def prefixEnd_1109359 : Nat := 4983230072969 + 3 ^ 40 * 1109359 * 2
def baseEnd_1109359 : Nat := 379756256927486907673771

theorem tailTrace_1109359 : CollatzResearch.WordTrace tailWord_1109359 prefixEnd_1109359 379756256927486907673771 := by
  unfold tailWord_1109359
  simp only [CollatzResearch.WordTrace]
  refine ⟨40461646787989281278355131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26974431191992854185570087 40461646787989281278355131)
  ·
    refine ⟨60692470181983921917532697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40461646787989281278355131 60692470181983921917532697)
    ·
      refine ⟨45519352636487941438149523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60692470181983921917532697 45519352636487941438149523)
      ·
        refine ⟨68279028954731912157224285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45519352636487941438149523 68279028954731912157224285)
        ·
          refine ⟨25604635858024467058959107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68279028954731912157224285 25604635858024467058959107)
          ·
            refine ⟨38406953787036700588438661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25604635858024467058959107 38406953787036700588438661)
            ·
              refine ⟨7201303835069381360332249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38406953787036700588438661 7201303835069381360332249)
              ·
                refine ⟨5400977876302036020249187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7201303835069381360332249 5400977876302036020249187)
                ·
                  refine ⟨8101466814453054030373781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5400977876302036020249187 8101466814453054030373781)
                  ·
                    refine ⟨379756256927486907673771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8101466814453054030373781 379756256927486907673771)
                    ·
                      rfl

theorem cell22_1109359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_1109359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109359 prefixEnd_1109359 := by exact prefixLift 1109359
  have htrace : WordTrace (prefixWord ++ tailWord_1109359) baseStart_1109359 baseEnd_1109359 := by
    simpa [prefixWord, tailWord_1109359, baseEnd_1109359] using wordTrace_append hprefix tailTrace_1109359
  have hstable : (prefixWord ++ tailWord_1109359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109359).length < 2 ^ (prefixWord ++ tailWord_1109359).sum := by decide
  have hdescent : baseEnd_1109359 < baseStart_1109359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109440 : List Nat := [2, 1, 1, 2, 3, 1, 5, 3, 1, 3]
def baseStart_1109440 : Nat := 118140960795 + 1109440 * 2 ^ 59
def prefixEnd_1109440 : Nat := 4983230072969 + 3 ^ 40 * 1109440 * 2
def baseEnd_1109440 : Nat := 379783984882829696398523

theorem tailTrace_1109440 : CollatzResearch.WordTrace tailWord_1109440 prefixEnd_1109440 379783984882829696398523 := by
  unfold tailWord_1109440
  simp only [CollatzResearch.WordTrace]
  refine ⟨20232300550347916056026887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26976400733797221408035849 20232300550347916056026887)
  ·
    refine ⟨30348450825521874084040331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20232300550347916056026887 30348450825521874084040331)
    ·
      refine ⟨45522676238282811126060497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30348450825521874084040331 45522676238282811126060497)
      ·
        refine ⟨34142007178712108344545373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45522676238282811126060497 34142007178712108344545373)
        ·
          refine ⟨12803252692017040629204515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34142007178712108344545373 12803252692017040629204515)
          ·
            refine ⟨19204879038025560943806773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12803252692017040629204515 19204879038025560943806773)
            ·
              refine ⟨1800457409814896338481885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19204879038025560943806773 1800457409814896338481885)
              ·
                refine ⟨675171528680586126930707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1800457409814896338481885 675171528680586126930707)
                ·
                  refine ⟨1012757293020879190396061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675171528680586126930707 1012757293020879190396061)
                  ·
                    refine ⟨379783984882829696398523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1012757293020879190396061 379783984882829696398523)
                    ·
                      rfl

theorem cell22_1109440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 1, 3].length) (baseStart_1109440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109440 prefixEnd_1109440 := by exact prefixLift 1109440
  have htrace : WordTrace (prefixWord ++ tailWord_1109440) baseStart_1109440 baseEnd_1109440 := by
    simpa [prefixWord, tailWord_1109440, baseEnd_1109440] using wordTrace_append hprefix tailTrace_1109440
  have hstable : (prefixWord ++ tailWord_1109440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109440).length < 2 ^ (prefixWord ++ tailWord_1109440).sum := by decide
  have hdescent : baseEnd_1109440 < baseStart_1109440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109496 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 3, 5]
def baseStart_1109496 : Nat := 118140960795 + 1109496 * 2 ^ 59
def prefixEnd_1109496 : Nat := 4983230072969 + 3 ^ 40 * 1109496 * 2
def baseEnd_1109496 : Nat := 379803154827264216998351

theorem tailTrace_1109496 : CollatzResearch.WordTrace tailWord_1109496 prefixEnd_1109496 379803154827264216998351 := by
  unfold tailWord_1109496
  simp only [CollatzResearch.WordTrace]
  refine ⟨20233321794246476838046171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26977762392328635784061561 20233321794246476838046171)
  ·
    refine ⟨30349982691369715257069257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20233321794246476838046171 30349982691369715257069257)
    ·
      refine ⟨22762487018527286442801943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30349982691369715257069257 22762487018527286442801943)
      ·
        refine ⟨34143730527790929664202915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22762487018527286442801943 34143730527790929664202915)
        ·
          refine ⟨51215595791686394496304373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34143730527790929664202915 51215595791686394496304373)
          ·
            refine ⟨4801462105470599484028535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51215595791686394496304373 4801462105470599484028535)
            ·
              refine ⟨7202193158205899226042803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4801462105470599484028535 7202193158205899226042803)
              ·
                refine ⟨10803289737308848839064205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7202193158205899226042803 10803289737308848839064205)
                ·
                  refine ⟨4051233651490818314649077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10803289737308848839064205 4051233651490818314649077)
                  ·
                    refine ⟨379803154827264216998351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4051233651490818314649077 379803154827264216998351)
                    ·
                      rfl

theorem cell22_1109496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_1109496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109496 prefixEnd_1109496 := by exact prefixLift 1109496
  have htrace : WordTrace (prefixWord ++ tailWord_1109496) baseStart_1109496 baseEnd_1109496 := by
    simpa [prefixWord, tailWord_1109496, baseEnd_1109496] using wordTrace_append hprefix tailTrace_1109496
  have hstable : (prefixWord ++ tailWord_1109496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109496).length < 2 ^ (prefixWord ++ tailWord_1109496).sum := by decide
  have hdescent : baseEnd_1109496 < baseStart_1109496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109498 : List Nat := [3, 1, 1, 1, 1, 2, 4, 5, 4]
def baseStart_1109498 : Nat := 118140960795 + 1109498 * 2 ^ 59
def prefixEnd_1109498 : Nat := 4983230072969 + 3 ^ 40 * 1109498 * 2
def baseEnd_1109498 : Nat := 126601279822712292816115

theorem tailTrace_1109498 : CollatzResearch.WordTrace tailWord_1109498 prefixEnd_1109498 126601279822712292816115 := by
  unfold tailWord_1109498
  simp only [CollatzResearch.WordTrace]
  refine ⟨10116679133621427004416287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26977811022990472011776765 10116679133621427004416287)
  ·
    refine ⟨15175018700432140506624431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10116679133621427004416287 15175018700432140506624431)
    ·
      refine ⟨22762528050648210759936647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15175018700432140506624431 22762528050648210759936647)
      ·
        refine ⟨34143792075972316139904971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22762528050648210759936647 34143792075972316139904971)
        ·
          refine ⟨51215688113958474209857457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34143792075972316139904971 51215688113958474209857457)
          ·
            refine ⟨38411766085468855657393093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51215688113958474209857457 38411766085468855657393093)
            ·
              refine ⟨7202206141025410435761205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38411766085468855657393093 7202206141025410435761205)
              ·
                refine ⟨675206825721132228352613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7202206141025410435761205 675206825721132228352613)
                ·
                  refine ⟨126601279822712292816115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 675206825721132228352613 126601279822712292816115)
                  ·
                    rfl

theorem cell22_1109498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_1109498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109498 prefixEnd_1109498 := by exact prefixLift 1109498
  have htrace : WordTrace (prefixWord ++ tailWord_1109498) baseStart_1109498 baseEnd_1109498 := by
    simpa [prefixWord, tailWord_1109498, baseEnd_1109498] using wordTrace_append hprefix tailTrace_1109498
  have hstable : (prefixWord ++ tailWord_1109498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109498).length < 2 ^ (prefixWord ++ tailWord_1109498).sum := by decide
  have hdescent : baseEnd_1109498 < baseStart_1109498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109515 : List Nat := [1, 1, 1, 1, 8, 1, 1, 4, 4]
def baseStart_1109515 : Nat := 118140960795 + 1109515 * 2 ^ 59
def prefixEnd_1109515 : Nat := 4983230072969 + 3 ^ 40 * 1109515 * 2
def baseEnd_1109515 : Nat := 126603219638518166924431

theorem tailTrace_1109515 : CollatzResearch.WordTrace tailWord_1109515 prefixEnd_1109515 126603219638518166924431 := by
  unfold tailWord_1109515
  simp only [CollatzResearch.WordTrace]
  refine ⟨40467336575424119921033999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26978224383616079947355999 40467336575424119921033999)
  ·
    refine ⟨60701004863136179881550999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40467336575424119921033999 60701004863136179881550999)
    ·
      refine ⟨91051507294704269822326499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60701004863136179881550999 91051507294704269822326499)
      ·
        refine ⟨136577260942056404733489749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91051507294704269822326499 136577260942056404733489749)
        ·
          refine ⟨1600514776664723492970583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 136577260942056404733489749 1600514776664723492970583)
          ·
            refine ⟨2400772164997085239455875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600514776664723492970583 2400772164997085239455875)
            ·
              refine ⟨3601158247495627859183813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2400772164997085239455875 3601158247495627859183813)
              ·
                refine ⟨675217171405430223596965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3601158247495627859183813 675217171405430223596965)
                ·
                  refine ⟨126603219638518166924431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 675217171405430223596965 126603219638518166924431)
                  ·
                    rfl

theorem cell22_1109515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 4].length) (baseStart_1109515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109515 prefixEnd_1109515 := by exact prefixLift 1109515
  have htrace : WordTrace (prefixWord ++ tailWord_1109515) baseStart_1109515 baseEnd_1109515 := by
    simpa [prefixWord, tailWord_1109515, baseEnd_1109515] using wordTrace_append hprefix tailTrace_1109515
  have hstable : (prefixWord ++ tailWord_1109515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109515).length < 2 ^ (prefixWord ++ tailWord_1109515).sum := by decide
  have hdescent : baseEnd_1109515 < baseStart_1109515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109564 : List Nat := [2, 2, 2, 2, 5, 1, 1, 2, 2, 3]
def baseStart_1109564 : Nat := 118140960795 + 1109564 * 2 ^ 59
def prefixEnd_1109564 : Nat := 4983230072969 + 3 ^ 40 * 1109564 * 2
def baseEnd_1109564 : Nat := 379826432616934706298143

theorem tailTrace_1109564 : CollatzResearch.WordTrace tailWord_1109564 prefixEnd_1109564 379826432616934706298143 := by
  unfold tailWord_1109564
  simp only [CollatzResearch.WordTrace]
  refine ⟨20234561876123300644783873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26979415834831067526378497 20234561876123300644783873)
  ·
    refine ⟨15175921407092475483587905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20234561876123300644783873 15175921407092475483587905)
    ·
      refine ⟨11381941055319356612690929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15175921407092475483587905 11381941055319356612690929)
      ·
        refine ⟨8536455791489517459518197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11381941055319356612690929 8536455791489517459518197)
        ·
          refine ⟨800292730452142261829831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8536455791489517459518197 800292730452142261829831)
          ·
            refine ⟨1200439095678213392744747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800292730452142261829831 1200439095678213392744747)
            ·
              refine ⟨1800658643517320089117121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200439095678213392744747 1800658643517320089117121)
              ·
                refine ⟨1350493982637990066837841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1800658643517320089117121 1350493982637990066837841)
                ·
                  refine ⟨1012870486978492550128381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1350493982637990066837841 1012870486978492550128381)
                  ·
                    refine ⟨379826432616934706298143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1012870486978492550128381 379826432616934706298143)
                    ·
                      rfl

theorem cell22_1109564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_1109564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109564 prefixEnd_1109564 := by exact prefixLift 1109564
  have htrace : WordTrace (prefixWord ++ tailWord_1109564) baseStart_1109564 baseEnd_1109564 := by
    simpa [prefixWord, tailWord_1109564, baseEnd_1109564] using wordTrace_append hprefix tailTrace_1109564
  have hstable : (prefixWord ++ tailWord_1109564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109564).length < 2 ^ (prefixWord ++ tailWord_1109564).sum := by decide
  have hdescent : baseEnd_1109564 < baseStart_1109564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109652 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1109652 : Nat := 118140960795 + 1109652 * 2 ^ 59
def prefixEnd_1109652 : Nat := 4983230072969 + 3 ^ 40 * 1109652 * 2
def baseEnd_1109652 : Nat := 379856556815331810097873

theorem tailTrace_1109652 : CollatzResearch.WordTrace tailWord_1109652 prefixEnd_1109652 379856556815331810097873 := by
  unfold tailWord_1109652
  simp only [CollatzResearch.WordTrace]
  refine ⟨20236166687963896159385605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26981555583951861545847473 20236166687963896159385605)
  ·
    refine ⟨3794281253993230529884801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20236166687963896159385605 3794281253993230529884801)
    ·
      refine ⟨2845710940494922897413601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3794281253993230529884801 2845710940494922897413601)
      ·
        refine ⟨2134283205371192173060201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2845710940494922897413601 2134283205371192173060201)
        ·
          refine ⟨1600712404028394129795151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2134283205371192173060201 1600712404028394129795151)
          ·
            refine ⟨2401068606042591194692727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600712404028394129795151 2401068606042591194692727)
            ·
              refine ⟨3601602909063886792039091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2401068606042591194692727 3601602909063886792039091)
              ·
                refine ⟨5402404363595830188058637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3601602909063886792039091 5402404363595830188058637)
                ·
                  refine ⟨2025901636348436320521989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5402404363595830188058637 2025901636348436320521989)
                  ·
                    refine ⟨379856556815331810097873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2025901636348436320521989 379856556815331810097873)
                    ·
                      rfl

theorem cell22_1109652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1109652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109652 prefixEnd_1109652 := by exact prefixLift 1109652
  have htrace : WordTrace (prefixWord ++ tailWord_1109652) baseStart_1109652 baseEnd_1109652 := by
    simpa [prefixWord, tailWord_1109652, baseEnd_1109652] using wordTrace_append hprefix tailTrace_1109652
  have hstable : (prefixWord ++ tailWord_1109652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109652).length < 2 ^ (prefixWord ++ tailWord_1109652).sum := by decide
  have hdescent : baseEnd_1109652 < baseStart_1109652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109665 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 1, 5]
def baseStart_1109665 : Nat := 118140960795 + 1109665 * 2 ^ 59
def prefixEnd_1109665 : Nat := 4983230072969 + 3 ^ 40 * 1109665 * 2
def baseEnd_1109665 : Nat := 379861006981004109522833

theorem tailTrace_1109665 : CollatzResearch.WordTrace tailWord_1109665 prefixEnd_1109665 379861006981004109522833 := by
  unfold tailWord_1109665
  simp only [CollatzResearch.WordTrace]
  refine ⟨40472807524880695538994449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26981871683253797025996299 40472807524880695538994449)
  ·
    refine ⟨30354605643660521654245837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40472807524880695538994449 30354605643660521654245837)
    ·
      refine ⟨11382977116372695620342189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30354605643660521654245837 11382977116372695620342189)
      ·
        refine ⟨4268616418639760857628321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11382977116372695620342189 4268616418639760857628321)
        ·
          refine ⟨3201462313979820643221241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4268616418639760857628321 3201462313979820643221241)
          ·
            refine ⟨2401096735484865482415931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3201462313979820643221241 2401096735484865482415931)
            ·
              refine ⟨3601645103227298223623897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2401096735484865482415931 3601645103227298223623897)
              ·
                refine ⟨2701233827420473667717923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3601645103227298223623897 2701233827420473667717923)
                ·
                  refine ⟨4051850741130710501576885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2701233827420473667717923 4051850741130710501576885)
                  ·
                    refine ⟨379861006981004109522833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4051850741130710501576885 379861006981004109522833)
                    ·
                      rfl

theorem cell22_1109665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_1109665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109665 prefixEnd_1109665 := by exact prefixLift 1109665
  have htrace : WordTrace (prefixWord ++ tailWord_1109665) baseStart_1109665 baseEnd_1109665 := by
    simpa [prefixWord, tailWord_1109665, baseEnd_1109665] using wordTrace_append hprefix tailTrace_1109665
  have hstable : (prefixWord ++ tailWord_1109665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109665).length < 2 ^ (prefixWord ++ tailWord_1109665).sum := by decide
  have hdescent : baseEnd_1109665 < baseStart_1109665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109740 : List Nat := [2, 2, 1, 1, 2, 2, 5, 2, 5]
def baseStart_1109740 : Nat := 118140960795 + 1109740 * 2 ^ 59
def prefixEnd_1109740 : Nat := 4983230072969 + 3 ^ 40 * 1109740 * 2
def baseEnd_1109740 : Nat := 126628893671242971299201

theorem tailTrace_1109740 : CollatzResearch.WordTrace tailWord_1109740 prefixEnd_1109740 126628893671242971299201 := by
  unfold tailWord_1109740
  simp only [CollatzResearch.WordTrace]
  refine ⟨20237771499804491673987337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26983695333072655565316449 20237771499804491673987337)
  ·
    refine ⟨15178328624853368755490503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20237771499804491673987337 15178328624853368755490503)
    ·
      refine ⟨22767492937280053133235755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15178328624853368755490503 22767492937280053133235755)
      ·
        refine ⟨34151239405920079699853633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22767492937280053133235755 34151239405920079699853633)
        ·
          refine ⟨25613429554440059774890225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34151239405920079699853633 25613429554440059774890225)
          ·
            refine ⟨19210072165830044831167669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25613429554440059774890225 19210072165830044831167669)
            ·
              refine ⟨1800944265546566702921969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19210072165830044831167669 1800944265546566702921969)
              ·
                refine ⟨1350708199159925027191477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1800944265546566702921969 1350708199159925027191477)
                ·
                  refine ⟨126628893671242971299201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1350708199159925027191477 126628893671242971299201)
                  ·
                    rfl

theorem cell22_1109740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_1109740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109740 prefixEnd_1109740 := by exact prefixLift 1109740
  have htrace : WordTrace (prefixWord ++ tailWord_1109740) baseStart_1109740 baseEnd_1109740 := by
    simpa [prefixWord, tailWord_1109740, baseEnd_1109740] using wordTrace_append hprefix tailTrace_1109740
  have hstable : (prefixWord ++ tailWord_1109740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109740).length < 2 ^ (prefixWord ++ tailWord_1109740).sum := by decide
  have hdescent : baseEnd_1109740 < baseStart_1109740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109778 : List Nat := [3, 2, 4, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1109778 : Nat := 118140960795 + 1109778 * 2 ^ 59
def prefixEnd_1109778 : Nat := 4983230072969 + 3 ^ 40 * 1109778 * 2
def baseEnd_1109778 : Nat := 379899689190309481447487

theorem tailTrace_1109778 : CollatzResearch.WordTrace tailWord_1109778 prefixEnd_1109778 379899689190309481447487 := by
  unfold tailWord_1109778
  simp only [CollatzResearch.WordTrace]
  refine ⟨10119232243367828959464497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26984619315647543891905325 10119232243367828959464497)
  ·
    refine ⟨7589424182525871719598373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10119232243367828959464497 7589424182525871719598373)
    ·
      refine ⟨1423017034223600947424695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7589424182525871719598373 1423017034223600947424695)
      ·
        refine ⟨2134525551335401421137043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1423017034223600947424695 2134525551335401421137043)
        ·
          refine ⟨3201788327003102131705565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2134525551335401421137043 3201788327003102131705565)
          ·
            refine ⟨1200670622626163299389587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3201788327003102131705565 1200670622626163299389587)
            ·
              refine ⟨1801005933939244949084381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200670622626163299389587 1801005933939244949084381)
              ·
                refine ⟨675377225227216855906643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1801005933939244949084381 675377225227216855906643)
                ·
                  refine ⟨1013065837840825283859965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675377225227216855906643 1013065837840825283859965)
                  ·
                    refine ⟨379899689190309481447487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1013065837840825283859965 379899689190309481447487)
                    ·
                      rfl

theorem cell22_1109778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1109778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109778 prefixEnd_1109778 := by exact prefixLift 1109778
  have htrace : WordTrace (prefixWord ++ tailWord_1109778) baseStart_1109778 baseEnd_1109778 := by
    simpa [prefixWord, tailWord_1109778, baseEnd_1109778] using wordTrace_append hprefix tailTrace_1109778
  have hstable : (prefixWord ++ tailWord_1109778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109778).length < 2 ^ (prefixWord ++ tailWord_1109778).sum := by decide
  have hdescent : baseEnd_1109778 < baseStart_1109778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109832 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 2, 4]
def baseStart_1109832 : Nat := 118140960795 + 1109832 * 2 ^ 59
def prefixEnd_1109832 : Nat := 4983230072969 + 3 ^ 40 * 1109832 * 2
def baseEnd_1109832 : Nat := 379918174493871340597321

theorem tailTrace_1109832 : CollatzResearch.WordTrace tailWord_1109832 prefixEnd_1109832 379918174493871340597321 := by
  unfold tailWord_1109832
  simp only [CollatzResearch.WordTrace]
  refine ⟨20239449257637841530161875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26985932343517122040215833 20239449257637841530161875)
  ·
    refine ⟨30359173886456762295242813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20239449257637841530161875 30359173886456762295242813)
    ·
      refine ⟨11384690207421285860716055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30359173886456762295242813 11384690207421285860716055)
      ·
        refine ⟨17077035311131928791074083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11384690207421285860716055 17077035311131928791074083)
        ·
          refine ⟨25615552966697893186611125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17077035311131928791074083 25615552966697893186611125)
          ·
            refine ⟨2401458090627927486244793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25615552966697893186611125 2401458090627927486244793)
            ·
              refine ⟨1801093567970945614683595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2401458090627927486244793 1801093567970945614683595)
              ·
                refine ⟨2701640351956418422025393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1801093567970945614683595 2701640351956418422025393)
                ·
                  refine ⟨2026230263967313816519045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2701640351956418422025393 2026230263967313816519045)
                  ·
                    refine ⟨379918174493871340597321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2026230263967313816519045 379918174493871340597321)
                    ·
                      rfl

theorem cell22_1109832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_1109832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109832 prefixEnd_1109832 := by exact prefixLift 1109832
  have htrace : WordTrace (prefixWord ++ tailWord_1109832) baseStart_1109832 baseEnd_1109832 := by
    simpa [prefixWord, tailWord_1109832, baseEnd_1109832] using wordTrace_append hprefix tailTrace_1109832
  have hstable : (prefixWord ++ tailWord_1109832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109832).length < 2 ^ (prefixWord ++ tailWord_1109832).sum := by decide
  have hdescent : baseEnd_1109832 < baseStart_1109832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109937 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 6]
def baseStart_1109937 : Nat := 118140960795 + 1109937 * 2 ^ 59
def prefixEnd_1109937 : Nat := 4983230072969 + 3 ^ 40 * 1109937 * 2
def baseEnd_1109937 : Nat := 126651372713228688907333

theorem tailTrace_1109937 : CollatzResearch.WordTrace tailWord_1109937 prefixEnd_1109937 126651372713228688907333 := by
  unfold tailWord_1109937
  simp only [CollatzResearch.WordTrace]
  refine ⟨40482728179895285992896065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26988485453263523995264043 40482728179895285992896065)
  ·
    refine ⟨30362046134921464494672049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40482728179895285992896065 30362046134921464494672049)
    ·
      refine ⟨22771534601191098371004037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30362046134921464494672049 22771534601191098371004037)
      ·
        refine ⟨4269662737723330944563257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22771534601191098371004037 4269662737723330944563257)
        ·
          refine ⟨3202247053292498208422443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4269662737723330944563257 3202247053292498208422443)
          ·
            refine ⟨4803370579938747312633665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3202247053292498208422443 4803370579938747312633665)
            ·
              refine ⟨3602527934954060484475249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4803370579938747312633665 3602527934954060484475249)
              ·
                refine ⟨2701895951215545363356437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3602527934954060484475249 2701895951215545363356437)
                ·
                  refine ⟨126651372713228688907333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2701895951215545363356437 126651372713228688907333)
                  ·
                    rfl

theorem cell22_1109937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 6].length) (baseStart_1109937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109937 prefixEnd_1109937 := by exact prefixLift 1109937
  have htrace : WordTrace (prefixWord ++ tailWord_1109937) baseStart_1109937 baseEnd_1109937 := by
    simpa [prefixWord, tailWord_1109937, baseEnd_1109937] using wordTrace_append hprefix tailTrace_1109937
  have hstable : (prefixWord ++ tailWord_1109937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109937).length < 2 ^ (prefixWord ++ tailWord_1109937).sum := by decide
  have hdescent : baseEnd_1109937 < baseStart_1109937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109952 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 6, 3]
def baseStart_1109952 : Nat := 118140960795 + 1109952 * 2 ^ 59
def prefixEnd_1109952 : Nat := 4983230072969 + 3 ^ 40 * 1109952 * 2
def baseEnd_1109952 : Nat := 379959252946231027596953

theorem tailTrace_1109952 : CollatzResearch.WordTrace tailWord_1109952 prefixEnd_1109952 379959252946231027596953 := by
  unfold tailWord_1109952
  simp only [CollatzResearch.WordTrace]
  refine ⟨20241637637420471777346055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26988850183227295703128073 20241637637420471777346055)
  ·
    refine ⟨30362456456130707666019083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20241637637420471777346055 30362456456130707666019083)
    ·
      refine ⟨45543684684196061499028625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30362456456130707666019083 45543684684196061499028625)
      ·
        refine ⟨34157763513147046124271469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45543684684196061499028625 34157763513147046124271469)
        ·
          refine ⟨12809161317430142296601801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34157763513147046124271469 12809161317430142296601801)
          ·
            refine ⟨9606870988072606722451351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12809161317430142296601801 9606870988072606722451351)
            ·
              refine ⟨14410306482108910083677027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9606870988072606722451351 14410306482108910083677027)
              ·
                refine ⟨21615459723163365125515541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14410306482108910083677027 21615459723163365125515541)
                ·
                  refine ⟨1013224674523282740258541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21615459723163365125515541 1013224674523282740258541)
                  ·
                    refine ⟨379959252946231027596953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1013224674523282740258541 379959252946231027596953)
                    ·
                      rfl

theorem cell22_1109952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6, 3].length) (baseStart_1109952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109952 prefixEnd_1109952 := by exact prefixLift 1109952
  have htrace : WordTrace (prefixWord ++ tailWord_1109952) baseStart_1109952 baseEnd_1109952 := by
    simpa [prefixWord, tailWord_1109952, baseEnd_1109952] using wordTrace_append hprefix tailTrace_1109952
  have hstable : (prefixWord ++ tailWord_1109952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109952).length < 2 ^ (prefixWord ++ tailWord_1109952).sum := by decide
  have hdescent : baseEnd_1109952 < baseStart_1109952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1109967 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 2, 4]
def baseStart_1109967 : Nat := 118140960795 + 1109967 * 2 ^ 59
def prefixEnd_1109967 : Nat := 4983230072969 + 3 ^ 40 * 1109967 * 2
def baseEnd_1109967 : Nat := 379964387752775988471907

theorem tailTrace_1109967 : CollatzResearch.WordTrace tailWord_1109967 prefixEnd_1109967 379964387752775988471907 := by
  unfold tailWord_1109967
  simp only [CollatzResearch.WordTrace]
  refine ⟨40483822369786601116488155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26989214913191067410992103 40483822369786601116488155)
  ·
    refine ⟨60725733554679901674732233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40483822369786601116488155 60725733554679901674732233)
    ·
      refine ⟨45544300166009926256049175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60725733554679901674732233 45544300166009926256049175)
      ·
        refine ⟨68316450249014889384073763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45544300166009926256049175 68316450249014889384073763)
        ·
          refine ⟨102474675373522334076110645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68316450249014889384073763 102474675373522334076110645)
          ·
            refine ⟨9607000816267718819635373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102474675373522334076110645 9607000816267718819635373)
            ·
              refine ⟨3602625306100394557363265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9607000816267718819635373 3602625306100394557363265)
              ·
                refine ⟨2701968979575295918022449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3602625306100394557363265 2701968979575295918022449)
                ·
                  refine ⟨2026476734681471938516837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2701968979575295918022449 2026476734681471938516837)
                  ·
                    refine ⟨379964387752775988471907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2026476734681471938516837 379964387752775988471907)
                    ·
                      rfl

theorem cell22_1109967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_1109967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1109967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1109967 prefixEnd_1109967 := by exact prefixLift 1109967
  have htrace : WordTrace (prefixWord ++ tailWord_1109967) baseStart_1109967 baseEnd_1109967 := by
    simpa [prefixWord, tailWord_1109967, baseEnd_1109967] using wordTrace_append hprefix tailTrace_1109967
  have hstable : (prefixWord ++ tailWord_1109967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1109967).length < 2 ^ (prefixWord ++ tailWord_1109967).sum := by decide
  have hdescent : baseEnd_1109967 < baseStart_1109967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1109967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110022 : List Nat := [6, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1110022 : Nat := 118140960795 + 1110022 * 2 ^ 59
def prefixEnd_1110022 : Nat := 4983230072969 + 3 ^ 40 * 1110022 * 2
def baseEnd_1110022 : Nat := 126661071792258059448913

theorem tailTrace_1110022 : CollatzResearch.WordTrace tailWord_1110022 prefixEnd_1110022 126661071792258059448913 := by
  unfold tailWord_1110022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265182137018354547179385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26990552256391563673160213 1265182137018354547179385)
  ·
    refine ⟨948886602763765910384539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1265182137018354547179385 948886602763765910384539)
    ·
      refine ⟨1423329904145648865576809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 948886602763765910384539 1423329904145648865576809)
      ·
        refine ⟨1067497428109236649182607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1423329904145648865576809 1067497428109236649182607)
        ·
          refine ⟨1601246142163854973773911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1067497428109236649182607 1601246142163854973773911)
          ·
            refine ⟨2401869213245782460660867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1601246142163854973773911 2401869213245782460660867)
            ·
              refine ⟨3602803819868673690991301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2401869213245782460660867 3602803819868673690991301)
              ·
                refine ⟨675525716225376317060869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3602803819868673690991301 675525716225376317060869)
                ·
                  refine ⟨126661071792258059448913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 675525716225376317060869 126661071792258059448913)
                  ·
                    rfl

theorem cell22_1110022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1110022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110022 prefixEnd_1110022 := by exact prefixLift 1110022
  have htrace : WordTrace (prefixWord ++ tailWord_1110022) baseStart_1110022 baseEnd_1110022 := by
    simpa [prefixWord, tailWord_1110022, baseEnd_1110022] using wordTrace_append hprefix tailTrace_1110022
  have hstable : (prefixWord ++ tailWord_1110022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110022).length < 2 ^ (prefixWord ++ tailWord_1110022).sum := by decide
  have hdescent : baseEnd_1110022 < baseStart_1110022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110042 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_1110042 : Nat := 118140960795 + 1110042 * 2 ^ 59
def prefixEnd_1110042 : Nat := 4983230072969 + 3 ^ 40 * 1110042 * 2
def baseEnd_1110042 : Nat := 379990061785500792846677

theorem tailTrace_1110042 : CollatzResearch.WordTrace tailWord_1110042 prefixEnd_1110042 379990061785500792846677 := by
  unfold tailWord_1110042
  simp only [CollatzResearch.WordTrace]
  refine ⟨10121639461128722231367095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26991038563009925950312253 10121639461128722231367095)
  ·
    refine ⟨15182459191693083347050643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10121639461128722231367095 15182459191693083347050643)
    ·
      refine ⟨22773688787539625020575965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15182459191693083347050643 22773688787539625020575965)
      ·
        refine ⟨8540133295327359382715987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22773688787539625020575965 8540133295327359382715987)
        ·
          refine ⟨12810199942991039074073981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8540133295327359382715987 12810199942991039074073981)
          ·
            refine ⟨4803824978621639652777743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12810199942991039074073981 4803824978621639652777743)
            ·
              refine ⟨7205737467932459479166615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4803824978621639652777743 7205737467932459479166615)
              ·
                refine ⟨10808606201898689218749923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7205737467932459479166615 10808606201898689218749923)
                ·
                  refine ⟨16212909302848033828124885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10808606201898689218749923 16212909302848033828124885)
                  ·
                    refine ⟨379990061785500792846677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16212909302848033828124885 379990061785500792846677)
                    ·
                      rfl

theorem cell22_1110042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_1110042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110042 prefixEnd_1110042 := by exact prefixLift 1110042
  have htrace : WordTrace (prefixWord ++ tailWord_1110042) baseStart_1110042 baseEnd_1110042 := by
    simpa [prefixWord, tailWord_1110042, baseEnd_1110042] using wordTrace_append hprefix tailTrace_1110042
  have hstable : (prefixWord ++ tailWord_1110042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110042).length < 2 ^ (prefixWord ++ tailWord_1110042).sum := by decide
  have hdescent : baseEnd_1110042 < baseStart_1110042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110044 : List Nat := [2, 2, 3, 1, 3, 1, 2, 3, 5]
def baseStart_1110044 : Nat := 118140960795 + 1110044 * 2 ^ 59
def prefixEnd_1110044 : Nat := 4983230072969 + 3 ^ 40 * 1110044 * 2
def baseEnd_1110044 : Nat := 126663582142124484765557

theorem tailTrace_1110044 : CollatzResearch.WordTrace tailWord_1110044 prefixEnd_1110044 126663582142124484765557 := by
  unfold tailWord_1110044
  simp only [CollatzResearch.WordTrace]
  refine ⟨20243315395253821633520593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26991087193671762178027457 20243315395253821633520593)
  ·
    refine ⟨15182486546440366225140445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20243315395253821633520593 15182486546440366225140445)
    ·
      refine ⟨5693432454915137334427667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15182486546440366225140445 5693432454915137334427667)
      ·
        refine ⟨8540148682372706001641501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5693432454915137334427667 8540148682372706001641501)
        ·
          refine ⟨3202555755889764750615563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8540148682372706001641501 3202555755889764750615563)
          ·
            refine ⟨4803833633834647125923345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3202555755889764750615563 4803833633834647125923345)
            ·
              refine ⟨3602875225375985344442509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4803833633834647125923345 3602875225375985344442509)
              ·
                refine ⟨1351078209515994504165941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3602875225375985344442509 1351078209515994504165941)
                ·
                  refine ⟨126663582142124484765557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1351078209515994504165941 126663582142124484765557)
                  ·
                    rfl

theorem cell22_1110044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_1110044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110044 prefixEnd_1110044 := by exact prefixLift 1110044
  have htrace : WordTrace (prefixWord ++ tailWord_1110044) baseStart_1110044 baseEnd_1110044 := by
    simpa [prefixWord, tailWord_1110044, baseEnd_1110044] using wordTrace_append hprefix tailTrace_1110044
  have hstable : (prefixWord ++ tailWord_1110044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110044).length < 2 ^ (prefixWord ++ tailWord_1110044).sum := by decide
  have hdescent : baseEnd_1110044 < baseStart_1110044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110078 : List Nat := [4, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_1110078 : Nat := 118140960795 + 1110078 * 2 ^ 59
def prefixEnd_1110078 : Nat := 4983230072969 + 3 ^ 40 * 1110078 * 2
def baseEnd_1110078 : Nat := 126667461773736232982189

theorem tailTrace_1110078 : CollatzResearch.WordTrace tailWord_1110078 prefixEnd_1110078 126667461773736232982189 := by
  unfold tailWord_1110078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5060983859048058384222361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26991913914922978049185925 5060983859048058384222361)
  ·
    refine ⟨3795737894286043788166771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5060983859048058384222361 3795737894286043788166771)
    ·
      refine ⟨5693606841429065682250157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3795737894286043788166771 5693606841429065682250157)
      ·
        refine ⟨2135102565535899630843809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5693606841429065682250157 2135102565535899630843809)
        ·
          refine ⟨1601326924151924723132857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2135102565535899630843809 1601326924151924723132857)
          ·
            refine ⟨1200995193113943542349643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1601326924151924723132857 1200995193113943542349643)
            ·
              refine ⟨1801492789670915313524465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1200995193113943542349643 1801492789670915313524465)
              ·
                refine ⟨1351119592253186485143349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1801492789670915313524465 1351119592253186485143349)
                ·
                  refine ⟨126667461773736232982189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1351119592253186485143349 126667461773736232982189)
                  ·
                    rfl

theorem cell22_1110078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_1110078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110078 prefixEnd_1110078 := by exact prefixLift 1110078
  have htrace : WordTrace (prefixWord ++ tailWord_1110078) baseStart_1110078 baseEnd_1110078 := by
    simpa [prefixWord, tailWord_1110078, baseEnd_1110078] using wordTrace_append hprefix tailTrace_1110078
  have hstable : (prefixWord ++ tailWord_1110078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110078).length < 2 ^ (prefixWord ++ tailWord_1110078).sum := by decide
  have hdescent : baseEnd_1110078 < baseStart_1110078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110089 : List Nat := [1, 2, 1, 1, 2, 2, 3, 6, 4]
def baseStart_1110089 : Nat := 118140960795 + 1110089 * 2 ^ 59
def prefixEnd_1110089 : Nat := 4983230072969 + 3 ^ 40 * 1110089 * 2
def baseEnd_1110089 : Nat := 126668716948669445640511

theorem tailTrace_1110089 : CollatzResearch.WordTrace tailWord_1110089 prefixEnd_1110089 126668716948669445640511 := by
  unfold tailWord_1110089
  simp only [CollatzResearch.WordTrace]
  refine ⟨40488272075344615952429321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26992181383563077301619547 40488272075344615952429321)
  ·
    refine ⟨30366204056508461964321991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40488272075344615952429321 30366204056508461964321991)
    ·
      refine ⟨45549306084762692946482987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30366204056508461964321991 45549306084762692946482987)
      ·
        refine ⟨68323959127144039419724481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45549306084762692946482987 68323959127144039419724481)
        ·
          refine ⟨51242969345358029564793361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68323959127144039419724481 51242969345358029564793361)
          ·
            refine ⟨38432227009018522173595021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51242969345358029564793361 38432227009018522173595021)
            ·
              refine ⟨14412085128381945815098133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38432227009018522173595021 14412085128381945815098133)
              ·
                refine ⟨675566490392903710082725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14412085128381945815098133 675566490392903710082725)
                ·
                  refine ⟨126668716948669445640511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 675566490392903710082725 126668716948669445640511)
                  ·
                    rfl

theorem cell22_1110089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 4].length) (baseStart_1110089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110089 prefixEnd_1110089 := by exact prefixLift 1110089
  have htrace : WordTrace (prefixWord ++ tailWord_1110089) baseStart_1110089 baseEnd_1110089 := by
    simpa [prefixWord, tailWord_1110089, baseEnd_1110089] using wordTrace_append hprefix tailTrace_1110089
  have hstable : (prefixWord ++ tailWord_1110089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110089).length < 2 ^ (prefixWord ++ tailWord_1110089).sum := by decide
  have hdescent : baseEnd_1110089 < baseStart_1110089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110104 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 1, 5]
def baseStart_1110104 : Nat := 118140960795 + 1110104 * 2 ^ 59
def prefixEnd_1110104 : Nat := 4983230072969 + 3 ^ 40 * 1110104 * 2
def baseEnd_1110104 : Nat := 380011285652553297796487

theorem tailTrace_1110104 : CollatzResearch.WordTrace tailWord_1110104 prefixEnd_1110104 380011285652553297796487 := by
  unfold tailWord_1110104
  simp only [CollatzResearch.WordTrace]
  refine ⟨20244409585145136757112683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26992546113526849009483577 20244409585145136757112683)
  ·
    refine ⟨30366614377717705135669025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20244409585145136757112683 30366614377717705135669025)
    ·
      refine ⟨22774960783288278851751769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30366614377717705135669025 22774960783288278851751769)
      ·
        refine ⟨17081220587466209138813827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22774960783288278851751769 17081220587466209138813827)
        ·
          refine ⟨25621830881199313708220741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17081220587466209138813827 25621830881199313708220741)
          ·
            refine ⟨4804093290224871320291389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25621830881199313708220741 4804093290224871320291389)
            ·
              refine ⟨1801534983834326745109271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4804093290224871320291389 1801534983834326745109271)
              ·
                refine ⟨2702302475751490117663907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1801534983834326745109271 2702302475751490117663907)
                ·
                  refine ⟨4053453713627235176495861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2702302475751490117663907 4053453713627235176495861)
                  ·
                    refine ⟨380011285652553297796487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4053453713627235176495861 380011285652553297796487)
                    ·
                      rfl

theorem cell22_1110104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_1110104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110104 prefixEnd_1110104 := by exact prefixLift 1110104
  have htrace : WordTrace (prefixWord ++ tailWord_1110104) baseStart_1110104 baseEnd_1110104 := by
    simpa [prefixWord, tailWord_1110104, baseEnd_1110104] using wordTrace_append hprefix tailTrace_1110104
  have hstable : (prefixWord ++ tailWord_1110104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110104).length < 2 ^ (prefixWord ++ tailWord_1110104).sum := by decide
  have hdescent : baseEnd_1110104 < baseStart_1110104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110119 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1110119 : Nat := 118140960795 + 1110119 * 2 ^ 59
def prefixEnd_1110119 : Nat := 4983230072969 + 3 ^ 40 * 1110119 * 2
def baseEnd_1110119 : Nat := 380016420459098258671441

theorem tailTrace_1110119 : CollatzResearch.WordTrace tailWord_1110119 prefixEnd_1110119 380016420459098258671441 := by
  unfold tailWord_1110119
  simp only [CollatzResearch.WordTrace]
  refine ⟨40489366265235931076021411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26992910843490620717347607 40489366265235931076021411)
  ·
    refine ⟨60734049397853896614032117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40489366265235931076021411 60734049397853896614032117)
    ·
      refine ⟨5693817131048802807565511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60734049397853896614032117 5693817131048802807565511)
      ·
        refine ⟨8540725696573204211348267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5693817131048802807565511 8540725696573204211348267)
        ·
          refine ⟨12811088544859806317022401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8540725696573204211348267 12811088544859806317022401)
          ·
            refine ⟨9608316408644854737766801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12811088544859806317022401 9608316408644854737766801)
            ·
              refine ⟨7206237306483641053325101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9608316408644854737766801 7206237306483641053325101)
              ·
                refine ⟨2702338989931365394996913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7206237306483641053325101 2702338989931365394996913)
                ·
                  refine ⟨2026754242448524046247685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2702338989931365394996913 2026754242448524046247685)
                  ·
                    refine ⟨380016420459098258671441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2026754242448524046247685 380016420459098258671441)
                    ·
                      rfl

theorem cell22_1110119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1110119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110119 prefixEnd_1110119 := by exact prefixLift 1110119
  have htrace : WordTrace (prefixWord ++ tailWord_1110119) baseStart_1110119 baseEnd_1110119 := by
    simpa [prefixWord, tailWord_1110119, baseEnd_1110119] using wordTrace_append hprefix tailTrace_1110119
  have hstable : (prefixWord ++ tailWord_1110119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110119).length < 2 ^ (prefixWord ++ tailWord_1110119).sum := by decide
  have hdescent : baseEnd_1110119 < baseStart_1110119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110134 : List Nat := [5, 1, 1, 2, 1, 2, 10]
def baseStart_1110134 : Nat := 118140960795 + 1110134 * 2 ^ 59
def prefixEnd_1110134 : Nat := 4983230072969 + 3 ^ 40 * 1110134 * 2
def baseEnd_1110134 : Nat := 14074872417246045168385

theorem tailTrace_1110134 : CollatzResearch.WordTrace tailWord_1110134 prefixEnd_1110134 14074872417246045168385 := by
  unfold tailWord_1110134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2530619585011349289863591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26993275573454392425211637 2530619585011349289863591)
  ·
    refine ⟨3795929377517023934795387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2530619585011349289863591 3795929377517023934795387)
    ·
      refine ⟨5693894066275535902193081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3795929377517023934795387 5693894066275535902193081)
      ·
        refine ⟨4270420549706651926644811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5693894066275535902193081 4270420549706651926644811)
        ·
          refine ⟨6405630824559977889967217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4270420549706651926644811 6405630824559977889967217)
          ·
            refine ⟨4804223118419983417475413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6405630824559977889967217 4804223118419983417475413)
            ·
              refine ⟨14074872417246045168385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4804223118419983417475413 14074872417246045168385)
              ·
                rfl

theorem cell22_1110134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 10].length) (baseStart_1110134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110134 prefixEnd_1110134 := by exact prefixLift 1110134
  have htrace : WordTrace (prefixWord ++ tailWord_1110134) baseStart_1110134 baseEnd_1110134 := by
    simpa [prefixWord, tailWord_1110134, baseEnd_1110134] using wordTrace_append hprefix tailTrace_1110134
  have hstable : (prefixWord ++ tailWord_1110134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110134).length < 2 ^ (prefixWord ++ tailWord_1110134).sum := by decide
  have hdescent : baseEnd_1110134 < baseStart_1110134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110194 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_1110194 : Nat := 118140960795 + 1110194 * 2 ^ 59
def prefixEnd_1110194 : Nat := 4983230072969 + 3 ^ 40 * 1110194 * 2
def baseEnd_1110194 : Nat := 380042094491823063046211

theorem tailTrace_1110194 : CollatzResearch.WordTrace tailWord_1110194 prefixEnd_1110194 380042094491823063046211 := by
  unfold tailWord_1110194
  simp only [CollatzResearch.WordTrace]
  refine ⟨10123025434991054721250409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26994734493309479256667757 10123025434991054721250409)
  ·
    refine ⟨7592269076243291040937807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10123025434991054721250409 7592269076243291040937807)
    ·
      refine ⟨11388403614364936561406711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7592269076243291040937807 11388403614364936561406711)
      ·
        refine ⟨17082605421547404842110067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11388403614364936561406711 17082605421547404842110067)
        ·
          refine ⟨25623908132321107263165101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17082605421547404842110067 25623908132321107263165101)
          ·
            refine ⟨9608965549620415223686913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25623908132321107263165101 9608965549620415223686913)
            ·
              refine ⟨7206724162215311417765185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9608965549620415223686913 7206724162215311417765185)
              ·
                refine ⟨5405043121661483563323889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7206724162215311417765185 5405043121661483563323889)
                ·
                  refine ⟨4053782341246112672492917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5405043121661483563323889 4053782341246112672492917)
                  ·
                    refine ⟨380042094491823063046211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4053782341246112672492917 380042094491823063046211)
                    ·
                      rfl

theorem cell22_1110194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_1110194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110194 prefixEnd_1110194 := by exact prefixLift 1110194
  have htrace : WordTrace (prefixWord ++ tailWord_1110194) baseStart_1110194 baseEnd_1110194 := by
    simpa [prefixWord, tailWord_1110194, baseEnd_1110194] using wordTrace_append hprefix tailTrace_1110194
  have hstable : (prefixWord ++ tailWord_1110194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110194).length < 2 ^ (prefixWord ++ tailWord_1110194).sum := by decide
  have hdescent : baseEnd_1110194 < baseStart_1110194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110226 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1110226 : Nat := 118140960795 + 1110226 * 2 ^ 59
def prefixEnd_1110226 : Nat := 4983230072969 + 3 ^ 40 * 1110226 * 2
def baseEnd_1110226 : Nat := 380053048745785646246113

theorem tailTrace_1110226 : CollatzResearch.WordTrace tailWord_1110226 prefixEnd_1110226 380053048745785646246113 := by
  unfold tailWord_1110226
  simp only [CollatzResearch.WordTrace]
  refine ⟨10123317218962072087541633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26995512583898858900111021 10123317218962072087541633)
  ·
    refine ⟨7592487914221554065656225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10123317218962072087541633 7592487914221554065656225)
    ·
      refine ⟨5694365935666165549242169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7592487914221554065656225 5694365935666165549242169)
      ·
        refine ⟨4270774451749624161931627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5694365935666165549242169 4270774451749624161931627)
        ·
          refine ⟨6406161677624436242897441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4270774451749624161931627 6406161677624436242897441)
          ·
            refine ⟨4804621258218327182173081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6406161677624436242897441 4804621258218327182173081)
            ·
              refine ⟨3603465943663745386629811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4804621258218327182173081 3603465943663745386629811)
              ·
                refine ⟨5405198915495618079944717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3603465943663745386629811 5405198915495618079944717)
                ·
                  refine ⟨2026949593310856779979269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5405198915495618079944717 2026949593310856779979269)
                  ·
                    refine ⟨380053048745785646246113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2026949593310856779979269 380053048745785646246113)
                    ·
                      rfl

theorem cell22_1110226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1110226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110226 prefixEnd_1110226 := by exact prefixLift 1110226
  have htrace : WordTrace (prefixWord ++ tailWord_1110226) baseStart_1110226 baseEnd_1110226 := by
    simpa [prefixWord, tailWord_1110226, baseEnd_1110226] using wordTrace_append hprefix tailTrace_1110226
  have hstable : (prefixWord ++ tailWord_1110226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110226).length < 2 ^ (prefixWord ++ tailWord_1110226).sum := by decide
  have hdescent : baseEnd_1110226 < baseStart_1110226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110258 : List Nat := [3, 2, 1, 3, 2, 1, 2, 4, 4]
def baseStart_1110258 : Nat := 118140960795 + 1110258 * 2 ^ 59
def prefixEnd_1110258 : Nat := 4983230072969 + 3 ^ 40 * 1110258 * 2
def baseEnd_1110258 : Nat := 126688000999916076482005

theorem tailTrace_1110258 : CollatzResearch.WordTrace tailWord_1110258 prefixEnd_1110258 126688000999916076482005 := by
  unfold tailWord_1110258
  simp only [CollatzResearch.WordTrace]
  refine ⟨10123609002933089453832857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26996290674488238543554285 10123609002933089453832857)
  ·
    refine ⟨7592706752199817090374643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10123609002933089453832857 7592706752199817090374643)
    ·
      refine ⟨11389060128299725635561965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7592706752199817090374643 11389060128299725635561965)
      ·
        refine ⟨4270897548112397113335737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11389060128299725635561965 4270897548112397113335737)
        ·
          refine ⟨3203173161084297835001803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4270897548112397113335737 3203173161084297835001803)
          ·
            refine ⟨4804759741626446752502705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3203173161084297835001803 4804759741626446752502705)
            ·
              refine ⟨3603569806219835064377029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4804759741626446752502705 3603569806219835064377029)
              ·
                refine ⟨675669338666219074570693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3603569806219835064377029 675669338666219074570693)
                ·
                  refine ⟨126688000999916076482005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 675669338666219074570693 126688000999916076482005)
                  ·
                    rfl

theorem cell22_1110258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_1110258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110258 prefixEnd_1110258 := by exact prefixLift 1110258
  have htrace : WordTrace (prefixWord ++ tailWord_1110258) baseStart_1110258 baseEnd_1110258 := by
    simpa [prefixWord, tailWord_1110258, baseEnd_1110258] using wordTrace_append hprefix tailTrace_1110258
  have hstable : (prefixWord ++ tailWord_1110258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110258).length < 2 ^ (prefixWord ++ tailWord_1110258).sum := by decide
  have hdescent : baseEnd_1110258 < baseStart_1110258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110284 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_1110284 : Nat := 118140960795 + 1110284 * 2 ^ 59
def prefixEnd_1110284 : Nat := 4983230072969 + 3 ^ 40 * 1110284 * 2
def baseEnd_1110284 : Nat := 380072903331092828295935

theorem tailTrace_1110284 : CollatzResearch.WordTrace tailWord_1110284 prefixEnd_1110284 380072903331092828295935 := by
  unfold tailWord_1110284
  simp only [CollatzResearch.WordTrace]
  refine ⟨20247692154819082127888953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26996922873092109503851937 20247692154819082127888953)
  ·
    refine ⟨15185769116114311595916715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20247692154819082127888953 15185769116114311595916715)
    ·
      refine ⟨22778653674171467393875073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15185769116114311595916715 22778653674171467393875073)
      ·
        refine ⟨17083990255628600545406305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22778653674171467393875073 17083990255628600545406305)
        ·
          refine ⟨12812992691721450409054729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17083990255628600545406305 12812992691721450409054729)
          ·
            refine ⟨9609744518791087806791047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12812992691721450409054729 9609744518791087806791047)
            ·
              refine ⟨14414616778186631710186571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9609744518791087806791047 14414616778186631710186571)
              ·
                refine ⟨21621925167279947565279857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14414616778186631710186571 21621925167279947565279857)
                ·
                  refine ⟨16216443875459960673959893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21621925167279947565279857 16216443875459960673959893)
                  ·
                    refine ⟨380072903331092828295935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16216443875459960673959893 380072903331092828295935)
                    ·
                      rfl

theorem cell22_1110284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_1110284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110284 prefixEnd_1110284 := by exact prefixLift 1110284
  have htrace : WordTrace (prefixWord ++ tailWord_1110284) baseStart_1110284 baseEnd_1110284 := by
    simpa [prefixWord, tailWord_1110284, baseEnd_1110284] using wordTrace_append hprefix tailTrace_1110284
  have hstable : (prefixWord ++ tailWord_1110284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110284).length < 2 ^ (prefixWord ++ tailWord_1110284).sum := by decide
  have hdescent : baseEnd_1110284 < baseStart_1110284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110378 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_1110378 : Nat := 118140960795 + 1110378 * 2 ^ 59
def prefixEnd_1110378 : Nat := 4983230072969 + 3 ^ 40 * 1110378 * 2
def baseEnd_1110378 : Nat := 380105081452107916445647

theorem tailTrace_1110378 : CollatzResearch.WordTrace tailWord_1110378 prefixEnd_1110378 380105081452107916445647 := by
  unfold tailWord_1110378
  simp only [CollatzResearch.WordTrace]
  refine ⟨10124703192824404577424947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26999208514198412206466525 10124703192824404577424947)
  ·
    refine ⟨15187054789236606866137421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10124703192824404577424947 15187054789236606866137421)
    ·
      refine ⟨5695145545963727574801533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15187054789236606866137421 5695145545963727574801533)
      ·
        refine ⟨2135679579736397840550575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5695145545963727574801533 2135679579736397840550575)
        ·
          refine ⟨3203519369604596760825863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2135679579736397840550575 3203519369604596760825863)
          ·
            refine ⟨4805279054406895141238795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3203519369604596760825863 4805279054406895141238795)
            ·
              refine ⟨7207918581610342711858193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4805279054406895141238795 7207918581610342711858193)
              ·
                refine ⟨5405938936207757033893645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7207918581610342711858193 5405938936207757033893645)
                ·
                  refine ⟨2027227101077908887710117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5405938936207757033893645 2027227101077908887710117)
                  ·
                    refine ⟨380105081452107916445647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2027227101077908887710117 380105081452107916445647)
                    ·
                      rfl

theorem cell22_1110378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_1110378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110378 prefixEnd_1110378 := by exact prefixLift 1110378
  have htrace : WordTrace (prefixWord ++ tailWord_1110378) baseStart_1110378 baseEnd_1110378 := by
    simpa [prefixWord, tailWord_1110378, baseEnd_1110378] using wordTrace_append hprefix tailTrace_1110378
  have hstable : (prefixWord ++ tailWord_1110378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110378).length < 2 ^ (prefixWord ++ tailWord_1110378).sum := by decide
  have hdescent : baseEnd_1110378 < baseStart_1110378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110408 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 4, 3]
def baseStart_1110408 : Nat := 118140960795 + 1110408 * 2 ^ 59
def prefixEnd_1110408 : Nat := 4983230072969 + 3 ^ 40 * 1110408 * 2
def baseEnd_1110408 : Nat := 380115351065197838195555

theorem tailTrace_1110408 : CollatzResearch.WordTrace tailWord_1110408 prefixEnd_1110408 380115351065197838195555 := by
  unfold tailWord_1110408
  simp only [CollatzResearch.WordTrace]
  refine ⟨20249953480594466716645939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26999937974125955622194585 20249953480594466716645939)
  ·
    refine ⟨30374930220891700074968909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20249953480594466716645939 30374930220891700074968909)
    ·
      refine ⟨11390598832834387528113341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30374930220891700074968909 11390598832834387528113341)
      ·
        refine ⟨4271474562312895323042503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11390598832834387528113341 4271474562312895323042503)
        ·
          refine ⟨6407211843469342984563755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4271474562312895323042503 6407211843469342984563755)
          ·
            refine ⟨9610817765204014476845633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6407211843469342984563755 9610817765204014476845633)
            ·
              refine ⟨7208113323903010857634225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9610817765204014476845633 7208113323903010857634225)
              ·
                refine ⟨5406084992927258143225669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7208113323903010857634225 5406084992927258143225669)
                ·
                  refine ⟨1013640936173860901854813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5406084992927258143225669 1013640936173860901854813)
                  ·
                    refine ⟨380115351065197838195555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1013640936173860901854813 380115351065197838195555)
                    ·
                      rfl

theorem cell22_1110408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_1110408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110408 prefixEnd_1110408 := by exact prefixLift 1110408
  have htrace : WordTrace (prefixWord ++ tailWord_1110408) baseStart_1110408 baseEnd_1110408 := by
    simpa [prefixWord, tailWord_1110408, baseEnd_1110408] using wordTrace_append hprefix tailTrace_1110408
  have hstable : (prefixWord ++ tailWord_1110408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110408).length < 2 ^ (prefixWord ++ tailWord_1110408).sum := by decide
  have hdescent : baseEnd_1110408 < baseStart_1110408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110481 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 4, 5]
def baseStart_1110481 : Nat := 118140960795 + 1110481 * 2 ^ 59
def prefixEnd_1110481 : Nat := 4983230072969 + 3 ^ 40 * 1110481 * 2
def baseEnd_1110481 : Nat := 380140340457049981120331

theorem tailTrace_1110481 : CollatzResearch.WordTrace tailWord_1110481 prefixEnd_1110481 380140340457049981120331 := by
  unfold tailWord_1110481
  simp only [CollatzResearch.WordTrace]
  refine ⟨40502569489924466900699297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27001712993282977933799531 40502569489924466900699297)
  ·
    refine ⟨30376927117443350175524473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40502569489924466900699297 30376927117443350175524473)
    ·
      refine ⟨22782695338082512631643355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30376927117443350175524473 22782695338082512631643355)
      ·
        refine ⟨34174043007123768947465033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22782695338082512631643355 34174043007123768947465033)
        ·
          refine ⟨25630532255342826710598775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34174043007123768947465033 25630532255342826710598775)
          ·
            refine ⟨38445798383014240065898163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25630532255342826710598775 38445798383014240065898163)
            ·
              refine ⟨57668697574521360098847245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38445798383014240065898163 57668697574521360098847245)
              ·
                refine ⟨21625761590445510037067717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57668697574521360098847245 21625761590445510037067717)
                ·
                  refine ⟨4054830298208533131950197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21625761590445510037067717 4054830298208533131950197)
                  ·
                    refine ⟨380140340457049981120331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4054830298208533131950197 380140340457049981120331)
                    ·
                      rfl

theorem cell22_1110481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_1110481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110481 prefixEnd_1110481 := by exact prefixLift 1110481
  have htrace : WordTrace (prefixWord ++ tailWord_1110481) baseStart_1110481 baseEnd_1110481 := by
    simpa [prefixWord, tailWord_1110481, baseEnd_1110481] using wordTrace_append hprefix tailTrace_1110481
  have hstable : (prefixWord ++ tailWord_1110481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110481).length < 2 ^ (prefixWord ++ tailWord_1110481).sum := by decide
  have hdescent : baseEnd_1110481 < baseStart_1110481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110511 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 8]
def baseStart_1110511 : Nat := 118140960795 + 1110511 * 2 ^ 59
def prefixEnd_1110511 : Nat := 4983230072969 + 3 ^ 40 * 1110511 * 2
def baseEnd_1110511 : Nat := 126716870023379967623413

theorem tailTrace_1110511 : CollatzResearch.WordTrace tailWord_1110511 prefixEnd_1110511 126716870023379967623413 := by
  unfold tailWord_1110511
  simp only [CollatzResearch.WordTrace]
  refine ⟨40503663679815782024291387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27002442453210521349527591 40503663679815782024291387)
  ·
    refine ⟨60755495519723673036437081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40503663679815782024291387 60755495519723673036437081)
    ·
      refine ⟨45566621639792754777327811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60755495519723673036437081 45566621639792754777327811)
      ·
        refine ⟨68349932459689132165991717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45566621639792754777327811 68349932459689132165991717)
        ·
          refine ⟨12815612336191712281123447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68349932459689132165991717 12815612336191712281123447)
          ·
            refine ⟨19223418504287568421685171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12815612336191712281123447 19223418504287568421685171)
            ·
              refine ⟨28835127756431352632527757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19223418504287568421685171 28835127756431352632527757)
              ·
                refine ⟨10813172908661757237197909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28835127756431352632527757 10813172908661757237197909)
                ·
                  refine ⟨126716870023379967623413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10813172908661757237197909 126716870023379967623413)
                  ·
                    rfl

theorem cell22_1110511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 8].length) (baseStart_1110511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110511 prefixEnd_1110511 := by exact prefixLift 1110511
  have htrace : WordTrace (prefixWord ++ tailWord_1110511) baseStart_1110511 baseEnd_1110511 := by
    simpa [prefixWord, tailWord_1110511, baseEnd_1110511] using wordTrace_append hprefix tailTrace_1110511
  have hstable : (prefixWord ++ tailWord_1110511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110511).length < 2 ^ (prefixWord ++ tailWord_1110511).sum := by decide
  have hdescent : baseEnd_1110511 < baseStart_1110511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110513 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 3, 4]
def baseStart_1110513 : Nat := 118140960795 + 1110513 * 2 ^ 59
def prefixEnd_1110513 : Nat := 4983230072969 + 3 ^ 40 * 1110513 * 2
def baseEnd_1110513 : Nat := 380151294711012564320233

theorem tailTrace_1110513 : CollatzResearch.WordTrace tailWord_1110513 prefixEnd_1110513 380151294711012564320233 := by
  unfold tailWord_1110513
  simp only [CollatzResearch.WordTrace]
  refine ⟨40503736625808536365864193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27002491083872357577242795 40503736625808536365864193)
  ·
    refine ⟨30377802469356402274398145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40503736625808536365864193 30377802469356402274398145)
    ·
      refine ⟨22783351852017301705798609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30377802469356402274398145 22783351852017301705798609)
      ·
        refine ⟨17087513889012976279348957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22783351852017301705798609 17087513889012976279348957)
        ·
          refine ⟨6407817708379866104755859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17087513889012976279348957 6407817708379866104755859)
          ·
            refine ⟨9611726562569799157133789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6407817708379866104755859 9611726562569799157133789)
            ·
              refine ⟨3604397460963674683925171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9611726562569799157133789 3604397460963674683925171)
              ·
                refine ⟨5406596191445512025887757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3604397460963674683925171 5406596191445512025887757)
                ·
                  refine ⟨2027473571792067009707909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5406596191445512025887757 2027473571792067009707909)
                  ·
                    refine ⟨380151294711012564320233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2027473571792067009707909 380151294711012564320233)
                    ·
                      rfl

theorem cell22_1110513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_1110513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110513 prefixEnd_1110513 := by exact prefixLift 1110513
  have htrace : WordTrace (prefixWord ++ tailWord_1110513) baseStart_1110513 baseEnd_1110513 := by
    simpa [prefixWord, tailWord_1110513, baseEnd_1110513] using wordTrace_append hprefix tailTrace_1110513
  have hstable : (prefixWord ++ tailWord_1110513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110513).length < 2 ^ (prefixWord ++ tailWord_1110513).sum := by decide
  have hdescent : baseEnd_1110513 < baseStart_1110513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110534 : List Nat := [6, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1110534 : Nat := 118140960795 + 1110534 * 2 ^ 59
def prefixEnd_1110534 : Nat := 4983230072969 + 3 ^ 40 * 1110534 * 2
def baseEnd_1110534 : Nat := 126719494480058503181723

theorem tailTrace_1110534 : CollatzResearch.WordTrace tailWord_1110534 prefixEnd_1110534 126719494480058503181723 := by
  unfold tailWord_1110534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265765704960389279761833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27003001705821637968252437 1265765704960389279761833)
  ·
    refine ⟨949324278720291959821375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1265765704960389279761833 949324278720291959821375)
    ·
      refine ⟨1423986418080437939732063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 949324278720291959821375 1423986418080437939732063)
      ·
        refine ⟨2135979627120656909598095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1423986418080437939732063 2135979627120656909598095)
        ·
          refine ⟨3203969440680985364397143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2135979627120656909598095 3203969440680985364397143)
          ·
            refine ⟨4805954161021478046595715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3203969440680985364397143 4805954161021478046595715)
            ·
              refine ⟨7208931241532217069893573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4805954161021478046595715 7208931241532217069893573)
              ·
                refine ⟨1351674607787290700605045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7208931241532217069893573 1351674607787290700605045)
                ·
                  refine ⟨126719494480058503181723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1351674607787290700605045 126719494480058503181723)
                  ·
                    rfl

theorem cell22_1110534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1110534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110534 prefixEnd_1110534 := by exact prefixLift 1110534
  have htrace : WordTrace (prefixWord ++ tailWord_1110534) baseStart_1110534 baseEnd_1110534 := by
    simpa [prefixWord, tailWord_1110534, baseEnd_1110534] using wordTrace_append hprefix tailTrace_1110534
  have hstable : (prefixWord ++ tailWord_1110534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110534).length < 2 ^ (prefixWord ++ tailWord_1110534).sum := by decide
  have hdescent : baseEnd_1110534 < baseStart_1110534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110774 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_1110774 : Nat := 118140960795 + 1110774 * 2 ^ 59
def prefixEnd_1110774 : Nat := 4983230072969 + 3 ^ 40 * 1110774 * 2
def baseEnd_1110774 : Nat := 380240640344894883544433

theorem tailTrace_1110774 : CollatzResearch.WordTrace tailWord_1110774 prefixEnd_1110774 380240640344894883544433 := by
  unfold tailWord_1110774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2532078504866436121319711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27008837385241985294076917 2532078504866436121319711)
  ·
    refine ⟨3798117757299654181979567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2532078504866436121319711 3798117757299654181979567)
    ·
      refine ⟨5697176635949481272969351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3798117757299654181979567 5697176635949481272969351)
      ·
        refine ⟨8545764953924221909454027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5697176635949481272969351 8545764953924221909454027)
        ·
          refine ⟨12818647430886332864181041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8545764953924221909454027 12818647430886332864181041)
          ·
            refine ⟨9613985573164749648135781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12818647430886332864181041 9613985573164749648135781)
            ·
              refine ⟨1802622294968390559025459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9613985573164749648135781 1802622294968390559025459)
              ·
                refine ⟨2703933442452585838538189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802622294968390559025459 2703933442452585838538189)
                ·
                  refine ⟨1013975040919719689451821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2703933442452585838538189 1013975040919719689451821)
                  ·
                    refine ⟨380240640344894883544433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1013975040919719689451821 380240640344894883544433)
                    ·
                      rfl

theorem cell22_1110774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_1110774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110774 prefixEnd_1110774 := by exact prefixLift 1110774
  have htrace : WordTrace (prefixWord ++ tailWord_1110774) baseStart_1110774 baseEnd_1110774 := by
    simpa [prefixWord, tailWord_1110774, baseEnd_1110774] using wordTrace_append hprefix tailTrace_1110774
  have hstable : (prefixWord ++ tailWord_1110774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110774).length < 2 ^ (prefixWord ++ tailWord_1110774).sum := by decide
  have hdescent : baseEnd_1110774 < baseStart_1110774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110817 : List Nat := [1, 2, 3, 2, 1, 2, 1, 5, 1, 4]
def baseStart_1110817 : Nat := 118140960795 + 1110817 * 2 ^ 59
def prefixEnd_1110817 : Nat := 4983230072969 + 3 ^ 40 * 1110817 * 2
def baseEnd_1110817 : Nat := 380255360123657104719301

theorem tailTrace_1110817 : CollatzResearch.WordTrace tailWord_1110817 prefixEnd_1110817 380255360123657104719301 := by
  unfold tailWord_1110817
  simp only [CollatzResearch.WordTrace]
  refine ⟨40514824416707196284930705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27009882944471464189953803 40514824416707196284930705)
  ·
    refine ⟨30386118312530397213698029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40514824416707196284930705 30386118312530397213698029)
    ·
      refine ⟨11394794367198898955136761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30386118312530397213698029 11394794367198898955136761)
      ·
        refine ⟨8546095775399174216352571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11394794367198898955136761 8546095775399174216352571)
        ·
          refine ⟨12819143663098761324528857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8546095775399174216352571 12819143663098761324528857)
          ·
            refine ⟨9614357747324070993396643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12819143663098761324528857 9614357747324070993396643)
            ·
              refine ⟨14421536620986106490094965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9614357747324070993396643 14421536620986106490094965)
              ·
                refine ⟨1352019058217447483446403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14421536620986106490094965 1352019058217447483446403)
                ·
                  refine ⟨2028028587326171225169605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352019058217447483446403 2028028587326171225169605)
                  ·
                    refine ⟨380255360123657104719301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2028028587326171225169605 380255360123657104719301)
                    ·
                      rfl

theorem cell22_1110817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_1110817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110817 prefixEnd_1110817 := by exact prefixLift 1110817
  have htrace : WordTrace (prefixWord ++ tailWord_1110817) baseStart_1110817 baseEnd_1110817 := by
    simpa [prefixWord, tailWord_1110817, baseEnd_1110817] using wordTrace_append hprefix tailTrace_1110817
  have hstable : (prefixWord ++ tailWord_1110817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110817).length < 2 ^ (prefixWord ++ tailWord_1110817).sum := by decide
  have hdescent : baseEnd_1110817 < baseStart_1110817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110832 : List Nat := [2, 1, 1, 1, 2, 2, 1, 8, 4]
def baseStart_1110832 : Nat := 118140960795 + 1110832 * 2 ^ 59
def prefixEnd_1110832 : Nat := 4983230072969 + 3 ^ 40 * 1110832 * 2
def baseEnd_1110832 : Nat := 126753498310067355198085

theorem tailTrace_1110832 : CollatzResearch.WordTrace tailWord_1110832 prefixEnd_1110832 126753498310067355198085 := by
  unfold tailWord_1110832
  simp only [CollatzResearch.WordTrace]
  refine ⟨20257685755826426923363375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27010247674435235897817833 20257685755826426923363375)
  ·
    refine ⟨30386528633739640385045063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20257685755826426923363375 30386528633739640385045063)
    ·
      refine ⟨45579792950609460577567595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30386528633739640385045063 45579792950609460577567595)
      ·
        refine ⟨68369689425914190866351393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45579792950609460577567595 68369689425914190866351393)
        ·
          refine ⟨51277267069435643149763545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68369689425914190866351393 51277267069435643149763545)
          ·
            refine ⟨38457950302076732362322659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51277267069435643149763545 38457950302076732362322659)
            ·
              refine ⟨57686925453115098543483989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38457950302076732362322659 57686925453115098543483989)
              ·
                refine ⟨676018657653692561056453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 57686925453115098543483989 676018657653692561056453)
                ·
                  refine ⟨126753498310067355198085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 676018657653692561056453 126753498310067355198085)
                  ·
                    rfl

theorem cell22_1110832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 4].length) (baseStart_1110832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110832 prefixEnd_1110832 := by exact prefixLift 1110832
  have htrace : WordTrace (prefixWord ++ tailWord_1110832) baseStart_1110832 baseEnd_1110832 := by
    simpa [prefixWord, tailWord_1110832, baseEnd_1110832] using wordTrace_append hprefix tailTrace_1110832
  have hstable : (prefixWord ++ tailWord_1110832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110832).length < 2 ^ (prefixWord ++ tailWord_1110832).sum := by decide
  have hdescent : baseEnd_1110832 < baseStart_1110832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110838 : List Nat := [5, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_1110838 : Nat := 118140960795 + 1110838 * 2 ^ 59
def prefixEnd_1110838 : Nat := 4983230072969 + 3 ^ 40 * 1110838 * 2
def baseEnd_1110838 : Nat := 126754182950940016648079

theorem tailTrace_1110838 : CollatzResearch.WordTrace tailWord_1110838 prefixEnd_1110838 126754182950940016648079 := by
  unfold tailWord_1110838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2532224396851944804465323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27010393566420744580963445 2532224396851944804465323)
  ·
    refine ⟨3798336595277917206697985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2532224396851944804465323 3798336595277917206697985)
    ·
      refine ⟨2848752446458437905023489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3798336595277917206697985 2848752446458437905023489)
      ·
        refine ⟨2136564334843828428767617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2848752446458437905023489 2136564334843828428767617)
        ·
          refine ⟨1602423251132871321575713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2136564334843828428767617 1602423251132871321575713)
          ·
            refine ⟨1201817438349653491181785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1602423251132871321575713 1201817438349653491181785)
            ·
              refine ⟨901363078762240118386339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1201817438349653491181785 901363078762240118386339)
              ·
                refine ⟨1352044618143360177579509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 901363078762240118386339 1352044618143360177579509)
                ·
                  refine ⟨126754182950940016648079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1352044618143360177579509 126754182950940016648079)
                  ·
                    rfl

theorem cell22_1110838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_1110838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110838 prefixEnd_1110838 := by exact prefixLift 1110838
  have htrace : WordTrace (prefixWord ++ tailWord_1110838) baseStart_1110838 baseEnd_1110838 := by
    simpa [prefixWord, tailWord_1110838, baseEnd_1110838] using wordTrace_append hprefix tailTrace_1110838
  have hstable : (prefixWord ++ tailWord_1110838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110838).length < 2 ^ (prefixWord ++ tailWord_1110838).sum := by decide
  have hdescent : baseEnd_1110838 < baseStart_1110838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110967 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 6]
def baseStart_1110967 : Nat := 118140960795 + 1110967 * 2 ^ 59
def prefixEnd_1110967 : Nat := 4983230072969 + 3 ^ 40 * 1110967 * 2
def baseEnd_1110967 : Nat := 126768902729702237822947

theorem tailTrace_1110967 : CollatzResearch.WordTrace tailWord_1110967 prefixEnd_1110967 126768902729702237822947 := by
  unfold tailWord_1110967
  simp only [CollatzResearch.WordTrace]
  refine ⟨40520295366163771902891155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27013530244109181268594103 40520295366163771902891155)
  ·
    refine ⟨60780443049245657854336733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40520295366163771902891155 60780443049245657854336733)
    ·
      refine ⟨22792666143467121695376275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60780443049245657854336733 22792666143467121695376275)
      ·
        refine ⟨34188999215200682543064413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22792666143467121695376275 34188999215200682543064413)
        ·
          refine ⟨12820874705700255953649155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34188999215200682543064413 12820874705700255953649155)
          ·
            refine ⟨19231312058550383930473733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12820874705700255953649155 19231312058550383930473733)
            ·
              refine ⟨3605871010978196986963825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19231312058550383930473733 3605871010978196986963825)
              ·
                refine ⟨2704403258233647740222869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3605871010978196986963825 2704403258233647740222869)
                ·
                  refine ⟨126768902729702237822947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2704403258233647740222869 126768902729702237822947)
                  ·
                    rfl

theorem cell22_1110967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 6].length) (baseStart_1110967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110967 prefixEnd_1110967 := by exact prefixLift 1110967
  have htrace : WordTrace (prefixWord ++ tailWord_1110967) baseStart_1110967 baseEnd_1110967 := by
    simpa [prefixWord, tailWord_1110967, baseEnd_1110967] using wordTrace_append hprefix tailTrace_1110967
  have hstable : (prefixWord ++ tailWord_1110967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110967).length < 2 ^ (prefixWord ++ tailWord_1110967).sum := by decide
  have hdescent : baseEnd_1110967 < baseStart_1110967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1110969 : List Nat := [1, 2, 1, 4, 2, 2, 1, 4, 1, 4]
def baseStart_1110969 : Nat := 118140960795 + 1110969 * 2 ^ 59
def prefixEnd_1110969 : Nat := 4983230072969 + 3 ^ 40 * 1110969 * 2
def baseEnd_1110969 : Nat := 380307392829979374918835

theorem tailTrace_1110969 : CollatzResearch.WordTrace tailWord_1110969 prefixEnd_1110969 380307392829979374918835 := by
  unfold tailWord_1110969
  simp only [CollatzResearch.WordTrace]
  refine ⟨40520368312156526244463961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27013578874771017496309307 40520368312156526244463961)
  ·
    refine ⟨30390276234117394683347971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40520368312156526244463961 30390276234117394683347971)
    ·
      refine ⟨45585414351176092025021957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30390276234117394683347971 45585414351176092025021957)
      ·
        refine ⟨8547265190845517254691617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45585414351176092025021957 8547265190845517254691617)
        ·
          refine ⟨6410448893134137941018713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8547265190845517254691617 6410448893134137941018713)
          ·
            refine ⟨4807836669850603455764035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6410448893134137941018713 4807836669850603455764035)
            ·
              refine ⟨7211755004775905183646053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4807836669850603455764035 7211755004775905183646053)
              ·
                refine ⟨1352204063395482221933635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7211755004775905183646053 1352204063395482221933635)
                ·
                  refine ⟨2028306095093223332900453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352204063395482221933635 2028306095093223332900453)
                  ·
                    refine ⟨380307392829979374918835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2028306095093223332900453 380307392829979374918835)
                    ·
                      rfl

theorem cell22_1110969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_1110969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1110969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1110969 prefixEnd_1110969 := by exact prefixLift 1110969
  have htrace : WordTrace (prefixWord ++ tailWord_1110969) baseStart_1110969 baseEnd_1110969 := by
    simpa [prefixWord, tailWord_1110969, baseEnd_1110969] using wordTrace_append hprefix tailTrace_1110969
  have hstable : (prefixWord ++ tailWord_1110969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1110969).length < 2 ^ (prefixWord ++ tailWord_1110969).sum := by decide
  have hdescent : baseEnd_1110969 < baseStart_1110969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1110969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111046 : List Nat := [6, 2, 1, 13]
def baseStart_1111046 : Nat := 118140960795 + 1111046 * 2 ^ 59
def prefixEnd_1111046 : Nat := 4983230072969 + 3 ^ 40 * 1111046 * 2
def baseEnd_1111046 : Nat := 521719823736045049031

theorem tailTrace_1111046 : CollatzResearch.WordTrace tailWord_1111046 prefixEnd_1111046 521719823736045049031 := by
  unfold tailWord_1111046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1266349272902424012344281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27015451155251712263344661 1266349272902424012344281)
  ·
    refine ⟨949761954676818009258211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1266349272902424012344281 949761954676818009258211)
    ·
      refine ⟨1424642932015227013887317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 949761954676818009258211 1424642932015227013887317)
      ·
        refine ⟨521719823736045049031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1424642932015227013887317 521719823736045049031)
        ·
          rfl

theorem cell22_1111046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 13].length) (baseStart_1111046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111046 prefixEnd_1111046 := by exact prefixLift 1111046
  have htrace : WordTrace (prefixWord ++ tailWord_1111046) baseStart_1111046 baseEnd_1111046 := by
    simpa [prefixWord, tailWord_1111046, baseEnd_1111046] using wordTrace_append hprefix tailTrace_1111046
  have hstable : (prefixWord ++ tailWord_1111046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111046).length < 2 ^ (prefixWord ++ tailWord_1111046).sum := by decide
  have hdescent : baseEnd_1111046 < baseStart_1111046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111057 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 7]
def baseStart_1111057 : Nat := 118140960795 + 1111057 * 2 ^ 59
def prefixEnd_1111057 : Nat := 4983230072969 + 3 ^ 40 * 1111057 * 2
def baseEnd_1111057 : Nat := 126779172342792159572855

theorem tailTrace_1111057 : CollatzResearch.WordTrace tailWord_1111057 prefixEnd_1111057 126779172342792159572855 := by
  unfold tailWord_1111057
  simp only [CollatzResearch.WordTrace]
  refine ⟨40523577935837717273667425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27015718623891811515778283 40523577935837717273667425)
  ·
    refine ⟨30392683451878287955250569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40523577935837717273667425 30392683451878287955250569)
    ·
      refine ⟨22794512588908715966437927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30392683451878287955250569 22794512588908715966437927)
      ·
        refine ⟨34191768883363073949656891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22794512588908715966437927 34191768883363073949656891)
        ·
          refine ⟨51287653325044610924485337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34191768883363073949656891 51287653325044610924485337)
          ·
            refine ⟨38465739993783458193364003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51287653325044610924485337 38465739993783458193364003)
            ·
              refine ⟨57698609990675187290046005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38465739993783458193364003 57698609990675187290046005)
              ·
                refine ⟨5409244686625798808441813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57698609990675187290046005 5409244686625798808441813)
                ·
                  refine ⟨126779172342792159572855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5409244686625798808441813 126779172342792159572855)
                  ·
                    rfl

theorem cell22_1111057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_1111057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111057 prefixEnd_1111057 := by exact prefixLift 1111057
  have htrace : WordTrace (prefixWord ++ tailWord_1111057) baseStart_1111057 baseEnd_1111057 := by
    simpa [prefixWord, tailWord_1111057, baseEnd_1111057] using wordTrace_append hprefix tailTrace_1111057
  have hstable : (prefixWord ++ tailWord_1111057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111057).length < 2 ^ (prefixWord ++ tailWord_1111057).sum := by decide
  have hdescent : baseEnd_1111057 < baseStart_1111057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111138 : List Nat := [3, 3, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1111138 : Nat := 118140960795 + 1111138 * 2 ^ 59
def prefixEnd_1111138 : Nat := 4983230072969 + 3 ^ 40 * 1111138 * 2
def baseEnd_1111138 : Nat := 380365244983719267443317

theorem tailTrace_1111138 : CollatzResearch.WordTrace tailWord_1111138 prefixEnd_1111138 380365244983719267443317 := by
  unfold tailWord_1111138
  simp only [CollatzResearch.WordTrace]
  refine ⟨10131633062136067026841517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27017688165696178738244045 10131633062136067026841517)
  ·
    refine ⟨3799362398301025135065569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10131633062136067026841517 3799362398301025135065569)
    ·
      refine ⟨2849521798725768851299177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3799362398301025135065569 2849521798725768851299177)
      ·
        refine ⟨2137141349044326638474383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2849521798725768851299177 2137141349044326638474383)
        ·
          refine ⟨3205712023566489957711575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137141349044326638474383 3205712023566489957711575)
          ·
            refine ⟨4808568035349734936567363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3205712023566489957711575 4808568035349734936567363)
            ·
              refine ⟨7212852053024602404851045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4808568035349734936567363 7212852053024602404851045)
              ·
                refine ⟨1352409759942112950909571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7212852053024602404851045 1352409759942112950909571)
                ·
                  refine ⟨2028614639913169426364357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352409759942112950909571 2028614639913169426364357)
                  ·
                    refine ⟨380365244983719267443317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2028614639913169426364357 380365244983719267443317)
                    ·
                      rfl

theorem cell22_1111138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1111138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111138 prefixEnd_1111138 := by exact prefixLift 1111138
  have htrace : WordTrace (prefixWord ++ tailWord_1111138) baseStart_1111138 baseEnd_1111138 := by
    simpa [prefixWord, tailWord_1111138, baseEnd_1111138] using wordTrace_append hprefix tailTrace_1111138
  have hstable : (prefixWord ++ tailWord_1111138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111138).length < 2 ^ (prefixWord ++ tailWord_1111138).sum := by decide
  have hdescent : baseEnd_1111138 < baseStart_1111138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111455 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 4, 3]
def baseStart_1111455 : Nat := 118140960795 + 1111455 * 2 ^ 59
def prefixEnd_1111455 : Nat := 4983230072969 + 3 ^ 40 * 1111455 * 2
def baseEnd_1111455 : Nat := 380473760562036107267345

theorem tailTrace_1111455 : CollatzResearch.WordTrace tailWord_1111455 prefixEnd_1111455 380473760562036107267345 := by
  unfold tailWord_1111455
  simp only [CollatzResearch.WordTrace]
  refine ⟨40538094188395831246655819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27025396125597220831103879 40538094188395831246655819)
  ·
    refine ⟨60807141282593746869983729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40538094188395831246655819 60807141282593746869983729)
    ·
      refine ⟨45605355961945310152487797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60807141282593746869983729 45605355961945310152487797)
      ·
        refine ⟨4275502121432372826795731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45605355961945310152487797 4275502121432372826795731)
        ·
          refine ⟨6413253182148559240193597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4275502121432372826795731 6413253182148559240193597)
          ·
            refine ⟨2404969943305709715072599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6413253182148559240193597 2404969943305709715072599)
            ·
              refine ⟨3607454914958564572608899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2404969943305709715072599 3607454914958564572608899)
              ·
                refine ⟨5411182372437846858913349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3607454914958564572608899 5411182372437846858913349)
                ·
                  refine ⟨1014596694832096286046253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5411182372437846858913349 1014596694832096286046253)
                  ·
                    refine ⟨380473760562036107267345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1014596694832096286046253 380473760562036107267345)
                    ·
                      rfl

theorem cell22_1111455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 3].length) (baseStart_1111455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111455 prefixEnd_1111455 := by exact prefixLift 1111455
  have htrace : WordTrace (prefixWord ++ tailWord_1111455) baseStart_1111455 baseEnd_1111455 := by
    simpa [prefixWord, tailWord_1111455, baseEnd_1111455] using wordTrace_append hprefix tailTrace_1111455
  have hstable : (prefixWord ++ tailWord_1111455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111455).length < 2 ^ (prefixWord ++ tailWord_1111455).sum := by decide
  have hdescent : baseEnd_1111455 < baseStart_1111455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111513 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 7]
def baseStart_1111513 : Nat := 118140960795 + 1111513 * 2 ^ 59
def prefixEnd_1111513 : Nat := 4983230072969 + 3 ^ 40 * 1111513 * 2
def baseEnd_1111513 : Nat := 126831205049114429772389

theorem tailTrace_1111513 : CollatzResearch.WordTrace tailWord_1111513 prefixEnd_1111513 126831205049114429772389 := by
  unfold tailWord_1111513
  simp only [CollatzResearch.WordTrace]
  refine ⟨40540209622185707152267193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27026806414790471434844795 40540209622185707152267193)
  ·
    refine ⟨30405157216639280364200395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40540209622185707152267193 30405157216639280364200395)
    ·
      refine ⟨45607735824958920546300593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30405157216639280364200395 45607735824958920546300593)
      ·
        refine ⟨34205801868719190409725445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45607735824958920546300593 34205801868719190409725445)
        ·
          refine ⟨6413587850384848201823521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34205801868719190409725445 6413587850384848201823521)
          ·
            refine ⟨4810190887788636151367641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6413587850384848201823521 4810190887788636151367641)
            ·
              refine ⟨3607643165841477113525731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4810190887788636151367641 3607643165841477113525731)
              ·
                refine ⟨5411464748762215670288597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3607643165841477113525731 5411464748762215670288597)
                ·
                  refine ⟨126831205049114429772389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5411464748762215670288597 126831205049114429772389)
                  ·
                    rfl

theorem cell22_1111513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 7].length) (baseStart_1111513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111513 prefixEnd_1111513 := by exact prefixLift 1111513
  have htrace : WordTrace (prefixWord ++ tailWord_1111513) baseStart_1111513 baseEnd_1111513 := by
    simpa [prefixWord, tailWord_1111513, baseEnd_1111513] using wordTrace_append hprefix tailTrace_1111513
  have hstable : (prefixWord ++ tailWord_1111513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111513).length < 2 ^ (prefixWord ++ tailWord_1111513).sum := by decide
  have hdescent : baseEnd_1111513 < baseStart_1111513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111517 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1111517 : Nat := 118140960795 + 1111517 * 2 ^ 59
def prefixEnd_1111517 : Nat := 4983230072969 + 3 ^ 40 * 1111517 * 2
def baseEnd_1111517 : Nat := 380494984429088612217155

theorem tailTrace_1111517 : CollatzResearch.WordTrace tailWord_1111517 prefixEnd_1111517 380494984429088612217155 := by
  unfold tailWord_1111517
  simp only [CollatzResearch.WordTrace]
  refine ⟨40540355514171215835412805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27026903676114143890275203 40540355514171215835412805)
  ·
    refine ⟨7601316658907102969139901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40540355514171215835412805 7601316658907102969139901)
    ·
      refine ⟨2850493747090163613427463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7601316658907102969139901 2850493747090163613427463)
      ·
        refine ⟨4275740620635245420141195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2850493747090163613427463 4275740620635245420141195)
        ·
          refine ⟨6413610930952868130211793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4275740620635245420141195 6413610930952868130211793)
          ·
            refine ⟨4810208198214651097658845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6413610930952868130211793 4810208198214651097658845)
            ·
              refine ⟨1803828074330494161622067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4810208198214651097658845 1803828074330494161622067)
              ·
                refine ⟨2705742111495741242433101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803828074330494161622067 2705742111495741242433101)
                ·
                  refine ⟨1014653291810902965912413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2705742111495741242433101 1014653291810902965912413)
                  ·
                    refine ⟨380494984429088612217155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1014653291810902965912413 380494984429088612217155)
                    ·
                      rfl

theorem cell22_1111517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1111517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111517 prefixEnd_1111517 := by exact prefixLift 1111517
  have htrace : WordTrace (prefixWord ++ tailWord_1111517) baseStart_1111517 baseEnd_1111517 := by
    simpa [prefixWord, tailWord_1111517, baseEnd_1111517] using wordTrace_append hprefix tailTrace_1111517
  have hstable : (prefixWord ++ tailWord_1111517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111517).length < 2 ^ (prefixWord ++ tailWord_1111517).sum := by decide
  have hdescent : baseEnd_1111517 < baseStart_1111517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111528 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1111528 : Nat := 118140960795 + 1111528 * 2 ^ 59
def prefixEnd_1111528 : Nat := 4983230072969 + 3 ^ 40 * 1111528 * 2
def baseEnd_1111528 : Nat := 380498749953888250192121

theorem tailTrace_1111528 : CollatzResearch.WordTrace tailWord_1111528 prefixEnd_1111528 380498749953888250192121 := by
  unfold tailWord_1111528
  simp only [CollatzResearch.WordTrace]
  refine ⟨20270378358565682357031619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27027171144754243142708825 20270378358565682357031619)
  ·
    refine ⟨30405567537848523535547429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20270378358565682357031619 30405567537848523535547429)
    ·
      refine ⟨5701043913346598162915143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30405567537848523535547429 5701043913346598162915143)
      ·
        refine ⟨8551565870019897244372715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5701043913346598162915143 8551565870019897244372715)
        ·
          refine ⟨12827348805029845866559073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8551565870019897244372715 12827348805029845866559073)
          ·
            refine ⟨9620511603772384399919305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12827348805029845866559073 9620511603772384399919305)
            ·
              refine ⟨7215383702829288299939479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9620511603772384399919305 7215383702829288299939479)
              ·
                refine ⟨10823075554243932449909219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7215383702829288299939479 10823075554243932449909219)
                ·
                  refine ⟨16234613331365898674863829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10823075554243932449909219 16234613331365898674863829)
                  ·
                    refine ⟨380498749953888250192121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16234613331365898674863829 380498749953888250192121)
                    ·
                      rfl

theorem cell22_1111528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1111528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111528 prefixEnd_1111528 := by exact prefixLift 1111528
  have htrace : WordTrace (prefixWord ++ tailWord_1111528) baseStart_1111528 baseEnd_1111528 := by
    simpa [prefixWord, tailWord_1111528, baseEnd_1111528] using wordTrace_append hprefix tailTrace_1111528
  have hstable : (prefixWord ++ tailWord_1111528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111528).length < 2 ^ (prefixWord ++ tailWord_1111528).sum := by decide
  have hdescent : baseEnd_1111528 < baseStart_1111528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111560 : List Nat := [2, 1, 3, 2, 1, 1, 2, 5, 1, 4]
def baseStart_1111560 : Nat := 118140960795 + 1111560 * 2 ^ 59
def prefixEnd_1111560 : Nat := 4983230072969 + 3 ^ 40 * 1111560 * 2
def baseEnd_1111560 : Nat := 380509704207850833392023

theorem tailTrace_1111560 : CollatzResearch.WordTrace tailWord_1111560 prefixEnd_1111560 380509704207850833392023 := by
  unfold tailWord_1111560
  simp only [CollatzResearch.WordTrace]
  refine ⟨20270961926507717089614067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27027949235343622786152089 20270961926507717089614067)
  ·
    refine ⟨30406442889761575634421101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20270961926507717089614067 30406442889761575634421101)
    ·
      refine ⟨11402416083660590862907913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30406442889761575634421101 11402416083660590862907913)
      ·
        refine ⟨8551812062745443147180935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11402416083660590862907913 8551812062745443147180935)
        ·
          refine ⟨12827718094118164720771403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8551812062745443147180935 12827718094118164720771403)
          ·
            refine ⟨19241577141177247081157105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12827718094118164720771403 19241577141177247081157105)
            ·
              refine ⟨14431182855882935310867829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19241577141177247081157105 14431182855882935310867829)
              ·
                refine ⟨1352923392739025185393859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14431182855882935310867829 1352923392739025185393859)
                ·
                  refine ⟨2029385089108537778090789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1352923392739025185393859 2029385089108537778090789)
                  ·
                    refine ⟨380509704207850833392023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2029385089108537778090789 380509704207850833392023)
                    ·
                      rfl

theorem cell22_1111560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_1111560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111560 prefixEnd_1111560 := by exact prefixLift 1111560
  have htrace : WordTrace (prefixWord ++ tailWord_1111560) baseStart_1111560 baseEnd_1111560 := by
    simpa [prefixWord, tailWord_1111560, baseEnd_1111560] using wordTrace_append hprefix tailTrace_1111560
  have hstable : (prefixWord ++ tailWord_1111560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111560).length < 2 ^ (prefixWord ++ tailWord_1111560).sum := by decide
  have hdescent : baseEnd_1111560 < baseStart_1111560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111592 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 6]
def baseStart_1111592 : Nat := 118140960795 + 1111592 * 2 ^ 59
def prefixEnd_1111592 : Nat := 4983230072969 + 3 ^ 40 * 1111592 * 2
def baseEnd_1111592 : Nat := 126840219487271138863975

theorem tailTrace_1111592 : CollatzResearch.WordTrace tailWord_1111592 prefixEnd_1111592 126840219487271138863975 := by
  unfold tailWord_1111592
  simp only [CollatzResearch.WordTrace]
  refine ⟨20271545494449751822196515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27028727325933002429595353 20271545494449751822196515)
  ·
    refine ⟨30407318241674627733294773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20271545494449751822196515 30407318241674627733294773)
    ·
      refine ⟨2850686085156996349996385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30407318241674627733294773 2850686085156996349996385)
      ·
        refine ⟨2138014563867747262497289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2850686085156996349996385 2138014563867747262497289)
        ·
          refine ⟨1603510922900810446872967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2138014563867747262497289 1603510922900810446872967)
          ·
            refine ⟨2405266384351215670309451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603510922900810446872967 2405266384351215670309451)
            ·
              refine ⟨3607899576526823505464177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405266384351215670309451 3607899576526823505464177)
              ·
                refine ⟨2705924682395117629098133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3607899576526823505464177 2705924682395117629098133)
                ·
                  refine ⟨126840219487271138863975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2705924682395117629098133 126840219487271138863975)
                  ·
                    rfl

theorem cell22_1111592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 6].length) (baseStart_1111592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111592 prefixEnd_1111592 := by exact prefixLift 1111592
  have htrace : WordTrace (prefixWord ++ tailWord_1111592) baseStart_1111592 baseEnd_1111592 := by
    simpa [prefixWord, tailWord_1111592, baseEnd_1111592] using wordTrace_append hprefix tailTrace_1111592
  have hstable : (prefixWord ++ tailWord_1111592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111592).length < 2 ^ (prefixWord ++ tailWord_1111592).sum := by decide
  have hdescent : baseEnd_1111592 < baseStart_1111592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111605 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_1111605 : Nat := 118140960795 + 1111605 * 2 ^ 59
def prefixEnd_1111605 : Nat := 4983230072969 + 3 ^ 40 * 1111605 * 2
def baseEnd_1111605 : Nat := 380525108627485716016885

theorem tailTrace_1111605 : CollatzResearch.WordTrace tailWord_1111605 prefixEnd_1111605 380525108627485716016885 := by
  unfold tailWord_1111605
  simp only [CollatzResearch.WordTrace]
  refine ⟨40543565137852406864616269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27029043425234937909744179 40543565137852406864616269)
  ·
    refine ⟨15203836926694652574231101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40543565137852406864616269 15203836926694652574231101)
    ·
      refine ⟨5701438847510494715336663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15203836926694652574231101 5701438847510494715336663)
      ·
        refine ⟨8552158271265742073004995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5701438847510494715336663 8552158271265742073004995)
        ·
          refine ⟨12828237406898613109507493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8552158271265742073004995 12828237406898613109507493)
          ·
            refine ⟨2405294513793489958032655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12828237406898613109507493 2405294513793489958032655)
            ·
              refine ⟨3607941770690234937048983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405294513793489958032655 3607941770690234937048983)
              ·
                refine ⟨5411912656035352405573475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3607941770690234937048983 5411912656035352405573475)
                ·
                  refine ⟨8117868984053028608360213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5411912656035352405573475 8117868984053028608360213)
                  ·
                    refine ⟨380525108627485716016885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8117868984053028608360213 380525108627485716016885)
                    ·
                      rfl

theorem cell22_1111605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_1111605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111605 prefixEnd_1111605 := by exact prefixLift 1111605
  have htrace : WordTrace (prefixWord ++ tailWord_1111605) baseStart_1111605 baseEnd_1111605 := by
    simpa [prefixWord, tailWord_1111605, baseEnd_1111605] using wordTrace_append hprefix tailTrace_1111605
  have hstable : (prefixWord ++ tailWord_1111605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111605).length < 2 ^ (prefixWord ++ tailWord_1111605).sum := by decide
  have hdescent : baseEnd_1111605 < baseStart_1111605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111652 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_1111652 : Nat := 118140960795 + 1111652 * 2 ^ 59
def prefixEnd_1111652 : Nat := 4983230072969 + 3 ^ 40 * 1111652 * 2
def baseEnd_1111652 : Nat := 380541197687993260091741

theorem tailTrace_1111652 : CollatzResearch.WordTrace tailWord_1111652 prefixEnd_1111652 380541197687993260091741 := by
  unfold tailWord_1111652
  simp only [CollatzResearch.WordTrace]
  refine ⟨20272639684341066945788605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27030186245788089261051473 20272639684341066945788605)
  ·
    refine ⟨7602239881627900104670727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20272639684341066945788605 7602239881627900104670727)
    ·
      refine ⟨11403359822441850157006091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7602239881627900104670727 11403359822441850157006091)
      ·
        refine ⟨17105039733662775235509137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11403359822441850157006091 17105039733662775235509137)
        ·
          refine ⟨12828779800247081426631853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17105039733662775235509137 12828779800247081426631853)
          ·
            refine ⟨4810792425092655534986945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12828779800247081426631853 4810792425092655534986945)
            ·
              refine ⟨3608094318819491651240209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4810792425092655534986945 3608094318819491651240209)
              ·
                refine ⟨2706070739114618738430157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3608094318819491651240209 2706070739114618738430157)
                ·
                  refine ⟨1014776527167982026911309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2706070739114618738430157 1014776527167982026911309)
                  ·
                    refine ⟨380541197687993260091741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1014776527167982026911309 380541197687993260091741)
                    ·
                      rfl

theorem cell22_1111652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_1111652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111652 prefixEnd_1111652 := by exact prefixLift 1111652
  have htrace : WordTrace (prefixWord ++ tailWord_1111652) baseStart_1111652 baseEnd_1111652 := by
    simpa [prefixWord, tailWord_1111652, baseEnd_1111652] using wordTrace_append hprefix tailTrace_1111652
  have hstable : (prefixWord ++ tailWord_1111652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111652).length < 2 ^ (prefixWord ++ tailWord_1111652).sum := by decide
  have hdescent : baseEnd_1111652 < baseStart_1111652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111712 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 3, 4]
def baseStart_1111712 : Nat := 118140960795 + 1111712 * 2 ^ 59
def prefixEnd_1111712 : Nat := 4983230072969 + 3 ^ 40 * 1111712 * 2
def baseEnd_1111712 : Nat := 380561736914173103591557

theorem tailTrace_1111712 : CollatzResearch.WordTrace tailWord_1111712 prefixEnd_1111712 380561736914173103591557 := by
  unfold tailWord_1111712
  simp only [CollatzResearch.WordTrace]
  refine ⟨20273733874232382069380695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27031645165643176092507593 20273733874232382069380695)
  ·
    refine ⟨30410600811348573104071043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20273733874232382069380695 30410600811348573104071043)
    ·
      refine ⟨45615901217022859656106565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30410600811348573104071043 45615901217022859656106565)
      ·
        refine ⟨8552981478191786185519981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45615901217022859656106565 8552981478191786185519981)
        ·
          refine ⟨3207368054321919819569993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8552981478191786185519981 3207368054321919819569993)
          ·
            refine ⟨2405526040741439864677495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3207368054321919819569993 2405526040741439864677495)
            ·
              refine ⟨3608289061112159797016243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405526040741439864677495 3608289061112159797016243)
              ·
                refine ⟨5412433591668239695524365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3608289061112159797016243 5412433591668239695524365)
                ·
                  refine ⟨2029662596875589885821637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5412433591668239695524365 2029662596875589885821637)
                  ·
                    refine ⟨380561736914173103591557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2029662596875589885821637 380561736914173103591557)
                    ·
                      rfl

theorem cell22_1111712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_1111712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111712 prefixEnd_1111712 := by exact prefixLift 1111712
  have htrace : WordTrace (prefixWord ++ tailWord_1111712) baseStart_1111712 baseEnd_1111712 := by
    simpa [prefixWord, tailWord_1111712, baseEnd_1111712] using wordTrace_append hprefix tailTrace_1111712
  have hstable : (prefixWord ++ tailWord_1111712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111712).length < 2 ^ (prefixWord ++ tailWord_1111712).sum := by decide
  have hdescent : baseEnd_1111712 < baseStart_1111712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111727 : List Nat := [1, 1, 2, 1, 2, 4, 2, 5, 4]
def baseStart_1111727 : Nat := 118140960795 + 1111727 * 2 ^ 59
def prefixEnd_1111727 : Nat := 4983230072969 + 3 ^ 40 * 1111727 * 2
def baseEnd_1111727 : Nat := 126855623906906021488837

theorem tailTrace_1111727 : CollatzResearch.WordTrace tailWord_1111727 prefixEnd_1111727 126855623906906021488837 := by
  unfold tailWord_1111727
  simp only [CollatzResearch.WordTrace]
  refine ⟨40548014843410421700557435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27032009895606947800371623 40548014843410421700557435)
  ·
    refine ⟨60822022265115632550836153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40548014843410421700557435 60822022265115632550836153)
    ·
      refine ⟨45616516698836724413127115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60822022265115632550836153 45616516698836724413127115)
      ·
        refine ⟨68424775048255086619690673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45616516698836724413127115 68424775048255086619690673)
        ·
          refine ⟨51318581286191314964768005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68424775048255086619690673 51318581286191314964768005)
          ·
            refine ⟨9622233991160871555894001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51318581286191314964768005 9622233991160871555894001)
            ·
              refine ⟨7216675493370653666920501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9622233991160871555894001 7216675493370653666920501)
              ·
                refine ⟨676563327503498781273797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7216675493370653666920501 676563327503498781273797)
                ·
                  refine ⟨126855623906906021488837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 676563327503498781273797 126855623906906021488837)
                  ·
                    rfl

theorem cell22_1111727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 4].length) (baseStart_1111727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111727 prefixEnd_1111727 := by exact prefixLift 1111727
  have htrace : WordTrace (prefixWord ++ tailWord_1111727) baseStart_1111727 baseEnd_1111727 := by
    simpa [prefixWord, tailWord_1111727, baseEnd_1111727] using wordTrace_append hprefix tailTrace_1111727
  have hstable : (prefixWord ++ tailWord_1111727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111727).length < 2 ^ (prefixWord ++ tailWord_1111727).sum := by decide
  have hdescent : baseEnd_1111727 < baseStart_1111727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111804 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 3, 3]
def baseStart_1111804 : Nat := 118140960795 + 1111804 * 2 ^ 59
def prefixEnd_1111804 : Nat := 4983230072969 + 3 ^ 40 * 1111804 * 2
def baseEnd_1111804 : Nat := 380593230394315530291275

theorem tailTrace_1111804 : CollatzResearch.WordTrace tailWord_1111804 prefixEnd_1111804 380593230394315530291275 := by
  unfold tailWord_1111804
  simp only [CollatzResearch.WordTrace]
  refine ⟨20275411632065731925555233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27033882176087642567406977 20275411632065731925555233)
  ·
    refine ⟨15206558724049298944166425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20275411632065731925555233 15206558724049298944166425)
    ·
      refine ⟨11404919043036974208124819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15206558724049298944166425 11404919043036974208124819)
      ·
        refine ⟨17107378564555461312187229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11404919043036974208124819 17107378564555461312187229)
        ·
          refine ⟨6415266961708297992070211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17107378564555461312187229 6415266961708297992070211)
          ·
            refine ⟨9622900442562446988105317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6415266961708297992070211 9622900442562446988105317)
            ·
              refine ⟨1804293832980458810269747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9622900442562446988105317 1804293832980458810269747)
              ·
                refine ⟨2706440749470688215404621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1804293832980458810269747 2706440749470688215404621)
                ·
                  refine ⟨1014915281051508080776733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2706440749470688215404621 1014915281051508080776733)
                  ·
                    refine ⟨380593230394315530291275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1014915281051508080776733 380593230394315530291275)
                    ·
                      rfl

theorem cell22_1111804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_1111804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111804 prefixEnd_1111804 := by exact prefixLift 1111804
  have htrace : WordTrace (prefixWord ++ tailWord_1111804) baseStart_1111804 baseEnd_1111804 := by
    simpa [prefixWord, tailWord_1111804, baseEnd_1111804] using wordTrace_append hprefix tailTrace_1111804
  have hstable : (prefixWord ++ tailWord_1111804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111804).length < 2 ^ (prefixWord ++ tailWord_1111804).sum := by decide
  have hdescent : baseEnd_1111804 < baseStart_1111804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111877 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_1111877 : Nat := 118140960795 + 1111877 * 2 ^ 59
def prefixEnd_1111877 : Nat := 4983230072969 + 3 ^ 40 * 1111877 * 2
def baseEnd_1111877 : Nat := 380618219786167673216051

theorem tailTrace_1111877 : CollatzResearch.WordTrace tailWord_1111877 prefixEnd_1111877 380618219786167673216051 := by
  unfold tailWord_1111877
  simp only [CollatzResearch.WordTrace]
  refine ⟨40553485792866997318517885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27035657195244664879011923 40553485792866997318517885)
  ·
    refine ⟨15207557172325123994444207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40553485792866997318517885 15207557172325123994444207)
    ·
      refine ⟨22811335758487685991666311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15207557172325123994444207 22811335758487685991666311)
      ·
        refine ⟨34217003637731528987499467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22811335758487685991666311 34217003637731528987499467)
        ·
          refine ⟨51325505456597293481249201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34217003637731528987499467 51325505456597293481249201)
          ·
            refine ⟨38494129092447970110936901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51325505456597293481249201 38494129092447970110936901)
            ·
              refine ⟨7217649204833994395800669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38494129092447970110936901 7217649204833994395800669)
              ·
                refine ⟨2706618451812747898425251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7217649204833994395800669 2706618451812747898425251)
                ·
                  refine ⟨4059927677719121847637877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2706618451812747898425251 4059927677719121847637877)
                  ·
                    refine ⟨380618219786167673216051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4059927677719121847637877 380618219786167673216051)
                    ·
                      rfl

theorem cell22_1111877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_1111877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111877 prefixEnd_1111877 := by exact prefixLift 1111877
  have htrace : WordTrace (prefixWord ++ tailWord_1111877) baseStart_1111877 baseEnd_1111877 := by
    simpa [prefixWord, tailWord_1111877, baseEnd_1111877] using wordTrace_append hprefix tailTrace_1111877
  have hstable : (prefixWord ++ tailWord_1111877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111877).length < 2 ^ (prefixWord ++ tailWord_1111877).sum := by decide
  have hdescent : baseEnd_1111877 < baseStart_1111877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111907 : List Nat := [1, 1, 1, 5, 4, 10]
def baseStart_1111907 : Nat := 118140960795 + 1111907 * 2 ^ 59
def prefixEnd_1111907 : Nat := 4983230072969 + 3 ^ 40 * 1111907 * 2
def baseEnd_1111907 : Nat := 4699117153077254258839

theorem tailTrace_1111907 : CollatzResearch.WordTrace tailWord_1111907 prefixEnd_1111907 4699117153077254258839 := by
  unfold tailWord_1111907
  simp only [CollatzResearch.WordTrace]
  refine ⟨40554579982758312442109975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27036386655172208294739983 40554579982758312442109975)
  ·
    refine ⟨60831869974137468663164963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40554579982758312442109975 60831869974137468663164963)
    ·
      refine ⟨91247804961206202994747445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60831869974137468663164963 91247804961206202994747445)
      ·
        refine ⟨8554481715113081530757573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91247804961206202994747445 8554481715113081530757573)
        ·
          refine ⟨1603965321583702787017045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8554481715113081530757573 1603965321583702787017045)
          ·
            refine ⟨4699117153077254258839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1603965321583702787017045 4699117153077254258839)
            ·
              rfl

theorem cell22_1111907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 10].length) (baseStart_1111907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111907 prefixEnd_1111907 := by exact prefixLift 1111907
  have htrace : WordTrace (prefixWord ++ tailWord_1111907) baseStart_1111907 baseEnd_1111907 := by
    simpa [prefixWord, tailWord_1111907, baseEnd_1111907] using wordTrace_append hprefix tailTrace_1111907
  have hstable : (prefixWord ++ tailWord_1111907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111907).length < 2 ^ (prefixWord ++ tailWord_1111907).sum := by decide
  have hdescent : baseEnd_1111907 < baseStart_1111907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111911 : List Nat := [1, 1, 5, 1, 2, 1, 4, 2, 2, 3]
def baseStart_1111911 : Nat := 118140960795 + 1111911 * 2 ^ 59
def prefixEnd_1111911 : Nat := 4983230072969 + 3 ^ 40 * 1111911 * 2
def baseEnd_1111911 : Nat := 380629858681002917865947

theorem tailTrace_1111911 : CollatzResearch.WordTrace tailWord_1111911 prefixEnd_1111911 380629858681002917865947 := by
  unfold tailWord_1111911
  simp only [CollatzResearch.WordTrace]
  refine ⟨40554725874743821125255587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27036483916495880750170391 40554725874743821125255587)
  ·
    refine ⟨60832088812115731687883381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40554725874743821125255587 60832088812115731687883381)
    ·
      refine ⟨5703008326135849845739067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60832088812115731687883381 5703008326135849845739067)
      ·
        refine ⟨8554512489203774768608601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5703008326135849845739067 8554512489203774768608601)
        ·
          refine ⟨6415884366902831076456451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8554512489203774768608601 6415884366902831076456451)
          ·
            refine ⟨9623826550354246614684677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6415884366902831076456451 9623826550354246614684677)
            ·
              refine ⟨1804467478191421240253377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9623826550354246614684677 1804467478191421240253377)
              ·
                refine ⟨1353350608643565930190033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1804467478191421240253377 1353350608643565930190033)
                ·
                  refine ⟨1015012956482674447642525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1353350608643565930190033 1015012956482674447642525)
                  ·
                    refine ⟨380629858681002917865947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1015012956482674447642525 380629858681002917865947)
                    ·
                      rfl

theorem cell22_1111911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_1111911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111911 prefixEnd_1111911 := by exact prefixLift 1111911
  have htrace : WordTrace (prefixWord ++ tailWord_1111911) baseStart_1111911 baseEnd_1111911 := by
    simpa [prefixWord, tailWord_1111911, baseEnd_1111911] using wordTrace_append hprefix tailTrace_1111911
  have hstable : (prefixWord ++ tailWord_1111911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111911).length < 2 ^ (prefixWord ++ tailWord_1111911).sum := by decide
  have hdescent : baseEnd_1111911 < baseStart_1111911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111922 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_1111922 : Nat := 118140960795 + 1111922 * 2 ^ 59
def prefixEnd_1111922 : Nat := 4983230072969 + 3 ^ 40 * 1111922 * 2
def baseEnd_1111922 : Nat := 380633624205802555840913

theorem tailTrace_1111922 : CollatzResearch.WordTrace tailWord_1111922 prefixEnd_1111922 380633624205802555840913 := by
  unfold tailWord_1111922
  simp only [CollatzResearch.WordTrace]
  refine ⟨10138781769425992500976505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27036751385135980002604013 10138781769425992500976505)
  ·
    refine ⟨7604086327069494375732379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10138781769425992500976505 7604086327069494375732379)
    ·
      refine ⟨11406129490604241563598569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7604086327069494375732379 11406129490604241563598569)
      ·
        refine ⟨8554597117953181172698927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11406129490604241563598569 8554597117953181172698927)
        ·
          refine ⟨12831895676929771759048391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8554597117953181172698927 12831895676929771759048391)
          ·
            refine ⟨19247843515394657638572587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12831895676929771759048391 19247843515394657638572587)
            ·
              refine ⟨28871765273091986457858881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19247843515394657638572587 28871765273091986457858881)
              ·
                refine ⟨21653823954818989843394161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28871765273091986457858881 21653823954818989843394161)
                ·
                  refine ⟨16240367966114242382545621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21653823954818989843394161 16240367966114242382545621)
                  ·
                    refine ⟨380633624205802555840913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16240367966114242382545621 380633624205802555840913)
                    ·
                      rfl

theorem cell22_1111922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_1111922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111922 prefixEnd_1111922 := by exact prefixLift 1111922
  have htrace : WordTrace (prefixWord ++ tailWord_1111922) baseStart_1111922 baseEnd_1111922 := by
    simpa [prefixWord, tailWord_1111922, baseEnd_1111922] using wordTrace_append hprefix tailTrace_1111922
  have hstable : (prefixWord ++ tailWord_1111922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111922).length < 2 ^ (prefixWord ++ tailWord_1111922).sum := by decide
  have hdescent : baseEnd_1111922 < baseStart_1111922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111939 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 5, 3]
def baseStart_1111939 : Nat := 118140960795 + 1111939 * 2 ^ 59
def prefixEnd_1111939 : Nat := 4983230072969 + 3 ^ 40 * 1111939 * 2
def baseEnd_1111939 : Nat := 380639443653220178165861

theorem tailTrace_1111939 : CollatzResearch.WordTrace tailWord_1111939 prefixEnd_1111939 380639443653220178165861 := by
  unfold tailWord_1111939
  simp only [CollatzResearch.WordTrace]
  refine ⟨40555747118642381907274871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27037164745761587938183247 40555747118642381907274871)
  ·
    refine ⟨60833620677963572860912307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40555747118642381907274871 60833620677963572860912307)
    ·
      refine ⟨91250431016945359291368461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60833620677963572860912307 91250431016945359291368461)
      ·
        refine ⟨34218911631354509734263173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91250431016945359291368461 34218911631354509734263173)
        ·
          refine ⟨6416045930878970575174345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34218911631354509734263173 6416045930878970575174345)
          ·
            refine ⟨4812034448159227931380759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6416045930878970575174345 4812034448159227931380759)
            ·
              refine ⟨7218051672238841897071139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4812034448159227931380759 7218051672238841897071139)
              ·
                refine ⟨10827077508358262845606709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7218051672238841897071139 10827077508358262845606709)
                ·
                  refine ⟨1015038516408587141775629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10827077508358262845606709 1015038516408587141775629)
                  ·
                    refine ⟨380639443653220178165861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1015038516408587141775629 380639443653220178165861)
                    ·
                      rfl

theorem cell22_1111939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 3].length) (baseStart_1111939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111939 prefixEnd_1111939 := by exact prefixLift 1111939
  have htrace : WordTrace (prefixWord ++ tailWord_1111939) baseStart_1111939 baseEnd_1111939 := by
    simpa [prefixWord, tailWord_1111939, baseEnd_1111939] using wordTrace_append hprefix tailTrace_1111939
  have hstable : (prefixWord ++ tailWord_1111939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111939).length < 2 ^ (prefixWord ++ tailWord_1111939).sum := by decide
  have hdescent : baseEnd_1111939 < baseStart_1111939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111943 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 2, 4]
def baseStart_1111943 : Nat := 118140960795 + 1111943 * 2 ^ 59
def prefixEnd_1111943 : Nat := 4983230072969 + 3 ^ 40 * 1111943 * 2
def baseEnd_1111943 : Nat := 380640812934965501065849

theorem tailTrace_1111943 : CollatzResearch.WordTrace tailWord_1111943 prefixEnd_1111943 380640812934965501065849 := by
  unfold tailWord_1111943
  simp only [CollatzResearch.WordTrace]
  refine ⟨40555893010627890590420483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27037262007085260393613655 40555893010627890590420483)
  ·
    refine ⟨60833839515941835885630725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40555893010627890590420483 60833839515941835885630725)
    ·
      refine ⟨11406344909239094228555761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60833839515941835885630725 11406344909239094228555761)
      ·
        refine ⟨8554758681929320671416821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11406344909239094228555761 8554758681929320671416821)
        ·
          refine ⟨802008626430873812945327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8554758681929320671416821 802008626430873812945327)
          ·
            refine ⟨1203012939646310719417991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802008626430873812945327 1203012939646310719417991)
            ·
              refine ⟨1804519409469466079126987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203012939646310719417991 1804519409469466079126987)
              ·
                refine ⟨2706779114204199118690481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1804519409469466079126987 2706779114204199118690481)
                ·
                  refine ⟨2030084335653149339017861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2706779114204199118690481 2030084335653149339017861)
                  ·
                    refine ⟨380640812934965501065849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2030084335653149339017861 380640812934965501065849)
                    ·
                      rfl

theorem cell22_1111943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_1111943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111943 prefixEnd_1111943 := by exact prefixLift 1111943
  have htrace : WordTrace (prefixWord ++ tailWord_1111943) baseStart_1111943 baseEnd_1111943 := by
    simpa [prefixWord, tailWord_1111943, baseEnd_1111943] using wordTrace_append hprefix tailTrace_1111943
  have hstable : (prefixWord ++ tailWord_1111943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111943).length < 2 ^ (prefixWord ++ tailWord_1111943).sum := by decide
  have hdescent : baseEnd_1111943 < baseStart_1111943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1111958 : List Nat := [5, 3, 1, 1, 2, 1, 9]
def baseStart_1111958 : Nat := 118140960795 + 1111958 * 2 ^ 59
def prefixEnd_1111958 : Nat := 4983230072969 + 3 ^ 40 * 1111958 * 2
def baseEnd_1111958 : Nat := 14097998064500387479289

theorem tailTrace_1111958 : CollatzResearch.WordTrace tailWord_1111958 prefixEnd_1111958 14097998064500387479289 := by
  unfold tailWord_1111958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2534777506598346759513533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27037626737049032101477685 2534777506598346759513533)
  ·
    refine ⟨950541564974380034817575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2534777506598346759513533 950541564974380034817575)
    ·
      refine ⟨1425812347461570052226363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 950541564974380034817575 1425812347461570052226363)
      ·
        refine ⟨2138718521192355078339545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1425812347461570052226363 2138718521192355078339545)
        ·
          refine ⟨1604038890894266308754659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2138718521192355078339545 1604038890894266308754659)
          ·
            refine ⟨2406058336341399463131989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1604038890894266308754659 2406058336341399463131989)
            ·
              refine ⟨14097998064500387479289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2406058336341399463131989 14097998064500387479289)
              ·
                rfl

theorem cell22_1111958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 9].length) (baseStart_1111958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1111958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1111958 prefixEnd_1111958 := by exact prefixLift 1111958
  have htrace : WordTrace (prefixWord ++ tailWord_1111958) baseStart_1111958 baseEnd_1111958 := by
    simpa [prefixWord, tailWord_1111958, baseEnd_1111958] using wordTrace_append hprefix tailTrace_1111958
  have hstable : (prefixWord ++ tailWord_1111958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1111958).length < 2 ^ (prefixWord ++ tailWord_1111958).sum := by decide
  have hdescent : baseEnd_1111958 < baseStart_1111958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1111958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112031 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 6]
def baseStart_1112031 : Nat := 118140960795 + 1112031 * 2 ^ 59
def prefixEnd_1112031 : Nat := 4983230072969 + 3 ^ 40 * 1112031 * 2
def baseEnd_1112031 : Nat := 126890312377787534955193

theorem tailTrace_1112031 : CollatzResearch.WordTrace tailWord_1112031 prefixEnd_1112031 126890312377787534955193 := by
  unfold tailWord_1112031
  simp only [CollatzResearch.WordTrace]
  refine ⟨40559102634309081619623947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27039401756206054413082631 40559102634309081619623947)
  ·
    refine ⟨60838653951463622429435921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40559102634309081619623947 60838653951463622429435921)
    ·
      refine ⟨45628990463597716822076941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60838653951463622429435921 45628990463597716822076941)
      ·
        refine ⟨17110871423849143808278853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45628990463597716822076941 17110871423849143808278853)
        ·
          refine ⟨3208288391971714464052285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17110871423849143808278853 3208288391971714464052285)
          ·
            refine ⟨1203108146989392924019607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3208288391971714464052285 1203108146989392924019607)
            ·
              refine ⟨1804662220484089386029411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203108146989392924019607 1804662220484089386029411)
              ·
                refine ⟨2706993330726134079044117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1804662220484089386029411 2706993330726134079044117)
                ·
                  refine ⟨126890312377787534955193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2706993330726134079044117 126890312377787534955193)
                  ·
                    rfl

theorem cell22_1112031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 6].length) (baseStart_1112031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112031 prefixEnd_1112031 := by exact prefixLift 1112031
  have htrace : WordTrace (prefixWord ++ tailWord_1112031) baseStart_1112031 baseEnd_1112031 := by
    simpa [prefixWord, tailWord_1112031, baseEnd_1112031] using wordTrace_append hprefix tailTrace_1112031
  have hstable : (prefixWord ++ tailWord_1112031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112031).length < 2 ^ (prefixWord ++ tailWord_1112031).sum := by decide
  have hdescent : baseEnd_1112031 < baseStart_1112031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112125 : List Nat := [1, 4, 1, 3, 1, 1, 4, 3, 1, 3]
def baseStart_1112125 : Nat := 118140960795 + 1112125 * 2 ^ 59
def prefixEnd_1112125 : Nat := 4983230072969 + 3 ^ 40 * 1112125 * 2
def baseEnd_1112125 : Nat := 380703115254377693015291

theorem tailTrace_1112125 : CollatzResearch.WordTrace tailWord_1112125 prefixEnd_1112125 380703115254377693015291 := by
  unfold tailWord_1112125
  simp only [CollatzResearch.WordTrace]
  refine ⟨40562531095968535673545829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27041687397312357115697219 40562531095968535673545829)
  ·
    refine ⟨7605474580494100438789843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40562531095968535673545829 7605474580494100438789843)
    ·
      refine ⟨11408211870741150658184765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7605474580494100438789843 11408211870741150658184765)
      ·
        refine ⟨4278079451527931496819287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11408211870741150658184765 4278079451527931496819287)
        ·
          refine ⟨6417119177291897245228931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4278079451527931496819287 6417119177291897245228931)
          ·
            refine ⟨9625678765937845867843397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6417119177291897245228931 9625678765937845867843397)
            ·
              refine ⟨1804814768613346100220637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9625678765937845867843397 1804814768613346100220637)
              ·
                refine ⟨676805538230004787582739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1804814768613346100220637 676805538230004787582739)
                ·
                  refine ⟨1015208307345007181374109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 676805538230004787582739 1015208307345007181374109)
                  ·
                    refine ⟨380703115254377693015291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1015208307345007181374109 380703115254377693015291)
                    ·
                      rfl

theorem cell22_1112125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_1112125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112125 prefixEnd_1112125 := by exact prefixLift 1112125
  have htrace : WordTrace (prefixWord ++ tailWord_1112125) baseStart_1112125 baseEnd_1112125 := by
    simpa [prefixWord, tailWord_1112125, baseEnd_1112125] using wordTrace_append hprefix tailTrace_1112125
  have hstable : (prefixWord ++ tailWord_1112125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112125).length < 2 ^ (prefixWord ++ tailWord_1112125).sum := by decide
  have hdescent : baseEnd_1112125 < baseStart_1112125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112183 : List Nat := [1, 1, 3, 1, 1, 5, 3, 3, 4]
def baseStart_1112183 : Nat := 118140960795 + 1112183 * 2 ^ 59
def prefixEnd_1112183 : Nat := 4983230072969 + 3 ^ 40 * 1112183 * 2
def baseEnd_1112183 : Nat := 126907656613228291688371

theorem tailTrace_1112183 : CollatzResearch.WordTrace tailWord_1112183 prefixEnd_1112183 126907656613228291688371 := by
  unfold tailWord_1112183
  simp only [CollatzResearch.WordTrace]
  refine ⟨40564646529758411579157203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27043097686505607719438135 40564646529758411579157203)
  ·
    refine ⟨60846969794637617368735805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40564646529758411579157203 60846969794637617368735805)
    ·
      refine ⟨22817613672989106513275927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60846969794637617368735805 22817613672989106513275927)
      ·
        refine ⟨34226420509483659769913891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22817613672989106513275927 34226420509483659769913891)
        ·
          refine ⟨51339630764225489654870837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34226420509483659769913891 51339630764225489654870837)
          ·
            refine ⟨4813090384146139655144141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51339630764225489654870837 4813090384146139655144141)
            ·
              refine ⟨1804908894054802370679053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4813090384146139655144141 1804908894054802370679053)
              ·
                refine ⟨676840835270550889004645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1804908894054802370679053 676840835270550889004645)
                ·
                  refine ⟨126907656613228291688371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 676840835270550889004645 126907656613228291688371)
                  ·
                    rfl

theorem cell22_1112183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 4].length) (baseStart_1112183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112183 prefixEnd_1112183 := by exact prefixLift 1112183
  have htrace : WordTrace (prefixWord ++ tailWord_1112183) baseStart_1112183 baseEnd_1112183 := by
    simpa [prefixWord, tailWord_1112183, baseEnd_1112183] using wordTrace_append hprefix tailTrace_1112183
  have hstable : (prefixWord ++ tailWord_1112183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112183).length < 2 ^ (prefixWord ++ tailWord_1112183).sum := by decide
  have hdescent : baseEnd_1112183 < baseStart_1112183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112215 : List Nat := [1, 1, 3, 3, 4, 1, 1, 3, 2, 3]
def baseStart_1112215 : Nat := 118140960795 + 1112215 * 2 ^ 59
def prefixEnd_1112215 : Nat := 4983230072969 + 3 ^ 40 * 1112215 * 2
def baseEnd_1112215 : Nat := 380733924093647458265015

theorem tailTrace_1112215 : CollatzResearch.WordTrace tailWord_1112215 prefixEnd_1112215 380733924093647458265015 := by
  unfold tailWord_1112215
  simp only [CollatzResearch.WordTrace]
  refine ⟨40565813665642481044322099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27043875777094987362881399 40565813665642481044322099)
  ·
    refine ⟨60848720498463721566483149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40565813665642481044322099 60848720498463721566483149)
    ·
      refine ⟨22818270186923895587431181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60848720498463721566483149 22818270186923895587431181)
      ·
        refine ⟨8556851320096460845286693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22818270186923895587431181 8556851320096460845286693)
        ·
          refine ⟨1604409622518086408491255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8556851320096460845286693 1604409622518086408491255)
          ·
            refine ⟨2406614433777129612736883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1604409622518086408491255 2406614433777129612736883)
            ·
              refine ⟨3609921650665694419105325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2406614433777129612736883 3609921650665694419105325)
              ·
                refine ⟨1353720618999635407164497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3609921650665694419105325 1353720618999635407164497)
                ·
                  refine ⟨1015290464249726555373373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1353720618999635407164497 1015290464249726555373373)
                  ·
                    refine ⟨380733924093647458265015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1015290464249726555373373 380733924093647458265015)
                    ·
                      rfl

theorem cell22_1112215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_1112215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112215 prefixEnd_1112215 := by exact prefixLift 1112215
  have htrace : WordTrace (prefixWord ++ tailWord_1112215) baseStart_1112215 baseEnd_1112215 := by
    simpa [prefixWord, tailWord_1112215, baseEnd_1112215] using wordTrace_append hprefix tailTrace_1112215
  have hstable : (prefixWord ++ tailWord_1112215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112215).length < 2 ^ (prefixWord ++ tailWord_1112215).sum := by decide
  have hdescent : baseEnd_1112215 < baseStart_1112215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112271 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 2, 5]
def baseStart_1112271 : Nat := 118140960795 + 1112271 * 2 ^ 59
def prefixEnd_1112271 : Nat := 4983230072969 + 3 ^ 40 * 1112271 * 2
def baseEnd_1112271 : Nat := 380753094038081978864843

theorem tailTrace_1112271 : CollatzResearch.WordTrace tailWord_1112271 prefixEnd_1112271 380753094038081978864843 := by
  unfold tailWord_1112271
  simp only [CollatzResearch.WordTrace]
  refine ⟨40567856153439602608360667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27045237435626401738907111 40567856153439602608360667)
  ·
    refine ⟨60851784230159403912541001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40567856153439602608360667 60851784230159403912541001)
    ·
      refine ⟨45638838172619552934405751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60851784230159403912541001 45638838172619552934405751)
      ·
        refine ⟨68458257258929329401608627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45638838172619552934405751 68458257258929329401608627)
        ·
          refine ⟨102687385888393994102412941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68458257258929329401608627 102687385888393994102412941)
          ·
            refine ⟨38507769708147747788404853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102687385888393994102412941 38507769708147747788404853)
            ·
              refine ⟨3610103410138851355162955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38507769708147747788404853 3610103410138851355162955)
              ·
                refine ⟨5415155115208277032744433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3610103410138851355162955 5415155115208277032744433)
                ·
                  refine ⟨4061366336406207774558325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5415155115208277032744433 4061366336406207774558325)
                  ·
                    refine ⟨380753094038081978864843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4061366336406207774558325 380753094038081978864843)
                    ·
                      rfl

theorem cell22_1112271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_1112271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112271 prefixEnd_1112271 := by exact prefixLift 1112271
  have htrace : WordTrace (prefixWord ++ tailWord_1112271) baseStart_1112271 baseEnd_1112271 := by
    simpa [prefixWord, tailWord_1112271, baseEnd_1112271] using wordTrace_append hprefix tailTrace_1112271
  have hstable : (prefixWord ++ tailWord_1112271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112271).length < 2 ^ (prefixWord ++ tailWord_1112271).sum := by decide
  have hdescent : baseEnd_1112271 < baseStart_1112271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112331 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 3, 6]
def baseStart_1112331 : Nat := 118140960795 + 1112331 * 2 ^ 59
def prefixEnd_1112331 : Nat := 4983230072969 + 3 ^ 40 * 1112331 * 2
def baseEnd_1112331 : Nat := 380773633264261822364659

theorem tailTrace_1112331 : CollatzResearch.WordTrace tailWord_1112331 prefixEnd_1112331 380773633264261822364659 := by
  unfold tailWord_1112331
  simp only [CollatzResearch.WordTrace]
  refine ⟨40570044533222232855544847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27046696355481488570363231 40570044533222232855544847)
  ·
    refine ⟨60855066799833349283317271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40570044533222232855544847 60855066799833349283317271)
    ·
      refine ⟨91282600199750023924975907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60855066799833349283317271 91282600199750023924975907)
      ·
        refine ⟨136923900299625035887463861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91282600199750023924975907 136923900299625035887463861)
        ·
          refine ⟨12836615653089847114449737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 136923900299625035887463861 12836615653089847114449737)
          ·
            refine ⟨9627461739817385335837303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12836615653089847114449737 9627461739817385335837303)
            ·
              refine ⟨14441192609726078003755955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9627461739817385335837303 14441192609726078003755955)
              ·
                refine ⟨21661788914589117005633933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14441192609726078003755955 21661788914589117005633933)
                ·
                  refine ⟨8123170842970918877112725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21661788914589117005633933 8123170842970918877112725)
                  ·
                    refine ⟨380773633264261822364659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8123170842970918877112725 380773633264261822364659)
                    ·
                      rfl

theorem cell22_1112331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 6].length) (baseStart_1112331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112331 prefixEnd_1112331 := by exact prefixLift 1112331
  have htrace : WordTrace (prefixWord ++ tailWord_1112331) baseStart_1112331 baseEnd_1112331 := by
    simpa [prefixWord, tailWord_1112331, baseEnd_1112331] using wordTrace_append hprefix tailTrace_1112331
  have hstable : (prefixWord ++ tailWord_1112331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112331).length < 2 ^ (prefixWord ++ tailWord_1112331).sum := by decide
  have hdescent : baseEnd_1112331 < baseStart_1112331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112348 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_1112348 : Nat := 118140960795 + 1112348 * 2 ^ 59
def prefixEnd_1112348 : Nat := 4983230072969 + 3 ^ 40 * 1112348 * 2
def baseEnd_1112348 : Nat := 380779452711679444689607

theorem tailTrace_1112348 : CollatzResearch.WordTrace tailWord_1112348 prefixEnd_1112348 380779452711679444689607 := by
  unfold tailWord_1112348
  simp only [CollatzResearch.WordTrace]
  refine ⟨20285332287080322379456849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27047109716107096505942465 20285332287080322379456849)
  ·
    refine ⟨15213999215310241784592637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20285332287080322379456849 15213999215310241784592637)
    ·
      refine ⟨5705249705741340669222239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15213999215310241784592637 5705249705741340669222239)
      ·
        refine ⟨8557874558612011003833359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5705249705741340669222239 8557874558612011003833359)
        ·
          refine ⟨12836811837918016505750039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8557874558612011003833359 12836811837918016505750039)
          ·
            refine ⟨19255217756877024758625059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12836811837918016505750039 19255217756877024758625059)
            ·
              refine ⟨28882826635315537137937589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19255217756877024758625059 28882826635315537137937589)
              ·
                refine ⟨2707764997060831606681649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28882826635315537137937589 2707764997060831606681649)
                ·
                  refine ⟨2030823747795623705011237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2707764997060831606681649 2030823747795623705011237)
                  ·
                    refine ⟨380779452711679444689607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2030823747795623705011237 380779452711679444689607)
                    ·
                      rfl

theorem cell22_1112348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_1112348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112348 prefixEnd_1112348 := by exact prefixLift 1112348
  have htrace : WordTrace (prefixWord ++ tailWord_1112348) baseStart_1112348 baseEnd_1112348 := by
    simpa [prefixWord, tailWord_1112348, baseEnd_1112348] using wordTrace_append hprefix tailTrace_1112348
  have hstable : (prefixWord ++ tailWord_1112348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112348).length < 2 ^ (prefixWord ++ tailWord_1112348).sum := by decide
  have hdescent : baseEnd_1112348 < baseStart_1112348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112352 : List Nat := [2, 1, 1, 5, 2, 3, 1, 3, 4]
def baseStart_1112352 : Nat := 118140960795 + 1112352 * 2 ^ 59
def prefixEnd_1112352 : Nat := 4983230072969 + 3 ^ 40 * 1112352 * 2
def baseEnd_1112352 : Nat := 126926940664474922529865

theorem tailTrace_1112352 : CollatzResearch.WordTrace tailWord_1112352 prefixEnd_1112352 126926940664474922529865 := by
  unfold tailWord_1112352
  simp only [CollatzResearch.WordTrace]
  refine ⟨20285405233073076721029655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27047206977430768961372873 20285405233073076721029655)
  ·
    refine ⟨30428107849609615081544483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20285405233073076721029655 30428107849609615081544483)
    ·
      refine ⟨45642161774414422622316725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30428107849609615081544483 45642161774414422622316725)
      ·
        refine ⟨4278952666351352120842193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45642161774414422622316725 4278952666351352120842193)
        ·
          refine ⟨3209214499763514090631645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4278952666351352120842193 3209214499763514090631645)
          ·
            refine ⟨1203455437411317783986867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3209214499763514090631645 1203455437411317783986867)
            ·
              refine ⟨1805183156116976675980301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203455437411317783986867 1805183156116976675980301)
              ·
                refine ⟨676943683543866253492613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1805183156116976675980301 676943683543866253492613)
                ·
                  refine ⟨126926940664474922529865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 676943683543866253492613 126926940664474922529865)
                  ·
                    rfl

theorem cell22_1112352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 4].length) (baseStart_1112352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112352 prefixEnd_1112352 := by exact prefixLift 1112352
  have htrace : WordTrace (prefixWord ++ tailWord_1112352) baseStart_1112352 baseEnd_1112352 := by
    simpa [prefixWord, tailWord_1112352, baseEnd_1112352] using wordTrace_append hprefix tailTrace_1112352
  have hstable : (prefixWord ++ tailWord_1112352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112352).length < 2 ^ (prefixWord ++ tailWord_1112352).sum := by decide
  have hdescent : baseEnd_1112352 < baseStart_1112352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112414 : List Nat := [4, 4, 2, 1, 1, 10]
def baseStart_1112414 : Nat := 118140960795 + 1112414 * 2 ^ 59
def prefixEnd_1112414 : Nat := 4983230072969 + 3 ^ 40 * 1112414 * 2
def baseEnd_1112414 : Nat := 4701259825437991019005

theorem tailTrace_1112414 : CollatzResearch.WordTrace tailWord_1112414 prefixEnd_1112414 4701259825437991019005 := by
  unfold tailWord_1112414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5071633973990192253852037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27048714527947692020544197 5071633973990192253852037)
  ·
    refine ⟨950931370123161047597257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5071633973990192253852037 950931370123161047597257)
    ·
      refine ⟨713198527592370785697943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 950931370123161047597257 713198527592370785697943)
      ·
        refine ⟨1069797791388556178546915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713198527592370785697943 1069797791388556178546915)
        ·
          refine ⟨1604696687082834267820373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1069797791388556178546915 1604696687082834267820373)
          ·
            refine ⟨4701259825437991019005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1604696687082834267820373 4701259825437991019005)
            ·
              rfl

theorem cell22_1112414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 10].length) (baseStart_1112414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112414 prefixEnd_1112414 := by exact prefixLift 1112414
  have htrace : WordTrace (prefixWord ++ tailWord_1112414) baseStart_1112414 baseEnd_1112414 := by
    simpa [prefixWord, tailWord_1112414, baseEnd_1112414] using wordTrace_append hprefix tailTrace_1112414
  have hstable : (prefixWord ++ tailWord_1112414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112414).length < 2 ^ (prefixWord ++ tailWord_1112414).sum := by decide
  have hdescent : baseEnd_1112414 < baseStart_1112414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112455 : List Nat := [1, 1, 4, 2, 2, 1, 2, 4, 1, 4]
def baseStart_1112455 : Nat := 118140960795 + 1112455 * 2 ^ 59
def prefixEnd_1112455 : Nat := 4983230072969 + 3 ^ 40 * 1112455 * 2
def baseEnd_1112455 : Nat := 380816080998366832264279

theorem tailTrace_1112455 : CollatzResearch.WordTrace tailWord_1112455 prefixEnd_1112455 380816080998366832264279 := by
  unfold tailWord_1112455
  simp only [CollatzResearch.WordTrace]
  refine ⟨40574567184773002033058819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27049711456515334688705879 40574567184773002033058819)
  ·
    refine ⟨60861850777159503049588229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40574567184773002033058819 60861850777159503049588229)
    ·
      refine ⟨11411597020717406821797793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60861850777159503049588229 11411597020717406821797793)
      ·
        refine ⟨8558697765538055116348345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11411597020717406821797793 8558697765538055116348345)
        ·
          refine ⟨6419023324153541337261259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8558697765538055116348345 6419023324153541337261259)
          ·
            refine ⟨9628534986230312005891889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6419023324153541337261259 9628534986230312005891889)
            ·
              refine ⟨7221401239672734004418917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9628534986230312005891889 7221401239672734004418917)
              ·
                refine ⟨1354012732438637625828547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7221401239672734004418917 1354012732438637625828547)
                ·
                  refine ⟨2031019098657956438742821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1354012732438637625828547 2031019098657956438742821)
                  ·
                    refine ⟨380816080998366832264279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2031019098657956438742821 380816080998366832264279)
                    ·
                      rfl

theorem cell22_1112455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_1112455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112455 prefixEnd_1112455 := by exact prefixLift 1112455
  have htrace : WordTrace (prefixWord ++ tailWord_1112455) baseStart_1112455 baseEnd_1112455 := by
    simpa [prefixWord, tailWord_1112455, baseEnd_1112455] using wordTrace_append hprefix tailTrace_1112455
  have hstable : (prefixWord ++ tailWord_1112455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112455).length < 2 ^ (prefixWord ++ tailWord_1112455).sum := by decide
  have hdescent : baseEnd_1112455 < baseStart_1112455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112472 : List Nat := [2, 1, 2, 5, 1, 2, 1, 3, 1, 4]
def baseStart_1112472 : Nat := 118140960795 + 1112472 * 2 ^ 59
def prefixEnd_1112472 : Nat := 4983230072969 + 3 ^ 40 * 1112472 * 2
def baseEnd_1112472 : Nat := 380821900445784454589227

theorem tailTrace_1112472 : CollatzResearch.WordTrace tailWord_1112472 prefixEnd_1112472 380821900445784454589227 := by
  unfold tailWord_1112472
  simp only [CollatzResearch.WordTrace]
  refine ⟨20287593612855706968213835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27050124817140942624285113 20287593612855706968213835)
  ·
    refine ⟨30431390419283560452320753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20287593612855706968213835 30431390419283560452320753)
    ·
      refine ⟨22823542814462670339240565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30431390419283560452320753 22823542814462670339240565)
      ·
        refine ⟨2139707138855875344303803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22823542814462670339240565 2139707138855875344303803)
        ·
          refine ⟨3209560708283813016455705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2139707138855875344303803 3209560708283813016455705)
          ·
            refine ⟨2407170531212859762341779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3209560708283813016455705 2407170531212859762341779)
            ·
              refine ⟨3610755796819289643512669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2407170531212859762341779 3610755796819289643512669)
              ·
                refine ⟨1354033423807233616317251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3610755796819289643512669 1354033423807233616317251)
                ·
                  refine ⟨2031050135710850424475877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1354033423807233616317251 2031050135710850424475877)
                  ·
                    refine ⟨380821900445784454589227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2031050135710850424475877 380821900445784454589227)
                    ·
                      rfl

theorem cell22_1112472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_1112472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112472 prefixEnd_1112472 := by exact prefixLift 1112472
  have htrace : WordTrace (prefixWord ++ tailWord_1112472) baseStart_1112472 baseEnd_1112472 := by
    simpa [prefixWord, tailWord_1112472, baseEnd_1112472] using wordTrace_append hprefix tailTrace_1112472
  have hstable : (prefixWord ++ tailWord_1112472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112472).length < 2 ^ (prefixWord ++ tailWord_1112472).sum := by decide
  have hdescent : baseEnd_1112472 < baseStart_1112472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112485 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 4, 3]
def baseStart_1112485 : Nat := 118140960795 + 1112485 * 2 ^ 59
def prefixEnd_1112485 : Nat := 4983230072969 + 3 ^ 40 * 1112485 * 2
def baseEnd_1112485 : Nat := 380826350611456754014187

theorem tailTrace_1112485 : CollatzResearch.WordTrace tailWord_1112485 prefixEnd_1112485 380826350611456754014187 := by
  unfold tailWord_1112485
  simp only [CollatzResearch.WordTrace]
  refine ⟨40575661374664317156650909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27050440916442878104433939 40575661374664317156650909)
  ·
    refine ⟨15215873015499118933744091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40575661374664317156650909 15215873015499118933744091)
    ·
      refine ⟨22823809523248678400616137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15215873015499118933744091 22823809523248678400616137)
      ·
        refine ⟨17117857142436508800462103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22823809523248678400616137 17117857142436508800462103)
        ·
          refine ⟨25676785713654763200693155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17117857142436508800462103 25676785713654763200693155)
          ·
            refine ⟨38515178570482144801039733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25676785713654763200693155 38515178570482144801039733)
            ·
              refine ⟨3610797990982701075097475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38515178570482144801039733 3610797990982701075097475)
              ·
                refine ⟨5416196986474051612646213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3610797990982701075097475 5416196986474051612646213)
                ·
                  refine ⟨1015536934963884677371165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5416196986474051612646213 1015536934963884677371165)
                  ·
                    refine ⟨380826350611456754014187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1015536934963884677371165 380826350611456754014187)
                    ·
                      rfl

theorem cell22_1112485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_1112485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112485 prefixEnd_1112485 := by exact prefixLift 1112485
  have htrace : WordTrace (prefixWord ++ tailWord_1112485) baseStart_1112485 baseEnd_1112485 := by
    simpa [prefixWord, tailWord_1112485, baseEnd_1112485] using wordTrace_append hprefix tailTrace_1112485
  have hstable : (prefixWord ++ tailWord_1112485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112485).length < 2 ^ (prefixWord ++ tailWord_1112485).sum := by decide
  have hdescent : baseEnd_1112485 < baseStart_1112485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112487 : List Nat := [1, 1, 6, 1, 1, 2, 2, 4, 4]
def baseStart_1112487 : Nat := 118140960795 + 1112487 * 2 ^ 59
def prefixEnd_1112487 : Nat := 4983230072969 + 3 ^ 40 * 1112487 * 2
def baseEnd_1112487 : Nat := 126942345084109805154727

theorem tailTrace_1112487 : CollatzResearch.WordTrace tailWord_1112487 prefixEnd_1112487 126942345084109805154727 := by
  unfold tailWord_1112487
  simp only [CollatzResearch.WordTrace]
  refine ⟨40575734320657071498223715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27050489547104714332149143 40575734320657071498223715)
  ·
    refine ⟨60863601480985607247335573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40575734320657071498223715 60863601480985607247335573)
    ·
      refine ⟨2852981319421200339718855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60863601480985607247335573 2852981319421200339718855)
      ·
        refine ⟨4279471979131800509578283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2852981319421200339718855 4279471979131800509578283)
        ·
          refine ⟨6419207968697700764367425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279471979131800509578283 6419207968697700764367425)
          ·
            refine ⟨4814405976523275573275569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6419207968697700764367425 4814405976523275573275569)
            ·
              refine ⟨3610804482392456679956677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4814405976523275573275569 3610804482392456679956677)
              ·
                refine ⟨677025840448585627491877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3610804482392456679956677 677025840448585627491877)
                ·
                  refine ⟨126942345084109805154727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 677025840448585627491877 126942345084109805154727)
                  ·
                    rfl

theorem cell22_1112487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 4].length) (baseStart_1112487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112487 prefixEnd_1112487 := by exact prefixLift 1112487
  have htrace : WordTrace (prefixWord ++ tailWord_1112487) baseStart_1112487 baseEnd_1112487 := by
    simpa [prefixWord, tailWord_1112487, baseEnd_1112487] using wordTrace_append hprefix tailTrace_1112487
  have hstable : (prefixWord ++ tailWord_1112487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112487).length < 2 ^ (prefixWord ++ tailWord_1112487).sum := by decide
  have hdescent : baseEnd_1112487 < baseStart_1112487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112498 : List Nat := [3, 2, 1, 1, 1, 1, 4, 9]
def baseStart_1112498 : Nat := 118140960795 + 1112498 * 2 ^ 59
def prefixEnd_1112498 : Nat := 4983230072969 + 3 ^ 40 * 1112498 * 2
def baseEnd_1112498 : Nat := 42314533419681005937683

theorem tailTrace_1112498 : CollatzResearch.WordTrace tailWord_1112498 prefixEnd_1112498 42314533419681005937683 := by
  unfold tailWord_1112498
  simp only [CollatzResearch.WordTrace]
  refine ⟨10144033880904305094218537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27050757015744813584582765 10144033880904305094218537)
  ·
    refine ⟨7608025410678228820663903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10144033880904305094218537 7608025410678228820663903)
    ·
      refine ⟨11412038116017343230995855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7608025410678228820663903 11412038116017343230995855)
      ·
        refine ⟨17118057174026014846493783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11412038116017343230995855 17118057174026014846493783)
        ·
          refine ⟨25677085761039022269740675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17118057174026014846493783 25677085761039022269740675)
          ·
            refine ⟨38515628641558533404611013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25677085761039022269740675 38515628641558533404611013)
            ·
              refine ⟨7221680370292225013364565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38515628641558533404611013 7221680370292225013364565)
              ·
                refine ⟨42314533419681005937683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7221680370292225013364565 42314533419681005937683)
                ·
                  rfl

theorem cell22_1112498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_1112498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112498 prefixEnd_1112498 := by exact prefixLift 1112498
  have htrace : WordTrace (prefixWord ++ tailWord_1112498) baseStart_1112498 baseEnd_1112498 := by
    simpa [prefixWord, tailWord_1112498, baseEnd_1112498] using wordTrace_append hprefix tailTrace_1112498
  have hstable : (prefixWord ++ tailWord_1112498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112498).length < 2 ^ (prefixWord ++ tailWord_1112498).sum := by decide
  have hdescent : baseEnd_1112498 < baseStart_1112498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112560 : List Nat := [2, 1, 1, 1, 3, 3, 3, 3, 5]
def baseStart_1112560 : Nat := 118140960795 + 1112560 * 2 ^ 59
def prefixEnd_1112560 : Nat := 4983230072969 + 3 ^ 40 * 1112560 * 2
def baseEnd_1112560 : Nat := 126950674881393852796319

theorem tailTrace_1112560 : CollatzResearch.WordTrace tailWord_1112560 prefixEnd_1112560 126950674881393852796319 := by
  unfold tailWord_1112560
  simp only [CollatzResearch.WordTrace]
  refine ⟨20289198424696302482815567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27052264566261736643754089 20289198424696302482815567)
  ·
    refine ⟨30433797637044453724223351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20289198424696302482815567 30433797637044453724223351)
    ·
      refine ⟨45650696455566680586335027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30433797637044453724223351 45650696455566680586335027)
      ·
        refine ⟨68476044683350020879502541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45650696455566680586335027 68476044683350020879502541)
        ·
          refine ⟨25678516756256257829813453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68476044683350020879502541 25678516756256257829813453)
          ·
            refine ⟨9629443783596096686180045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25678516756256257829813453 9629443783596096686180045)
            ·
              refine ⟨3611041418848536257317517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9629443783596096686180045 3611041418848536257317517)
              ·
                refine ⟨1354140532068201096494069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3611041418848536257317517 1354140532068201096494069)
                ·
                  refine ⟨126950674881393852796319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1354140532068201096494069 126950674881393852796319)
                  ·
                    rfl

theorem cell22_1112560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 5].length) (baseStart_1112560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112560 prefixEnd_1112560 := by exact prefixLift 1112560
  have htrace : WordTrace (prefixWord ++ tailWord_1112560) baseStart_1112560 baseEnd_1112560 := by
    simpa [prefixWord, tailWord_1112560, baseEnd_1112560] using wordTrace_append hprefix tailTrace_1112560
  have hstable : (prefixWord ++ tailWord_1112560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112560).length < 2 ^ (prefixWord ++ tailWord_1112560).sum := by decide
  have hdescent : baseEnd_1112560 < baseStart_1112560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112637 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_1112637 : Nat := 118140960795 + 1112637 * 2 ^ 59
def prefixEnd_1112637 : Nat := 4983230072969 + 3 ^ 40 * 1112637 * 2
def baseEnd_1112637 : Nat := 380878383317779024213721

theorem tailTrace_1112637 : CollatzResearch.WordTrace tailWord_1112637 prefixEnd_1112637 380878383317779024213721 := by
  unfold tailWord_1112637
  simp only [CollatzResearch.WordTrace]
  refine ⟨40581205270113647116184165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27054136846742431410789443 40581205270113647116184165)
  ·
    refine ⟨7608975988146308834284531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40581205270113647116184165 7608975988146308834284531)
    ·
      refine ⟨11413463982219463251426797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7608975988146308834284531 11413463982219463251426797)
      ·
        refine ⟨4280048993332298719285049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11413463982219463251426797 4280048993332298719285049)
        ·
          refine ⟨3210036744999224039463787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4280048993332298719285049 3210036744999224039463787)
          ·
            refine ⟨4815055117498836059195681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3210036744999224039463787 4815055117498836059195681)
            ·
              refine ⟨3611291338124127044396761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4815055117498836059195681 3611291338124127044396761)
              ·
                refine ⟨2708468503593095283297571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3611291338124127044396761 2708468503593095283297571)
                ·
                  refine ⟨4062702755389642924946357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2708468503593095283297571 4062702755389642924946357)
                  ·
                    refine ⟨380878383317779024213721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4062702755389642924946357 380878383317779024213721)
                    ·
                      rfl

theorem cell22_1112637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_1112637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112637 prefixEnd_1112637 := by exact prefixLift 1112637
  have htrace : WordTrace (prefixWord ++ tailWord_1112637) baseStart_1112637 baseEnd_1112637 := by
    simpa [prefixWord, tailWord_1112637, baseEnd_1112637] using wordTrace_append hprefix tailTrace_1112637
  have hstable : (prefixWord ++ tailWord_1112637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112637).length < 2 ^ (prefixWord ++ tailWord_1112637).sum := by decide
  have hdescent : baseEnd_1112637 < baseStart_1112637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112641 : List Nat := [1, 2, 5, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1112641 : Nat := 118140960795 + 1112641 * 2 ^ 59
def prefixEnd_1112641 : Nat := 4983230072969 + 3 ^ 40 * 1112641 * 2
def baseEnd_1112641 : Nat := 380879752599524347113709

theorem tailTrace_1112641 : CollatzResearch.WordTrace tailWord_1112641 prefixEnd_1112641 380879752599524347113709 := by
  unfold tailWord_1112641
  simp only [CollatzResearch.WordTrace]
  refine ⟨40581351162099155799329777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27054234108066103866219851 40581351162099155799329777)
  ·
    refine ⟨30436013371574366849497333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40581351162099155799329777 30436013371574366849497333)
    ·
      refine ⟨2853376253585096892140375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30436013371574366849497333 2853376253585096892140375)
      ·
        refine ⟨4280064380377645338210563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2853376253585096892140375 4280064380377645338210563)
        ·
          refine ⟨6420096570566468007315845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4280064380377645338210563 6420096570566468007315845)
          ·
            refine ⟨1203768106981212751371721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6420096570566468007315845 1203768106981212751371721)
            ·
              refine ⟨902826080235909563528791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1203768106981212751371721 902826080235909563528791)
              ·
                refine ⟨1354239120353864345293187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 902826080235909563528791 1354239120353864345293187)
                ·
                  refine ⟨2031358680530796517939781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1354239120353864345293187 2031358680530796517939781)
                  ·
                    refine ⟨380879752599524347113709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2031358680530796517939781 380879752599524347113709)
                    ·
                      rfl

theorem cell22_1112641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1112641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112641 prefixEnd_1112641 := by exact prefixLift 1112641
  have htrace : WordTrace (prefixWord ++ tailWord_1112641) baseStart_1112641 baseEnd_1112641 := by
    simpa [prefixWord, tailWord_1112641, baseEnd_1112641] using wordTrace_append hprefix tailTrace_1112641
  have hstable : (prefixWord ++ tailWord_1112641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112641).length < 2 ^ (prefixWord ++ tailWord_1112641).sum := by decide
  have hdescent : baseEnd_1112641 < baseStart_1112641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112650 : List Nat := [3, 1, 2, 1, 1, 5, 9]
def baseStart_1112650 : Nat := 118140960795 + 1112650 * 2 ^ 59
def prefixEnd_1112650 : Nat := 4983230072969 + 3 ^ 40 * 1112650 * 2
def baseEnd_1112650 : Nat := 14106771610498197171803

theorem tailTrace_1112650 : CollatzResearch.WordTrace tailWord_1112650 prefixEnd_1112650 14106771610498197171803 := by
  unfold tailWord_1112650
  simp only [CollatzResearch.WordTrace]
  refine ⟨10145419854766637584101851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27054452946044366890938269 10145419854766637584101851)
  ·
    refine ⟨15218129782149956376152777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10145419854766637584101851 15218129782149956376152777)
    ·
      refine ⟨11413597336612467282114583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15218129782149956376152777 11413597336612467282114583)
      ·
        refine ⟨17120396004918700923171875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11413597336612467282114583 17120396004918700923171875)
        ·
          refine ⟨25680594007378051384757813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17120396004918700923171875 25680594007378051384757813)
          ·
            refine ⟨2407555688191692317321045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25680594007378051384757813 2407555688191692317321045)
            ·
              refine ⟨14106771610498197171803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2407555688191692317321045 14106771610498197171803)
              ·
                rfl

theorem cell22_1112650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 9].length) (baseStart_1112650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112650 prefixEnd_1112650 := by exact prefixLift 1112650
  have htrace : WordTrace (prefixWord ++ tailWord_1112650) baseStart_1112650 baseEnd_1112650 := by
    simpa [prefixWord, tailWord_1112650, baseEnd_1112650] using wordTrace_append hprefix tailTrace_1112650
  have hstable : (prefixWord ++ tailWord_1112650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112650).length < 2 ^ (prefixWord ++ tailWord_1112650).sum := by decide
  have hdescent : baseEnd_1112650 < baseStart_1112650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112654 : List Nat := [4, 1, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_1112654 : Nat := 118140960795 + 1112654 * 2 ^ 59
def prefixEnd_1112654 : Nat := 4983230072969 + 3 ^ 40 * 1112654 * 2
def baseEnd_1112654 : Nat := 380884202765196646538669

theorem tailTrace_1112654 : CollatzResearch.WordTrace tailWord_1112654 prefixEnd_1112654 380884202765196646538669 := by
  unfold tailWord_1112654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5072728163881507377444127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27054550207368039346368677 5072728163881507377444127)
  ·
    refine ⟨7609092245822261066166191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5072728163881507377444127 7609092245822261066166191)
    ·
      refine ⟨11413638368733391599249287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7609092245822261066166191 11413638368733391599249287)
      ·
        refine ⟨17120457553100087398873931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11413638368733391599249287 17120457553100087398873931)
        ·
          refine ⟨25680686329650131098310897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17120457553100087398873931 25680686329650131098310897)
          ·
            refine ⟨19260514747237598323733173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25680686329650131098310897 19260514747237598323733173)
            ·
              refine ⟨1805673257553524842849985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19260514747237598323733173 1805673257553524842849985)
              ·
                refine ⟨1354254943165143632137489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1805673257553524842849985 1354254943165143632137489)
                ·
                  refine ⟨1015691207373857724103117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1354254943165143632137489 1015691207373857724103117)
                  ·
                    refine ⟨380884202765196646538669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1015691207373857724103117 380884202765196646538669)
                    ·
                      rfl

theorem cell22_1112654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_1112654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112654 prefixEnd_1112654 := by exact prefixLift 1112654
  have htrace : WordTrace (prefixWord ++ tailWord_1112654) baseStart_1112654 baseEnd_1112654 := by
    simpa [prefixWord, tailWord_1112654, baseEnd_1112654] using wordTrace_append hprefix tailTrace_1112654
  have hstable : (prefixWord ++ tailWord_1112654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112654).length < 2 ^ (prefixWord ++ tailWord_1112654).sum := by decide
  have hdescent : baseEnd_1112654 < baseStart_1112654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112695 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 7]
def baseStart_1112695 : Nat := 118140960795 + 1112695 * 2 ^ 59
def prefixEnd_1112695 : Nat := 4983230072969 + 3 ^ 40 * 1112695 * 2
def baseEnd_1112695 : Nat := 126966079301028735421181

theorem tailTrace_1112695 : CollatzResearch.WordTrace tailWord_1112695 prefixEnd_1112695 126966079301028735421181 := by
  unfold tailWord_1112695
  simp only [CollatzResearch.WordTrace]
  refine ⟨40583320703903523021795539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27055547135935682014530359 40583320703903523021795539)
  ·
    refine ⟨60874981055855284532693309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40583320703903523021795539 60874981055855284532693309)
    ·
      refine ⟨22828117895945731699759991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60874981055855284532693309 22828117895945731699759991)
      ·
        refine ⟨34242176843918597549639987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22828117895945731699759991 34242176843918597549639987)
        ·
          refine ⟨51363265265877896324459981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34242176843918597549639987 51363265265877896324459981)
          ·
            refine ⟨19261224474704211121672493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51363265265877896324459981 19261224474704211121672493)
            ·
              refine ⟨7222959178014079170627185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19261224474704211121672493 7222959178014079170627185)
              ·
                refine ⟨5417219383510559377970389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7222959178014079170627185 5417219383510559377970389)
                ·
                  refine ⟨126966079301028735421181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5417219383510559377970389 126966079301028735421181)
                  ·
                    rfl

theorem cell22_1112695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 7].length) (baseStart_1112695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112695 prefixEnd_1112695 := by exact prefixLift 1112695
  have htrace : WordTrace (prefixWord ++ tailWord_1112695) baseStart_1112695 baseEnd_1112695 := by
    simpa [prefixWord, tailWord_1112695, baseEnd_1112695] using wordTrace_append hprefix tailTrace_1112695
  have hstable : (prefixWord ++ tailWord_1112695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112695).length < 2 ^ (prefixWord ++ tailWord_1112695).sum := by decide
  have hdescent : baseEnd_1112695 < baseStart_1112695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112699 : List Nat := [1, 1, 1, 1, 1, 4, 2, 7, 1, 3]
def baseStart_1112699 : Nat := 118140960795 + 1112699 * 2 ^ 59
def prefixEnd_1112699 : Nat := 4983230072969 + 3 ^ 40 * 1112699 * 2
def baseEnd_1112699 : Nat := 380899607184831529163531

theorem tailTrace_1112699 : CollatzResearch.WordTrace tailWord_1112699 prefixEnd_1112699 380899607184831529163531 := by
  unfold tailWord_1112699
  simp only [CollatzResearch.WordTrace]
  refine ⟨40583466595889031704941151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27055644397259354469960767 40583466595889031704941151)
  ·
    refine ⟨60875199893833547557411727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40583466595889031704941151 60875199893833547557411727)
    ·
      refine ⟨91312799840750321336117591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60875199893833547557411727 91312799840750321336117591)
      ·
        refine ⟨136969199761125482004176387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91312799840750321336117591 136969199761125482004176387)
        ·
          refine ⟨205453799641688223006264581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136969199761125482004176387 205453799641688223006264581)
          ·
            refine ⟨38522587432816541813674609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205453799641688223006264581 38522587432816541813674609)
            ·
              refine ⟨28891940574612406360255957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38522587432816541813674609 28891940574612406360255957)
              ·
                refine ⟨677154857217478274068499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28891940574612406360255957 677154857217478274068499)
                ·
                  refine ⟨1015732285826217411102749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677154857217478274068499 1015732285826217411102749)
                  ·
                    refine ⟨380899607184831529163531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1015732285826217411102749 380899607184831529163531)
                    ·
                      rfl

theorem cell22_1112699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 1, 3].length) (baseStart_1112699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112699 prefixEnd_1112699 := by exact prefixLift 1112699
  have htrace : WordTrace (prefixWord ++ tailWord_1112699) baseStart_1112699 baseEnd_1112699 := by
    simpa [prefixWord, tailWord_1112699, baseEnd_1112699] using wordTrace_append hprefix tailTrace_1112699
  have hstable : (prefixWord ++ tailWord_1112699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112699).length < 2 ^ (prefixWord ++ tailWord_1112699).sum := by decide
  have hdescent : baseEnd_1112699 < baseStart_1112699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112725 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_1112725 : Nat := 118140960795 + 1112725 * 2 ^ 59
def prefixEnd_1112725 : Nat := 4983230072969 + 3 ^ 40 * 1112725 * 2
def baseEnd_1112725 : Nat := 380908507516176128013451

theorem tailTrace_1112725 : CollatzResearch.WordTrace tailWord_1112725 prefixEnd_1112725 380908507516176128013451 := by
  unfold tailWord_1112725
  simp only [CollatzResearch.WordTrace]
  refine ⟨40584414893794838145387629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27056276595863225430258419 40584414893794838145387629)
  ·
    refine ⟨15219155585173064304520361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40584414893794838145387629 15219155585173064304520361)
    ·
      refine ⟨11414366688879798228390271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15219155585173064304520361 11414366688879798228390271)
      ·
        refine ⟨17121550033319697342585407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11414366688879798228390271 17121550033319697342585407)
        ·
          refine ⟨25682325049979546013878111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17121550033319697342585407 25682325049979546013878111)
          ·
            refine ⟨38523487574969319020817167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25682325049979546013878111 38523487574969319020817167)
            ·
              refine ⟨57785231362453978531225751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38523487574969319020817167 57785231362453978531225751)
              ·
                refine ⟨86677847043680967796838627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57785231362453978531225751 86677847043680967796838627)
                ·
                  refine ⟨130016770565521451695257941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86677847043680967796838627 130016770565521451695257941)
                  ·
                    refine ⟨380908507516176128013451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 130016770565521451695257941 380908507516176128013451)
                    ·
                      rfl

theorem cell22_1112725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_1112725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112725 prefixEnd_1112725 := by exact prefixLift 1112725
  have htrace : WordTrace (prefixWord ++ tailWord_1112725) baseStart_1112725 baseEnd_1112725 := by
    simpa [prefixWord, tailWord_1112725, baseEnd_1112725] using wordTrace_append hprefix tailTrace_1112725
  have hstable : (prefixWord ++ tailWord_1112725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112725).length < 2 ^ (prefixWord ++ tailWord_1112725).sum := by decide
  have hdescent : baseEnd_1112725 < baseStart_1112725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112804 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_1112804 : Nat := 118140960795 + 1112804 * 2 ^ 59
def prefixEnd_1112804 : Nat := 4983230072969 + 3 ^ 40 * 1112804 * 2
def baseEnd_1112804 : Nat := 380935550830646255288209

theorem tailTrace_1112804 : CollatzResearch.WordTrace tailWord_1112804 prefixEnd_1112804 380935550830646255288209 := by
  unfold tailWord_1112804
  simp only [CollatzResearch.WordTrace]
  refine ⟨20293648130254317318756733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27058197507005756425008977 20293648130254317318756733)
  ·
    refine ⟨7610118048845368994533775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20293648130254317318756733 7610118048845368994533775)
    ·
      refine ⟨11415177073268053491800663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7610118048845368994533775 11415177073268053491800663)
      ·
        refine ⟨17122765609902080237700995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11415177073268053491800663 17122765609902080237700995)
        ·
          refine ⟨25684148414853120356551493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17122765609902080237700995 25684148414853120356551493)
          ·
            refine ⟨4815777827784960066853405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25684148414853120356551493 4815777827784960066853405)
            ·
              refine ⟨1805916685419360025070027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4815777827784960066853405 1805916685419360025070027)
              ·
                refine ⟨2708875028129040037605041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805916685419360025070027 2708875028129040037605041)
                ·
                  refine ⟨2031656271096780028203781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2708875028129040037605041 2031656271096780028203781)
                  ·
                    refine ⟨380935550830646255288209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2031656271096780028203781 380935550830646255288209)
                    ·
                      rfl

theorem cell22_1112804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_1112804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112804 prefixEnd_1112804 := by exact prefixLift 1112804
  have htrace : WordTrace (prefixWord ++ tailWord_1112804) baseStart_1112804 baseEnd_1112804 := by
    simpa [prefixWord, tailWord_1112804, baseEnd_1112804] using wordTrace_append hprefix tailTrace_1112804
  have hstable : (prefixWord ++ tailWord_1112804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112804).length < 2 ^ (prefixWord ++ tailWord_1112804).sum := by decide
  have hdescent : baseEnd_1112804 < baseStart_1112804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112885 : List Nat := [1, 3, 3, 1, 3, 2, 3, 2, 1, 3]
def baseStart_1112885 : Nat := 118140960795 + 1112885 * 2 ^ 59
def prefixEnd_1112885 : Nat := 4983230072969 + 3 ^ 40 * 1112885 * 2
def baseEnd_1112885 : Nat := 380963278785989044012961

theorem tailTrace_1112885 : CollatzResearch.WordTrace tailWord_1112885 prefixEnd_1112885 380963278785989044012961 := by
  unfold tailWord_1112885
  simp only [CollatzResearch.WordTrace]
  refine ⟨40590250573215185471212109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27060167048810123647474739 40590250573215185471212109)
  ·
    refine ⟨15221343964955694551704541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40590250573215185471212109 15221343964955694551704541)
    ·
      refine ⟨5708003986858385456889203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15221343964955694551704541 5708003986858385456889203)
      ·
        refine ⟨8562005980287578185333805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5708003986858385456889203 8562005980287578185333805)
        ·
          refine ⟨3210752242607841819500177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8562005980287578185333805 3210752242607841819500177)
          ·
            refine ⟨2408064181955881364625133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3210752242607841819500177 2408064181955881364625133)
            ·
              refine ⟨903024068233455511734425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2408064181955881364625133 903024068233455511734425)
              ·
                refine ⟨677268051175091633800819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 903024068233455511734425 677268051175091633800819)
                ·
                  refine ⟨1015902076762637450701229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677268051175091633800819 1015902076762637450701229)
                  ·
                    refine ⟨380963278785989044012961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1015902076762637450701229 380963278785989044012961)
                    ·
                      rfl

theorem cell22_1112885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_1112885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112885 prefixEnd_1112885 := by exact prefixLift 1112885
  have htrace : WordTrace (prefixWord ++ tailWord_1112885) baseStart_1112885 baseEnd_1112885 := by
    simpa [prefixWord, tailWord_1112885, baseEnd_1112885] using wordTrace_append hprefix tailTrace_1112885
  have hstable : (prefixWord ++ tailWord_1112885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112885).length < 2 ^ (prefixWord ++ tailWord_1112885).sum := by decide
  have hdescent : baseEnd_1112885 < baseStart_1112885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112907 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 7, 5]
def baseStart_1112907 : Nat := 118140960795 + 1112907 * 2 ^ 59
def prefixEnd_1112907 : Nat := 4983230072969 + 3 ^ 40 * 1112907 * 2
def baseEnd_1112907 : Nat := 380970809835588319962893

theorem tailTrace_1112907 : CollatzResearch.WordTrace tailWord_1112907 prefixEnd_1112907 380970809835588319962893 := by
  unfold tailWord_1112907
  simp only [CollatzResearch.WordTrace]
  refine ⟨40591052979135483228512975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27060701986090322152341983 40591052979135483228512975)
  ·
    refine ⟨60886579468703224842769463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40591052979135483228512975 60886579468703224842769463)
    ·
      refine ⟨91329869203054837264154195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60886579468703224842769463 91329869203054837264154195)
      ·
        refine ⟨136994803804582255896231293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91329869203054837264154195 136994803804582255896231293)
        ·
          refine ⟨51373051426718345961086735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136994803804582255896231293 51373051426718345961086735)
          ·
            refine ⟨77059577140077518941630103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51373051426718345961086735 77059577140077518941630103)
            ·
              refine ⟨115589365710116278412445155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77059577140077518941630103 115589365710116278412445155)
              ·
                refine ⟨173384048565174417618667733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115589365710116278412445155 173384048565174417618667733)
                ·
                  refine ⟨4063688638246275412937525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 173384048565174417618667733 4063688638246275412937525)
                  ·
                    refine ⟨380970809835588319962893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4063688638246275412937525 380970809835588319962893)
                    ·
                      rfl

theorem cell22_1112907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 5].length) (baseStart_1112907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112907 prefixEnd_1112907 := by exact prefixLift 1112907
  have htrace : WordTrace (prefixWord ++ tailWord_1112907) baseStart_1112907 baseEnd_1112907 := by
    simpa [prefixWord, tailWord_1112907, baseEnd_1112907] using wordTrace_append hprefix tailTrace_1112907
  have hstable : (prefixWord ++ tailWord_1112907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112907).length < 2 ^ (prefixWord ++ tailWord_1112907).sum := by decide
  have hdescent : baseEnd_1112907 < baseStart_1112907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1112939 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 2, 4]
def baseStart_1112939 : Nat := 118140960795 + 1112939 * 2 ^ 59
def prefixEnd_1112939 : Nat := 4983230072969 + 3 ^ 40 * 1112939 * 2
def baseEnd_1112939 : Nat := 380981764089550903162795

theorem tailTrace_1112939 : CollatzResearch.WordTrace tailWord_1112939 prefixEnd_1112939 380981764089550903162795 := by
  unfold tailWord_1112939
  simp only [CollatzResearch.WordTrace]
  refine ⟨40592220115019552693677871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27061480076679701795785247 40592220115019552693677871)
  ·
    refine ⟨60888330172529329040516807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40592220115019552693677871 60888330172529329040516807)
    ·
      refine ⟨91332495258793993560775211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60888330172529329040516807 91332495258793993560775211)
      ·
        refine ⟨136998742888190990341162817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91332495258793993560775211 136998742888190990341162817)
        ·
          refine ⟨102749057166143242755872113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136998742888190990341162817 102749057166143242755872113)
          ·
            refine ⟨77061792874607432066904085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102749057166143242755872113 77061792874607432066904085)
            ·
              refine ⟨3612271540997223378136129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77061792874607432066904085 3612271540997223378136129)
              ·
                refine ⟨2709203655747917533602097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3612271540997223378136129 2709203655747917533602097)
                ·
                  refine ⟨2031902741810938150201573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2709203655747917533602097 2031902741810938150201573)
                  ·
                    refine ⟨380981764089550903162795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2031902741810938150201573 380981764089550903162795)
                    ·
                      rfl

theorem cell22_1112939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 4].length) (baseStart_1112939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1112939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1112939 prefixEnd_1112939 := by exact prefixLift 1112939
  have htrace : WordTrace (prefixWord ++ tailWord_1112939) baseStart_1112939 baseEnd_1112939 := by
    simpa [prefixWord, tailWord_1112939, baseEnd_1112939] using wordTrace_append hprefix tailTrace_1112939
  have hstable : (prefixWord ++ tailWord_1112939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1112939).length < 2 ^ (prefixWord ++ tailWord_1112939).sum := by decide
  have hdescent : baseEnd_1112939 < baseStart_1112939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1112939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113029 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_1113029 : Nat := 118140960795 + 1113029 * 2 ^ 59
def prefixEnd_1113029 : Nat := 4983230072969 + 3 ^ 40 * 1113029 * 2
def baseEnd_1113029 : Nat := 381012572928820668412519

theorem tailTrace_1113029 : CollatzResearch.WordTrace tailWord_1113029 prefixEnd_1113029 381012572928820668412519 := by
  unfold tailWord_1113029
  simp only [CollatzResearch.WordTrace]
  refine ⟨40595502684693498064454141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27063668456462332042969427 40595502684693498064454141)
  ·
    refine ⟨15223313506760061774170303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40595502684693498064454141 15223313506760061774170303)
    ·
      refine ⟨22834970260140092661255455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15223313506760061774170303 22834970260140092661255455)
      ·
        refine ⟨34252455390210138991883183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22834970260140092661255455 34252455390210138991883183)
        ·
          refine ⟨51378683085315208487824775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34252455390210138991883183 51378683085315208487824775)
          ·
            refine ⟨77068024627972812731737163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51378683085315208487824775 77068024627972812731737163)
            ·
              refine ⟨115602036941959219097605745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77068024627972812731737163 115602036941959219097605745)
              ·
                refine ⟨86701527706469414323204309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115602036941959219097605745 86701527706469414323204309)
                ·
                  refine ⟨2032067055620376898200101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 86701527706469414323204309 2032067055620376898200101)
                  ·
                    refine ⟨381012572928820668412519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2032067055620376898200101 381012572928820668412519)
                    ·
                      rfl

theorem cell22_1113029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_1113029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113029 prefixEnd_1113029 := by exact prefixLift 1113029
  have htrace : WordTrace (prefixWord ++ tailWord_1113029) baseStart_1113029 baseEnd_1113029 := by
    simpa [prefixWord, tailWord_1113029, baseEnd_1113029] using wordTrace_append hprefix tailTrace_1113029
  have hstable : (prefixWord ++ tailWord_1113029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113029).length < 2 ^ (prefixWord ++ tailWord_1113029).sum := by decide
  have hdescent : baseEnd_1113029 < baseStart_1113029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113138 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_1113138 : Nat := 118140960795 + 1113138 * 2 ^ 59
def prefixEnd_1113138 : Nat := 4983230072969 + 3 ^ 40 * 1113138 * 2
def baseEnd_1113138 : Nat := 381049885856380717437185

theorem tailTrace_1113138 : CollatzResearch.WordTrace tailWord_1113138 prefixEnd_1113138 381049885856380717437185 := by
  unfold tailWord_1113138
  simp only [CollatzResearch.WordTrace]
  refine ⟨10149869560324652420043017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27066318827532406453448045 10149869560324652420043017)
  ·
    refine ⟨7612402170243489315032263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10149869560324652420043017 7612402170243489315032263)
    ·
      refine ⟨11418603255365233972548395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7612402170243489315032263 11418603255365233972548395)
      ·
        refine ⟨17127904883047850958822593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11418603255365233972548395 17127904883047850958822593)
        ·
          refine ⟨12845928662285888219116945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17127904883047850958822593 12845928662285888219116945)
          ·
            refine ⟨9634446496714416164337709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12845928662285888219116945 9634446496714416164337709)
            ·
              refine ⟨3612917436267906061626641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9634446496714416164337709 3612917436267906061626641)
              ·
                refine ⟨2709688077200929546219981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3612917436267906061626641 2709688077200929546219981)
                ·
                  refine ⟨1016133028950348579832493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2709688077200929546219981 1016133028950348579832493)
                  ·
                    refine ⟨381049885856380717437185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1016133028950348579832493 381049885856380717437185)
                    ·
                      rfl

theorem cell22_1113138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_1113138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113138 prefixEnd_1113138 := by exact prefixLift 1113138
  have htrace : WordTrace (prefixWord ++ tailWord_1113138) baseStart_1113138 baseEnd_1113138 := by
    simpa [prefixWord, tailWord_1113138, baseEnd_1113138] using wordTrace_append hprefix tailTrace_1113138
  have hstable : (prefixWord ++ tailWord_1113138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113138).length < 2 ^ (prefixWord ++ tailWord_1113138).sum := by decide
  have hdescent : baseEnd_1113138 < baseStart_1113138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113140 : List Nat := [2, 5, 1, 2, 1, 2, 3, 6]
def baseStart_1113140 : Nat := 118140960795 + 1113140 * 2 ^ 59
def prefixEnd_1113140 : Nat := 4983230072969 + 3 ^ 40 * 1113140 * 2
def baseEnd_1113140 : Nat := 42338952277472597654131

theorem tailTrace_1113140 : CollatzResearch.WordTrace tailWord_1113140 prefixEnd_1113140 42338952277472597654131 := by
  unfold tailWord_1113140
  simp only [CollatzResearch.WordTrace]
  refine ⟨20299775593645682010872437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27066367458194242681163249 20299775593645682010872437)
  ·
    refine ⟨1903103961904282688519291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20299775593645682010872437 1903103961904282688519291)
    ·
      refine ⟨2854655942856424032778937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1903103961904282688519291 2854655942856424032778937)
      ·
        refine ⟨2140991957142318024584203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2854655942856424032778937 2140991957142318024584203)
        ·
          refine ⟨3211487935713477036876305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2140991957142318024584203 3211487935713477036876305)
          ·
            refine ⟨2408615951785107777657229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3211487935713477036876305 2408615951785107777657229)
            ·
              refine ⟨903230981919415416621461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2408615951785107777657229 903230981919415416621461)
              ·
                refine ⟨42338952277472597654131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 903230981919415416621461 42338952277472597654131)
                ·
                  rfl

theorem cell22_1113140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 6].length) (baseStart_1113140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113140 prefixEnd_1113140 := by exact prefixLift 1113140
  have htrace : WordTrace (prefixWord ++ tailWord_1113140) baseStart_1113140 baseEnd_1113140 := by
    simpa [prefixWord, tailWord_1113140, baseEnd_1113140] using wordTrace_append hprefix tailTrace_1113140
  have hstable : (prefixWord ++ tailWord_1113140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113140).length < 2 ^ (prefixWord ++ tailWord_1113140).sum := by decide
  have hdescent : baseEnd_1113140 < baseStart_1113140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113155 : List Nat := [1, 1, 1, 3, 1, 2, 6, 3, 1, 3]
def baseStart_1113155 : Nat := 118140960795 + 1113155 * 2 ^ 59
def prefixEnd_1113155 : Nat := 4983230072969 + 3 ^ 40 * 1113155 * 2
def baseEnd_1113155 : Nat := 381055705303798339762133

theorem tailTrace_1113155 : CollatzResearch.WordTrace tailWord_1113155 prefixEnd_1113155 381055705303798339762133 := by
  unfold tailWord_1113155
  simp only [CollatzResearch.WordTrace]
  refine ⟨40600098282237021583540919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27066732188158014389027279 40600098282237021583540919)
  ·
    refine ⟨60900147423355532375311379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40600098282237021583540919 60900147423355532375311379)
    ·
      refine ⟨91350221135033298562967069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60900147423355532375311379 91350221135033298562967069)
      ·
        refine ⟨34256332925637486961112651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91350221135033298562967069 34256332925637486961112651)
        ·
          refine ⟨51384499388456230441668977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34256332925637486961112651 51384499388456230441668977)
          ·
            refine ⟨38538374541342172831251733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51384499388456230441668977 38538374541342172831251733)
            ·
              refine ⟨1806486306625414351464925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38538374541342172831251733 1806486306625414351464925)
              ·
                refine ⟨677432364984530381799347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1806486306625414351464925 677432364984530381799347)
                ·
                  refine ⟨1016148547476795572699021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677432364984530381799347 1016148547476795572699021)
                  ·
                    refine ⟨381055705303798339762133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1016148547476795572699021 381055705303798339762133)
                    ·
                      rfl

theorem cell22_1113155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 1, 3].length) (baseStart_1113155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113155 prefixEnd_1113155 := by exact prefixLift 1113155
  have htrace : WordTrace (prefixWord ++ tailWord_1113155) baseStart_1113155 baseEnd_1113155 := by
    simpa [prefixWord, tailWord_1113155, baseEnd_1113155] using wordTrace_append hprefix tailTrace_1113155
  have hstable : (prefixWord ++ tailWord_1113155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113155).length < 2 ^ (prefixWord ++ tailWord_1113155).sum := by decide
  have hdescent : baseEnd_1113155 < baseStart_1113155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113166 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_1113166 : Nat := 118140960795 + 1113166 * 2 ^ 59
def prefixEnd_1113166 : Nat := 4983230072969 + 3 ^ 40 * 1113166 * 2
def baseEnd_1113166 : Nat := 381059470828597977737099

theorem tailTrace_1113166 : CollatzResearch.WordTrace tailWord_1113166 prefixEnd_1113166 381059470828597977737099 := by
  unfold tailWord_1113166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5075062435649646307773919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27066999656798113641460901 5075062435649646307773919)
  ·
    refine ⟨7612593653474469461660879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5075062435649646307773919 7612593653474469461660879)
    ·
      refine ⟨11418890480211704192491319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7612593653474469461660879 11418890480211704192491319)
      ·
        refine ⟨17128335720317556288736979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11418890480211704192491319 17128335720317556288736979)
        ·
          refine ⟨25692503580476334433105469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17128335720317556288736979 25692503580476334433105469)
          ·
            refine ⟨9634688842678625412414551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25692503580476334433105469 9634688842678625412414551)
            ·
              refine ⟨14452033264017938118621827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9634688842678625412414551 14452033264017938118621827)
              ·
                refine ⟨21678049896026907177932741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14452033264017938118621827 21678049896026907177932741)
                ·
                  refine ⟨4064634355505045095862389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21678049896026907177932741 4064634355505045095862389)
                  ·
                    refine ⟨381059470828597977737099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4064634355505045095862389 381059470828597977737099)
                    ·
                      rfl

theorem cell22_1113166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_1113166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113166 prefixEnd_1113166 := by exact prefixLift 1113166
  have htrace : WordTrace (prefixWord ++ tailWord_1113166) baseStart_1113166 baseEnd_1113166 := by
    simpa [prefixWord, tailWord_1113166, baseEnd_1113166] using wordTrace_append hprefix tailTrace_1113166
  have hstable : (prefixWord ++ tailWord_1113166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113166).length < 2 ^ (prefixWord ++ tailWord_1113166).sum := by decide
  have hdescent : baseEnd_1113166 < baseStart_1113166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113196 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 6]
def baseStart_1113196 : Nat := 118140960795 + 1113196 * 2 ^ 59
def prefixEnd_1113196 : Nat := 4983230072969 + 3 ^ 40 * 1113196 * 2
def baseEnd_1113196 : Nat := 127023246813895966495669

theorem tailTrace_1113196 : CollatzResearch.WordTrace tailWord_1113196 prefixEnd_1113196 127023246813895966495669 := by
  unfold tailWord_1113196
  simp only [CollatzResearch.WordTrace]
  refine ⟨20300796837544242792891721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27067729116725657057188961 20300796837544242792891721)
  ·
    refine ⟨15225597628158182094668791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20300796837544242792891721 15225597628158182094668791)
    ·
      refine ⟨22838396442237273142003187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15225597628158182094668791 22838396442237273142003187)
      ·
        refine ⟨34257594663355909713004781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22838396442237273142003187 34257594663355909713004781)
        ·
          refine ⟨12846597998758466142376793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34257594663355909713004781 12846597998758466142376793)
          ·
            refine ⟨9634948499068849606782595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12846597998758466142376793 9634948499068849606782595)
            ·
              refine ⟨14452422748603274410173893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9634948499068849606782595 14452422748603274410173893)
              ·
                refine ⟨2709829265363113951907605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14452422748603274410173893 2709829265363113951907605)
                ·
                  refine ⟨127023246813895966495669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2709829265363113951907605 127023246813895966495669)
                  ·
                    rfl

theorem cell22_1113196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_1113196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113196 prefixEnd_1113196 := by exact prefixLift 1113196
  have htrace : WordTrace (prefixWord ++ tailWord_1113196) baseStart_1113196 baseEnd_1113196 := by
    simpa [prefixWord, tailWord_1113196, baseEnd_1113196] using wordTrace_append hprefix tailTrace_1113196
  have hstable : (prefixWord ++ tailWord_1113196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113196).length < 2 ^ (prefixWord ++ tailWord_1113196).sum := by decide
  have hdescent : baseEnd_1113196 < baseStart_1113196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113211 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 1, 5]
def baseStart_1113211 : Nat := 118140960795 + 1113211 * 2 ^ 59
def prefixEnd_1113211 : Nat := 4983230072969 + 3 ^ 40 * 1113211 * 2
def baseEnd_1113211 : Nat := 381074875248232860361961

theorem tailTrace_1113211 : CollatzResearch.WordTrace tailWord_1113211 prefixEnd_1113211 381074875248232860361961 := by
  unfold tailWord_1113211
  simp only [CollatzResearch.WordTrace]
  refine ⟨40602140770034143147579487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27068093846689428765052991 40602140770034143147579487)
  ·
    refine ⟨60903211155051214721369231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40602140770034143147579487 60903211155051214721369231)
    ·
      refine ⟨91354816732576822082053847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60903211155051214721369231 91354816732576822082053847)
      ·
        refine ⟨137032225098865233123080771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91354816732576822082053847 137032225098865233123080771)
        ·
          refine ⟨205548337648297849684621157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137032225098865233123080771 205548337648297849684621157)
          ·
            refine ⟨38540313309055846815866467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 205548337648297849684621157 38540313309055846815866467)
            ·
              refine ⟨57810469963583770223799701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38540313309055846815866467 57810469963583770223799701)
              ·
                refine ⟨2709865779542989229240611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57810469963583770223799701 2709865779542989229240611)
                ·
                  refine ⟨4064798669314483843860917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2709865779542989229240611 4064798669314483843860917)
                  ·
                    refine ⟨381074875248232860361961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4064798669314483843860917 381074875248232860361961)
                    ·
                      rfl

theorem cell22_1113211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 5].length) (baseStart_1113211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113211 prefixEnd_1113211 := by exact prefixLift 1113211
  have htrace : WordTrace (prefixWord ++ tailWord_1113211) baseStart_1113211 baseEnd_1113211 := by
    simpa [prefixWord, tailWord_1113211, baseEnd_1113211] using wordTrace_append hprefix tailTrace_1113211
  have hstable : (prefixWord ++ tailWord_1113211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113211).length < 2 ^ (prefixWord ++ tailWord_1113211).sum := by decide
  have hdescent : baseEnd_1113211 < baseStart_1113211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113230 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_1113230 : Nat := 118140960795 + 1113230 * 2 ^ 59
def prefixEnd_1113230 : Nat := 4983230072969 + 3 ^ 40 * 1113230 * 2
def baseEnd_1113230 : Nat := 127027126445507714712301

theorem tailTrace_1113230 : CollatzResearch.WordTrace tailWord_1113230 prefixEnd_1113230 127027126445507714712301 := by
  unfold tailWord_1113230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5075354219620663674065143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27068555837976872928347429 5075354219620663674065143)
  ·
    refine ⟨7613031329430995511097715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5075354219620663674065143 7613031329430995511097715)
    ·
      refine ⟨11419546994146493266646573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7613031329430995511097715 11419546994146493266646573)
      ·
        refine ⟨4282330122804934974992465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11419546994146493266646573 4282330122804934974992465)
        ·
          refine ⟨3211747592103701231244349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4282330122804934974992465 3211747592103701231244349)
          ·
            refine ⟨1204405347038887961716631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3211747592103701231244349 1204405347038887961716631)
            ·
              refine ⟨1806608020558331942574947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204405347038887961716631 1806608020558331942574947)
              ·
                refine ⟨2709912030837497913862421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806608020558331942574947 2709912030837497913862421)
                ·
                  refine ⟨127027126445507714712301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2709912030837497913862421 127027126445507714712301)
                  ·
                    rfl

theorem cell22_1113230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_1113230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113230 prefixEnd_1113230 := by exact prefixLift 1113230
  have htrace : WordTrace (prefixWord ++ tailWord_1113230) baseStart_1113230 baseEnd_1113230 := by
    simpa [prefixWord, tailWord_1113230, baseEnd_1113230] using wordTrace_append hprefix tailTrace_1113230
  have hstable : (prefixWord ++ tailWord_1113230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113230).length < 2 ^ (prefixWord ++ tailWord_1113230).sum := by decide
  have hdescent : baseEnd_1113230 < baseStart_1113230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113245 : List Nat := [1, 4, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_1113245 : Nat := 118140960795 + 1113245 * 2 ^ 59
def prefixEnd_1113245 : Nat := 4983230072969 + 3 ^ 40 * 1113245 * 2
def baseEnd_1113245 : Nat := 381086514143068105011857

theorem tailTrace_1113245 : CollatzResearch.WordTrace tailWord_1113245 prefixEnd_1113245 381086514143068105011857 := by
  unfold tailWord_1113245
  simp only [CollatzResearch.WordTrace]
  refine ⟨40603380851910966954317189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27068920567940644636211459 40603380851910966954317189)
  ·
    refine ⟨7613133909733306303934473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40603380851910966954317189 7613133909733306303934473)
    ·
      refine ⟨5709850432299979727950855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7613133909733306303934473 5709850432299979727950855)
      ·
        refine ⟨8564775648449969591926283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5709850432299979727950855 8564775648449969591926283)
        ·
          refine ⟨12847163472674954387889425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8564775648449969591926283 12847163472674954387889425)
          ·
            refine ⟨9635372604506215790917069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12847163472674954387889425 9635372604506215790917069)
            ·
              refine ⟨3613264726689830921593901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9635372604506215790917069 3613264726689830921593901)
              ·
                refine ⟨1354974272508686595597713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3613264726689830921593901 1354974272508686595597713)
                ·
                  refine ⟨1016230704381514946698285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1354974272508686595597713 1016230704381514946698285)
                  ·
                    refine ⟨381086514143068105011857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1016230704381514946698285 381086514143068105011857)
                    ·
                      rfl

theorem cell22_1113245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_1113245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113245 prefixEnd_1113245 := by exact prefixLift 1113245
  have htrace : WordTrace (prefixWord ++ tailWord_1113245) baseStart_1113245 baseEnd_1113245 := by
    simpa [prefixWord, tailWord_1113245, baseEnd_1113245] using wordTrace_append hprefix tailTrace_1113245
  have hstable : (prefixWord ++ tailWord_1113245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113245).length < 2 ^ (prefixWord ++ tailWord_1113245).sum := by decide
  have hdescent : baseEnd_1113245 < baseStart_1113245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113303 : List Nat := [1, 1, 3, 2, 1, 2, 4, 3, 5]
def baseStart_1113303 : Nat := 118140960795 + 1113303 * 2 ^ 59
def prefixEnd_1113303 : Nat := 4983230072969 + 3 ^ 40 * 1113303 * 2
def baseEnd_1113303 : Nat := 127035456242791762353893

theorem tailTrace_1113303 : CollatzResearch.WordTrace tailWord_1113303 prefixEnd_1113303 127035456242791762353893 := by
  unfold tailWord_1113303
  simp only [CollatzResearch.WordTrace]
  refine ⟨40605496285700842859928563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27070330857133895239952375 40605496285700842859928563)
  ·
    refine ⟨60908244428551264289892845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40605496285700842859928563 60908244428551264289892845)
    ·
      refine ⟨22840591660706724108709817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60908244428551264289892845 22840591660706724108709817)
      ·
        refine ⟨17130443745530043081532363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22840591660706724108709817 17130443745530043081532363)
        ·
          refine ⟨25695665618295064622298545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17130443745530043081532363 25695665618295064622298545)
          ·
            refine ⟨19271749213721298466723909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25695665618295064622298545 19271749213721298466723909)
            ·
              refine ⟨3613452977572743462510733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19271749213721298466723909 3613452977572743462510733)
              ·
                refine ⟨1355044866589778798441525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3613452977572743462510733 1355044866589778798441525)
                ·
                  refine ⟨127035456242791762353893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1355044866589778798441525 127035456242791762353893)
                  ·
                    rfl

theorem cell22_1113303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 5].length) (baseStart_1113303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113303 prefixEnd_1113303 := by exact prefixLift 1113303
  have htrace : WordTrace (prefixWord ++ tailWord_1113303) baseStart_1113303 baseEnd_1113303 := by
    simpa [prefixWord, tailWord_1113303, baseEnd_1113303] using wordTrace_append hprefix tailTrace_1113303
  have hstable : (prefixWord ++ tailWord_1113303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113303).length < 2 ^ (prefixWord ++ tailWord_1113303).sum := by decide
  have hdescent : baseEnd_1113303 < baseStart_1113303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113380 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_1113380 : Nat := 118140960795 + 1113380 * 2 ^ 59
def prefixEnd_1113380 : Nat := 4983230072969 + 3 ^ 40 * 1113380 * 2
def baseEnd_1113380 : Nat := 381132727401972752886443

theorem tailTrace_1113380 : CollatzResearch.WordTrace tailWord_1113380 prefixEnd_1113380 381132727401972752886443 := by
  unfold tailWord_1113380
  simp only [CollatzResearch.WordTrace]
  refine ⟨20304152353210942505240797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27072203137614590006987729 20304152353210942505240797)
  ·
    refine ⟨7614057132454103439465299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20304152353210942505240797 7614057132454103439465299)
    ·
      refine ⟨11421085698681155159197949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7614057132454103439465299 11421085698681155159197949)
      ·
        refine ⟨4282907137005433184699231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11421085698681155159197949 4282907137005433184699231)
        ·
          refine ⟨6424360705508149777048847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4282907137005433184699231 6424360705508149777048847)
          ·
            refine ⟨9636541058262224665573271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6424360705508149777048847 9636541058262224665573271)
            ·
              refine ⟨14454811587393336998359907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9636541058262224665573271 14454811587393336998359907)
              ·
                refine ⟨21682217381090005497539861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14454811587393336998359907 21682217381090005497539861)
                ·
                  refine ⟨1016353939738594007697181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21682217381090005497539861 1016353939738594007697181)
                  ·
                    refine ⟨381132727401972752886443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1016353939738594007697181 381132727401972752886443)
                    ·
                      rfl

theorem cell22_1113380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_1113380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113380 prefixEnd_1113380 := by exact prefixLift 1113380
  have htrace : WordTrace (prefixWord ++ tailWord_1113380) baseStart_1113380 baseEnd_1113380 := by
    simpa [prefixWord, tailWord_1113380, baseEnd_1113380] using wordTrace_append hprefix tailTrace_1113380
  have hstable : (prefixWord ++ tailWord_1113380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113380).length < 2 ^ (prefixWord ++ tailWord_1113380).sum := by decide
  have hdescent : baseEnd_1113380 < baseStart_1113380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113393 : List Nat := [1, 2, 2, 3, 3, 1, 10]
def baseStart_1113393 : Nat := 118140960795 + 1113393 * 2 ^ 59
def prefixEnd_1113393 : Nat := 4983230072969 + 3 ^ 40 * 1113393 * 2
def baseEnd_1113393 : Nat := 14116191761764631567089

theorem tailTrace_1113393 : CollatzResearch.WordTrace tailWord_1113393 prefixEnd_1113393 14116191761764631567089 := by
  unfold tailWord_1113393
  simp only [CollatzResearch.WordTrace]
  refine ⟨40608778855374788230704833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27072519236916525487136555 40608778855374788230704833)
  ·
    refine ⟨30456584141531091173028625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40608778855374788230704833 30456584141531091173028625)
    ·
      refine ⟨22842438106148318379771469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30456584141531091173028625 22842438106148318379771469)
      ·
        refine ⟨8565914289805619392414301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22842438106148318379771469 8565914289805619392414301)
        ·
          refine ⟨3212217858677107272155363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8565914289805619392414301 3212217858677107272155363)
          ·
            refine ⟨4818326788015660908233045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3212217858677107272155363 4818326788015660908233045)
            ·
              refine ⟨14116191761764631567089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4818326788015660908233045 14116191761764631567089)
              ·
                rfl

theorem cell22_1113393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 10].length) (baseStart_1113393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113393 prefixEnd_1113393 := by exact prefixLift 1113393
  have htrace : WordTrace (prefixWord ++ tailWord_1113393) baseStart_1113393 baseEnd_1113393 := by
    simpa [prefixWord, tailWord_1113393, baseEnd_1113393] using wordTrace_append hprefix tailTrace_1113393
  have hstable : (prefixWord ++ tailWord_1113393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113393).length < 2 ^ (prefixWord ++ tailWord_1113393).sum := by decide
  have hdescent : baseEnd_1113393 < baseStart_1113393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113395 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 2, 4]
def baseStart_1113395 : Nat := 118140960795 + 1113395 * 2 ^ 59
def prefixEnd_1113395 : Nat := 4983230072969 + 3 ^ 40 * 1113395 * 2
def baseEnd_1113395 : Nat := 381137862208517713761397

theorem tailTrace_1113395 : CollatzResearch.WordTrace tailWord_1113395 prefixEnd_1113395 381137862208517713761397 := by
  unfold tailWord_1113395
  simp only [CollatzResearch.WordTrace]
  refine ⟨40608851801367542572277639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27072567867578361714851759 40608851801367542572277639)
  ·
    refine ⟨60913277702051313858416459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40608851801367542572277639 60913277702051313858416459)
    ·
      refine ⟨91369916553076970787624689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60913277702051313858416459 91369916553076970787624689)
      ·
        refine ⟨68527437414807728090718517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91369916553076970787624689 68527437414807728090718517)
        ·
          refine ⟨6424447257638224508504861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68527437414807728090718517 6424447257638224508504861)
          ·
            refine ⟨2409167721614334190689323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6424447257638224508504861 2409167721614334190689323)
            ·
              refine ⟨3613751582421501286033985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2409167721614334190689323 3613751582421501286033985)
              ·
                refine ⟨2710313686816125964525489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3613751582421501286033985 2710313686816125964525489)
                ·
                  refine ⟨2032735265112094473394117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2710313686816125964525489 2032735265112094473394117)
                  ·
                    refine ⟨381137862208517713761397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2032735265112094473394117 381137862208517713761397)
                    ·
                      rfl

theorem cell22_1113395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 4].length) (baseStart_1113395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113395 prefixEnd_1113395 := by exact prefixLift 1113395
  have htrace : WordTrace (prefixWord ++ tailWord_1113395) baseStart_1113395 baseEnd_1113395 := by
    simpa [prefixWord, tailWord_1113395, baseEnd_1113395] using wordTrace_append hprefix tailTrace_1113395
  have hstable : (prefixWord ++ tailWord_1113395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113395).length < 2 ^ (prefixWord ++ tailWord_1113395).sum := by decide
  have hdescent : baseEnd_1113395 < baseStart_1113395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113425 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 5, 3]
def baseStart_1113425 : Nat := 118140960795 + 1113425 * 2 ^ 59
def prefixEnd_1113425 : Nat := 4983230072969 + 3 ^ 40 * 1113425 * 2
def baseEnd_1113425 : Nat := 381148131821607635511305

theorem tailTrace_1113425 : CollatzResearch.WordTrace tailWord_1113425 prefixEnd_1113425 381148131821607635511305 := by
  unfold tailWord_1113425
  simp only [CollatzResearch.WordTrace]
  refine ⟨40609945991258857695869729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27073297327505905130579819 40609945991258857695869729)
  ·
    refine ⟨30457459493444143271902297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40609945991258857695869729 30457459493444143271902297)
    ·
      refine ⟨22843094620083107453926723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30457459493444143271902297 22843094620083107453926723)
      ·
        refine ⟨34264641930124661180890085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22843094620083107453926723 34264641930124661180890085)
        ·
          refine ⟨6424620361898373971416891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34264641930124661180890085 6424620361898373971416891)
          ·
            refine ⟨9636930542847560957125337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6424620361898373971416891 9636930542847560957125337)
            ·
              refine ⟨7227697907135670717844003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9636930542847560957125337 7227697907135670717844003)
              ·
                refine ⟨10841546860703506076766005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7227697907135670717844003 10841546860703506076766005)
                ·
                  refine ⟨1016395018190953694696813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10841546860703506076766005 1016395018190953694696813)
                  ·
                    refine ⟨381148131821607635511305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1016395018190953694696813 381148131821607635511305)
                    ·
                      rfl

theorem cell22_1113425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_1113425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113425 prefixEnd_1113425 := by exact prefixLift 1113425
  have htrace : WordTrace (prefixWord ++ tailWord_1113425) baseStart_1113425 baseEnd_1113425 := by
    simpa [prefixWord, tailWord_1113425, baseEnd_1113425] using wordTrace_append hprefix tailTrace_1113425
  have hstable : (prefixWord ++ tailWord_1113425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113425).length < 2 ^ (prefixWord ++ tailWord_1113425).sum := by decide
  have hdescent : baseEnd_1113425 < baseStart_1113425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113455 : List Nat := [1, 1, 2, 1, 3, 1, 6, 2, 5]
def baseStart_1113455 : Nat := 118140960795 + 1113455 * 2 ^ 59
def prefixEnd_1113455 : Nat := 4983230072969 + 3 ^ 40 * 1113455 * 2
def baseEnd_1113455 : Nat := 127052800478232519087071

theorem tailTrace_1113455 : CollatzResearch.WordTrace tailWord_1113455 prefixEnd_1113455 127052800478232519087071 := by
  unfold tailWord_1113455
  simp only [CollatzResearch.WordTrace]
  refine ⟨40611040181150172819461819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27074026787433448546307879 40611040181150172819461819)
  ·
    refine ⟨60916560271725259229192729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40611040181150172819461819 60916560271725259229192729)
    ·
      refine ⟨45687420203793944421894547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60916560271725259229192729 45687420203793944421894547)
      ·
        refine ⟨68531130305690916632841821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45687420203793944421894547 68531130305690916632841821)
        ·
          refine ⟨25699173864634093737315683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68531130305690916632841821 25699173864634093737315683)
          ·
            refine ⟨38548760796951140605973525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25699173864634093737315683 38548760796951140605973525)
            ·
              refine ⟨1806973162357084715905009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38548760796951140605973525 1806973162357084715905009)
              ·
                refine ⟨1355229871767813536928757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1806973162357084715905009 1355229871767813536928757)
                ·
                  refine ⟨127052800478232519087071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1355229871767813536928757 127052800478232519087071)
                  ·
                    rfl

theorem cell22_1113455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 5].length) (baseStart_1113455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113455 prefixEnd_1113455 := by exact prefixLift 1113455
  have htrace : WordTrace (prefixWord ++ tailWord_1113455) baseStart_1113455 baseEnd_1113455 := by
    simpa [prefixWord, tailWord_1113455, baseEnd_1113455] using wordTrace_append hprefix tailTrace_1113455
  have hstable : (prefixWord ++ tailWord_1113455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113455).length < 2 ^ (prefixWord ++ tailWord_1113455).sum := by decide
  have hdescent : baseEnd_1113455 < baseStart_1113455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113517 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 6]
def baseStart_1113517 : Nat := 118140960795 + 1113517 * 2 ^ 59
def prefixEnd_1113517 : Nat := 4983230072969 + 3 ^ 40 * 1113517 * 2
def baseEnd_1113517 : Nat := 127059875100583354070341

theorem tailTrace_1113517 : CollatzResearch.WordTrace tailWord_1113517 prefixEnd_1113517 127059875100583354070341 := by
  unfold tailWord_1113517
  simp only [CollatzResearch.WordTrace]
  refine ⟨40613301506925557408218805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27075534337950371605479203 40613301506925557408218805)
  ·
    refine ⟨3807497016274271007020513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40613301506925557408218805 3807497016274271007020513)
    ·
      refine ⟨2855622762205703255265385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3807497016274271007020513 2855622762205703255265385)
      ·
        refine ⟨2141717071654277441449039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2855622762205703255265385 2141717071654277441449039)
        ·
          refine ⟨3212575607481416162173559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2141717071654277441449039 3212575607481416162173559)
          ·
            refine ⟨4818863411222124243260339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3212575607481416162173559 4818863411222124243260339)
            ·
              refine ⟨7228295116833186364890509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4818863411222124243260339 7228295116833186364890509)
              ·
                refine ⟨2710610668812444886833941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7228295116833186364890509 2710610668812444886833941)
                ·
                  refine ⟨127059875100583354070341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2710610668812444886833941 127059875100583354070341)
                  ·
                    rfl

theorem cell22_1113517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_1113517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113517 prefixEnd_1113517 := by exact prefixLift 1113517
  have htrace : WordTrace (prefixWord ++ tailWord_1113517) baseStart_1113517 baseEnd_1113517 := by
    simpa [prefixWord, tailWord_1113517, baseEnd_1113517] using wordTrace_append hprefix tailTrace_1113517
  have hstable : (prefixWord ++ tailWord_1113517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113517).length < 2 ^ (prefixWord ++ tailWord_1113517).sum := by decide
  have hdescent : baseEnd_1113517 < baseStart_1113517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113605 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_1113605 : Nat := 118140960795 + 1113605 * 2 ^ 59
def prefixEnd_1113605 : Nat := 4983230072969 + 3 ^ 40 * 1113605 * 2
def baseEnd_1113605 : Nat := 381209749500147166010753

theorem tailTrace_1113605 : CollatzResearch.WordTrace tailWord_1113605 prefixEnd_1113605 381209749500147166010753 := by
  unfold tailWord_1113605
  simp only [CollatzResearch.WordTrace]
  refine ⟨40616511130606748437422269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27077674087071165624948179 40616511130606748437422269)
  ·
    refine ⟨15231191673977530664033351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40616511130606748437422269 15231191673977530664033351)
    ·
      refine ⟨22846787510966295996050027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15231191673977530664033351 22846787510966295996050027)
      ·
        refine ⟨34270181266449443994075041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22846787510966295996050027 34270181266449443994075041)
        ·
          refine ⟨25702635949837082995556281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34270181266449443994075041 25702635949837082995556281)
          ·
            refine ⟨19276976962377812246667211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25702635949837082995556281 19276976962377812246667211)
            ·
              refine ⟨28915465443566718370000817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19276976962377812246667211 28915465443566718370000817)
              ·
                refine ⟨21686599082675038777500613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28915465443566718370000817 21686599082675038777500613)
                ·
                  refine ⟨4066237328001569770781365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21686599082675038777500613 4066237328001569770781365)
                  ·
                    refine ⟨381209749500147166010753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4066237328001569770781365 381209749500147166010753)
                    ·
                      rfl

theorem cell22_1113605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_1113605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113605 prefixEnd_1113605 := by exact prefixLift 1113605
  have htrace : WordTrace (prefixWord ++ tailWord_1113605) baseStart_1113605 baseEnd_1113605 := by
    simpa [prefixWord, tailWord_1113605, baseEnd_1113605] using wordTrace_append hprefix tailTrace_1113605
  have hstable : (prefixWord ++ tailWord_1113605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113605).length < 2 ^ (prefixWord ++ tailWord_1113605).sum := by decide
  have hdescent : baseEnd_1113605 < baseStart_1113605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113624 : List Nat := [2, 1, 2, 3, 4, 1, 2, 2, 5]
def baseStart_1113624 : Nat := 118140960795 + 1113624 * 2 ^ 59
def prefixEnd_1113624 : Nat := 4983230072969 + 3 ^ 40 * 1113624 * 2
def baseEnd_1113624 : Nat := 127072084529479149928565

theorem tailTrace_1113624 : CollatzResearch.WordTrace tailWord_1113624 prefixEnd_1113624 127072084529479149928565 := by
  unfold tailWord_1113624
  simp only [CollatzResearch.WordTrace]
  refine ⟨20308602058768957341181963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27078136078358609788242617 20308602058768957341181963)
  ·
    refine ⟨30462903088153436011772945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20308602058768957341181963 30462903088153436011772945)
    ·
      refine ⟨22847177316115077008829709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30462903088153436011772945 22847177316115077008829709)
      ·
        refine ⟨8567691493543153878311141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22847177316115077008829709 8567691493543153878311141)
        ·
          refine ⟨1606442155039341352183339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8567691493543153878311141 1606442155039341352183339)
          ·
            refine ⟨2409663232559012028275009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1606442155039341352183339 2409663232559012028275009)
            ·
              refine ⟨1807247424419259021206257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2409663232559012028275009 1807247424419259021206257)
              ·
                refine ⟨1355435568314444265904693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1807247424419259021206257 1355435568314444265904693)
                ·
                  refine ⟨127072084529479149928565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1355435568314444265904693 127072084529479149928565)
                  ·
                    rfl

theorem cell22_1113624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 5].length) (baseStart_1113624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113624 prefixEnd_1113624 := by exact prefixLift 1113624
  have htrace : WordTrace (prefixWord ++ tailWord_1113624) baseStart_1113624 baseEnd_1113624 := by
    simpa [prefixWord, tailWord_1113624, baseEnd_1113624] using wordTrace_append hprefix tailTrace_1113624
  have hstable : (prefixWord ++ tailWord_1113624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113624).length < 2 ^ (prefixWord ++ tailWord_1113624).sum := by decide
  have hdescent : baseEnd_1113624 < baseStart_1113624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113630 : List Nat := [4, 3, 3, 1, 2, 1, 1, 7]
def baseStart_1113630 : Nat := 118140960795 + 1113630 * 2 ^ 59
def prefixEnd_1113630 : Nat := 4983230072969 + 3 ^ 40 * 1113630 * 2
def baseEnd_1113630 : Nat := 42357589723450603792853

theorem tailTrace_1113630 : CollatzResearch.WordTrace tailWord_1113630 prefixEnd_1113630 42357589723450603792853 := by
  unfold tailWord_1113630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5077177869439522213385293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27078281970344118471388229 5077177869439522213385293)
  ·
    refine ⟨1903941701039820830019485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5077177869439522213385293 1903941701039820830019485)
    ·
      refine ⟨713978137889932811257307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1903941701039820830019485 713978137889932811257307)
      ·
        refine ⟨1070967206834899216885961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713978137889932811257307 1070967206834899216885961)
        ·
          refine ⟨803225405126174412664471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1070967206834899216885961 803225405126174412664471)
          ·
            refine ⟨1204838107689261618996707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803225405126174412664471 1204838107689261618996707)
            ·
              refine ⟨1807257161533892428495061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204838107689261618996707 1807257161533892428495061)
              ·
                refine ⟨42357589723450603792853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1807257161533892428495061 42357589723450603792853)
                ·
                  rfl

theorem cell22_1113630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_1113630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113630 prefixEnd_1113630 := by exact prefixLift 1113630
  have htrace : WordTrace (prefixWord ++ tailWord_1113630) baseStart_1113630 baseEnd_1113630 := by
    simpa [prefixWord, tailWord_1113630, baseEnd_1113630] using wordTrace_append hprefix tailTrace_1113630
  have hstable : (prefixWord ++ tailWord_1113630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113630).length < 2 ^ (prefixWord ++ tailWord_1113630).sum := by decide
  have hdescent : baseEnd_1113630 < baseStart_1113630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113669 : List Nat := [1, 3, 1, 1, 1, 4, 4, 3, 4]
def baseStart_1113669 : Nat := 118140960795 + 1113669 * 2 ^ 59
def prefixEnd_1113669 : Nat := 4983230072969 + 3 ^ 40 * 1113669 * 2
def baseEnd_1113669 : Nat := 127077219336024110803519

theorem tailTrace_1113669 : CollatzResearch.WordTrace tailWord_1113669 prefixEnd_1113669 127077219336024110803519 := by
  unfold tailWord_1113669
  simp only [CollatzResearch.WordTrace]
  refine ⟨40618845402374887367752061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27079230268249924911834707 40618845402374887367752061)
  ·
    refine ⟨15232067025890582762907023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40618845402374887367752061 15232067025890582762907023)
    ·
      refine ⟨22848100538835874144360535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15232067025890582762907023 22848100538835874144360535)
      ·
        refine ⟨34272150808253811216540803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22848100538835874144360535 34272150808253811216540803)
        ·
          refine ⟨51408226212380716824811205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34272150808253811216540803 51408226212380716824811205)
          ·
            refine ⟨9639042414821384404652101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51408226212380716824811205 9639042414821384404652101)
            ·
              refine ⟨1807320452779009575872269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9639042414821384404652101 1807320452779009575872269)
              ·
                refine ⟨677745169792128590952101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1807320452779009575872269 677745169792128590952101)
                ·
                  refine ⟨127077219336024110803519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 677745169792128590952101 127077219336024110803519)
                  ·
                    rfl

theorem cell22_1113669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_1113669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113669 prefixEnd_1113669 := by exact prefixLift 1113669
  have htrace : WordTrace (prefixWord ++ tailWord_1113669) baseStart_1113669 baseEnd_1113669 := by
    simpa [prefixWord, tailWord_1113669, baseEnd_1113669] using wordTrace_append hprefix tailTrace_1113669
  have hstable : (prefixWord ++ tailWord_1113669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113669).length < 2 ^ (prefixWord ++ tailWord_1113669).sum := by decide
  have hdescent : baseEnd_1113669 < baseStart_1113669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113680 : List Nat := [2, 1, 1, 1, 1, 3, 13]
def baseStart_1113680 : Nat := 118140960795 + 1113680 * 2 ^ 59
def prefixEnd_1113680 : Nat := 4983230072969 + 3 ^ 40 * 1113680 * 2
def baseEnd_1113680 : Nat := 14119830501217480384649

theorem tailTrace_1113680 : CollatzResearch.WordTrace tailWord_1113680 prefixEnd_1113680 14119830501217480384649 := by
  unfold tailWord_1113680
  simp only [CollatzResearch.WordTrace]
  refine ⟨20309623302667518123201247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27079497736890024164268329 20309623302667518123201247)
  ·
    refine ⟨30464434954001277184801871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20309623302667518123201247 30464434954001277184801871)
    ·
      refine ⟨45696652431001915777202807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30464434954001277184801871 45696652431001915777202807)
      ·
        refine ⟨68544978646502873665804211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45696652431001915777202807 68544978646502873665804211)
        ·
          refine ⟨102817467969754310498706317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68544978646502873665804211 102817467969754310498706317)
          ·
            refine ⟨38556550488657866437014869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102817467969754310498706317 38556550488657866437014869)
            ·
              refine ⟨14119830501217480384649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 38556550488657866437014869 14119830501217480384649)
              ·
                rfl

theorem cell22_1113680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 13].length) (baseStart_1113680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113680 prefixEnd_1113680 := by exact prefixLift 1113680
  have htrace : WordTrace (prefixWord ++ tailWord_1113680) baseStart_1113680 baseEnd_1113680 := by
    simpa [prefixWord, tailWord_1113680, baseEnd_1113680] using wordTrace_append hprefix tailTrace_1113680
  have hstable : (prefixWord ++ tailWord_1113680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113680).length < 2 ^ (prefixWord ++ tailWord_1113680).sum := by decide
  have hdescent : baseEnd_1113680 < baseStart_1113680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113684 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_1113684 : Nat := 118140960795 + 1113684 * 2 ^ 59
def prefixEnd_1113684 : Nat := 4983230072969 + 3 ^ 40 * 1113684 * 2
def baseEnd_1113684 : Nat := 381236792814617293285511

theorem tailTrace_1113684 : CollatzResearch.WordTrace tailWord_1113684 prefixEnd_1113684 381236792814617293285511 := by
  unfold tailWord_1113684
  simp only [CollatzResearch.WordTrace]
  refine ⟨20309696248660272464774053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27079594998213696619698737 20309696248660272464774053)
  ·
    refine ⟨3808068046623801087145135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20309696248660272464774053 3808068046623801087145135)
    ·
      refine ⟨5712102069935701630717703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3808068046623801087145135 5712102069935701630717703)
      ·
        refine ⟨8568153104903552446076555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5712102069935701630717703 8568153104903552446076555)
        ·
          refine ⟨12852229657355328669114833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8568153104903552446076555 12852229657355328669114833)
          ·
            refine ⟨9639172243016496501836125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12852229657355328669114833 9639172243016496501836125)
            ·
              refine ⟨3614689591131186188188547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9639172243016496501836125 3614689591131186188188547)
              ·
                refine ⟨5422034386696779282282821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3614689591131186188188547 5422034386696779282282821)
                ·
                  refine ⟨1016631447505646115428029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5422034386696779282282821 1016631447505646115428029)
                  ·
                    refine ⟨381236792814617293285511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1016631447505646115428029 381236792814617293285511)
                    ·
                      rfl

theorem cell22_1113684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_1113684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113684 prefixEnd_1113684 := by exact prefixLift 1113684
  have htrace : WordTrace (prefixWord ++ tailWord_1113684) baseStart_1113684 baseEnd_1113684 := by
    simpa [prefixWord, tailWord_1113684, baseEnd_1113684] using wordTrace_append hprefix tailTrace_1113684
  have hstable : (prefixWord ++ tailWord_1113684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113684).length < 2 ^ (prefixWord ++ tailWord_1113684).sum := by decide
  have hdescent : baseEnd_1113684 < baseStart_1113684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113714 : List Nat := [3, 2, 1, 2, 3, 1, 4, 6]
def baseStart_1113714 : Nat := 118140960795 + 1113714 * 2 ^ 59
def prefixEnd_1113714 : Nat := 4983230072969 + 3 ^ 40 * 1113714 * 2
def baseEnd_1113714 : Nat := 42360784714189690559491

theorem tailTrace_1113714 : CollatzResearch.WordTrace tailWord_1113714 prefixEnd_1113714 42360784714189690559491 := by
  unfold tailWord_1113714
  simp only [CollatzResearch.WordTrace]
  refine ⟨10155121671802965013285049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27080324458141240035426797 10155121671802965013285049)
  ·
    refine ⟨7616341253852223759963787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10155121671802965013285049 7616341253852223759963787)
    ·
      refine ⟨11424511880778335639945681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7616341253852223759963787 11424511880778335639945681)
      ·
        refine ⟨8568383910583751729959261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11424511880778335639945681 8568383910583751729959261)
        ·
          refine ⟨3213143966468906898734723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8568383910583751729959261 3213143966468906898734723)
          ·
            refine ⟨4819715949703360348102085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3213143966468906898734723 4819715949703360348102085)
            ·
              refine ⟨903696740569380065269141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4819715949703360348102085 903696740569380065269141)
              ·
                refine ⟨42360784714189690559491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 903696740569380065269141 42360784714189690559491)
                ·
                  rfl

theorem cell22_1113714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 6].length) (baseStart_1113714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113714 prefixEnd_1113714 := by exact prefixLift 1113714
  have htrace : WordTrace (prefixWord ++ tailWord_1113714) baseStart_1113714 baseEnd_1113714 := by
    simpa [prefixWord, tailWord_1113714, baseEnd_1113714] using wordTrace_append hprefix tailTrace_1113714
  have hstable : (prefixWord ++ tailWord_1113714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113714).length < 2 ^ (prefixWord ++ tailWord_1113714).sum := by decide
  have hdescent : baseEnd_1113714 < baseStart_1113714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113757 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_1113757 : Nat := 118140960795 + 1113757 * 2 ^ 59
def prefixEnd_1113757 : Nat := 4983230072969 + 3 ^ 40 * 1113757 * 2
def baseEnd_1113757 : Nat := 381261782206469436210287

theorem tailTrace_1113757 : CollatzResearch.WordTrace tailWord_1113757 prefixEnd_1113757 381261782206469436210287 := by
  unfold tailWord_1113757
  simp only [CollatzResearch.WordTrace]
  refine ⟨40622055026056078396955525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27081370017370718931303683 40622055026056078396955525)
  ·
    refine ⟨7616635317385514699429161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40622055026056078396955525 7616635317385514699429161)
    ·
      refine ⟨5712476488039136024571871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7616635317385514699429161 5712476488039136024571871)
      ·
        refine ⟨8568714732058704036857807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5712476488039136024571871 8568714732058704036857807)
        ·
          refine ⟨12853072098088056055286711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8568714732058704036857807 12853072098088056055286711)
          ·
            refine ⟨19279608147132084082930067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12853072098088056055286711 19279608147132084082930067)
            ·
              refine ⟨28919412220698126124395101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19279608147132084082930067 28919412220698126124395101)
              ·
                refine ⟨10844779582761797296648163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28919412220698126124395101 10844779582761797296648163)
                ·
                  refine ⟨16267169374142695944972245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10844779582761797296648163 16267169374142695944972245)
                  ·
                    refine ⟨381261782206469436210287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16267169374142695944972245 381261782206469436210287)
                    ·
                      rfl

theorem cell22_1113757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_1113757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113757 prefixEnd_1113757 := by exact prefixLift 1113757
  have htrace : WordTrace (prefixWord ++ tailWord_1113757) baseStart_1113757 baseEnd_1113757 := by
    simpa [prefixWord, tailWord_1113757, baseEnd_1113757] using wordTrace_append hprefix tailTrace_1113757
  have hstable : (prefixWord ++ tailWord_1113757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113757).length < 2 ^ (prefixWord ++ tailWord_1113757).sum := by decide
  have hdescent : baseEnd_1113757 < baseStart_1113757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113928 : List Nat := [2, 1, 3, 1, 1, 6, 2, 1, 5]
def baseStart_1113928 : Nat := 118140960795 + 1113928 * 2 ^ 59
def prefixEnd_1113928 : Nat := 4983230072969 + 3 ^ 40 * 1113928 * 2
def baseEnd_1113928 : Nat := 127106773000360663394921

theorem tailTrace_1113928 : CollatzResearch.WordTrace tailWord_1113928 prefixEnd_1113928 127106773000360663394921 := by
  unfold tailWord_1113928
  simp only [CollatzResearch.WordTrace]
  refine ⟨20314145954218287300715219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27085527938957716400953625 20314145954218287300715219)
  ·
    refine ⟨30471218931327430951072829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20314145954218287300715219 30471218931327430951072829)
    ·
      refine ⟨11426707099247786606652311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30471218931327430951072829 11426707099247786606652311)
      ·
        refine ⟨17140060648871679909978467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11426707099247786606652311 17140060648871679909978467)
        ·
          refine ⟨25710090973307519864967701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17140060648871679909978467 25710090973307519864967701)
          ·
            refine ⟨1205160514373789993670361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25710090973307519864967701 1205160514373789993670361)
            ·
              refine ⟨903870385780342495252771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1205160514373789993670361 903870385780342495252771)
              ·
                refine ⟨1355805578670513742879157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903870385780342495252771 1355805578670513742879157)
                ·
                  refine ⟨127106773000360663394921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1355805578670513742879157 127106773000360663394921)
                  ·
                    rfl

theorem cell22_1113928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 5].length) (baseStart_1113928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113928 prefixEnd_1113928 := by exact prefixLift 1113928
  have htrace : WordTrace (prefixWord ++ tailWord_1113928) baseStart_1113928 baseEnd_1113928 := by
    simpa [prefixWord, tailWord_1113928, baseEnd_1113928] using wordTrace_append hprefix tailTrace_1113928
  have hstable : (prefixWord ++ tailWord_1113928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113928).length < 2 ^ (prefixWord ++ tailWord_1113928).sum := by decide
  have hdescent : baseEnd_1113928 < baseStart_1113928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113941 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_1113941 : Nat := 118140960795 + 1113941 * 2 ^ 59
def prefixEnd_1113941 : Nat := 4983230072969 + 3 ^ 40 * 1113941 * 2
def baseEnd_1113941 : Nat := 381324769166754289609723

theorem tailTrace_1113941 : CollatzResearch.WordTrace tailWord_1113941 prefixEnd_1113941 381324769166754289609723 := by
  unfold tailWord_1113941
  simp only [CollatzResearch.WordTrace]
  refine ⟨40628766057389477821653677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27085844038259651881102451 40628766057389477821653677)
  ·
    refine ⟨15235787271521054183120129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40628766057389477821653677 15235787271521054183120129)
    ·
      refine ⟨11426840453640790637340097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15235787271521054183120129 11426840453640790637340097)
      ·
        refine ⟨8570130340230592978005073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11426840453640790637340097 8570130340230592978005073)
        ·
          refine ⟨6427597755172944733503805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8570130340230592978005073 6427597755172944733503805)
          ·
            refine ⟨2410349158189854275063927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6427597755172944733503805 2410349158189854275063927)
            ·
              refine ⟨3615523737284781412595891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2410349158189854275063927 3615523737284781412595891)
              ·
                refine ⟨5423285605927172118893837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3615523737284781412595891 5423285605927172118893837)
                ·
                  refine ⟨2033732102222689544585189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5423285605927172118893837 2033732102222689544585189)
                  ·
                    refine ⟨381324769166754289609723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2033732102222689544585189 381324769166754289609723)
                    ·
                      rfl

theorem cell22_1113941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_1113941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113941 prefixEnd_1113941 := by exact prefixLift 1113941
  have htrace : WordTrace (prefixWord ++ tailWord_1113941) baseStart_1113941 baseEnd_1113941 := by
    simpa [prefixWord, tailWord_1113941, baseEnd_1113941] using wordTrace_append hprefix tailTrace_1113941
  have hstable : (prefixWord ++ tailWord_1113941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113941).length < 2 ^ (prefixWord ++ tailWord_1113941).sum := by decide
  have hdescent : baseEnd_1113941 < baseStart_1113941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113973 : List Nat := [1, 3, 4, 1, 1, 1, 3, 4, 4]
def baseStart_1113973 : Nat := 118140960795 + 1113973 * 2 ^ 59
def prefixEnd_1113973 : Nat := 4983230072969 + 3 ^ 40 * 1113973 * 2
def baseEnd_1113973 : Nat := 127111907806905624269875

theorem tailTrace_1113973 : CollatzResearch.WordTrace tailWord_1113973 prefixEnd_1113973 127111907806905624269875 := by
  unfold tailWord_1113973
  simp only [CollatzResearch.WordTrace]
  refine ⟨40629933193273547286818573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27086622128849031524545715 40629933193273547286818573)
  ·
    refine ⟨15236224947477580232556965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40629933193273547286818573 15236224947477580232556965)
    ·
      refine ⟨2856792177652046293604431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15236224947477580232556965 2856792177652046293604431)
      ·
        refine ⟨4285188266478069440406647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2856792177652046293604431 4285188266478069440406647)
        ·
          refine ⟨6427782399717104160609971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4285188266478069440406647 6427782399717104160609971)
          ·
            refine ⟨9641673599575656240914957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6427782399717104160609971 9641673599575656240914957)
            ·
              refine ⟨3615627599840871090343109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9641673599575656240914957 3615627599840871090343109)
              ·
                refine ⟨677930174970163329439333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3615627599840871090343109 677930174970163329439333)
                ·
                  refine ⟨127111907806905624269875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 677930174970163329439333 127111907806905624269875)
                  ·
                    rfl

theorem cell22_1113973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_1113973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113973 prefixEnd_1113973 := by exact prefixLift 1113973
  have htrace : WordTrace (prefixWord ++ tailWord_1113973) baseStart_1113973 baseEnd_1113973 := by
    simpa [prefixWord, tailWord_1113973, baseEnd_1113973] using wordTrace_append hprefix tailTrace_1113973
  have hstable : (prefixWord ++ tailWord_1113973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113973).length < 2 ^ (prefixWord ++ tailWord_1113973).sum := by decide
  have hdescent : baseEnd_1113973 < baseStart_1113973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1113988 : List Nat := [2, 3, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_1113988 : Nat := 118140960795 + 1113988 * 2 ^ 59
def prefixEnd_1113988 : Nat := 4983230072969 + 3 ^ 40 * 1113988 * 2
def baseEnd_1113988 : Nat := 381340858227261833684579

theorem tailTrace_1113988 : CollatzResearch.WordTrace tailWord_1113988 prefixEnd_1113988 381340858227261833684579 := by
  unfold tailWord_1113988
  simp only [CollatzResearch.WordTrace]
  refine ⟨20315240144109602424307309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27086986858812803232409745 20315240144109602424307309)
  ·
    refine ⟨7618215054041100909115241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20315240144109602424307309 7618215054041100909115241)
    ·
      refine ⟨5713661290530825681836431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7618215054041100909115241 5713661290530825681836431)
      ·
        refine ⟨8570491935796238522754647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5713661290530825681836431 8570491935796238522754647)
        ·
          refine ⟨12855737903694357784131971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8570491935796238522754647 12855737903694357784131971)
          ·
            refine ⟨19283606855541536676197957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12855737903694357784131971 19283606855541536676197957)
            ·
              refine ⟨3615676285414038126787117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19283606855541536676197957 3615676285414038126787117)
              ·
                refine ⟨1355878607030264297545169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3615676285414038126787117 1355878607030264297545169)
                ·
                  refine ⟨1016908955272698223158877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1355878607030264297545169 1016908955272698223158877)
                  ·
                    refine ⟨381340858227261833684579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1016908955272698223158877 381340858227261833684579)
                    ·
                      rfl

theorem cell22_1113988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_1113988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1113988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1113988 prefixEnd_1113988 := by exact prefixLift 1113988
  have htrace : WordTrace (prefixWord ++ tailWord_1113988) baseStart_1113988 baseEnd_1113988 := by
    simpa [prefixWord, tailWord_1113988, baseEnd_1113988] using wordTrace_append hprefix tailTrace_1113988
  have hstable : (prefixWord ++ tailWord_1113988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1113988).length < 2 ^ (prefixWord ++ tailWord_1113988).sum := by decide
  have hdescent : baseEnd_1113988 < baseStart_1113988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1113988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114016 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 7, 3]
def baseStart_1114016 : Nat := 118140960795 + 1114016 * 2 ^ 59
def prefixEnd_1114016 : Nat := 4983230072969 + 3 ^ 40 * 1114016 * 2
def baseEnd_1114016 : Nat := 381350443199479093984493

theorem tailTrace_1114016 : CollatzResearch.WordTrace tailWord_1114016 prefixEnd_1114016 381350443199479093984493 := by
  unfold tailWord_1114016
  simp only [CollatzResearch.WordTrace]
  refine ⟨20315750766058882815316951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27087667688078510420422601 20315750766058882815316951)
  ·
    refine ⟨30473626149088324222975427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20315750766058882815316951 30473626149088324222975427)
    ·
      refine ⟨45710439223632486334463141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30473626149088324222975427 45710439223632486334463141)
      ·
        refine ⟨8570707354431091187711839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45710439223632486334463141 8570707354431091187711839)
        ·
          refine ⟨12856061031646636781567759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8570707354431091187711839 12856061031646636781567759)
          ·
            refine ⟨19284091547469955172351639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12856061031646636781567759 19284091547469955172351639)
            ·
              refine ⟨28926137321204932758527459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19284091547469955172351639 28926137321204932758527459)
              ·
                refine ⟨43389205981807399137791189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28926137321204932758527459 43389205981807399137791189)
                ·
                  refine ⟨1016934515198610917291981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 43389205981807399137791189 1016934515198610917291981)
                  ·
                    refine ⟨381350443199479093984493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1016934515198610917291981 381350443199479093984493)
                    ·
                      rfl

theorem cell22_1114016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 7, 3].length) (baseStart_1114016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114016 prefixEnd_1114016 := by exact prefixLift 1114016
  have htrace : WordTrace (prefixWord ++ tailWord_1114016) baseStart_1114016 baseEnd_1114016 := by
    simpa [prefixWord, tailWord_1114016, baseEnd_1114016] using wordTrace_append hprefix tailTrace_1114016
  have hstable : (prefixWord ++ tailWord_1114016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114016).length < 2 ^ (prefixWord ++ tailWord_1114016).sum := by decide
  have hdescent : baseEnd_1114016 < baseStart_1114016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114033 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 3, 3]
def baseStart_1114033 : Nat := 118140960795 + 1114033 * 2 ^ 59
def prefixEnd_1114033 : Nat := 4983230072969 + 3 ^ 40 * 1114033 * 2
def baseEnd_1114033 : Nat := 381356262646896716309441

theorem tailTrace_1114033 : CollatzResearch.WordTrace tailWord_1114033 prefixEnd_1114033 381356262646896716309441 := by
  unfold tailWord_1114033
  simp only [CollatzResearch.WordTrace]
  refine ⟨40632121573056177534002753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27088081048704118356001835 40632121573056177534002753)
  ·
    refine ⟨30474091179792133150502065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40632121573056177534002753 30474091179792133150502065)
    ·
      refine ⟨22855568384844099862876549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30474091179792133150502065 22855568384844099862876549)
      ·
        refine ⟨4285419072158268724289353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22855568384844099862876549 4285419072158268724289353)
        ·
          refine ⟨3214064304118701543217015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4285419072158268724289353 3214064304118701543217015)
          ·
            refine ⟨4821096456178052314825523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3214064304118701543217015 4821096456178052314825523)
            ·
              refine ⟨7231644684267078472238285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4821096456178052314825523 7231644684267078472238285)
              ·
                refine ⟨2711866756600154427089357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7231644684267078472238285 2711866756600154427089357)
                ·
                  refine ⟨1016950033725057910158509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2711866756600154427089357 1016950033725057910158509)
                  ·
                    refine ⟨381356262646896716309441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1016950033725057910158509 381356262646896716309441)
                    ·
                      rfl

theorem cell22_1114033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_1114033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114033 prefixEnd_1114033 := by exact prefixLift 1114033
  have htrace : WordTrace (prefixWord ++ tailWord_1114033) baseStart_1114033 baseEnd_1114033 := by
    simpa [prefixWord, tailWord_1114033, baseEnd_1114033] using wordTrace_append hprefix tailTrace_1114033
  have hstable : (prefixWord ++ tailWord_1114033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114033).length < 2 ^ (prefixWord ++ tailWord_1114033).sum := by decide
  have hdescent : baseEnd_1114033 < baseStart_1114033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114097 : List Nat := [1, 2, 2, 2, 6, 1, 2, 1, 5]
def baseStart_1114097 : Nat := 118140960795 + 1114097 * 2 ^ 59
def prefixEnd_1114097 : Nat := 4983230072969 + 3 ^ 40 * 1114097 * 2
def baseEnd_1114097 : Nat := 127126057051607294236415

theorem tailTrace_1114097 : CollatzResearch.WordTrace tailWord_1114097 prefixEnd_1114097 127126057051607294236415 := by
  unfold tailWord_1114097
  simp only [CollatzResearch.WordTrace]
  refine ⟨40634455844824316464332545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27089637229882877642888363 40634455844824316464332545)
  ·
    refine ⟨30475841883618237348249409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40634455844824316464332545 30475841883618237348249409)
    ·
      refine ⟨22856881412713678011187057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30475841883618237348249409 22856881412713678011187057)
      ·
        refine ⟨17142661059535258508390293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22856881412713678011187057 17142661059535258508390293)
        ·
          refine ⟨803562237165715242580795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17142661059535258508390293 803562237165715242580795)
          ·
            refine ⟨1205343355748572863871193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803562237165715242580795 1205343355748572863871193)
            ·
              refine ⟨904007516811429647903395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1205343355748572863871193 904007516811429647903395)
              ·
                refine ⟨1356011275217144471855093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904007516811429647903395 1356011275217144471855093)
                ·
                  refine ⟨127126057051607294236415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1356011275217144471855093 127126057051607294236415)
                  ·
                    rfl

theorem cell22_1114097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 5].length) (baseStart_1114097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114097 prefixEnd_1114097 := by exact prefixLift 1114097
  have htrace : WordTrace (prefixWord ++ tailWord_1114097) baseStart_1114097 baseEnd_1114097 := by
    simpa [prefixWord, tailWord_1114097, baseEnd_1114097] using wordTrace_append hprefix tailTrace_1114097
  have hstable : (prefixWord ++ tailWord_1114097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114097).length < 2 ^ (prefixWord ++ tailWord_1114097).sum := by decide
  have hdescent : baseEnd_1114097 < baseStart_1114097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114110 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1114110 : Nat := 118140960795 + 1114110 * 2 ^ 59
def prefixEnd_1114110 : Nat := 4983230072969 + 3 ^ 40 * 1114110 * 2
def baseEnd_1114110 : Nat := 381382621320494182134205

theorem tailTrace_1114110 : CollatzResearch.WordTrace tailWord_1114110 prefixEnd_1114110 381382621320494182134205 := by
  unfold tailWord_1114110
  simp only [CollatzResearch.WordTrace]
  refine ⟨5079366249222152460569473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27089953329184813123037189 5079366249222152460569473)
  ·
    refine ⟨3809524686916614345427105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5079366249222152460569473 3809524686916614345427105)
    ·
      refine ⟨2857143515187460759070329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3809524686916614345427105 2857143515187460759070329)
      ·
        refine ⟨2142857636390595569302747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2857143515187460759070329 2142857636390595569302747)
        ·
          refine ⟨3214286454585893353954121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2142857636390595569302747 3214286454585893353954121)
          ·
            refine ⟨2410714840939420015465591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3214286454585893353954121 2410714840939420015465591)
            ·
              refine ⟨3616072261409130023198387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2410714840939420015465591 3616072261409130023198387)
              ·
                refine ⟨5424108392113695034797581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3616072261409130023198387 5424108392113695034797581)
                ·
                  refine ⟨2034040647042635638049093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5424108392113695034797581 2034040647042635638049093)
                  ·
                    refine ⟨381382621320494182134205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2034040647042635638049093 381382621320494182134205)
                    ·
                      rfl

theorem cell22_1114110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1114110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114110 prefixEnd_1114110 := by exact prefixLift 1114110
  have htrace : WordTrace (prefixWord ++ tailWord_1114110) baseStart_1114110 baseEnd_1114110 := by
    simpa [prefixWord, tailWord_1114110, baseEnd_1114110] using wordTrace_append hprefix tailTrace_1114110
  have hstable : (prefixWord ++ tailWord_1114110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114110).length < 2 ^ (prefixWord ++ tailWord_1114110).sum := by decide
  have hdescent : baseEnd_1114110 < baseStart_1114110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114138 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_1114138 : Nat := 118140960795 + 1114138 * 2 ^ 59
def prefixEnd_1114138 : Nat := 4983230072969 + 3 ^ 40 * 1114138 * 2
def baseEnd_1114138 : Nat := 381392206292711442434119

theorem tailTrace_1114138 : CollatzResearch.WordTrace tailWord_1114138 prefixEnd_1114138 381392206292711442434119 := by
  unfold tailWord_1114138
  simp only [CollatzResearch.WordTrace]
  refine ⟨10158987809418945116643767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27090634158450520311050045 10158987809418945116643767)
  ·
    refine ⟨15238481714128417674965651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10158987809418945116643767 15238481714128417674965651)
    ·
      refine ⟨22857722571192626512448477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15238481714128417674965651 22857722571192626512448477)
      ·
        refine ⟨8571645964197234942168179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22857722571192626512448477 8571645964197234942168179)
        ·
          refine ⟨12857468946295852413252269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8571645964197234942168179 12857468946295852413252269)
          ·
            refine ⟨4821550854860944654969601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12857468946295852413252269 4821550854860944654969601)
            ·
              refine ⟨3616163141145708491227201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4821550854860944654969601 3616163141145708491227201)
              ·
                refine ⟨2712122355859281368420401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3616163141145708491227201 2712122355859281368420401)
                ·
                  refine ⟨2034091766894461026315301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2712122355859281368420401 2034091766894461026315301)
                  ·
                    refine ⟨381392206292711442434119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2034091766894461026315301 381392206292711442434119)
                    ·
                      rfl

theorem cell22_1114138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_1114138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114138 prefixEnd_1114138 := by exact prefixLift 1114138
  have htrace : WordTrace (prefixWord ++ tailWord_1114138) baseStart_1114138 baseEnd_1114138 := by
    simpa [prefixWord, tailWord_1114138, baseEnd_1114138] using wordTrace_append hprefix tailTrace_1114138
  have hstable : (prefixWord ++ tailWord_1114138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114138).length < 2 ^ (prefixWord ++ tailWord_1114138).sum := by decide
  have hdescent : baseEnd_1114138 < baseStart_1114138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114140 : List Nat := [2, 2, 3, 1, 3, 1, 1, 4, 2, 3]
def baseStart_1114140 : Nat := 118140960795 + 1114140 * 2 ^ 59
def prefixEnd_1114140 : Nat := 4983230072969 + 3 ^ 40 * 1114140 * 2
def baseEnd_1114140 : Nat := 381392890933584103884113

theorem tailTrace_1114140 : CollatzResearch.WordTrace tailWord_1114140 prefixEnd_1114140 381392890933584103884113 := by
  unfold tailWord_1114140
  simp only [CollatzResearch.WordTrace]
  refine ⟨20318012091834267404073937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27090682789112356538765249 20318012091834267404073937)
  ·
    refine ⟨15238509068875700553055453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20318012091834267404073937 15238509068875700553055453)
    ·
      refine ⟨5714440900828387707395795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15238509068875700553055453 5714440900828387707395795)
      ·
        refine ⟨8571661351242581561093693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5714440900828387707395795 8571661351242581561093693)
        ·
          refine ⟨3214373006715968085410135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8571661351242581561093693 3214373006715968085410135)
          ·
            refine ⟨4821559510073952128115203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3214373006715968085410135 4821559510073952128115203)
            ·
              refine ⟨7232339265110928192172805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4821559510073952128115203 7232339265110928192172805)
              ·
                refine ⟨1356063612208299036032401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7232339265110928192172805 1356063612208299036032401)
                ·
                  refine ⟨1017047709156224277024301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1356063612208299036032401 1017047709156224277024301)
                  ·
                    refine ⟨381392890933584103884113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1017047709156224277024301 381392890933584103884113)
                    ·
                      rfl

theorem cell22_1114140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_1114140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114140 prefixEnd_1114140 := by exact prefixLift 1114140
  have htrace : WordTrace (prefixWord ++ tailWord_1114140) baseStart_1114140 baseEnd_1114140 := by
    simpa [prefixWord, tailWord_1114140, baseEnd_1114140] using wordTrace_append hprefix tailTrace_1114140
  have hstable : (prefixWord ++ tailWord_1114140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114140).length < 2 ^ (prefixWord ++ tailWord_1114140).sum := by decide
  have hdescent : baseEnd_1114140 < baseStart_1114140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114181 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 7]
def baseStart_1114181 : Nat := 118140960795 + 1114181 * 2 ^ 59
def prefixEnd_1114181 : Nat := 4983230072969 + 3 ^ 40 * 1114181 * 2
def baseEnd_1114181 : Nat := 127135642023824554536329

theorem tailTrace_1114181 : CollatzResearch.WordTrace tailWord_1114181 prefixEnd_1114181 127135642023824554536329 := by
  unfold tailWord_1114181
  simp only [CollatzResearch.WordTrace]
  refine ⟨40637519576519998810390397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27091679717679999206926931 40637519576519998810390397)
  ·
    refine ⟨15239069841194999553896399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40637519576519998810390397 15239069841194999553896399)
    ·
      refine ⟨22858604761792499330844599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15239069841194999553896399 22858604761792499330844599)
      ·
        refine ⟨34287907142688748996266899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22858604761792499330844599 34287907142688748996266899)
        ·
          refine ⟨51431860714033123494400349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34287907142688748996266899 51431860714033123494400349)
          ·
            refine ⟨19286947767762421310400131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51431860714033123494400349 19286947767762421310400131)
            ·
              refine ⟨28930421651643631965600197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19286947767762421310400131 28930421651643631965600197)
              ·
                refine ⟨5424454059683180993550037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28930421651643631965600197 5424454059683180993550037)
                ·
                  refine ⟨127135642023824554536329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5424454059683180993550037 127135642023824554536329)
                  ·
                    rfl

theorem cell22_1114181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_1114181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114181 prefixEnd_1114181 := by exact prefixLift 1114181
  have htrace : WordTrace (prefixWord ++ tailWord_1114181) baseStart_1114181 baseEnd_1114181 := by
    simpa [prefixWord, tailWord_1114181, baseEnd_1114181] using wordTrace_append hprefix tailTrace_1114181
  have hstable : (prefixWord ++ tailWord_1114181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114181).length < 2 ^ (prefixWord ++ tailWord_1114181).sum := by decide
  have hdescent : baseEnd_1114181 < baseStart_1114181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114213 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_1114213 : Nat := 118140960795 + 1114213 * 2 ^ 59
def prefixEnd_1114213 : Nat := 4983230072969 + 3 ^ 40 * 1114213 * 2
def baseEnd_1114213 : Nat := 381417880325436246808889

theorem tailTrace_1114213 : CollatzResearch.WordTrace tailWord_1114213 prefixEnd_1114213 381417880325436246808889 := by
  unfold tailWord_1114213
  simp only [CollatzResearch.WordTrace]
  refine ⟨40638686712404068275555293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27092457808269378850370195 40638686712404068275555293)
  ·
    refine ⟨15239507517151525603333235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40638686712404068275555293 15239507517151525603333235)
    ·
      refine ⟨22859261275727288404999853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15239507517151525603333235 22859261275727288404999853)
      ·
        refine ⟨8572222978397733151874945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22859261275727288404999853 8572222978397733151874945)
        ·
          refine ⟨6429167233798299863906209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8572222978397733151874945 6429167233798299863906209)
          ·
            refine ⟨4821875425348724897929657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6429167233798299863906209 4821875425348724897929657)
            ·
              refine ⟨3616406569011543673447243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4821875425348724897929657 3616406569011543673447243)
              ·
                refine ⟨5424609853517315510170865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3616406569011543673447243 5424609853517315510170865)
                ·
                  refine ⟨4068457390137986632628149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5424609853517315510170865 4068457390137986632628149)
                  ·
                    refine ⟨381417880325436246808889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4068457390137986632628149 381417880325436246808889)
                    ·
                      rfl

theorem cell22_1114213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_1114213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114213 prefixEnd_1114213 := by exact prefixLift 1114213
  have htrace : WordTrace (prefixWord ++ tailWord_1114213) baseStart_1114213 baseEnd_1114213 := by
    simpa [prefixWord, tailWord_1114213, baseEnd_1114213] using wordTrace_append hprefix tailTrace_1114213
  have hstable : (prefixWord ++ tailWord_1114213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114213).length < 2 ^ (prefixWord ++ tailWord_1114213).sum := by decide
  have hdescent : baseEnd_1114213 < baseStart_1114213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114215 : List Nat := [1, 1, 5, 1, 1, 2, 5, 1, 5]
def baseStart_1114215 : Nat := 118140960795 + 1114215 * 2 ^ 59
def prefixEnd_1114215 : Nat := 4983230072969 + 3 ^ 40 * 1114215 * 2
def baseEnd_1114215 : Nat := 127139521655436302752961

theorem tailTrace_1114215 : CollatzResearch.WordTrace tailWord_1114215 prefixEnd_1114215 127139521655436302752961 := by
  unfold tailWord_1114215
  simp only [CollatzResearch.WordTrace]
  refine ⟨40638759658396822617128099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27092506438931215078085399 40638759658396822617128099)
  ·
    refine ⟨60958139487595233925692149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40638759658396822617128099 60958139487595233925692149)
    ·
      refine ⟨5714825576962053180533639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60958139487595233925692149 5714825576962053180533639)
      ·
        refine ⟨8572238365443079770800459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5714825576962053180533639 8572238365443079770800459)
        ·
          refine ⟨12858357548164619656200689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8572238365443079770800459 12858357548164619656200689)
          ·
            refine ⟨9643768161123464742150517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12858357548164619656200689 9643768161123464742150517)
            ·
              refine ⟨904103265105324819576611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9643768161123464742150517 904103265105324819576611)
              ·
                refine ⟨1356154897657987229364917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904103265105324819576611 1356154897657987229364917)
                ·
                  refine ⟨127139521655436302752961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1356154897657987229364917 127139521655436302752961)
                  ·
                    rfl

theorem cell22_1114215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 5].length) (baseStart_1114215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114215 prefixEnd_1114215 := by exact prefixLift 1114215
  have htrace : WordTrace (prefixWord ++ tailWord_1114215) baseStart_1114215 baseEnd_1114215 := by
    simpa [prefixWord, tailWord_1114215, baseEnd_1114215] using wordTrace_append hprefix tailTrace_1114215
  have hstable : (prefixWord ++ tailWord_1114215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114215).length < 2 ^ (prefixWord ++ tailWord_1114215).sum := by decide
  have hdescent : baseEnd_1114215 < baseStart_1114215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114245 : List Nat := [1, 3, 1, 1, 5, 1, 2, 3, 1, 4]
def baseStart_1114245 : Nat := 118140960795 + 1114245 * 2 ^ 59
def prefixEnd_1114245 : Nat := 4983230072969 + 3 ^ 40 * 1114245 * 2
def baseEnd_1114245 : Nat := 381428834579398830008791

theorem tailTrace_1114245 : CollatzResearch.WordTrace tailWord_1114245 prefixEnd_1114245 381428834579398830008791 := by
  unfold tailWord_1114245
  simp only [CollatzResearch.WordTrace]
  refine ⟨40639853848288137740720189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27093235898858758493813459 40639853848288137740720189)
  ·
    refine ⟨15239945193108051652770071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40639853848288137740720189 15239945193108051652770071)
    ·
      refine ⟨22859917789662077479155107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15239945193108051652770071 22859917789662077479155107)
      ·
        refine ⟨34289876684493116218732661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22859917789662077479155107 34289876684493116218732661)
        ·
          refine ⟨3214675939171229645506187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34289876684493116218732661 3214675939171229645506187)
          ·
            refine ⟨4822013908756844468259281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3214675939171229645506187 4822013908756844468259281)
            ·
              refine ⟨3616510431567633351194461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4822013908756844468259281 3616510431567633351194461)
              ·
                refine ⟨1356191411837862506697923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3616510431567633351194461 1356191411837862506697923)
                ·
                  refine ⟨2034287117756793760046885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356191411837862506697923 2034287117756793760046885)
                  ·
                    refine ⟨381428834579398830008791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2034287117756793760046885 381428834579398830008791)
                    ·
                      rfl

theorem cell22_1114245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_1114245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114245 prefixEnd_1114245 := by exact prefixLift 1114245
  have htrace : WordTrace (prefixWord ++ tailWord_1114245) baseStart_1114245 baseEnd_1114245 := by
    simpa [prefixWord, tailWord_1114245, baseEnd_1114245] using wordTrace_append hprefix tailTrace_1114245
  have hstable : (prefixWord ++ tailWord_1114245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114245).length < 2 ^ (prefixWord ++ tailWord_1114245).sum := by decide
  have hdescent : baseEnd_1114245 < baseStart_1114245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114279 : List Nat := [1, 1, 6, 2, 2, 2, 1, 2, 1, 4]
def baseStart_1114279 : Nat := 118140960795 + 1114279 * 2 ^ 59
def prefixEnd_1114279 : Nat := 4983230072969 + 3 ^ 40 * 1114279 * 2
def baseEnd_1114279 : Nat := 381440473474234074658687

theorem tailTrace_1114279 : CollatzResearch.WordTrace tailWord_1114279 prefixEnd_1114279 381440473474234074658687 := by
  unfold tailWord_1114279
  simp only [CollatzResearch.WordTrace]
  refine ⟨40641093930164961547457891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27094062620109974364971927 40641093930164961547457891)
  ·
    refine ⟨60961640895247442321186837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40641093930164961547457891 60961640895247442321186837)
    ·
      refine ⟨2857576916964723858805633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60961640895247442321186837 2857576916964723858805633)
      ·
        refine ⟨2143182687723542894104225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2857576916964723858805633 2143182687723542894104225)
        ·
          refine ⟨1607387015792657170578169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2143182687723542894104225 1607387015792657170578169)
          ·
            refine ⟨1205540261844492877933627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1607387015792657170578169 1205540261844492877933627)
            ·
              refine ⟨1808310392766739316900441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205540261844492877933627 1808310392766739316900441)
              ·
                refine ⟨1356232794575054487675331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1808310392766739316900441 1356232794575054487675331)
                ·
                  refine ⟨2034349191862581731512997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1356232794575054487675331 2034349191862581731512997)
                  ·
                    refine ⟨381440473474234074658687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2034349191862581731512997 381440473474234074658687)
                    ·
                      rfl

theorem cell22_1114279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_1114279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114279 prefixEnd_1114279 := by exact prefixLift 1114279
  have htrace : WordTrace (prefixWord ++ tailWord_1114279) baseStart_1114279 baseEnd_1114279 := by
    simpa [prefixWord, tailWord_1114279, baseEnd_1114279] using wordTrace_append hprefix tailTrace_1114279
  have hstable : (prefixWord ++ tailWord_1114279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114279).length < 2 ^ (prefixWord ++ tailWord_1114279).sum := by decide
  have hdescent : baseEnd_1114279 < baseStart_1114279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114290 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_1114290 : Nat := 118140960795 + 1114290 * 2 ^ 59
def prefixEnd_1114290 : Nat := 4983230072969 + 3 ^ 40 * 1114290 * 2
def baseEnd_1114290 : Nat := 381444238999033712633653

theorem tailTrace_1114290 : CollatzResearch.WordTrace tailWord_1114290 prefixEnd_1114290 381444238999033712633653 := by
  unfold tailWord_1114290
  simp only [CollatzResearch.WordTrace]
  refine ⟨10160373783281277606527081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27094330088750073617405549 10160373783281277606527081)
  ·
    refine ⟨7620280337460958204895311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10160373783281277606527081 7620280337460958204895311)
    ·
      refine ⟨11430420506191437307342967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7620280337460958204895311 11430420506191437307342967)
      ·
        refine ⟨17145630759287155961014451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11430420506191437307342967 17145630759287155961014451)
        ·
          refine ⟨25718446138930733941521677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17145630759287155961014451 25718446138930733941521677)
          ·
            refine ⟨9644417302099025228070629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25718446138930733941521677 9644417302099025228070629)
            ·
              refine ⟨1808328244143567230263243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9644417302099025228070629 1808328244143567230263243)
              ·
                refine ⟨2712492366215350845394865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1808328244143567230263243 2712492366215350845394865)
                ·
                  refine ⟨2034369274661513134046149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2712492366215350845394865 2034369274661513134046149)
                  ·
                    refine ⟨381444238999033712633653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2034369274661513134046149 381444238999033712633653)
                    ·
                      rfl

theorem cell22_1114290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_1114290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114290 prefixEnd_1114290 := by exact prefixLift 1114290
  have htrace : WordTrace (prefixWord ++ tailWord_1114290) baseStart_1114290 baseEnd_1114290 := by
    simpa [prefixWord, tailWord_1114290, baseEnd_1114290] using wordTrace_append hprefix tailTrace_1114290
  have hstable : (prefixWord ++ tailWord_1114290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114290).length < 2 ^ (prefixWord ++ tailWord_1114290).sum := by decide
  have hdescent : baseEnd_1114290 < baseStart_1114290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114305 : List Nat := [1, 2, 6, 1, 2, 10]
def baseStart_1114305 : Nat := 118140960795 + 1114305 * 2 ^ 59
def prefixEnd_1114305 : Nat := 4983230072969 + 3 ^ 40 * 1114305 * 2
def baseEnd_1114305 : Nat := 4709251528463934240847

theorem tailTrace_1114305 : CollatzResearch.WordTrace tailWord_1114305 prefixEnd_1114305 4709251528463934240847 := by
  unfold tailWord_1114305
  simp only [CollatzResearch.WordTrace]
  refine ⟨40642042228070767987904369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27094694818713845325269579 40642042228070767987904369)
  ·
    refine ⟨30481531671053075990928277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40642042228070767987904369 30481531671053075990928277)
    ·
      refine ⟨1428821797080612937074763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30481531671053075990928277 1428821797080612937074763)
      ·
        refine ⟨2143232695620919405612145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428821797080612937074763 2143232695620919405612145)
        ·
          refine ⟨1607424521715689554209109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2143232695620919405612145 1607424521715689554209109)
          ·
            refine ⟨4709251528463934240847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1607424521715689554209109 4709251528463934240847)
            ·
              rfl

theorem cell22_1114305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 10].length) (baseStart_1114305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114305 prefixEnd_1114305 := by exact prefixLift 1114305
  have htrace : WordTrace (prefixWord ++ tailWord_1114305) baseStart_1114305 baseEnd_1114305 := by
    simpa [prefixWord, tailWord_1114305, baseEnd_1114305] using wordTrace_append hprefix tailTrace_1114305
  have hstable : (prefixWord ++ tailWord_1114305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114305).length < 2 ^ (prefixWord ++ tailWord_1114305).sum := by decide
  have hdescent : baseEnd_1114305 < baseStart_1114305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114348 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_1114348 : Nat := 118140960795 + 1114348 * 2 ^ 59
def prefixEnd_1114348 : Nat := 4983230072969 + 3 ^ 40 * 1114348 * 2
def baseEnd_1114348 : Nat := 381464093584340894683475

theorem tailTrace_1114348 : CollatzResearch.WordTrace tailWord_1114348 prefixEnd_1114348 381464093584340894683475 := by
  unfold tailWord_1114348
  simp only [CollatzResearch.WordTrace]
  refine ⟨20321805283457493165859849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27095740377943324221146465 20321805283457493165859849)
  ·
    refine ⟨15241353962593119874394887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20321805283457493165859849 15241353962593119874394887)
    ·
      refine ⟨22862030943889679811592331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15241353962593119874394887 22862030943889679811592331)
      ·
        refine ⟨34293046415834519717388497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22862030943889679811592331 34293046415834519717388497)
        ·
          refine ⟨25719784811875889788041373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34293046415834519717388497 25719784811875889788041373)
          ·
            refine ⟨9644919304453458670515515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25719784811875889788041373 9644919304453458670515515)
            ·
              refine ⟨14467378956680188005773273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9644919304453458670515515 14467378956680188005773273)
              ·
                refine ⟨10850534217510141004329955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14467378956680188005773273 10850534217510141004329955)
                ·
                  refine ⟨16275801326265211506494933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10850534217510141004329955 16275801326265211506494933)
                  ·
                    refine ⟨381464093584340894683475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16275801326265211506494933 381464093584340894683475)
                    ·
                      rfl

theorem cell22_1114348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_1114348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114348 prefixEnd_1114348 := by exact prefixLift 1114348
  have htrace : WordTrace (prefixWord ++ tailWord_1114348) baseStart_1114348 baseEnd_1114348 := by
    simpa [prefixWord, tailWord_1114348, baseEnd_1114348] using wordTrace_append hprefix tailTrace_1114348
  have hstable : (prefixWord ++ tailWord_1114348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114348).length < 2 ^ (prefixWord ++ tailWord_1114348).sum := by decide
  have hdescent : baseEnd_1114348 < baseStart_1114348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114354 : List Nat := [3, 2, 1, 3, 2, 1, 1, 5, 1, 3]
def baseStart_1114354 : Nat := 118140960795 + 1114354 * 2 ^ 59
def prefixEnd_1114354 : Nat := 4983230072969 + 3 ^ 40 * 1114354 * 2
def baseEnd_1114354 : Nat := 381466147506958879033457

theorem tailTrace_1114354 : CollatzResearch.WordTrace tailWord_1114354 prefixEnd_1114354 381466147506958879033457 := by
  unfold tailWord_1114354
  simp only [CollatzResearch.WordTrace]
  refine ⟨10160957351223312339109529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27095886269928832904292077 10160957351223312339109529)
  ·
    refine ⟨7620718013417484254332147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10160957351223312339109529 7620718013417484254332147)
    ·
      refine ⟨11431077020126226381498221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7620718013417484254332147 11431077020126226381498221)
      ·
        refine ⟨4286653882547334893061833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11431077020126226381498221 4286653882547334893061833)
        ·
          refine ⟨3214990411910501169796375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4286653882547334893061833 3214990411910501169796375)
          ·
            refine ⟨4822485617865751754694563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3214990411910501169796375 4822485617865751754694563)
            ·
              refine ⟨7233728426798627632041845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4822485617865751754694563 7233728426798627632041845)
              ·
                refine ⟨678162040012371340503923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7233728426798627632041845 678162040012371340503923)
                ·
                  refine ⟨1017243060018557010755885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678162040012371340503923 1017243060018557010755885)
                  ·
                    refine ⟨381466147506958879033457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1017243060018557010755885 381466147506958879033457)
                    ·
                      rfl

theorem cell22_1114354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_1114354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114354 prefixEnd_1114354 := by exact prefixLift 1114354
  have htrace : WordTrace (prefixWord ++ tailWord_1114354) baseStart_1114354 baseEnd_1114354 := by
    simpa [prefixWord, tailWord_1114354, baseEnd_1114354] using wordTrace_append hprefix tailTrace_1114354
  have hstable : (prefixWord ++ tailWord_1114354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114354).length < 2 ^ (prefixWord ++ tailWord_1114354).sum := by decide
  have hdescent : baseEnd_1114354 < baseStart_1114354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114412 : List Nat := [2, 2, 1, 1, 1, 3, 5, 3, 4]
def baseStart_1114412 : Nat := 118140960795 + 1114412 * 2 ^ 59
def prefixEnd_1114412 : Nat := 4983230072969 + 3 ^ 40 * 1114412 * 2
def baseEnd_1114412 : Nat := 127162000697422020361093

theorem tailTrace_1114412 : CollatzResearch.WordTrace tailWord_1114412 prefixEnd_1114412 127162000697422020361093 := by
  unfold tailWord_1114412
  simp only [CollatzResearch.WordTrace]
  refine ⟨20322972419341562631024745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27097296559122083508032993 20322972419341562631024745)
  ·
    refine ⟨15242229314506171973268559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20322972419341562631024745 15242229314506171973268559)
    ·
      refine ⟨22863343971759257959902839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15242229314506171973268559 22863343971759257959902839)
      ·
        refine ⟨34295015957638886939854259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22863343971759257959902839 34295015957638886939854259)
        ·
          refine ⟨51442523936458330409781389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34295015957638886939854259 51442523936458330409781389)
          ·
            refine ⟨19290946476171873903668021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51442523936458330409781389 19290946476171873903668021)
            ·
              refine ⟨1808526232141113178468877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19290946476171873903668021 1808526232141113178468877)
              ·
                refine ⟨678197337052917441925829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1808526232141113178468877 678197337052917441925829)
                ·
                  refine ⟨127162000697422020361093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 678197337052917441925829 127162000697422020361093)
                  ·
                    rfl

theorem cell22_1114412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_1114412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114412 prefixEnd_1114412 := by exact prefixLift 1114412
  have htrace : WordTrace (prefixWord ++ tailWord_1114412) baseStart_1114412 baseEnd_1114412 := by
    simpa [prefixWord, tailWord_1114412, baseEnd_1114412] using wordTrace_append hprefix tailTrace_1114412
  have hstable : (prefixWord ++ tailWord_1114412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114412).length < 2 ^ (prefixWord ++ tailWord_1114412).sum := by decide
  have hdescent : baseEnd_1114412 < baseStart_1114412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114506 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 3, 3]
def baseStart_1114506 : Nat := 118140960795 + 1114506 * 2 ^ 59
def prefixEnd_1114506 : Nat := 4983230072969 + 3 ^ 40 * 1114506 * 2
def baseEnd_1114506 : Nat := 381518180213281149232991

theorem tailTrace_1114506 : CollatzResearch.WordTrace tailWord_1114506 prefixEnd_1114506 381518180213281149232991 := by
  unfold tailWord_1114506
  simp only [CollatzResearch.WordTrace]
  refine ⟨10162343325085644828992843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27099582200228386210647581 10162343325085644828992843)
  ·
    refine ⟨15243514987628467243489265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10162343325085644828992843 15243514987628467243489265)
    ·
      refine ⟨11432636240721350432616949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15243514987628467243489265 11432636240721350432616949)
      ·
        refine ⟨1071809647567626603057839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11432636240721350432616949 1071809647567626603057839)
        ·
          refine ⟨1607714471351439904586759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071809647567626603057839 1607714471351439904586759)
          ·
            refine ⟨2411571707027159856880139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607714471351439904586759 2411571707027159856880139)
            ·
              refine ⟨3617357560540739785320209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411571707027159856880139 3617357560540739785320209)
              ·
                refine ⟨2713018170405554838990157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3617357560540739785320209 2713018170405554838990157)
                ·
                  refine ⟨1017381813902083064621309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2713018170405554838990157 1017381813902083064621309)
                  ·
                    refine ⟨381518180213281149232991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1017381813902083064621309 381518180213281149232991)
                    ·
                      rfl

theorem cell22_1114506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_1114506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114506 prefixEnd_1114506 := by exact prefixLift 1114506
  have htrace : WordTrace (prefixWord ++ tailWord_1114506) baseStart_1114506 baseEnd_1114506 := by
    simpa [prefixWord, tailWord_1114506, baseEnd_1114506] using wordTrace_append hprefix tailTrace_1114506
  have hstable : (prefixWord ++ tailWord_1114506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114506).length < 2 ^ (prefixWord ++ tailWord_1114506).sum := by decide
  have hdescent : baseEnd_1114506 < baseStart_1114506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114536 : List Nat := [2, 1, 6, 1, 1, 3, 1, 2, 5]
def baseStart_1114536 : Nat := 118140960795 + 1114536 * 2 ^ 59
def prefixEnd_1114536 : Nat := 4983230072969 + 3 ^ 40 * 1114536 * 2
def baseEnd_1114536 : Nat := 127176149942123690327633

theorem tailTrace_1114536 : CollatzResearch.WordTrace tailWord_1114536 prefixEnd_1114536 127176149942123690327633 := by
  unfold tailWord_1114536
  simp only [CollatzResearch.WordTrace]
  refine ⟨20325233745116947219781731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27100311660155929626375641 20325233745116947219781731)
  ·
    refine ⟨30487850617675420829672597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20325233745116947219781731 30487850617675420829672597)
    ·
      refine ⟨1429117997703535351390903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30487850617675420829672597 1429117997703535351390903)
      ·
        refine ⟨2143676996555303027086355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1429117997703535351390903 2143676996555303027086355)
        ·
          refine ⟨3215515494832954540629533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2143676996555303027086355 3215515494832954540629533)
          ·
            refine ⟨1205818310562357952736075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3215515494832954540629533 1205818310562357952736075)
            ·
              refine ⟨1808727465843536929104113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205818310562357952736075 1808727465843536929104113)
              ·
                refine ⟨1356545599382652696828085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1808727465843536929104113 1356545599382652696828085)
                ·
                  refine ⟨127176149942123690327633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1356545599382652696828085 127176149942123690327633)
                  ·
                    rfl

theorem cell22_1114536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 5].length) (baseStart_1114536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114536 prefixEnd_1114536 := by exact prefixLift 1114536
  have htrace : WordTrace (prefixWord ++ tailWord_1114536) baseStart_1114536 baseEnd_1114536 := by
    simpa [prefixWord, tailWord_1114536, baseEnd_1114536] using wordTrace_append hprefix tailTrace_1114536
  have hstable : (prefixWord ++ tailWord_1114536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114536).length < 2 ^ (prefixWord ++ tailWord_1114536).sum := by decide
  have hdescent : baseEnd_1114536 < baseStart_1114536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114581 : List Nat := [1, 3, 2, 3, 1, 4, 1, 3, 4]
def baseStart_1114581 : Nat := 118140960795 + 1114581 * 2 ^ 59
def prefixEnd_1114581 : Nat := 4983230072969 + 3 ^ 40 * 1114581 * 2
def baseEnd_1114581 : Nat := 127181284748668651202587

theorem tailTrace_1114581 : CollatzResearch.WordTrace tailWord_1114581 prefixEnd_1114581 127181284748668651202587 := by
  unfold tailWord_1114581
  simp only [CollatzResearch.WordTrace]
  refine ⟨40652108775070867124951597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27101405850047244749967731 40652108775070867124951597)
  ·
    refine ⟨15244540790651575171856849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40652108775070867124951597 15244540790651575171856849)
    ·
      refine ⟨11433405592988681378892637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15244540790651575171856849 11433405592988681378892637)
      ·
        refine ⟨4287527097370755517084739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11433405592988681378892637 4287527097370755517084739)
        ·
          refine ⟨6431290646056133275627109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4287527097370755517084739 6431290646056133275627109)
          ·
            refine ⟨1205866996135524989180083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6431290646056133275627109 1205866996135524989180083)
            ·
              refine ⟨1808800494203287483770125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205866996135524989180083 1808800494203287483770125)
              ·
                refine ⟨678300185326232806413797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1808800494203287483770125 678300185326232806413797)
                ·
                  refine ⟨127181284748668651202587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 678300185326232806413797 127181284748668651202587)
                  ·
                    rfl

theorem cell22_1114581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_1114581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114581 prefixEnd_1114581 := by exact prefixLift 1114581
  have htrace : WordTrace (prefixWord ++ tailWord_1114581) baseStart_1114581 baseEnd_1114581 := by
    simpa [prefixWord, tailWord_1114581, baseEnd_1114581] using wordTrace_append hprefix tailTrace_1114581
  have hstable : (prefixWord ++ tailWord_1114581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114581).length < 2 ^ (prefixWord ++ tailWord_1114581).sum := by decide
  have hdescent : baseEnd_1114581 < baseStart_1114581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114613 : List Nat := [1, 3, 5, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1114613 : Nat := 118140960795 + 1114613 * 2 ^ 59
def prefixEnd_1114613 : Nat := 4983230072969 + 3 ^ 40 * 1114613 * 2
def baseEnd_1114613 : Nat := 381554808499968536807663

theorem tailTrace_1114613 : CollatzResearch.WordTrace tailWord_1114613 prefixEnd_1114613 381554808499968536807663 := by
  unfold tailWord_1114613
  simp only [CollatzResearch.WordTrace]
  refine ⟨40653275910954936590116493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27102183940636624393410995 40653275910954936590116493)
  ·
    refine ⟨15244978466608101221293685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40653275910954936590116493 15244978466608101221293685)
    ·
      refine ⟨1429216731244509489496283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15244978466608101221293685 1429216731244509489496283)
      ·
        refine ⟨2143825096866764234244425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1429216731244509489496283 2143825096866764234244425)
        ·
          refine ⟨1607868822650073175683319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2143825096866764234244425 1607868822650073175683319)
          ·
            refine ⟨2411803233975109763524979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607868822650073175683319 2411803233975109763524979)
            ·
              refine ⟨3617704850962664645287469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411803233975109763524979 3617704850962664645287469)
              ·
                refine ⟨1356639319110999241982801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3617704850962664645287469 1356639319110999241982801)
                ·
                  refine ⟨1017479489333249431487101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1356639319110999241982801 1017479489333249431487101)
                  ·
                    refine ⟨381554808499968536807663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1017479489333249431487101 381554808499968536807663)
                    ·
                      rfl

theorem cell22_1114613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1114613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114613 prefixEnd_1114613 := by exact prefixLift 1114613
  have htrace : WordTrace (prefixWord ++ tailWord_1114613) baseStart_1114613 baseEnd_1114613 := by
    simpa [prefixWord, tailWord_1114613, baseEnd_1114613] using wordTrace_append hprefix tailTrace_1114613
  have hstable : (prefixWord ++ tailWord_1114613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114613).length < 2 ^ (prefixWord ++ tailWord_1114613).sum := by decide
  have hdescent : baseEnd_1114613 < baseStart_1114613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114682 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 8]
def baseStart_1114682 : Nat := 118140960795 + 1114682 * 2 ^ 59
def prefixEnd_1114682 : Nat := 4983230072969 + 3 ^ 40 * 1114682 * 2
def baseEnd_1114682 : Nat := 127192809536691785610817

theorem tailTrace_1114682 : CollatzResearch.WordTrace tailWord_1114682 prefixEnd_1114682 127192809536691785610817 := by
  unfold tailWord_1114682
  simp only [CollatzResearch.WordTrace]
  refine ⟨10163948136926240343594575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27103861698469974249585533 10163948136926240343594575)
  ·
    refine ⟨15245922205389360515391863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10163948136926240343594575 15245922205389360515391863)
    ·
      refine ⟨22868883308084040773087795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15245922205389360515391863 22868883308084040773087795)
      ·
        refine ⟨34303324962126061159631693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22868883308084040773087795 34303324962126061159631693)
        ·
          refine ⟨12863746860797272934861885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34303324962126061159631693 12863746860797272934861885)
          ·
            refine ⟨4823905072798977350573207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12863746860797272934861885 4823905072798977350573207)
            ·
              refine ⟨7235857609198466025859811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4823905072798977350573207 7235857609198466025859811)
              ·
                refine ⟨10853786413797699038789717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7235857609198466025859811 10853786413797699038789717)
                ·
                  refine ⟨127192809536691785610817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10853786413797699038789717 127192809536691785610817)
                  ·
                    rfl

theorem cell22_1114682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_1114682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114682 prefixEnd_1114682 := by exact prefixLift 1114682
  have htrace : WordTrace (prefixWord ++ tailWord_1114682) baseStart_1114682 baseEnd_1114682 := by
    simpa [prefixWord, tailWord_1114682, baseEnd_1114682] using wordTrace_append hprefix tailTrace_1114682
  have hstable : (prefixWord ++ tailWord_1114682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114682).length < 2 ^ (prefixWord ++ tailWord_1114682).sum := by decide
  have hdescent : baseEnd_1114682 < baseStart_1114682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114684 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_1114684 : Nat := 118140960795 + 1114684 * 2 ^ 59
def prefixEnd_1114684 : Nat := 4983230072969 + 3 ^ 40 * 1114684 * 2
def baseEnd_1114684 : Nat := 381579113250948018282445

theorem tailTrace_1114684 : CollatzResearch.WordTrace tailWord_1114684 prefixEnd_1114684 381579113250948018282445 := by
  unfold tailWord_1114684
  simp only [CollatzResearch.WordTrace]
  refine ⟨20327932746848857857975553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27103910329131810477300737 20327932746848857857975553)
  ·
    refine ⟨15245949560136643393481665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20327932746848857857975553 15245949560136643393481665)
    ·
      refine ⟨11434462170102482545111249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15245949560136643393481665 11434462170102482545111249)
      ·
        refine ⟨8575846627576861908833437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11434462170102482545111249 8575846627576861908833437)
        ·
          refine ⟨3215942485341323215812539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8575846627576861908833437 3215942485341323215812539)
          ·
            refine ⟨4823913728011984823718809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3215942485341323215812539 4823913728011984823718809)
            ·
              refine ⟨3617935296008988617789107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4823913728011984823718809 3617935296008988617789107)
              ·
                refine ⟨5426902944013482926683661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3617935296008988617789107 5426902944013482926683661)
                ·
                  refine ⟨2035088604005056097506373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5426902944013482926683661 2035088604005056097506373)
                  ·
                    refine ⟨381579113250948018282445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2035088604005056097506373 381579113250948018282445)
                    ·
                      rfl

theorem cell22_1114684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_1114684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114684 prefixEnd_1114684 := by exact prefixLift 1114684
  have htrace : WordTrace (prefixWord ++ tailWord_1114684) baseStart_1114684 baseEnd_1114684 := by
    simpa [prefixWord, tailWord_1114684, baseEnd_1114684] using wordTrace_append hprefix tailTrace_1114684
  have hstable : (prefixWord ++ tailWord_1114684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114684).length < 2 ^ (prefixWord ++ tailWord_1114684).sum := by decide
  have hdescent : baseEnd_1114684 < baseStart_1114684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114699 : List Nat := [1, 1, 1, 1, 3, 1, 5, 5, 4]
def baseStart_1114699 : Nat := 118140960795 + 1114699 * 2 ^ 59
def prefixEnd_1114699 : Nat := 4983230072969 + 3 ^ 40 * 1114699 * 2
def baseEnd_1114699 : Nat := 127194749352497659719133

theorem tailTrace_1114699 : CollatzResearch.WordTrace tailWord_1114699 prefixEnd_1114699 127194749352497659719133 := by
  unfold tailWord_1114699
  simp only [CollatzResearch.WordTrace]
  refine ⟨40656412588643373277747151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27104275059095582185164767 40656412588643373277747151)
  ·
    refine ⟨60984618882965059916620727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40656412588643373277747151 60984618882965059916620727)
    ·
      refine ⟨91476928324447589874931091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60984618882965059916620727 91476928324447589874931091)
      ·
        refine ⟨137215392486671384812396637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91476928324447589874931091 137215392486671384812396637)
        ·
          refine ⟨51455772182501769304648739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137215392486671384812396637 51455772182501769304648739)
          ·
            refine ⟨77183658273752653956973109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51455772182501769304648739 77183658273752653956973109)
            ·
              refine ⟨7235967963164311308466229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77183658273752653956973109 7235967963164311308466229)
              ·
                refine ⟨678371996546654185168709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7235967963164311308466229 678371996546654185168709)
                ·
                  refine ⟨127194749352497659719133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 678371996546654185168709 127194749352497659719133)
                  ·
                    rfl

theorem cell22_1114699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 4].length) (baseStart_1114699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114699 prefixEnd_1114699 := by exact prefixLift 1114699
  have htrace : WordTrace (prefixWord ++ tailWord_1114699) baseStart_1114699 baseEnd_1114699 := by
    simpa [prefixWord, tailWord_1114699, baseEnd_1114699] using wordTrace_append hprefix tailTrace_1114699
  have hstable : (prefixWord ++ tailWord_1114699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114699).length < 2 ^ (prefixWord ++ tailWord_1114699).sum := by decide
  have hdescent : baseEnd_1114699 < baseStart_1114699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114716 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 6]
def baseStart_1114716 : Nat := 118140960795 + 1114716 * 2 ^ 59
def prefixEnd_1114716 : Nat := 4983230072969 + 3 ^ 40 * 1114716 * 2
def baseEnd_1114716 : Nat := 127196689168303533827449

theorem tailTrace_1114716 : CollatzResearch.WordTrace tailWord_1114716 prefixEnd_1114716 127196689168303533827449 := by
  unfold tailWord_1114716
  simp only [CollatzResearch.WordTrace]
  refine ⟨20328516314790892590558001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27104688419721190120744001 20328516314790892590558001)
  ·
    refine ⟨15246387236093169442918501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20328516314790892590558001 15246387236093169442918501)
    ·
      refine ⟨2858697606767469270547219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15246387236093169442918501 2858697606767469270547219)
      ·
        refine ⟨4288046410151203905820829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2858697606767469270547219 4288046410151203905820829)
        ·
          refine ⟨1608017403806701464682811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4288046410151203905820829 1608017403806701464682811)
          ·
            refine ⟨2412026105710052197024217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1608017403806701464682811 2412026105710052197024217)
            ·
              refine ⟨1809019579282539147768163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2412026105710052197024217 1809019579282539147768163)
              ·
                refine ⟨2713529368923808721652245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1809019579282539147768163 2713529368923808721652245)
                ·
                  refine ⟨127196689168303533827449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2713529368923808721652245 127196689168303533827449)
                  ·
                    rfl

theorem cell22_1114716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_1114716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114716 prefixEnd_1114716 := by exact prefixLift 1114716
  have htrace : WordTrace (prefixWord ++ tailWord_1114716) baseStart_1114716 baseEnd_1114716 := by
    simpa [prefixWord, tailWord_1114716, baseEnd_1114716] using wordTrace_append hprefix tailTrace_1114716
  have hstable : (prefixWord ++ tailWord_1114716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114716).length < 2 ^ (prefixWord ++ tailWord_1114716).sum := by decide
  have hdescent : baseEnd_1114716 < baseStart_1114716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114727 : List Nat := [1, 1, 5, 1, 1, 1, 1, 11]
def baseStart_1114727 : Nat := 118140960795 + 1114727 * 2 ^ 59
def prefixEnd_1114727 : Nat := 4983230072969 + 3 ^ 40 * 1114727 * 2
def baseEnd_1114727 : Nat := 42399314781078915495257

theorem tailTrace_1114727 : CollatzResearch.WordTrace tailWord_1114727 prefixEnd_1114727 42399314781078915495257 := by
  unfold tailWord_1114727
  simp only [CollatzResearch.WordTrace]
  refine ⟨40657433832541934059766435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27104955888361289373177623 40657433832541934059766435)
  ·
    refine ⟨60986150748812901089649653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40657433832541934059766435 60986150748812901089649653)
    ·
      refine ⟨5717451632701209477154655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60986150748812901089649653 5717451632701209477154655)
      ·
        refine ⟨8576177449051814215731983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5717451632701209477154655 8576177449051814215731983)
        ·
          refine ⟨12864266173577721323597975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8576177449051814215731983 12864266173577721323597975)
          ·
            refine ⟨19296399260366581985396963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12864266173577721323597975 19296399260366581985396963)
            ·
              refine ⟨28944598890549872978095445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19296399260366581985396963 28944598890549872978095445)
              ·
                refine ⟨42399314781078915495257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 28944598890549872978095445 42399314781078915495257)
                ·
                  rfl

theorem cell22_1114727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 11].length) (baseStart_1114727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114727 prefixEnd_1114727 := by exact prefixLift 1114727
  have htrace : WordTrace (prefixWord ++ tailWord_1114727) baseStart_1114727 baseEnd_1114727 := by
    simpa [prefixWord, tailWord_1114727, baseEnd_1114727] using wordTrace_append hprefix tailTrace_1114727
  have hstable : (prefixWord ++ tailWord_1114727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114727).length < 2 ^ (prefixWord ++ tailWord_1114727).sum := by decide
  have hdescent : baseEnd_1114727 < baseStart_1114727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114851 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 6]
def baseStart_1114851 : Nat := 118140960795 + 1114851 * 2 ^ 59
def prefixEnd_1114851 : Nat := 4983230072969 + 3 ^ 40 * 1114851 * 2
def baseEnd_1114851 : Nat := 127212093587938416452311

theorem tailTrace_1114851 : CollatzResearch.WordTrace tailWord_1114851 prefixEnd_1114851 127212093587938416452311 := by
  unfold tailWord_1114851
  simp only [CollatzResearch.WordTrace]
  refine ⟨40661956484092703237280407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27107970989395135491520271 40661956484092703237280407)
  ·
    refine ⟨60992934726139054855920611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40661956484092703237280407 60992934726139054855920611)
    ·
      refine ⟨91489402089208582283880917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60992934726139054855920611 91489402089208582283880917)
      ·
        refine ⟨2144282861465826147278459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 91489402089208582283880917 2144282861465826147278459)
        ·
          refine ⟨3216424292198739220917689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2144282861465826147278459 3216424292198739220917689)
          ·
            refine ⟨2412318219149054415688267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3216424292198739220917689 2412318219149054415688267)
            ·
              refine ⟨3618477328723581623532401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2412318219149054415688267 3618477328723581623532401)
              ·
                refine ⟨2713857996542686217649301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3618477328723581623532401 2713857996542686217649301)
                ·
                  refine ⟨127212093587938416452311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2713857996542686217649301 127212093587938416452311)
                  ·
                    rfl

theorem cell22_1114851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 6].length) (baseStart_1114851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114851 prefixEnd_1114851 := by exact prefixLift 1114851
  have htrace : WordTrace (prefixWord ++ tailWord_1114851) baseStart_1114851 baseEnd_1114851 := by
    simpa [prefixWord, tailWord_1114851, baseEnd_1114851] using wordTrace_append hprefix tailTrace_1114851
  have hstable : (prefixWord ++ tailWord_1114851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114851).length < 2 ^ (prefixWord ++ tailWord_1114851).sum := by decide
  have hdescent : baseEnd_1114851 < baseStart_1114851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114864 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 1, 6]
def baseStart_1114864 : Nat := 118140960795 + 1114864 * 2 ^ 59
def prefixEnd_1114864 : Nat := 4983230072969 + 3 ^ 40 * 1114864 * 2
def baseEnd_1114864 : Nat := 381640730929487548781893

theorem tailTrace_1114864 : CollatzResearch.WordTrace tailWord_1114864 prefixEnd_1114864 381640730929487548781893 := by
  unfold tailWord_1114864
  simp only [CollatzResearch.WordTrace]
  refine ⟨20331215316522803228751823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27108287088697070971669097 20331215316522803228751823)
  ·
    refine ⟨30496822974784204843127735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20331215316522803228751823 30496822974784204843127735)
    ·
      refine ⟨45745234462176307264691603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30496822974784204843127735 45745234462176307264691603)
      ·
        refine ⟨68617851693264460897037405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45745234462176307264691603 68617851693264460897037405)
        ·
          refine ⟨25731694384974172836389027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68617851693264460897037405 25731694384974172836389027)
          ·
            refine ⟨38597541577461259254583541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25731694384974172836389027 38597541577461259254583541)
            ·
              refine ⟨3618519522886993055117207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38597541577461259254583541 3618519522886993055117207)
              ·
                refine ⟨5427779284330489582675811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3618519522886993055117207 5427779284330489582675811)
                ·
                  refine ⟨8141668926495734374013717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5427779284330489582675811 8141668926495734374013717)
                  ·
                    refine ⟨381640730929487548781893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8141668926495734374013717 381640730929487548781893)
                    ·
                      rfl

theorem cell22_1114864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_1114864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114864 prefixEnd_1114864 := by exact prefixLift 1114864
  have htrace : WordTrace (prefixWord ++ tailWord_1114864) baseStart_1114864 baseEnd_1114864 := by
    simpa [prefixWord, tailWord_1114864, baseEnd_1114864] using wordTrace_append hprefix tailTrace_1114864
  have hstable : (prefixWord ++ tailWord_1114864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114864).length < 2 ^ (prefixWord ++ tailWord_1114864).sum := by decide
  have hdescent : baseEnd_1114864 < baseStart_1114864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114866 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_1114866 : Nat := 118140960795 + 1114866 * 2 ^ 59
def prefixEnd_1114866 : Nat := 4983230072969 + 3 ^ 40 * 1114866 * 2
def baseEnd_1114866 : Nat := 381641415570360210231887

theorem tailTrace_1114866 : CollatzResearch.WordTrace tailWord_1114866 prefixEnd_1114866 381641415570360210231887 := by
  unfold tailWord_1114866
  simp only [CollatzResearch.WordTrace]
  refine ⟨10165625894759590199769113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27108335719358907199384301 10165625894759590199769113)
  ·
    refine ⟨7624219421069692649826835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10165625894759590199769113 7624219421069692649826835)
    ·
      refine ⟨11436329131604538974740253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7624219421069692649826835 11436329131604538974740253)
      ·
        refine ⟨4288623424351702115527595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11436329131604538974740253 4288623424351702115527595)
        ·
          refine ⟨6432935136527553173291393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4288623424351702115527595 6432935136527553173291393)
          ·
            refine ⟨4824701352395664879968545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6432935136527553173291393 4824701352395664879968545)
            ·
              refine ⟨3618526014296748659976409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4824701352395664879968545 3618526014296748659976409)
              ·
                refine ⟨2713894510722561494982307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3618526014296748659976409 2713894510722561494982307)
                ·
                  refine ⟨4070841766083842242473461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2713894510722561494982307 4070841766083842242473461)
                  ·
                    refine ⟨381641415570360210231887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4070841766083842242473461 381641415570360210231887)
                    ·
                      rfl

theorem cell22_1114866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_1114866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114866 prefixEnd_1114866 := by exact prefixLift 1114866
  have htrace : WordTrace (prefixWord ++ tailWord_1114866) baseStart_1114866 baseEnd_1114866 := by
    simpa [prefixWord, tailWord_1114866, baseEnd_1114866] using wordTrace_append hprefix tailTrace_1114866
  have hstable : (prefixWord ++ tailWord_1114866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114866).length < 2 ^ (prefixWord ++ tailWord_1114866).sum := by decide
  have hdescent : baseEnd_1114866 < baseStart_1114866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1114924 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 9]
def baseStart_1114924 : Nat := 118140960795 + 1114924 * 2 ^ 59
def prefixEnd_1114924 : Nat := 4983230072969 + 3 ^ 40 * 1114924 * 2
def baseEnd_1114924 : Nat := 127220423385222464093903

theorem tailTrace_1114924 : CollatzResearch.WordTrace tailWord_1114924 prefixEnd_1114924 127220423385222464093903 := by
  unfold tailWord_1114924
  simp only [CollatzResearch.WordTrace]
  refine ⟨20332309506414118352343913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27109746008552157803125217 20332309506414118352343913)
  ·
    refine ⟨15249232129810588764257935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20332309506414118352343913 15249232129810588764257935)
    ·
      refine ⟨22873848194715883146386903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15249232129810588764257935 22873848194715883146386903)
      ·
        refine ⟨34310772292073824719580355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22873848194715883146386903 34310772292073824719580355)
        ·
          refine ⟨51466158438110737079370533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34310772292073824719580355 51466158438110737079370533)
          ·
            refine ⟨9649904707145763202381975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51466158438110737079370533 9649904707145763202381975)
            ·
              refine ⟨14474857060718644803572963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9649904707145763202381975 14474857060718644803572963)
              ·
                refine ⟨21712285591077967205359445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14474857060718644803572963 21712285591077967205359445)
                ·
                  refine ⟨127220423385222464093903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21712285591077967205359445 127220423385222464093903)
                  ·
                    rfl

theorem cell22_1114924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_1114924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1114924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1114924 prefixEnd_1114924 := by exact prefixLift 1114924
  have htrace : WordTrace (prefixWord ++ tailWord_1114924) baseStart_1114924 baseEnd_1114924 := by
    simpa [prefixWord, tailWord_1114924, baseEnd_1114924] using wordTrace_append hprefix tailTrace_1114924
  have hstable : (prefixWord ++ tailWord_1114924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1114924).length < 2 ^ (prefixWord ++ tailWord_1114924).sum := by decide
  have hdescent : baseEnd_1114924 < baseStart_1114924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1114924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115018 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_1115018 : Nat := 118140960795 + 1115018 * 2 ^ 59
def prefixEnd_1115018 : Nat := 4983230072969 + 3 ^ 40 * 1115018 * 2
def baseEnd_1115018 : Nat := 381693448276682480431421

theorem tailTrace_1115018 : CollatzResearch.WordTrace tailWord_1115018 prefixEnd_1115018 381693448276682480431421 := by
  unfold tailWord_1115018
  simp only [CollatzResearch.WordTrace]
  refine ⟨10167011868621922689652427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27112031649658460505739805 10167011868621922689652427)
  ·
    refine ⟨15250517802932884034478641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10167011868621922689652427 15250517802932884034478641)
    ·
      refine ⟨11437888352199663025858981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15250517802932884034478641 11437888352199663025858981)
      ·
        refine ⟨2144604066037436817348559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11437888352199663025858981 2144604066037436817348559)
        ·
          refine ⟨3216906099056155226022839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2144604066037436817348559 3216906099056155226022839)
          ·
            refine ⟨4825359148584232839034259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3216906099056155226022839 4825359148584232839034259)
            ·
              refine ⟨7238038722876349258551389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4825359148584232839034259 7238038722876349258551389)
              ·
                refine ⟨2714264521078630971956771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7238038722876349258551389 2714264521078630971956771)
                ·
                  refine ⟨4071396781617946457935157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2714264521078630971956771 4071396781617946457935157)
                  ·
                    refine ⟨381693448276682480431421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4071396781617946457935157 381693448276682480431421)
                    ·
                      rfl

theorem cell22_1115018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_1115018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115018 prefixEnd_1115018 := by exact prefixLift 1115018
  have htrace : WordTrace (prefixWord ++ tailWord_1115018) baseStart_1115018 baseEnd_1115018 := by
    simpa [prefixWord, tailWord_1115018, baseEnd_1115018] using wordTrace_append hprefix tailTrace_1115018
  have hstable : (prefixWord ++ tailWord_1115018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115018).length < 2 ^ (prefixWord ++ tailWord_1115018).sum := by decide
  have hdescent : baseEnd_1115018 < baseStart_1115018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115063 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 3, 3]
def baseStart_1115063 : Nat := 118140960795 + 1115063 * 2 ^ 59
def prefixEnd_1115063 : Nat := 4983230072969 + 3 ^ 40 * 1115063 * 2
def baseEnd_1115063 : Nat := 381708852696317363056283

theorem tailTrace_1115063 : CollatzResearch.WordTrace tailWord_1115063 prefixEnd_1115063 381708852696317363056283 := by
  unfold tailWord_1115063
  simp only [CollatzResearch.WordTrace]
  refine ⟨40669688759324663443997843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27113125839549775629331895 40669688759324663443997843)
  ·
    refine ⟨61004533138986995165996765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40669688759324663443997843 61004533138986995165996765)
    ·
      refine ⟨22876699927120123187248787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61004533138986995165996765 22876699927120123187248787)
      ·
        refine ⟨34315049890680184780873181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22876699927120123187248787 34315049890680184780873181)
        ·
          refine ⟨12868143709005069292827443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34315049890680184780873181 12868143709005069292827443)
          ·
            refine ⟨19302215563507603939241165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12868143709005069292827443 19302215563507603939241165)
            ·
              refine ⟨7238330836315351477215437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19302215563507603939241165 7238330836315351477215437)
              ·
                refine ⟨2714374063618256803955789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7238330836315351477215437 2714374063618256803955789)
                ·
                  refine ⟨1017890273856846301483421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2714374063618256803955789 1017890273856846301483421)
                  ·
                    refine ⟨381708852696317363056283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1017890273856846301483421 381708852696317363056283)
                    ·
                      rfl

theorem cell22_1115063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_1115063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115063 prefixEnd_1115063 := by exact prefixLift 1115063
  have htrace : WordTrace (prefixWord ++ tailWord_1115063) baseStart_1115063 baseEnd_1115063 := by
    simpa [prefixWord, tailWord_1115063, baseEnd_1115063] using wordTrace_append hprefix tailTrace_1115063
  have hstable : (prefixWord ++ tailWord_1115063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115063).length < 2 ^ (prefixWord ++ tailWord_1115063).sum := by decide
  have hdescent : baseEnd_1115063 < baseStart_1115063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115097 : List Nat := [1, 2, 1, 2, 5, 1, 3, 3, 1, 3]
def baseStart_1115097 : Nat := 118140960795 + 1115097 * 2 ^ 59
def prefixEnd_1115097 : Nat := 4983230072969 + 3 ^ 40 * 1115097 * 2
def baseEnd_1115097 : Nat := 381720491591152607706179

theorem tailTrace_1115097 : CollatzResearch.WordTrace tailWord_1115097 prefixEnd_1115097 381720491591152607706179 := by
  unfold tailWord_1115097
  simp only [CollatzResearch.WordTrace]
  refine ⟨40670928841201487250735545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27113952560800991500490363 40670928841201487250735545)
  ·
    refine ⟨30503196630901115438051659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40670928841201487250735545 30503196630901115438051659)
    ·
      refine ⟨45754794946351673157077489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30503196630901115438051659 45754794946351673157077489)
      ·
        refine ⟨34316096209763754867808117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45754794946351673157077489 34316096209763754867808117)
        ·
          refine ⟨3217134019665352018857011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34316096209763754867808117 3217134019665352018857011)
          ·
            refine ⟨4825701029498028028285517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217134019665352018857011 4825701029498028028285517)
            ·
              refine ⟨1809637886061760510607069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4825701029498028028285517 1809637886061760510607069)
              ·
                refine ⟨678614207273160191477651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1809637886061760510607069 678614207273160191477651)
                ·
                  refine ⟨1017921310909740287216477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678614207273160191477651 1017921310909740287216477)
                  ·
                    refine ⟨381720491591152607706179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1017921310909740287216477 381720491591152607706179)
                    ·
                      rfl

theorem cell22_1115097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 1, 3].length) (baseStart_1115097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115097 prefixEnd_1115097 := by exact prefixLift 1115097
  have htrace : WordTrace (prefixWord ++ tailWord_1115097) baseStart_1115097 baseEnd_1115097 := by
    simpa [prefixWord, tailWord_1115097, baseEnd_1115097] using wordTrace_append hprefix tailTrace_1115097
  have hstable : (prefixWord ++ tailWord_1115097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115097).length < 2 ^ (prefixWord ++ tailWord_1115097).sum := by decide
  have hdescent : baseEnd_1115097 < baseStart_1115097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115114 : List Nat := [3, 1, 3, 1, 2, 3, 3, 2, 1, 3]
def baseStart_1115114 : Nat := 118140960795 + 1115114 * 2 ^ 59
def prefixEnd_1115114 : Nat := 4983230072969 + 3 ^ 40 * 1115114 * 2
def baseEnd_1115114 : Nat := 381726311038570230031127

theorem tailTrace_1115114 : CollatzResearch.WordTrace tailWord_1115114 prefixEnd_1115114 381726311038570230031127 := by
  unfold tailWord_1115114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10167887220534974788526099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27114365921426599436069597 10167887220534974788526099)
  ·
    refine ⟨15251830830802462182789149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10167887220534974788526099 15251830830802462182789149)
    ·
      refine ⟨5719436561550923318545931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15251830830802462182789149 5719436561550923318545931)
      ·
        refine ⟨8579154842326384977818897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5719436561550923318545931 8579154842326384977818897)
        ·
          refine ⟨6434366131744788733364173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8579154842326384977818897 6434366131744788733364173)
          ·
            refine ⟨2412887299404295775011565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6434366131744788733364173 2412887299404295775011565)
            ·
              refine ⟨904832737276610915629337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2412887299404295775011565 904832737276610915629337)
              ·
                refine ⟨678624552957458186722003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904832737276610915629337 678624552957458186722003)
                ·
                  refine ⟨1017936829436187280083005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678624552957458186722003 1017936829436187280083005)
                  ·
                    refine ⟨381726311038570230031127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1017936829436187280083005 381726311038570230031127)
                    ·
                      rfl

theorem cell22_1115114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_1115114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115114 prefixEnd_1115114 := by exact prefixLift 1115114
  have htrace : WordTrace (prefixWord ++ tailWord_1115114) baseStart_1115114 baseEnd_1115114 := by
    simpa [prefixWord, tailWord_1115114, baseEnd_1115114] using wordTrace_append hprefix tailTrace_1115114
  have hstable : (prefixWord ++ tailWord_1115114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115114).length < 2 ^ (prefixWord ++ tailWord_1115114).sum := by decide
  have hdescent : baseEnd_1115114 < baseStart_1115114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115153 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 6, 3]
def baseStart_1115153 : Nat := 118140960795 + 1115153 * 2 ^ 59
def prefixEnd_1115153 : Nat := 4983230072969 + 3 ^ 40 * 1115153 * 2
def baseEnd_1115153 : Nat := 381739661535587128306007

theorem tailTrace_1115153 : CollatzResearch.WordTrace tailWord_1115153 prefixEnd_1115153 381739661535587128306007 := by
  unfold tailWord_1115153
  simp only [CollatzResearch.WordTrace]
  refine ⟨40672971328998608814774113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27115314219332405876516075 40672971328998608814774113)
  ·
    refine ⟨30504728496748956611080585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40672971328998608814774113 30504728496748956611080585)
    ·
      refine ⟨22878546372561717458310439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30504728496748956611080585 22878546372561717458310439)
      ·
        refine ⟨34317819558842576187465659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22878546372561717458310439 34317819558842576187465659)
        ·
          refine ⟨51476729338263864281198489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34317819558842576187465659 51476729338263864281198489)
          ·
            refine ⟨38607547003697898210898867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51476729338263864281198489 38607547003697898210898867)
            ·
              refine ⟨57911320505546847316348301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38607547003697898210898867 57911320505546847316348301)
              ·
                refine ⟨21716745189580067743630613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57911320505546847316348301 21716745189580067743630613)
                ·
                  refine ⟨1017972430761565675482685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21716745189580067743630613 1017972430761565675482685)
                  ·
                    refine ⟨381739661535587128306007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1017972430761565675482685 381739661535587128306007)
                    ·
                      rfl

theorem cell22_1115153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_1115153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115153 prefixEnd_1115153 := by exact prefixLift 1115153
  have htrace : WordTrace (prefixWord ++ tailWord_1115153) baseStart_1115153 baseEnd_1115153 := by
    simpa [prefixWord, tailWord_1115153, baseEnd_1115153] using wordTrace_append hprefix tailTrace_1115153
  have hstable : (prefixWord ++ tailWord_1115153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115153).length < 2 ^ (prefixWord ++ tailWord_1115153).sum := by decide
  have hdescent : baseEnd_1115153 < baseStart_1115153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115157 : List Nat := [1, 3, 2, 1, 4, 2, 3, 1, 1, 4]
def baseStart_1115157 : Nat := 118140960795 + 1115157 * 2 ^ 59
def prefixEnd_1115157 : Nat := 4983230072969 + 3 ^ 40 * 1115157 * 2
def baseEnd_1115157 : Nat := 381741030817332451205995

theorem tailTrace_1115157 : CollatzResearch.WordTrace tailWord_1115157 prefixEnd_1115157 381741030817332451205995 := by
  unfold tailWord_1115157
  simp only [CollatzResearch.WordTrace]
  refine ⟨40673117220984117497919725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27115411480656078331946483 40673117220984117497919725)
  ·
    refine ⟨15252418957869044061719897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40673117220984117497919725 15252418957869044061719897)
    ·
      refine ⟨11439314218401783046289923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15252418957869044061719897 11439314218401783046289923)
      ·
        refine ⟨17158971327602674569434885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11439314218401783046289923 17158971327602674569434885)
        ·
          refine ⟨3217307123925501481769041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17158971327602674569434885 3217307123925501481769041)
          ·
            refine ⟨2412980342944126111326781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3217307123925501481769041 2412980342944126111326781)
            ·
              refine ⟨904867628604047291747543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2412980342944126111326781 904867628604047291747543)
              ·
                refine ⟨1357301442906070937621315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904867628604047291747543 1357301442906070937621315)
                ·
                  refine ⟨2035952164359106406431973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357301442906070937621315 2035952164359106406431973)
                  ·
                    refine ⟨381741030817332451205995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2035952164359106406431973 381741030817332451205995)
                    ·
                      rfl

theorem cell22_1115157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_1115157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115157 prefixEnd_1115157 := by exact prefixLift 1115157
  have htrace : WordTrace (prefixWord ++ tailWord_1115157) baseStart_1115157 baseEnd_1115157 := by
    simpa [prefixWord, tailWord_1115157, baseEnd_1115157] using wordTrace_append hprefix tailTrace_1115157
  have hstable : (prefixWord ++ tailWord_1115157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115157).length < 2 ^ (prefixWord ++ tailWord_1115157).sum := by decide
  have hdescent : baseEnd_1115157 < baseStart_1115157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115172 : List Nat := [2, 3, 1, 4, 1, 2, 1, 4, 4]
def baseStart_1115172 : Nat := 118140960795 + 1115172 * 2 ^ 59
def prefixEnd_1115172 : Nat := 4983230072969 + 3 ^ 40 * 1115172 * 2
def baseEnd_1115172 : Nat := 127248721874625804026983

theorem tailTrace_1115172 : CollatzResearch.WordTrace tailWord_1115172 prefixEnd_1115172 127248721874625804026983 := by
  unfold tailWord_1115172
  simp only [CollatzResearch.WordTrace]
  refine ⟨20336832157964887529857885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27115776210619850039810513 20336832157964887529857885)
  ·
    refine ⟨7626312059236832823696707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20336832157964887529857885 7626312059236832823696707)
    ·
      refine ⟨11439468088855249235545061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7626312059236832823696707 11439468088855249235545061)
      ·
        refine ⟨2144900266660359231664699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11439468088855249235545061 2144900266660359231664699)
        ·
          refine ⟨3217350399990538847497049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2144900266660359231664699 3217350399990538847497049)
          ·
            refine ⟨2413012799992904135622787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3217350399990538847497049 2413012799992904135622787)
            ·
              refine ⟨3619519199989356203434181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2413012799992904135622787 3619519199989356203434181)
              ·
                refine ⟨678659849998004288143909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3619519199989356203434181 678659849998004288143909)
                ·
                  refine ⟨127248721874625804026983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 678659849998004288143909 127248721874625804026983)
                  ·
                    rfl

theorem cell22_1115172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_1115172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115172 prefixEnd_1115172 := by exact prefixLift 1115172
  have htrace : WordTrace (prefixWord ++ tailWord_1115172) baseStart_1115172 baseEnd_1115172 := by
    simpa [prefixWord, tailWord_1115172, baseEnd_1115172] using wordTrace_append hprefix tailTrace_1115172
  have hstable : (prefixWord ++ tailWord_1115172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115172).length < 2 ^ (prefixWord ++ tailWord_1115172).sum := by decide
  have hdescent : baseEnd_1115172 < baseStart_1115172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115232 : List Nat := [2, 1, 1, 3, 2, 2, 1, 6, 1, 3]
def baseStart_1115232 : Nat := 118140960795 + 1115232 * 2 ^ 59
def prefixEnd_1115232 : Nat := 4983230072969 + 3 ^ 40 * 1115232 * 2
def baseEnd_1115232 : Nat := 381766704850057255580765

theorem tailTrace_1115232 : CollatzResearch.WordTrace tailWord_1115232 prefixEnd_1115232 381766704850057255580765 := by
  unfold tailWord_1115232
  simp only [CollatzResearch.WordTrace]
  refine ⟨20337926347856202653449975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27117235130474936871266633 20337926347856202653449975)
  ·
    refine ⟨30506889521784303980174963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20337926347856202653449975 30506889521784303980174963)
    ·
      refine ⟨45760334282676455970262445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30506889521784303980174963 45760334282676455970262445)
      ·
        refine ⟨17160125356003670988848417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45760334282676455970262445 17160125356003670988848417)
        ·
          refine ⟨12870094017002753241636313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17160125356003670988848417 12870094017002753241636313)
          ·
            refine ⟨9652570512752064931227235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12870094017002753241636313 9652570512752064931227235)
            ·
              refine ⟨14478855769128097396840853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9652570512752064931227235 14478855769128097396840853)
              ·
                refine ⟨678696364177879565476915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14478855769128097396840853 678696364177879565476915)
                ·
                  refine ⟨1018044546266819348215373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678696364177879565476915 1018044546266819348215373)
                  ·
                    refine ⟨381766704850057255580765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1018044546266819348215373 381766704850057255580765)
                    ·
                      rfl

theorem cell22_1115232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 1, 3].length) (baseStart_1115232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115232 prefixEnd_1115232 := by exact prefixLift 1115232
  have htrace : WordTrace (prefixWord ++ tailWord_1115232) baseStart_1115232 baseEnd_1115232 := by
    simpa [prefixWord, tailWord_1115232, baseEnd_1115232] using wordTrace_append hprefix tailTrace_1115232
  have hstable : (prefixWord ++ tailWord_1115232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115232).length < 2 ^ (prefixWord ++ tailWord_1115232).sum := by decide
  have hdescent : baseEnd_1115232 < baseStart_1115232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115334 : List Nat := [6, 1, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1115334 : Nat := 118140960795 + 1115334 * 2 ^ 59
def prefixEnd_1115334 : Nat := 4983230072969 + 3 ^ 40 * 1115334 * 2
def baseEnd_1115334 : Nat := 381801621534562989530453

theorem tailTrace_1115334 : CollatzResearch.WordTrace tailWord_1115334 prefixEnd_1115334 381801621534562989530453 := by
  unfold tailWord_1115334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1271236654416964897722283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27119715294228584484742037 1271236654416964897722283)
  ·
    refine ⟨1906854981625447346583425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1271236654416964897722283 1906854981625447346583425)
    ·
      refine ⟨1430141236219085509937569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1906854981625447346583425 1430141236219085509937569)
      ·
        refine ⟨1072605927164314132453177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1430141236219085509937569 1072605927164314132453177)
        ·
          refine ⟨804454445373235599339883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1072605927164314132453177 804454445373235599339883)
          ·
            refine ⟨1206681668059853399009825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804454445373235599339883 1206681668059853399009825)
            ·
              refine ⟨905011251044890049257369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1206681668059853399009825 905011251044890049257369)
              ·
                refine ⟨678758438283667536943027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 905011251044890049257369 678758438283667536943027)
                ·
                  refine ⟨1018137657425501305414541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678758438283667536943027 1018137657425501305414541)
                  ·
                    refine ⟨381801621534562989530453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1018137657425501305414541 381801621534562989530453)
                    ·
                      rfl

theorem cell22_1115334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1115334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115334 prefixEnd_1115334 := by exact prefixLift 1115334
  have htrace : WordTrace (prefixWord ++ tailWord_1115334) baseStart_1115334 baseEnd_1115334 := by
    simpa [prefixWord, tailWord_1115334, baseEnd_1115334] using wordTrace_append hprefix tailTrace_1115334
  have hstable : (prefixWord ++ tailWord_1115334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115334).length < 2 ^ (prefixWord ++ tailWord_1115334).sum := by decide
  have hdescent : baseEnd_1115334 < baseStart_1115334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115352 : List Nat := [2, 1, 2, 2, 5, 2, 1, 7]
def baseStart_1115352 : Nat := 118140960795 + 1115352 * 2 ^ 59
def prefixEnd_1115352 : Nat := 4983230072969 + 3 ^ 40 * 1115352 * 2
def baseEnd_1115352 : Nat := 42423087033601882508933

theorem tailTrace_1115352 : CollatzResearch.WordTrace tailWord_1115352 prefixEnd_1115352 42423087033601882508933 := by
  unfold tailWord_1115352
  simp only [CollatzResearch.WordTrace]
  refine ⟨20340114727638832900634155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27120152970185110534178873 20340114727638832900634155)
  ·
    refine ⟨30510172091458249350951233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20340114727638832900634155 30510172091458249350951233)
    ·
      refine ⟨22882629068593687013213425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30510172091458249350951233 22882629068593687013213425)
      ·
        refine ⟨17161971801445265259910069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22882629068593687013213425 17161971801445265259910069)
        ·
          refine ⟨1608934856385493618116569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17161971801445265259910069 1608934856385493618116569)
          ·
            refine ⟨1206701142289120213587427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1608934856385493618116569 1206701142289120213587427)
            ·
              refine ⟨1810051713433680320381141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206701142289120213587427 1810051713433680320381141)
              ·
                refine ⟨42423087033601882508933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1810051713433680320381141 42423087033601882508933)
                ·
                  rfl

theorem cell22_1115352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 7].length) (baseStart_1115352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115352 prefixEnd_1115352 := by exact prefixLift 1115352
  have htrace : WordTrace (prefixWord ++ tailWord_1115352) baseStart_1115352 baseEnd_1115352 := by
    simpa [prefixWord, tailWord_1115352, baseEnd_1115352] using wordTrace_append hprefix tailTrace_1115352
  have hstable : (prefixWord ++ tailWord_1115352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115352).length < 2 ^ (prefixWord ++ tailWord_1115352).sum := by decide
  have hdescent : baseEnd_1115352 < baseStart_1115352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115395 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 2, 5]
def baseStart_1115395 : Nat := 118140960795 + 1115395 * 2 ^ 59
def prefixEnd_1115395 : Nat := 4983230072969 + 3 ^ 40 * 1115395 * 2
def baseEnd_1115395 : Nat := 381822503081179163755265

theorem tailTrace_1115395 : CollatzResearch.WordTrace tailWord_1115395 prefixEnd_1115395 381822503081179163755265 := by
  unfold tailWord_1115395
  simp only [CollatzResearch.WordTrace]
  refine ⟨40681797794121884145083639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27121198529414589430055759 40681797794121884145083639)
  ·
    refine ⟨61022696691182826217625459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40681797794121884145083639 61022696691182826217625459)
    ·
      refine ⟨91534045036774239326438189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61022696691182826217625459 91534045036774239326438189)
      ·
        refine ⟨34325266888790339747414321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91534045036774239326438189 34325266888790339747414321)
        ·
          refine ⟨25743950166592754810560741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34325266888790339747414321 25743950166592754810560741)
          ·
            refine ⟨4826990656236141526980139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25743950166592754810560741 4826990656236141526980139)
            ·
              refine ⟨7240485984354212290470209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4826990656236141526980139 7240485984354212290470209)
              ·
                refine ⟨5430364488265659217852657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7240485984354212290470209 5430364488265659217852657)
                ·
                  refine ⟨4072773366199244413389493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5430364488265659217852657 4072773366199244413389493)
                  ·
                    refine ⟨381822503081179163755265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4072773366199244413389493 381822503081179163755265)
                    ·
                      rfl

theorem cell22_1115395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 5].length) (baseStart_1115395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115395 prefixEnd_1115395 := by exact prefixLift 1115395
  have htrace : WordTrace (prefixWord ++ tailWord_1115395) baseStart_1115395 baseEnd_1115395 := by
    simpa [prefixWord, tailWord_1115395, baseEnd_1115395] using wordTrace_append hprefix tailTrace_1115395
  have hstable : (prefixWord ++ tailWord_1115395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115395).length < 2 ^ (prefixWord ++ tailWord_1115395).sum := by decide
  have hdescent : baseEnd_1115395 < baseStart_1115395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115427 : List Nat := [1, 1, 1, 4, 2, 3, 1, 4, 1, 4]
def baseStart_1115427 : Nat := 118140960795 + 1115427 * 2 ^ 59
def prefixEnd_1115427 : Nat := 4983230072969 + 3 ^ 40 * 1115427 * 2
def baseEnd_1115427 : Nat := 381833457335141746955167

theorem tailTrace_1115427 : CollatzResearch.WordTrace tailWord_1115427 prefixEnd_1115427 381833457335141746955167 := by
  unfold tailWord_1115427
  simp only [CollatzResearch.WordTrace]
  refine ⟨40682964930005953610248535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27121976620003969073499023 40682964930005953610248535)
  ·
    refine ⟨61024447395008930415372803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40682964930005953610248535 61024447395008930415372803)
    ·
      refine ⟨91536671092513395623059205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61024447395008930415372803 91536671092513395623059205)
      ·
        refine ⟨17163125829846261679323601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91536671092513395623059205 17163125829846261679323601)
        ·
          refine ⟨12872344372384696259492701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17163125829846261679323601 12872344372384696259492701)
          ·
            refine ⟨4827129139644261097309763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12872344372384696259492701 4827129139644261097309763)
            ·
              refine ⟨7240693709466391645964645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4827129139644261097309763 7240693709466391645964645)
              ·
                refine ⟨1357630070524948433618371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7240693709466391645964645 1357630070524948433618371)
                ·
                  refine ⟨2036445105787422650427557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357630070524948433618371 2036445105787422650427557)
                  ·
                    refine ⟨381833457335141746955167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2036445105787422650427557 381833457335141746955167)
                    ·
                      rfl

theorem cell22_1115427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 4].length) (baseStart_1115427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115427 prefixEnd_1115427 := by exact prefixLift 1115427
  have htrace : WordTrace (prefixWord ++ tailWord_1115427) baseStart_1115427 baseEnd_1115427 := by
    simpa [prefixWord, tailWord_1115427, baseEnd_1115427] using wordTrace_append hprefix tailTrace_1115427
  have hstable : (prefixWord ++ tailWord_1115427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115427).length < 2 ^ (prefixWord ++ tailWord_1115427).sum := by decide
  have hdescent : baseEnd_1115427 < baseStart_1115427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115440 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 3, 5]
def baseStart_1115440 : Nat := 118140960795 + 1115440 * 2 ^ 59
def prefixEnd_1115440 : Nat := 4983230072969 + 3 ^ 40 * 1115440 * 2
def baseEnd_1115440 : Nat := 381837907500814046380127

theorem tailTrace_1115440 : CollatzResearch.WordTrace tailWord_1115440 prefixEnd_1115440 381837907500814046380127 := by
  unfold tailWord_1115440
  simp only [CollatzResearch.WordTrace]
  refine ⟨20341719539479428415235887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27122292719305904553647849 20341719539479428415235887)
  ·
    refine ⟨30512579309219142622853831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20341719539479428415235887 30512579309219142622853831)
    ·
      refine ⟨45768868963828713934280747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30512579309219142622853831 45768868963828713934280747)
      ·
        refine ⟨68653303445743070901421121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45768868963828713934280747 68653303445743070901421121)
        ·
          refine ⟨51489977584307303176065841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68653303445743070901421121 51489977584307303176065841)
          ·
            refine ⟨38617483188230477382049381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51489977584307303176065841 38617483188230477382049381)
            ·
              refine ⟨7240778097793214509134259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38617483188230477382049381 7240778097793214509134259)
              ·
                refine ⟨10861167146689821763701389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7240778097793214509134259 10861167146689821763701389)
                ·
                  refine ⟨4072937680008683161388021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10861167146689821763701389 4072937680008683161388021)
                  ·
                    refine ⟨381837907500814046380127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4072937680008683161388021 381837907500814046380127)
                    ·
                      rfl

theorem cell22_1115440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_1115440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115440 prefixEnd_1115440 := by exact prefixLift 1115440
  have htrace : WordTrace (prefixWord ++ tailWord_1115440) baseStart_1115440 baseEnd_1115440 := by
    simpa [prefixWord, tailWord_1115440, baseEnd_1115440] using wordTrace_append hprefix tailTrace_1115440
  have hstable : (prefixWord ++ tailWord_1115440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115440).length < 2 ^ (prefixWord ++ tailWord_1115440).sum := by decide
  have hdescent : baseEnd_1115440 < baseStart_1115440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115444 : List Nat := [2, 5, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_1115444 : Nat := 118140960795 + 1115444 * 2 ^ 59
def prefixEnd_1115444 : Nat := 4983230072969 + 3 ^ 40 * 1115444 * 2
def baseEnd_1115444 : Nat := 381839276782559369280115

theorem tailTrace_1115444 : CollatzResearch.WordTrace tailWord_1115444 prefixEnd_1115444 381839276782559369280115 := by
  unfold tailWord_1115444
  simp only [CollatzResearch.WordTrace]
  refine ⟨20341792485472182756808693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27122389980629577009078257 20341792485472182756808693)
  ·
    refine ⟨1907043045513017133450815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20341792485472182756808693 1907043045513017133450815)
    ·
      refine ⟨2860564568269525700176223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1907043045513017133450815 2860564568269525700176223)
      ·
        refine ⟨4290846852404288550264335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2860564568269525700176223 4290846852404288550264335)
        ·
          refine ⟨6436270278606432825396503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4290846852404288550264335 6436270278606432825396503)
          ·
            refine ⟨9654405417909649238094755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6436270278606432825396503 9654405417909649238094755)
            ·
              refine ⟨14481608126864473857142133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9654405417909649238094755 14481608126864473857142133)
              ·
                refine ⟨1357650761893544424107075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14481608126864473857142133 1357650761893544424107075)
                ·
                  refine ⟨2036476142840316636160613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357650761893544424107075 2036476142840316636160613)
                  ·
                    refine ⟨381839276782559369280115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2036476142840316636160613 381839276782559369280115)
                    ·
                      rfl

theorem cell22_1115444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_1115444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115444 prefixEnd_1115444 := by exact prefixLift 1115444
  have htrace : WordTrace (prefixWord ++ tailWord_1115444) baseStart_1115444 baseEnd_1115444 := by
    simpa [prefixWord, tailWord_1115444, baseEnd_1115444] using wordTrace_append hprefix tailTrace_1115444
  have hstable : (prefixWord ++ tailWord_1115444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115444).length < 2 ^ (prefixWord ++ tailWord_1115444).sum := by decide
  have hdescent : baseEnd_1115444 < baseStart_1115444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115521 : List Nat := [1, 2, 4, 3, 3, 1, 1, 7]
def baseStart_1115521 : Nat := 118140960795 + 1115521 * 2 ^ 59
def prefixEnd_1115521 : Nat := 4983230072969 + 3 ^ 40 * 1115521 * 2
def baseEnd_1115521 : Nat := 42429515050684092789431

theorem tailTrace_1115521 : CollatzResearch.WordTrace tailWord_1115521 prefixEnd_1115521 42429515050684092789431 := by
  unfold tailWord_1115521
  simp only [CollatzResearch.WordTrace]
  refine ⟨40686393391665407664170417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27124262261110271776113611 40686393391665407664170417)
  ·
    refine ⟨30514795043749055748127813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40686393391665407664170417 30514795043749055748127813)
    ·
      refine ⟨5721524070702947952773965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30514795043749055748127813 5721524070702947952773965)
      ·
        refine ⟨2145571526513605482290237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5721524070702947952773965 2145571526513605482290237)
        ·
          refine ⟨804589322442602055858839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2145571526513605482290237 804589322442602055858839)
          ·
            refine ⟨1206883983663903083788259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804589322442602055858839 1206883983663903083788259)
            ·
              refine ⟨1810325975495854625682389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206883983663903083788259 1810325975495854625682389)
              ·
                refine ⟨42429515050684092789431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1810325975495854625682389 42429515050684092789431)
                ·
                  rfl

theorem cell22_1115521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 7].length) (baseStart_1115521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115521 prefixEnd_1115521 := by exact prefixLift 1115521
  have htrace : WordTrace (prefixWord ++ tailWord_1115521) baseStart_1115521 baseEnd_1115521 := by
    simpa [prefixWord, tailWord_1115521, baseEnd_1115521] using wordTrace_append hprefix tailTrace_1115521
  have hstable : (prefixWord ++ tailWord_1115521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115521).length < 2 ^ (prefixWord ++ tailWord_1115521).sum := by decide
  have hdescent : baseEnd_1115521 < baseStart_1115521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115532 : List Nat := [2, 2, 1, 2, 1, 3, 1, 5, 5]
def baseStart_1115532 : Nat := 118140960795 + 1115532 * 2 ^ 59
def prefixEnd_1115532 : Nat := 4983230072969 + 3 ^ 40 * 1115532 * 2
def baseEnd_1115532 : Nat := 127289800326985491026615

theorem tailTrace_1115532 : CollatzResearch.WordTrace tailWord_1115532 prefixEnd_1115532 127289800326985491026615 := by
  unfold tailWord_1115532
  simp only [CollatzResearch.WordTrace]
  refine ⟨20343397297312778271410425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27124529729750371028547233 20343397297312778271410425)
  ·
    refine ⟨15257547972984583703557819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20343397297312778271410425 15257547972984583703557819)
    ·
      refine ⟨22886321959476875555336729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15257547972984583703557819 22886321959476875555336729)
      ·
        refine ⟨17164741469607656666502547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22886321959476875555336729 17164741469607656666502547)
        ·
          refine ⟨25747112204411484999753821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17164741469607656666502547 25747112204411484999753821)
          ·
            refine ⟨9655167076654306874907683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25747112204411484999753821 9655167076654306874907683)
            ·
              refine ⟨14482750614981460312361525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9655167076654306874907683 14482750614981460312361525)
              ·
                refine ⟨1357757870154511904283893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14482750614981460312361525 1357757870154511904283893)
                ·
                  refine ⟨127289800326985491026615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1357757870154511904283893 127289800326985491026615)
                  ·
                    rfl

theorem cell22_1115532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_1115532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115532 prefixEnd_1115532 := by exact prefixLift 1115532
  have htrace : WordTrace (prefixWord ++ tailWord_1115532) baseStart_1115532 baseEnd_1115532 := by
    simpa [prefixWord, tailWord_1115532, baseEnd_1115532] using wordTrace_append hprefix tailTrace_1115532
  have hstable : (prefixWord ++ tailWord_1115532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115532).length < 2 ^ (prefixWord ++ tailWord_1115532).sum := by decide
  have hdescent : baseEnd_1115532 < baseStart_1115532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115596 : List Nat := [2, 2, 1, 4, 2, 2, 2, 2, 1, 4]
def baseStart_1115596 : Nat := 118140960795 + 1115596 * 2 ^ 59
def prefixEnd_1115596 : Nat := 4983230072969 + 3 ^ 40 * 1115596 * 2
def baseEnd_1115596 : Nat := 381891309488881639479649

theorem tailTrace_1115596 : CollatzResearch.WordTrace tailWord_1115596 prefixEnd_1115596 381891309488881639479649 := by
  unfold tailWord_1115596
  simp only [CollatzResearch.WordTrace]
  refine ⟨20344564433196847736575321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27126085910929130315433761 20344564433196847736575321)
  ·
    refine ⟨15258423324897635802431491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20344564433196847736575321 15258423324897635802431491)
    ·
      refine ⟨22887634987346453703647237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15258423324897635802431491 22887634987346453703647237)
      ·
        refine ⟨4291431560127460069433857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22887634987346453703647237 4291431560127460069433857)
        ·
          refine ⟨3218573670095595052075393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4291431560127460069433857 3218573670095595052075393)
          ·
            refine ⟨2413930252571696289056545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3218573670095595052075393 2413930252571696289056545)
            ·
              refine ⟨1810447689428772216792409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2413930252571696289056545 1810447689428772216792409)
              ·
                refine ⟨1357835767071579162594307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1810447689428772216792409 1357835767071579162594307)
                ·
                  refine ⟨2036753650607368743891461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1357835767071579162594307 2036753650607368743891461)
                  ·
                    refine ⟨381891309488881639479649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2036753650607368743891461 381891309488881639479649)
                    ·
                      rfl

theorem cell22_1115596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_1115596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115596 prefixEnd_1115596 := by exact prefixLift 1115596
  have htrace : WordTrace (prefixWord ++ tailWord_1115596) baseStart_1115596 baseEnd_1115596 := by
    simpa [prefixWord, tailWord_1115596, baseEnd_1115596] using wordTrace_append hprefix tailTrace_1115596
  have hstable : (prefixWord ++ tailWord_1115596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115596).length < 2 ^ (prefixWord ++ tailWord_1115596).sum := by decide
  have hdescent : baseEnd_1115596 < baseStart_1115596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115607 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 6, 4]
def baseStart_1115607 : Nat := 118140960795 + 1115607 * 2 ^ 59
def prefixEnd_1115607 : Nat := 4983230072969 + 3 ^ 40 * 1115607 * 2
def baseEnd_1115607 : Nat := 381895075013681277454615

theorem tailTrace_1115607 : CollatzResearch.WordTrace tailWord_1115607 prefixEnd_1115607 381895075013681277454615 := by
  unfold tailWord_1115607
  simp only [CollatzResearch.WordTrace]
  refine ⟨40689530069353844351801075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27126353379569229567867383 40689530069353844351801075)
  ·
    refine ⟨61034295104030766527701613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40689530069353844351801075 61034295104030766527701613)
    ·
      refine ⟨22887860664011537447888105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61034295104030766527701613 22887860664011537447888105)
      ·
        refine ⟨17165895498008653085916079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22887860664011537447888105 17165895498008653085916079)
        ·
          refine ⟨25748843247012979628874119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17165895498008653085916079 25748843247012979628874119)
          ·
            refine ⟨38623264870519469443311179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25748843247012979628874119 38623264870519469443311179)
            ·
              refine ⟨57934897305779204164966769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38623264870519469443311179 57934897305779204164966769)
              ·
                refine ⟨43451172979334403123725077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57934897305779204164966769 43451172979334403123725077)
                ·
                  refine ⟨2036773733406300146424613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43451172979334403123725077 2036773733406300146424613)
                  ·
                    refine ⟨381895075013681277454615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2036773733406300146424613 381895075013681277454615)
                    ·
                      rfl

theorem cell22_1115607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_1115607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115607 prefixEnd_1115607 := by exact prefixLift 1115607
  have htrace : WordTrace (prefixWord ++ tailWord_1115607) baseStart_1115607 baseEnd_1115607 := by
    simpa [prefixWord, tailWord_1115607, baseEnd_1115607] using wordTrace_append hprefix tailTrace_1115607
  have hstable : (prefixWord ++ tailWord_1115607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115607).length < 2 ^ (prefixWord ++ tailWord_1115607).sum := by decide
  have hdescent : baseEnd_1115607 < baseStart_1115607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115609 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 4, 3]
def baseStart_1115609 : Nat := 118140960795 + 1115609 * 2 ^ 59
def prefixEnd_1115609 : Nat := 4983230072969 + 3 ^ 40 * 1115609 * 2
def baseEnd_1115609 : Nat := 381895759654553938904609

theorem tailTrace_1115609 : CollatzResearch.WordTrace tailWord_1115609 prefixEnd_1115609 381895759654553938904609 := by
  unfold tailWord_1115609
  simp only [CollatzResearch.WordTrace]
  refine ⟨40689603015346598693373881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27126402010231065795582587 40689603015346598693373881)
  ·
    refine ⟨30517202261509949020030411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40689603015346598693373881 30517202261509949020030411)
    ·
      refine ⟨45775803392264923530045617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30517202261509949020030411 45775803392264923530045617)
      ·
        refine ⟨34331852544198692647534213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45775803392264923530045617 34331852544198692647534213)
        ·
          refine ⟨6437222352037254871412665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34331852544198692647534213 6437222352037254871412665)
          ·
            refine ⟨4827916764027941153559499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6437222352037254871412665 4827916764027941153559499)
            ·
              refine ⟨7241875146041911730339249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4827916764027941153559499 7241875146041911730339249)
              ·
                refine ⟨5431406359531433797754437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7241875146041911730339249 5431406359531433797754437)
                ·
                  refine ⟨1018388692412143837078957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5431406359531433797754437 1018388692412143837078957)
                  ·
                    refine ⟨381895759654553938904609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1018388692412143837078957 381895759654553938904609)
                    ·
                      rfl

theorem cell22_1115609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 3].length) (baseStart_1115609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115609 prefixEnd_1115609 := by exact prefixLift 1115609
  have htrace : WordTrace (prefixWord ++ tailWord_1115609) baseStart_1115609 baseEnd_1115609 := by
    simpa [prefixWord, tailWord_1115609, baseEnd_1115609] using wordTrace_append hprefix tailTrace_1115609
  have hstable : (prefixWord ++ tailWord_1115609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115609).length < 2 ^ (prefixWord ++ tailWord_1115609).sum := by decide
  have hdescent : baseEnd_1115609 < baseStart_1115609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115624 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1115624 : Nat := 118140960795 + 1115624 * 2 ^ 59
def prefixEnd_1115624 : Nat := 4983230072969 + 3 ^ 40 * 1115624 * 2
def baseEnd_1115624 : Nat := 381900894461098899779563

theorem tailTrace_1115624 : CollatzResearch.WordTrace tailWord_1115624 prefixEnd_1115624 381900894461098899779563 := by
  unfold tailWord_1115624
  simp only [CollatzResearch.WordTrace]
  refine ⟨20345075055146128127584963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27126766740194837503446617 20345075055146128127584963)
  ·
    refine ⟨30517612582719192191377445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20345075055146128127584963 30517612582719192191377445)
    ·
      refine ⟨5722052359259848535883271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30517612582719192191377445 5722052359259848535883271)
      ·
        refine ⟨8583078538889772803824907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5722052359259848535883271 8583078538889772803824907)
        ·
          refine ⟨12874617808334659205737361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8583078538889772803824907 12874617808334659205737361)
          ·
            refine ⟨9655963356250994404303021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12874617808334659205737361 9655963356250994404303021)
            ·
              refine ⟨3620986258594122901613633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9655963356250994404303021 3620986258594122901613633)
              ·
                refine ⟨2715739693945592176210225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3620986258594122901613633 2715739693945592176210225)
                ·
                  refine ⟨2036804770459194132157669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2715739693945592176210225 2036804770459194132157669)
                  ·
                    refine ⟨381900894461098899779563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2036804770459194132157669 381900894461098899779563)
                    ·
                      rfl

theorem cell22_1115624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1115624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115624 prefixEnd_1115624 := by exact prefixLift 1115624
  have htrace : WordTrace (prefixWord ++ tailWord_1115624) baseStart_1115624 baseEnd_1115624 := by
    simpa [prefixWord, tailWord_1115624, baseEnd_1115624] using wordTrace_append hprefix tailTrace_1115624
  have hstable : (prefixWord ++ tailWord_1115624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115624).length < 2 ^ (prefixWord ++ tailWord_1115624).sum := by decide
  have hdescent : baseEnd_1115624 < baseStart_1115624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115699 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 2, 5]
def baseStart_1115699 : Nat := 118140960795 + 1115699 * 2 ^ 59
def prefixEnd_1115699 : Nat := 4983230072969 + 3 ^ 40 * 1115699 * 2
def baseEnd_1115699 : Nat := 381926568493823704154333

theorem tailTrace_1115699 : CollatzResearch.WordTrace tailWord_1115699 prefixEnd_1115699 381926568493823704154333 := by
  unfold tailWord_1115699
  simp only [CollatzResearch.WordTrace]
  refine ⟨40692885585020544064150151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27128590390013696042766767 40692885585020544064150151)
  ·
    refine ⟨61039328377530816096225227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40692885585020544064150151 61039328377530816096225227)
    ·
      refine ⟨91558992566296224144337841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61039328377530816096225227 91558992566296224144337841)
      ·
        refine ⟨68669244424722168108253381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91558992566296224144337841 68669244424722168108253381)
        ·
          refine ⟨12875483329635406520297509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68669244424722168108253381 12875483329635406520297509)
          ·
            refine ⟨2414153124306638722555783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12875483329635406520297509 2414153124306638722555783)
            ·
              refine ⟨3621229686459958083833675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2414153124306638722555783 3621229686459958083833675)
              ·
                refine ⟨5431844529689937125750513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3621229686459958083833675 5431844529689937125750513)
                ·
                  refine ⟨4073883397267452844312885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5431844529689937125750513 4073883397267452844312885)
                  ·
                    refine ⟨381926568493823704154333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4073883397267452844312885 381926568493823704154333)
                    ·
                      rfl

theorem cell22_1115699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 5].length) (baseStart_1115699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115699 prefixEnd_1115699 := by exact prefixLift 1115699
  have htrace : WordTrace (prefixWord ++ tailWord_1115699) baseStart_1115699 baseEnd_1115699 := by
    simpa [prefixWord, tailWord_1115699, baseEnd_1115699] using wordTrace_append hprefix tailTrace_1115699
  have hstable : (prefixWord ++ tailWord_1115699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115699).length < 2 ^ (prefixWord ++ tailWord_1115699).sum := by decide
  have hdescent : baseEnd_1115699 < baseStart_1115699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115761 : List Nat := [1, 2, 2, 2, 1, 1, 1, 7, 2, 3]
def baseStart_1115761 : Nat := 118140960795 + 1115761 * 2 ^ 59
def prefixEnd_1115761 : Nat := 4983230072969 + 3 ^ 40 * 1115761 * 2
def baseEnd_1115761 : Nat := 381947792360876209104143

theorem tailTrace_1115761 : CollatzResearch.WordTrace tailWord_1115761 prefixEnd_1115761 381947792360876209104143 := by
  unfold tailWord_1115761
  simp only [CollatzResearch.WordTrace]
  refine ⟨40695146910795928652907137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27130097940530619101938091 40695146910795928652907137)
  ·
    refine ⟨30521360183096946489680353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40695146910795928652907137 30521360183096946489680353)
    ·
      refine ⟨22891020137322709867260265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30521360183096946489680353 22891020137322709867260265)
      ·
        refine ⟨17168265102992032400445199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22891020137322709867260265 17168265102992032400445199)
        ·
          refine ⟨25752397654488048600667799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17168265102992032400445199 25752397654488048600667799)
          ·
            refine ⟨38628596481732072901001699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25752397654488048600667799 38628596481732072901001699)
            ·
              refine ⟨57942894722598109351502549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38628596481732072901001699 57942894722598109351502549)
              ·
                refine ⟨1358036595060893187925841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 57942894722598109351502549 1358036595060893187925841)
                ·
                  refine ⟨1018527446295669890944381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1358036595060893187925841 1018527446295669890944381)
                  ·
                    refine ⟨381947792360876209104143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1018527446295669890944381 381947792360876209104143)
                    ·
                      rfl

theorem cell22_1115761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_1115761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115761 prefixEnd_1115761 := by exact prefixLift 1115761
  have htrace : WordTrace (prefixWord ++ tailWord_1115761) baseStart_1115761 baseEnd_1115761 := by
    simpa [prefixWord, tailWord_1115761, baseEnd_1115761] using wordTrace_append hprefix tailTrace_1115761
  have hstable : (prefixWord ++ tailWord_1115761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115761).length < 2 ^ (prefixWord ++ tailWord_1115761).sum := by decide
  have hdescent : baseEnd_1115761 < baseStart_1115761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115780 : List Nat := [2, 3, 2, 1, 4, 2, 1, 3, 4]
def baseStart_1115780 : Nat := 118140960795 + 1115780 * 2 ^ 59
def prefixEnd_1115780 : Nat := 4983230072969 + 3 ^ 40 * 1115780 * 2
def baseEnd_1115780 : Nat := 127318098816388830959695

theorem tailTrace_1115780 : CollatzResearch.WordTrace tailWord_1115780 prefixEnd_1115780 127318098816388830959695 := by
  unfold tailWord_1115780
  simp only [CollatzResearch.WordTrace]
  refine ⟨20347919948863547448924397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27130559931818063265232529 20347919948863547448924397)
  ·
    refine ⟨7630469980823830293346649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20347919948863547448924397 7630469980823830293346649)
    ·
      refine ⟨5722852485617872720009987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7630469980823830293346649 5722852485617872720009987)
      ·
        refine ⟨8584278728426809080014981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5722852485617872720009987 8584278728426809080014981)
        ·
          refine ⟨1609552261580026702502809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8584278728426809080014981 1609552261580026702502809)
          ·
            refine ⟨1207164196185020026877107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1609552261580026702502809 1207164196185020026877107)
            ·
              refine ⟨1810746294277530040315661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207164196185020026877107 1810746294277530040315661)
              ·
                refine ⟨679029860354073765118373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1810746294277530040315661 679029860354073765118373)
                ·
                  refine ⟨127318098816388830959695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 679029860354073765118373 127318098816388830959695)
                  ·
                    rfl

theorem cell22_1115780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_1115780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115780 prefixEnd_1115780 := by exact prefixLift 1115780
  have htrace : WordTrace (prefixWord ++ tailWord_1115780) baseStart_1115780 baseEnd_1115780 := by
    simpa [prefixWord, tailWord_1115780, baseEnd_1115780] using wordTrace_append hprefix tailTrace_1115780
  have hstable : (prefixWord ++ tailWord_1115780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115780).length < 2 ^ (prefixWord ++ tailWord_1115780).sum := by decide
  have hdescent : baseEnd_1115780 < baseStart_1115780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115857 : List Nat := [1, 2, 2, 1, 2, 6, 2, 2, 1, 3]
def baseStart_1115857 : Nat := 118140960795 + 1115857 * 2 ^ 59
def prefixEnd_1115857 : Nat := 4983230072969 + 3 ^ 40 * 1115857 * 2
def baseEnd_1115857 : Nat := 381980655122763958703849

theorem tailTrace_1115857 : CollatzResearch.WordTrace tailWord_1115857 prefixEnd_1115857 381980655122763958703849 := by
  unfold tailWord_1115857
  simp only [CollatzResearch.WordTrace]
  refine ⟨40698648318448137048401825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27132432212298758032267883 40698648318448137048401825)
  ·
    refine ⟨30523986238836102786301369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40698648318448137048401825 30523986238836102786301369)
    ·
      refine ⟨22892989679127077089726027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30523986238836102786301369 22892989679127077089726027)
      ·
        refine ⟨34339484518690615634589041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22892989679127077089726027 34339484518690615634589041)
        ·
          refine ⟨25754613389017961725941781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34339484518690615634589041 25754613389017961725941781)
          ·
            refine ⟨1207247502610216955903521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25754613389017961725941781 1207247502610216955903521)
            ·
              refine ⟨905435626957662716927641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1207247502610216955903521 905435626957662716927641)
              ·
                refine ⟨679076720218247037695731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 905435626957662716927641 679076720218247037695731)
                ·
                  refine ⟨1018615080327370556543597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679076720218247037695731 1018615080327370556543597)
                  ·
                    refine ⟨381980655122763958703849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1018615080327370556543597 381980655122763958703849)
                    ·
                      rfl

theorem cell22_1115857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_1115857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115857 prefixEnd_1115857 := by exact prefixLift 1115857
  have htrace : WordTrace (prefixWord ++ tailWord_1115857) baseStart_1115857 baseEnd_1115857 := by
    simpa [prefixWord, tailWord_1115857, baseEnd_1115857] using wordTrace_append hprefix tailTrace_1115857
  have hstable : (prefixWord ++ tailWord_1115857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115857).length < 2 ^ (prefixWord ++ tailWord_1115857).sum := by decide
  have hdescent : baseEnd_1115857 < baseStart_1115857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115866 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_1115866 : Nat := 118140960795 + 1115866 * 2 ^ 59
def prefixEnd_1115866 : Nat := 4983230072969 + 3 ^ 40 * 1115866 * 2
def baseEnd_1115866 : Nat := 381983736006690935228821

theorem tailTrace_1115866 : CollatzResearch.WordTrace tailWord_1115866 prefixEnd_1115866 381983736006690935228821 := by
  unfold tailWord_1115866
  simp only [CollatzResearch.WordTrace]
  refine ⟨10174744143853882896369863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27132651050277021056986301 10174744143853882896369863)
  ·
    refine ⟨15262116215780824344554795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10174744143853882896369863 15262116215780824344554795)
    ·
      refine ⟨22893174323671236516832193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15262116215780824344554795 22893174323671236516832193)
      ·
        refine ⟨17169880742753427387624145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22893174323671236516832193 17169880742753427387624145)
        ·
          refine ⟨12877410557065070540718109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17169880742753427387624145 12877410557065070540718109)
          ·
            refine ⟨4829028958899401452769291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12877410557065070540718109 4829028958899401452769291)
            ·
              refine ⟨7243543438349102179153937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4829028958899401452769291 7243543438349102179153937)
              ·
                refine ⟨5432657578761826634365453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7243543438349102179153937 5432657578761826634365453)
                ·
                  refine ⟨2037246592035684987887045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5432657578761826634365453 2037246592035684987887045)
                  ·
                    refine ⟨381983736006690935228821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2037246592035684987887045 381983736006690935228821)
                    ·
                      rfl

theorem cell22_1115866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_1115866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115866 prefixEnd_1115866 := by exact prefixLift 1115866
  have htrace : WordTrace (prefixWord ++ tailWord_1115866) baseStart_1115866 baseEnd_1115866 := by
    simpa [prefixWord, tailWord_1115866, baseEnd_1115866] using wordTrace_append hprefix tailTrace_1115866
  have hstable : (prefixWord ++ tailWord_1115866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115866).length < 2 ^ (prefixWord ++ tailWord_1115866).sum := by decide
  have hdescent : baseEnd_1115866 < baseStart_1115866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115934 : List Nat := [4, 3, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1115934 : Nat := 118140960795 + 1115934 * 2 ^ 59
def prefixEnd_1115934 : Nat := 4983230072969 + 3 ^ 40 * 1115934 * 2
def baseEnd_1115934 : Nat := 382007013796361424528613

theorem tailTrace_1115934 : CollatzResearch.WordTrace tailWord_1115934 prefixEnd_1115934 382007013796361424528613 := by
  unfold tailWord_1115934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5087682092396147399869357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27134304492779452799303237 5087682092396147399869357)
  ·
    refine ⟨1907880784648555274951009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5087682092396147399869357 1907880784648555274951009)
    ·
      refine ⟨1430910588486416456213257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1907880784648555274951009 1430910588486416456213257)
      ·
        refine ⟨1073182941364812342159943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1430910588486416456213257 1073182941364812342159943)
        ·
          refine ⟨1609774412047218513239915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1073182941364812342159943 1609774412047218513239915)
          ·
            refine ⟨2414661618070827769859873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1609774412047218513239915 2414661618070827769859873)
            ·
              refine ⟨1810996213553120827394905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2414661618070827769859873 1810996213553120827394905)
              ·
                refine ⟨1358247160164840620546179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1810996213553120827394905 1358247160164840620546179)
                ·
                  refine ⟨2037370740247260930819269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358247160164840620546179 2037370740247260930819269)
                  ·
                    refine ⟨382007013796361424528613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2037370740247260930819269 382007013796361424528613)
                    ·
                      rfl

theorem cell22_1115934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1115934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115934 prefixEnd_1115934 := by exact prefixLift 1115934
  have htrace : WordTrace (prefixWord ++ tailWord_1115934) baseStart_1115934 baseEnd_1115934 := by
    simpa [prefixWord, tailWord_1115934, baseEnd_1115934] using wordTrace_append hprefix tailTrace_1115934
  have hstable : (prefixWord ++ tailWord_1115934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115934).length < 2 ^ (prefixWord ++ tailWord_1115934).sum := by decide
  have hdescent : baseEnd_1115934 < baseStart_1115934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115971 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 7]
def baseStart_1115971 : Nat := 118140960795 + 1115971 * 2 ^ 59
def prefixEnd_1115971 : Nat := 4983230072969 + 3 ^ 40 * 1115971 * 2
def baseEnd_1115971 : Nat := 127339893217501887117833

theorem tailTrace_1115971 : CollatzResearch.WordTrace tailWord_1115971 prefixEnd_1115971 127339893217501887117833 := by
  unfold tailWord_1115971
  simp only [CollatzResearch.WordTrace]
  refine ⟨40702806240035134518051767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27135204160023423012034511 40702806240035134518051767)
  ·
    refine ⟨61054209360052701777077651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40702806240035134518051767 61054209360052701777077651)
    ·
      refine ⟨91581314040079052665616477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61054209360052701777077651 91581314040079052665616477)
      ·
        refine ⟨34342992765029644749606179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91581314040079052665616477 34342992765029644749606179)
        ·
          refine ⟨51514489147544467124409269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34342992765029644749606179 51514489147544467124409269)
          ·
            refine ⟨4829483357582293792913369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51514489147544467124409269 4829483357582293792913369)
            ·
              refine ⟨3622112518186720344685027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4829483357582293792913369 3622112518186720344685027)
              ·
                refine ⟨5433168777280080517027541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3622112518186720344685027 5433168777280080517027541)
                ·
                  refine ⟨127339893217501887117833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5433168777280080517027541 127339893217501887117833)
                  ·
                    rfl

theorem cell22_1115971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 7].length) (baseStart_1115971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115971 prefixEnd_1115971 := by exact prefixLift 1115971
  have htrace : WordTrace (prefixWord ++ tailWord_1115971) baseStart_1115971 baseEnd_1115971 := by
    simpa [prefixWord, tailWord_1115971, baseEnd_1115971] using wordTrace_append hprefix tailTrace_1115971
  have hstable : (prefixWord ++ tailWord_1115971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115971).length < 2 ^ (prefixWord ++ tailWord_1115971).sum := by decide
  have hdescent : baseEnd_1115971 < baseStart_1115971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1115975 : List Nat := [1, 1, 4, 1, 2, 1, 2, 6, 1, 3]
def baseStart_1115975 : Nat := 118140960795 + 1115975 * 2 ^ 59
def prefixEnd_1115975 : Nat := 4983230072969 + 3 ^ 40 * 1115975 * 2
def baseEnd_1115975 : Nat := 382021048934250984253487

theorem tailTrace_1115975 : CollatzResearch.WordTrace tailWord_1115975 prefixEnd_1115975 382021048934250984253487 := by
  unfold tailWord_1115975
  simp only [CollatzResearch.WordTrace]
  refine ⟨40702952132020643201197379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27135301421347095467464919 40702952132020643201197379)
  ·
    refine ⟨61054428198030964801796069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40702952132020643201197379 61054428198030964801796069)
    ·
      refine ⟨11447705287130805900336763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61054428198030964801796069 11447705287130805900336763)
      ·
        refine ⟨17171557930696208850505145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11447705287130805900336763 17171557930696208850505145)
        ·
          refine ⟨12878668448022156637878859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17171557930696208850505145 12878668448022156637878859)
          ·
            refine ⟨19318002672033234956818289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12878668448022156637878859 19318002672033234956818289)
            ·
              refine ⟨14488502004024926217613717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19318002672033234956818289 14488502004024926217613717)
              ·
                refine ⟨679148531438668416450643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14488502004024926217613717 679148531438668416450643)
                ·
                  refine ⟨1018722797158002624675965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679148531438668416450643 1018722797158002624675965)
                  ·
                    refine ⟨382021048934250984253487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1018722797158002624675965 382021048934250984253487)
                    ·
                      rfl

theorem cell22_1115975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_1115975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1115975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1115975 prefixEnd_1115975 := by exact prefixLift 1115975
  have htrace : WordTrace (prefixWord ++ tailWord_1115975) baseStart_1115975 baseEnd_1115975 := by
    simpa [prefixWord, tailWord_1115975, baseEnd_1115975] using wordTrace_append hprefix tailTrace_1115975
  have hstable : (prefixWord ++ tailWord_1115975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1115975).length < 2 ^ (prefixWord ++ tailWord_1115975).sum := by decide
  have hdescent : baseEnd_1115975 < baseStart_1115975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1115975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116022 : List Nat := [5, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_1116022 : Nat := 118140960795 + 1116022 * 2 ^ 59
def prefixEnd_1116022 : Nat := 4983230072969 + 3 ^ 40 * 1116022 * 2
def baseEnd_1116022 : Nat := 127345712664919509442781

theorem tailTrace_1116022 : CollatzResearch.WordTrace tailWord_1116022 prefixEnd_1116022 127345712664919509442781 := by
  unfold tailWord_1116022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2544041647678148139259895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27136444241900246818772213 2544041647678148139259895)
  ·
    refine ⟨3816062471517222208889843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2544041647678148139259895 3816062471517222208889843)
    ·
      refine ⟨5724093707275833313334765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3816062471517222208889843 5724093707275833313334765)
      ·
        refine ⟨2146535140228437492500537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5724093707275833313334765 2146535140228437492500537)
        ·
          refine ⟨1609901355171328119375403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2146535140228437492500537 1609901355171328119375403)
          ·
            refine ⟨2414852032756992179063105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1609901355171328119375403 2414852032756992179063105)
            ·
              refine ⟨1811139024567744134297329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2414852032756992179063105 1811139024567744134297329)
              ·
                refine ⟨1358354268425808100722997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1811139024567744134297329 1358354268425808100722997)
                ·
                  refine ⟨127345712664919509442781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1358354268425808100722997 127345712664919509442781)
                  ·
                    rfl

theorem cell22_1116022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_1116022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116022 prefixEnd_1116022 := by exact prefixLift 1116022
  have htrace : WordTrace (prefixWord ++ tailWord_1116022) baseStart_1116022 baseEnd_1116022 := by
    simpa [prefixWord, tailWord_1116022, baseEnd_1116022] using wordTrace_append hprefix tailTrace_1116022
  have hstable : (prefixWord ++ tailWord_1116022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116022).length < 2 ^ (prefixWord ++ tailWord_1116022).sum := by decide
  have hdescent : baseEnd_1116022 < baseStart_1116022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116031 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 5, 5]
def baseStart_1116031 : Nat := 118140960795 + 1116031 * 2 ^ 59
def prefixEnd_1116031 : Nat := 4983230072969 + 3 ^ 40 * 1116031 * 2
def baseEnd_1116031 : Nat := 382040218878685504853315

theorem tailTrace_1116031 : CollatzResearch.WordTrace tailWord_1116031 prefixEnd_1116031 382040218878685504853315 := by
  unfold tailWord_1116031
  simp only [CollatzResearch.WordTrace]
  refine ⟨40704994619817764765235947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27136663079878509843490631 40704994619817764765235947)
  ·
    refine ⟨61057491929726647147853921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40704994619817764765235947 61057491929726647147853921)
    ·
      refine ⟨45793118947294985360890441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61057491929726647147853921 45793118947294985360890441)
      ·
        refine ⟨34344839210471239020667831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45793118947294985360890441 34344839210471239020667831)
        ·
          refine ⟨51517258815706858531001747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34344839210471239020667831 51517258815706858531001747)
          ·
            refine ⟨77275888223560287796502621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51517258815706858531001747 77275888223560287796502621)
            ·
              refine ⟨28978458083835107923688483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77275888223560287796502621 28978458083835107923688483)
              ·
                refine ⟨43467687125752661885532725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28978458083835107923688483 43467687125752661885532725)
                ·
                  refine ⟨4075095668039312051768693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43467687125752661885532725 4075095668039312051768693)
                  ·
                    refine ⟨382040218878685504853315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4075095668039312051768693 382040218878685504853315)
                    ·
                      rfl

theorem cell22_1116031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_1116031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116031 prefixEnd_1116031 := by exact prefixLift 1116031
  have htrace : WordTrace (prefixWord ++ tailWord_1116031) baseStart_1116031 baseEnd_1116031 := by
    simpa [prefixWord, tailWord_1116031, baseEnd_1116031] using wordTrace_append hprefix tailTrace_1116031
  have hstable : (prefixWord ++ tailWord_1116031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116031).length < 2 ^ (prefixWord ++ tailWord_1116031).sum := by decide
  have hdescent : baseEnd_1116031 < baseStart_1116031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116050 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 6]
def baseStart_1116050 : Nat := 118140960795 + 1116050 * 2 ^ 59
def prefixEnd_1116050 : Nat := 4983230072969 + 3 ^ 40 * 1116050 * 2
def baseEnd_1116050 : Nat := 127348907655658596209419

theorem tailTrace_1116050 : CollatzResearch.WordTrace tailWord_1116050 prefixEnd_1116050 127348907655658596209419 := by
  unfold tailWord_1116050
  simp only [CollatzResearch.WordTrace]
  refine ⟨10176421901687232752544401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27137125071165954006785069 10176421901687232752544401)
  ·
    refine ⟨7632316426265424564408301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10176421901687232752544401 7632316426265424564408301)
    ·
      refine ⟨2862118659849534211653113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7632316426265424564408301 2862118659849534211653113)
      ·
        refine ⟨2146588994887150658739835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2862118659849534211653113 2146588994887150658739835)
        ·
          refine ⟨3219883492330725988109753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2146588994887150658739835 3219883492330725988109753)
          ·
            refine ⟨2414912619248044491082315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3219883492330725988109753 2414912619248044491082315)
            ·
              refine ⟨3622368928872066736623473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2414912619248044491082315 3622368928872066736623473)
              ·
                refine ⟨2716776696654050052467605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3622368928872066736623473 2716776696654050052467605)
                ·
                  refine ⟨127348907655658596209419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2716776696654050052467605 127348907655658596209419)
                  ·
                    rfl

theorem cell22_1116050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_1116050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116050 prefixEnd_1116050 := by exact prefixLift 1116050
  have htrace : WordTrace (prefixWord ++ tailWord_1116050) baseStart_1116050 baseEnd_1116050 := by
    simpa [prefixWord, tailWord_1116050, baseEnd_1116050] using wordTrace_append hprefix tailTrace_1116050
  have hstable : (prefixWord ++ tailWord_1116050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116050).length < 2 ^ (prefixWord ++ tailWord_1116050).sum := by decide
  have hdescent : baseEnd_1116050 < baseStart_1116050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116110 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_1116110 : Nat := 118140960795 + 1116110 * 2 ^ 59
def prefixEnd_1116110 : Nat := 4983230072969 + 3 ^ 40 * 1116110 * 2
def baseEnd_1116110 : Nat := 382067262193155632128073

theorem tailTrace_1116110 : CollatzResearch.WordTrace tailWord_1116110 prefixEnd_1116110 382067262193155632128073 := by
  unfold tailWord_1116110
  simp only [CollatzResearch.WordTrace]
  refine ⟨5088484498316445157170223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27138583991021040838241189 5088484498316445157170223)
  ·
    refine ⟨7632726747474667735755335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5088484498316445157170223 7632726747474667735755335)
    ·
      refine ⟨11449090121212001603633003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7632726747474667735755335 11449090121212001603633003)
      ·
        refine ⟨17173635181818002405449505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11449090121212001603633003 17173635181818002405449505)
        ·
          refine ⟨12880226386363501804087129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17173635181818002405449505 12880226386363501804087129)
          ·
            refine ⟨9660169789772626353065347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12880226386363501804087129 9660169789772626353065347)
            ·
              refine ⟨14490254684658939529598021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9660169789772626353065347 14490254684658939529598021)
              ·
                refine ⟨2716922753373551161799629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14490254684658939529598021 2716922753373551161799629)
                ·
                  refine ⟨1018846032515081685674861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2716922753373551161799629 1018846032515081685674861)
                  ·
                    refine ⟨382067262193155632128073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1018846032515081685674861 382067262193155632128073)
                    ·
                      rfl

theorem cell22_1116110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_1116110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116110 prefixEnd_1116110 := by exact prefixLift 1116110
  have htrace : WordTrace (prefixWord ++ tailWord_1116110) baseStart_1116110 baseEnd_1116110 := by
    simpa [prefixWord, tailWord_1116110, baseEnd_1116110] using wordTrace_append hprefix tailTrace_1116110
  have hstable : (prefixWord ++ tailWord_1116110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116110).length < 2 ^ (prefixWord ++ tailWord_1116110).sum := by decide
  have hdescent : baseEnd_1116110 < baseStart_1116110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116168 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 8]
def baseStart_1116168 : Nat := 118140960795 + 1116168 * 2 ^ 59
def prefixEnd_1116168 : Nat := 4983230072969 + 3 ^ 40 * 1116168 * 2
def baseEnd_1116168 : Nat := 127362372259487604725965

theorem tailTrace_1116168 : CollatzResearch.WordTrace tailWord_1116168 prefixEnd_1116168 127362372259487604725965 := by
  unfold tailWord_1116168
  simp only [CollatzResearch.WordTrace]
  refine ⟨20354995710160718581486579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27139994280214291441982105 20354995710160718581486579)
  ·
    refine ⟨30532493565241077872229869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20354995710160718581486579 30532493565241077872229869)
    ·
      refine ⟨11449685086965404202086201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30532493565241077872229869 11449685086965404202086201)
      ·
        refine ⟨8587263815224053151564651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11449685086965404202086201 8587263815224053151564651)
        ·
          refine ⟨12880895722836079727346977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8587263815224053151564651 12880895722836079727346977)
          ·
            refine ⟨9660671792127059795510233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12880895722836079727346977 9660671792127059795510233)
            ·
              refine ⟨7245503844095294846632675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9660671792127059795510233 7245503844095294846632675)
              ·
                refine ⟨10868255766142942269949013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7245503844095294846632675 10868255766142942269949013)
                ·
                  refine ⟨127362372259487604725965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10868255766142942269949013 127362372259487604725965)
                  ·
                    rfl

theorem cell22_1116168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_1116168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116168 prefixEnd_1116168 := by exact prefixLift 1116168
  have htrace : WordTrace (prefixWord ++ tailWord_1116168) baseStart_1116168 baseEnd_1116168 := by
    simpa [prefixWord, tailWord_1116168, baseEnd_1116168] using wordTrace_append hprefix tailTrace_1116168
  have hstable : (prefixWord ++ tailWord_1116168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116168).length < 2 ^ (prefixWord ++ tailWord_1116168).sum := by decide
  have hdescent : baseEnd_1116168 < baseStart_1116168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116185 : List Nat := [1, 2, 1, 2, 1, 1, 3, 7, 4]
def baseStart_1116185 : Nat := 118140960795 + 1116185 * 2 ^ 59
def prefixEnd_1116185 : Nat := 4983230072969 + 3 ^ 40 * 1116185 * 2
def baseEnd_1116185 : Nat := 127364312075293478834281

theorem tailTrace_1116185 : CollatzResearch.WordTrace tailWord_1116185 prefixEnd_1116185 127364312075293478834281 := by
  unfold tailWord_1116185
  simp only [CollatzResearch.WordTrace]
  refine ⟨40710611461259849066342009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27140407640839899377561339 40710611461259849066342009)
  ·
    refine ⟨30532958595944886799756507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40710611461259849066342009 30532958595944886799756507)
    ·
      refine ⟨45799437893917330199634761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30532958595944886799756507 45799437893917330199634761)
      ·
        refine ⟨34349578420437997649726071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45799437893917330199634761 34349578420437997649726071)
        ·
          refine ⟨51524367630656996474589107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34349578420437997649726071 51524367630656996474589107)
          ·
            refine ⟨77286551445985494711883661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51524367630656996474589107 77286551445985494711883661)
            ·
              refine ⟨28982456792244560516956373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77286551445985494711883661 28982456792244560516956373)
              ·
                refine ⟨679276331068231887116165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28982456792244560516956373 679276331068231887116165)
                ·
                  refine ⟨127364312075293478834281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 679276331068231887116165 127364312075293478834281)
                  ·
                    rfl

theorem cell22_1116185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 4].length) (baseStart_1116185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116185 prefixEnd_1116185 := by exact prefixLift 1116185
  have htrace : WordTrace (prefixWord ++ tailWord_1116185) baseStart_1116185 baseEnd_1116185 := by
    simpa [prefixWord, tailWord_1116185, baseEnd_1116185] using wordTrace_append hprefix tailTrace_1116185
  have hstable : (prefixWord ++ tailWord_1116185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116185).length < 2 ^ (prefixWord ++ tailWord_1116185).sum := by decide
  have hdescent : baseEnd_1116185 < baseStart_1116185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116217 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 1, 5]
def baseStart_1116217 : Nat := 118140960795 + 1116217 * 2 ^ 59
def prefixEnd_1116217 : Nat := 4983230072969 + 3 ^ 40 * 1116217 * 2
def baseEnd_1116217 : Nat := 382103890479843019702745

theorem tailTrace_1116217 : CollatzResearch.WordTrace tailWord_1116217 prefixEnd_1116217 382103890479843019702745 := by
  unfold tailWord_1116217
  simp only [CollatzResearch.WordTrace]
  refine ⟨40711778597143918531506905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27141185731429279021004603 40711778597143918531506905)
  ·
    refine ⟨30533833947857938898630179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40711778597143918531506905 30533833947857938898630179)
    ·
      refine ⟨45800750921786908347945269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30533833947857938898630179 45800750921786908347945269)
      ·
        refine ⟨4293820398917522657619869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45800750921786908347945269 4293820398917522657619869)
        ·
          refine ⟨1610182649594070996607451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4293820398917522657619869 1610182649594070996607451)
          ·
            refine ⟨2415273974391106494911177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1610182649594070996607451 2415273974391106494911177)
            ·
              refine ⟨1811455480793329871183383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2415273974391106494911177 1811455480793329871183383)
              ·
                refine ⟨2717183221189994806775075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1811455480793329871183383 2717183221189994806775075)
                ·
                  refine ⟨4075774831784992210162613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717183221189994806775075 4075774831784992210162613)
                  ·
                    refine ⟨382103890479843019702745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4075774831784992210162613 382103890479843019702745)
                    ·
                      rfl

theorem cell22_1116217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_1116217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116217 prefixEnd_1116217 := by exact prefixLift 1116217
  have htrace : WordTrace (prefixWord ++ tailWord_1116217) baseStart_1116217 baseEnd_1116217 := by
    simpa [prefixWord, tailWord_1116217, baseEnd_1116217] using wordTrace_append hprefix tailTrace_1116217
  have hstable : (prefixWord ++ tailWord_1116217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116217).length < 2 ^ (prefixWord ++ tailWord_1116217).sum := by decide
  have hdescent : baseEnd_1116217 < baseStart_1116217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116296 : List Nat := [2, 1, 3, 4, 1, 1, 3, 3, 1, 3]
def baseStart_1116296 : Nat := 118140960795 + 1116296 * 2 ^ 59
def prefixEnd_1116296 : Nat := 4983230072969 + 3 ^ 40 * 1116296 * 2
def baseEnd_1116296 : Nat := 382130933794313146977503

theorem tailTrace_1116296 : CollatzResearch.WordTrace tailWord_1116296 prefixEnd_1116296 382130933794313146977503 := by
  unfold tailWord_1116296
  simp only [CollatzResearch.WordTrace]
  refine ⟨20357329981928857511816371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27143106642571810015755161 20357329981928857511816371)
  ·
    refine ⟨30535994972893286267724557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20357329981928857511816371 30535994972893286267724557)
    ·
      refine ⟨11450998114834982350396709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30535994972893286267724557 11450998114834982350396709)
      ·
        refine ⟨2147062146531559190699383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11450998114834982350396709 2147062146531559190699383)
        ·
          refine ⟨3220593219797338786049075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2147062146531559190699383 3220593219797338786049075)
          ·
            refine ⟨4830889829696008179073613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3220593219797338786049075 4830889829696008179073613)
            ·
              refine ⟨1811583686136003067152605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4830889829696008179073613 1811583686136003067152605)
              ·
                refine ⟨679343882301001150182227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1811583686136003067152605 679343882301001150182227)
                ·
                  refine ⟨1019015823451501725273341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679343882301001150182227 1019015823451501725273341)
                  ·
                    refine ⟨382130933794313146977503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1019015823451501725273341 382130933794313146977503)
                    ·
                      rfl

theorem cell22_1116296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_1116296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116296 prefixEnd_1116296 := by exact prefixLift 1116296
  have htrace : WordTrace (prefixWord ++ tailWord_1116296) baseStart_1116296 baseEnd_1116296 := by
    simpa [prefixWord, tailWord_1116296, baseEnd_1116296] using wordTrace_append hprefix tailTrace_1116296
  have hstable : (prefixWord ++ tailWord_1116296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116296).length < 2 ^ (prefixWord ++ tailWord_1116296).sum := by decide
  have hdescent : baseEnd_1116296 < baseStart_1116296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116335 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 1, 5]
def baseStart_1116335 : Nat := 118140960795 + 1116335 * 2 ^ 59
def prefixEnd_1116335 : Nat := 4983230072969 + 3 ^ 40 * 1116335 * 2
def baseEnd_1116335 : Nat := 382144284291330045252383

theorem tailTrace_1116335 : CollatzResearch.WordTrace tailWord_1116335 prefixEnd_1116335 382144284291330045252383 := by
  unfold tailWord_1116335
  simp only [CollatzResearch.WordTrace]
  refine ⟨40716082410716424684302459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27144054940477616456201639 40716082410716424684302459)
  ·
    refine ⟨61074123616074637026453689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40716082410716424684302459 61074123616074637026453689)
    ·
      refine ⟨45805592712055977769840267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61074123616074637026453689 45805592712055977769840267)
      ·
        refine ⟨68708389068083966654760401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45805592712055977769840267 68708389068083966654760401)
        ·
          refine ⟨51531291801062974991070301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68708389068083966654760401 51531291801062974991070301)
          ·
            refine ⟨19324234425398615621651363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51531291801062974991070301 19324234425398615621651363)
            ·
              refine ⟨28986351638097923432477045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19324234425398615621651363 28986351638097923432477045)
              ·
                refine ⟨2717470466071680321794723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28986351638097923432477045 2717470466071680321794723)
                ·
                  refine ⟨4076205699107520482692085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717470466071680321794723 4076205699107520482692085)
                  ·
                    refine ⟨382144284291330045252383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4076205699107520482692085 382144284291330045252383)
                    ·
                      rfl

theorem cell22_1116335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_1116335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116335 prefixEnd_1116335 := by exact prefixLift 1116335
  have htrace : WordTrace (prefixWord ++ tailWord_1116335) baseStart_1116335 baseEnd_1116335 := by
    simpa [prefixWord, tailWord_1116335, baseEnd_1116335] using wordTrace_append hprefix tailTrace_1116335
  have hstable : (prefixWord ++ tailWord_1116335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116335).length < 2 ^ (prefixWord ++ tailWord_1116335).sum := by decide
  have hdescent : baseEnd_1116335 < baseStart_1116335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116352 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 1, 5]
def baseStart_1116352 : Nat := 118140960795 + 1116352 * 2 ^ 59
def prefixEnd_1116352 : Nat := 4983230072969 + 3 ^ 40 * 1116352 * 2
def baseEnd_1116352 : Nat := 382150103738747667577331

theorem tailTrace_1116352 : CollatzResearch.WordTrace tailWord_1116352 prefixEnd_1116352 382150103738747667577331 := by
  unfold tailWord_1116352
  simp only [CollatzResearch.WordTrace]
  refine ⟨20358351225827418293835655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27144468301103224391780873 20358351225827418293835655)
  ·
    refine ⟨30537526838741127440753483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20358351225827418293835655 30537526838741127440753483)
    ·
      refine ⟨45806290258111691161130225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30537526838741127440753483 45806290258111691161130225)
      ·
        refine ⟨34354717693583768370847669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45806290258111691161130225 34354717693583768370847669)
        ·
          refine ⟨3220754783773478284766969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34354717693583768370847669 3220754783773478284766969)
          ·
            refine ⟨2415566087830108713575227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3220754783773478284766969 2415566087830108713575227)
            ·
              refine ⟨3623349131745163070362841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2415566087830108713575227 3623349131745163070362841)
              ·
                refine ⟨2717511848808872302772131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3623349131745163070362841 2717511848808872302772131)
                ·
                  refine ⟨4076267773213308454158197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717511848808872302772131 4076267773213308454158197)
                  ·
                    refine ⟨382150103738747667577331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4076267773213308454158197 382150103738747667577331)
                    ·
                      rfl

theorem cell22_1116352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_1116352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116352 prefixEnd_1116352 := by exact prefixLift 1116352
  have htrace : WordTrace (prefixWord ++ tailWord_1116352) baseStart_1116352 baseEnd_1116352 := by
    simpa [prefixWord, tailWord_1116352, baseEnd_1116352] using wordTrace_append hprefix tailTrace_1116352
  have hstable : (prefixWord ++ tailWord_1116352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116352).length < 2 ^ (prefixWord ++ tailWord_1116352).sum := by decide
  have hdescent : baseEnd_1116352 < baseStart_1116352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116356 : List Nat := [2, 3, 3, 1, 2, 2, 3, 1, 1, 4]
def baseStart_1116356 : Nat := 118140960795 + 1116356 * 2 ^ 59
def prefixEnd_1116356 : Nat := 4983230072969 + 3 ^ 40 * 1116356 * 2
def baseEnd_1116356 : Nat := 382151473020492990477319

theorem tailTrace_1116356 : CollatzResearch.WordTrace tailWord_1116356 prefixEnd_1116356 382151473020492990477319 := by
  unfold tailWord_1116356
  simp only [CollatzResearch.WordTrace]
  refine ⟨20358424171820172635408461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27144565562426896847211281 20358424171820172635408461)
  ·
    refine ⟨7634409064432564738278173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20358424171820172635408461 7634409064432564738278173)
    ·
      refine ⟨2862903399162211776854315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7634409064432564738278173 2862903399162211776854315)
      ·
        refine ⟨4294355098743317665281473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2862903399162211776854315 4294355098743317665281473)
        ·
          refine ⟨3220766324057488248961105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4294355098743317665281473 3220766324057488248961105)
          ·
            refine ⟨2415574743043116186720829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3220766324057488248961105 2415574743043116186720829)
            ·
              refine ⟨905840528641168570020311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2415574743043116186720829 905840528641168570020311)
              ·
                refine ⟨1358760792961752855030467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 905840528641168570020311 1358760792961752855030467)
                ·
                  refine ⟨2038141189442629282545701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358760792961752855030467 2038141189442629282545701)
                  ·
                    refine ⟨382151473020492990477319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2038141189442629282545701 382151473020492990477319)
                    ·
                      rfl

theorem cell22_1116356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_1116356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116356 prefixEnd_1116356 := by exact prefixLift 1116356
  have htrace : WordTrace (prefixWord ++ tailWord_1116356) baseStart_1116356 baseEnd_1116356 := by
    simpa [prefixWord, tailWord_1116356, baseEnd_1116356] using wordTrace_append hprefix tailTrace_1116356
  have hstable : (prefixWord ++ tailWord_1116356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116356).length < 2 ^ (prefixWord ++ tailWord_1116356).sum := by decide
  have hdescent : baseEnd_1116356 < baseStart_1116356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116395 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 2, 6]
def baseStart_1116395 : Nat := 118140960795 + 1116395 * 2 ^ 59
def prefixEnd_1116395 : Nat := 4983230072969 + 3 ^ 40 * 1116395 * 2
def baseEnd_1116395 : Nat := 382164823517509888752199

theorem tailTrace_1116395 : CollatzResearch.WordTrace tailWord_1116395 prefixEnd_1116395 382164823517509888752199 := by
  unfold tailWord_1116395
  simp only [CollatzResearch.WordTrace]
  refine ⟨40718270790499054931486639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27145513860332703287657759 40718270790499054931486639)
  ·
    refine ⟨61077406185748582397229959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40718270790499054931486639 61077406185748582397229959)
    ·
      refine ⟨91616109278622873595844939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61077406185748582397229959 91616109278622873595844939)
      ·
        refine ⟨137424163917934310393767409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91616109278622873595844939 137424163917934310393767409)
        ·
          refine ⟨103068122938450732795325557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137424163917934310393767409 103068122938450732795325557)
          ·
            refine ⟨9662636525479756199561771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103068122938450732795325557 9662636525479756199561771)
            ·
              refine ⟨14493954788219634299342657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9662636525479756199561771 14493954788219634299342657)
              ·
                refine ⟨10870466091164725724506993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14493954788219634299342657 10870466091164725724506993)
                ·
                  refine ⟨8152849568373544293380245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10870466091164725724506993 8152849568373544293380245)
                  ·
                    refine ⟨382164823517509888752199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8152849568373544293380245 382164823517509888752199)
                    ·
                      rfl

theorem cell22_1116395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 6].length) (baseStart_1116395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116395 prefixEnd_1116395 := by exact prefixLift 1116395
  have htrace : WordTrace (prefixWord ++ tailWord_1116395) baseStart_1116395 baseEnd_1116395 := by
    simpa [prefixWord, tailWord_1116395, baseEnd_1116395] using wordTrace_append hprefix tailTrace_1116395
  have hstable : (prefixWord ++ tailWord_1116395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116395).length < 2 ^ (prefixWord ++ tailWord_1116395).sum := by decide
  have hdescent : baseEnd_1116395 < baseStart_1116395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116414 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_1116414 : Nat := 118140960795 + 1116414 * 2 ^ 59
def prefixEnd_1116414 : Nat := 4983230072969 + 3 ^ 40 * 1116414 * 2
def baseEnd_1116414 : Nat := 382171327605800172527141

theorem tailTrace_1116414 : CollatzResearch.WordTrace tailWord_1116414 prefixEnd_1116414 382171327605800172527141 := by
  unfold tailWord_1116414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5089870472178777647053537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27145975851620147450952197 5089870472178777647053537)
  ·
    refine ⟨3817402854134083235290153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5089870472178777647053537 3817402854134083235290153)
    ·
      refine ⟨2863052140600562426467615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3817402854134083235290153 2863052140600562426467615)
      ·
        refine ⟨4294578210900843639701423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2863052140600562426467615 4294578210900843639701423)
        ·
          refine ⟨6441867316351265459552135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4294578210900843639701423 6441867316351265459552135)
          ·
            refine ⟨9662800974526898189328203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6441867316351265459552135 9662800974526898189328203)
            ·
              refine ⟨14494201461790347283992305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9662800974526898189328203 14494201461790347283992305)
              ·
                refine ⟨10870651096342760462994229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14494201461790347283992305 10870651096342760462994229)
                ·
                  refine ⟨1019123540282133793405709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10870651096342760462994229 1019123540282133793405709)
                  ·
                    refine ⟨382171327605800172527141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1019123540282133793405709 382171327605800172527141)
                    ·
                      rfl

theorem cell22_1116414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_1116414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116414 prefixEnd_1116414 := by exact prefixLift 1116414
  have htrace : WordTrace (prefixWord ++ tailWord_1116414) baseStart_1116414 baseEnd_1116414 := by
    simpa [prefixWord, tailWord_1116414, baseEnd_1116414] using wordTrace_append hprefix tailTrace_1116414
  have hstable : (prefixWord ++ tailWord_1116414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116414).length < 2 ^ (prefixWord ++ tailWord_1116414).sum := by decide
  have hdescent : baseEnd_1116414 < baseStart_1116414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116465 : List Nat := [1, 2, 2, 3, 5, 1, 1, 3, 1, 3]
def baseStart_1116465 : Nat := 118140960795 + 1116465 * 2 ^ 59
def prefixEnd_1116465 : Nat := 4983230072969 + 3 ^ 40 * 1116465 * 2
def baseEnd_1116465 : Nat := 382188785948053039501985

theorem tailTrace_1116465 : CollatzResearch.WordTrace tailWord_1116465 prefixEnd_1116465 382188785948053039501985 := by
  unfold tailWord_1116465
  simp only [CollatzResearch.WordTrace]
  refine ⟨40720823900245456886534849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27147215933496971257689899 40720823900245456886534849)
  ·
    refine ⟨30540617925184092664901137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40720823900245456886534849 30540617925184092664901137)
    ·
      refine ⟨22905463443888069498675853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30540617925184092664901137 22905463443888069498675853)
      ·
        refine ⟨8589548791458026062003445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22905463443888069498675853 8589548791458026062003445)
        ·
          refine ⟨805270199199189943312823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8589548791458026062003445 805270199199189943312823)
          ·
            refine ⟨1207905298798784914969235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805270199199189943312823 1207905298798784914969235)
            ·
              refine ⟨1811857948198177372453853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207905298798784914969235 1811857948198177372453853)
              ·
                refine ⟨679446730574316514670195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1811857948198177372453853 679446730574316514670195)
                ·
                  refine ⟨1019170095861474772005293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679446730574316514670195 1019170095861474772005293)
                  ·
                    refine ⟨382188785948053039501985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1019170095861474772005293 382188785948053039501985)
                    ·
                      rfl

theorem cell22_1116465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_1116465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116465 prefixEnd_1116465 := by exact prefixLift 1116465
  have htrace : WordTrace (prefixWord ++ tailWord_1116465) baseStart_1116465 baseEnd_1116465 := by
    simpa [prefixWord, tailWord_1116465, baseEnd_1116465] using wordTrace_append hprefix tailTrace_1116465
  have hstable : (prefixWord ++ tailWord_1116465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116465).length < 2 ^ (prefixWord ++ tailWord_1116465).sum := by decide
  have hdescent : baseEnd_1116465 < baseStart_1116465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116474 : List Nat := [3, 1, 1, 1, 4, 2, 2, 3, 1, 4]
def baseStart_1116474 : Nat := 118140960795 + 1116474 * 2 ^ 59
def prefixEnd_1116474 : Nat := 4983230072969 + 3 ^ 40 * 1116474 * 2
def baseEnd_1116474 : Nat := 382191866831980016026957

theorem tailTrace_1116474 : CollatzResearch.WordTrace tailWord_1116474 prefixEnd_1116474 382191866831980016026957 := by
  unfold tailWord_1116474
  simp only [CollatzResearch.WordTrace]
  refine ⟨10180288039303212855903119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27147434771475234282408317 10180288039303212855903119)
  ·
    refine ⟨15270432058954819283854679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10180288039303212855903119 15270432058954819283854679)
    ·
      refine ⟨22905648088432228925782019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15270432058954819283854679 22905648088432228925782019)
      ·
        refine ⟨34358472132648343388673029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22905648088432228925782019 34358472132648343388673029)
        ·
          refine ⟨6442213524871564385376193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34358472132648343388673029 6442213524871564385376193)
          ·
            refine ⟨4831660143653673289032145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6442213524871564385376193 4831660143653673289032145)
            ·
              refine ⟨3623745107740254966774109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4831660143653673289032145 3623745107740254966774109)
              ·
                refine ⟨1358904415402595612540291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3623745107740254966774109 1358904415402595612540291)
                ·
                  refine ⟨2038356623103893418810437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1358904415402595612540291 2038356623103893418810437)
                  ·
                    refine ⟨382191866831980016026957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2038356623103893418810437 382191866831980016026957)
                    ·
                      rfl

theorem cell22_1116474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_1116474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116474 prefixEnd_1116474 := by exact prefixLift 1116474
  have htrace : WordTrace (prefixWord ++ tailWord_1116474) baseStart_1116474 baseEnd_1116474 := by
    simpa [prefixWord, tailWord_1116474, baseEnd_1116474] using wordTrace_append hprefix tailTrace_1116474
  have hstable : (prefixWord ++ tailWord_1116474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116474).length < 2 ^ (prefixWord ++ tailWord_1116474).sum := by decide
  have hdescent : baseEnd_1116474 < baseStart_1116474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116517 : List Nat := [1, 3, 1, 3, 1, 3, 2, 8]
def baseStart_1116517 : Nat := 118140960795 + 1116517 * 2 ^ 59
def prefixEnd_1116517 : Nat := 4983230072969 + 3 ^ 40 * 1116517 * 2
def baseEnd_1116517 : Nat := 42467398512304693022425

theorem tailTrace_1116517 : CollatzResearch.WordTrace tailWord_1116517 prefixEnd_1116517 42467398512304693022425 := by
  unfold tailWord_1116517
  simp only [CollatzResearch.WordTrace]
  refine ⟨40722720496057069767427805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27148480330704713178285203 40722720496057069767427805)
  ·
    refine ⟨15271020186021401162785427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40722720496057069767427805 15271020186021401162785427)
    ·
      refine ⟨22906530279032101744178141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15271020186021401162785427 22906530279032101744178141)
      ·
        refine ⟨8589948854637038154066803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22906530279032101744178141 8589948854637038154066803)
        ·
          refine ⟨12884923281955557231100205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8589948854637038154066803 12884923281955557231100205)
          ·
            refine ⟨4831846230733333961662577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12884923281955557231100205 4831846230733333961662577)
            ·
              refine ⟨3623884673050000471246933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4831846230733333961662577 3623884673050000471246933)
              ·
                refine ⟨42467398512304693022425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3623884673050000471246933 42467398512304693022425)
                ·
                  rfl

theorem cell22_1116517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 8].length) (baseStart_1116517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116517 prefixEnd_1116517 := by exact prefixLift 1116517
  have htrace : WordTrace (prefixWord ++ tailWord_1116517) baseStart_1116517 baseEnd_1116517 := by
    simpa [prefixWord, tailWord_1116517, baseEnd_1116517] using wordTrace_append hprefix tailTrace_1116517
  have hstable : (prefixWord ++ tailWord_1116517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116517).length < 2 ^ (prefixWord ++ tailWord_1116517).sum := by decide
  have hdescent : baseEnd_1116517 < baseStart_1116517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116519 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 2, 4]
def baseStart_1116519 : Nat := 118140960795 + 1116519 * 2 ^ 59
def prefixEnd_1116519 : Nat := 4983230072969 + 3 ^ 40 * 1116519 * 2
def baseEnd_1116519 : Nat := 382207271251614898651819

theorem tailTrace_1116519 : CollatzResearch.WordTrace tailWord_1116519 prefixEnd_1116519 382207271251614898651819 := by
  unfold tailWord_1116519
  simp only [CollatzResearch.WordTrace]
  refine ⟨40722793442049824109000611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27148528961366549406000407 40722793442049824109000611)
  ·
    refine ⟨61084190163074736163500917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40722793442049824109000611 61084190163074736163500917)
    ·
      refine ⟨5726642827788256515328211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61084190163074736163500917 5726642827788256515328211)
      ·
        refine ⟨8589964241682384772992317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5726642827788256515328211 8589964241682384772992317)
        ·
          refine ⟨3221236590630894289872119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8589964241682384772992317 3221236590630894289872119)
          ·
            refine ⟨4831854885946341434808179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221236590630894289872119 4831854885946341434808179)
            ·
              refine ⟨7247782328919512152212269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4831854885946341434808179 7247782328919512152212269)
              ·
                refine ⟨2717918373344817057079601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7247782328919512152212269 2717918373344817057079601)
                ·
                  refine ⟨2038438780008612792809701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2717918373344817057079601 2038438780008612792809701)
                  ·
                    refine ⟨382207271251614898651819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2038438780008612792809701 382207271251614898651819)
                    ·
                      rfl

theorem cell22_1116519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_1116519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116519 prefixEnd_1116519 := by exact prefixLift 1116519
  have htrace : WordTrace (prefixWord ++ tailWord_1116519) baseStart_1116519 baseEnd_1116519 := by
    simpa [prefixWord, tailWord_1116519, baseEnd_1116519] using wordTrace_append hprefix tailTrace_1116519
  have hstable : (prefixWord ++ tailWord_1116519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116519).length < 2 ^ (prefixWord ++ tailWord_1116519).sum := by decide
  have hdescent : baseEnd_1116519 < baseStart_1116519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116534 : List Nat := [5, 1, 1, 4, 11]
def baseStart_1116534 : Nat := 118140960795 + 1116534 * 2 ^ 59
def prefixEnd_1116534 : Nat := 4983230072969 + 3 ^ 40 * 1116534 * 2
def baseEnd_1116534 : Nat := 1572890559910122878711

theorem tailTrace_1116534 : CollatzResearch.WordTrace tailWord_1116534 prefixEnd_1116534 1572890559910122878711 := by
  unfold tailWord_1116534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2545208783562217604424791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27148893691330321113864437 2545208783562217604424791)
  ·
    refine ⟨3817813175343326406637187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2545208783562217604424791 3817813175343326406637187)
    ·
      refine ⟨5726719763014989609955781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3817813175343326406637187 5726719763014989609955781)
      ·
        refine ⟨1073759955565310551866709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5726719763014989609955781 1073759955565310551866709)
        ·
          refine ⟨1572890559910122878711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1073759955565310551866709 1572890559910122878711)
          ·
            rfl

theorem cell22_1116534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 11].length) (baseStart_1116534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116534 prefixEnd_1116534 := by exact prefixLift 1116534
  have htrace : WordTrace (prefixWord ++ tailWord_1116534) baseStart_1116534 baseEnd_1116534 := by
    simpa [prefixWord, tailWord_1116534, baseEnd_1116534] using wordTrace_append hprefix tailTrace_1116534
  have hstable : (prefixWord ++ tailWord_1116534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116534).length < 2 ^ (prefixWord ++ tailWord_1116534).sum := by decide
  have hdescent : baseEnd_1116534 < baseStart_1116534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116549 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 3, 3]
def baseStart_1116549 : Nat := 118140960795 + 1116549 * 2 ^ 59
def prefixEnd_1116549 : Nat := 4983230072969 + 3 ^ 40 * 1116549 * 2
def baseEnd_1116549 : Nat := 382217540864704820401727

theorem tailTrace_1116549 : CollatzResearch.WordTrace tailWord_1116549 prefixEnd_1116549 382217540864704820401727 := by
  unfold tailWord_1116549
  simp only [CollatzResearch.WordTrace]
  refine ⟨40723887631941139232592701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27149258421294092821728467 40723887631941139232592701)
  ·
    refine ⟨15271457861977927212222263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40723887631941139232592701 15271457861977927212222263)
    ·
      refine ⟨22907186792966890818333395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15271457861977927212222263 22907186792966890818333395)
      ·
        refine ⟨34360780189450336227500093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22907186792966890818333395 34360780189450336227500093)
        ·
          refine ⟨12885292571043876085312535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34360780189450336227500093 12885292571043876085312535)
          ·
            refine ⟨19327938856565814127968803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12885292571043876085312535 19327938856565814127968803)
            ·
              refine ⟨28991908284848721191953205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19327938856565814127968803 28991908284848721191953205)
              ·
                refine ⟨2717991401704567611745613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28991908284848721191953205 2717991401704567611745613)
                ·
                  refine ⟨1019246775639212854404605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2717991401704567611745613 1019246775639212854404605)
                  ·
                    refine ⟨382217540864704820401727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1019246775639212854404605 382217540864704820401727)
                    ·
                      rfl

theorem cell22_1116549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_1116549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116549 prefixEnd_1116549 := by exact prefixLift 1116549
  have htrace : WordTrace (prefixWord ++ tailWord_1116549) baseStart_1116549 baseEnd_1116549 := by
    simpa [prefixWord, tailWord_1116549, baseEnd_1116549] using wordTrace_append hprefix tailTrace_1116549
  have hstable : (prefixWord ++ tailWord_1116549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116549).length < 2 ^ (prefixWord ++ tailWord_1116549).sum := by decide
  have hdescent : baseEnd_1116549 < baseStart_1116549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116583 : List Nat := [1, 1, 6, 1, 1, 2, 1, 5, 1, 3]
def baseStart_1116583 : Nat := 118140960795 + 1116583 * 2 ^ 59
def prefixEnd_1116583 : Nat := 4983230072969 + 3 ^ 40 * 1116583 * 2
def baseEnd_1116583 : Nat := 382229179759540065051623

theorem tailTrace_1116583 : CollatzResearch.WordTrace tailWord_1116583 prefixEnd_1116583 382229179759540065051623 := by
  unfold tailWord_1116583
  simp only [CollatzResearch.WordTrace]
  refine ⟨40725127713817963039330403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27150085142545308692886935 40725127713817963039330403)
  ·
    refine ⟨61087691570726944558995605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40725127713817963039330403 61087691570726944558995605)
    ·
      refine ⟨2863485542377825526202919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 61087691570726944558995605 2863485542377825526202919)
      ·
        refine ⟨4295228313566738289304379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2863485542377825526202919 4295228313566738289304379)
        ·
          refine ⟨6442842470350107433956569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4295228313566738289304379 6442842470350107433956569)
          ·
            refine ⟨4832131852762580575467427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6442842470350107433956569 4832131852762580575467427)
            ·
              refine ⟨7248197779143870863201141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4832131852762580575467427 7248197779143870863201141)
              ·
                refine ⟨679518541794737893425107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7248197779143870863201141 679518541794737893425107)
                ·
                  refine ⟨1019277812692106840137661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679518541794737893425107 1019277812692106840137661)
                  ·
                    refine ⟨382229179759540065051623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1019277812692106840137661 382229179759540065051623)
                    ·
                      rfl

theorem cell22_1116583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_1116583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116583 prefixEnd_1116583 := by exact prefixLift 1116583
  have htrace : WordTrace (prefixWord ++ tailWord_1116583) baseStart_1116583 baseEnd_1116583 := by
    simpa [prefixWord, tailWord_1116583, baseEnd_1116583] using wordTrace_append hprefix tailTrace_1116583
  have hstable : (prefixWord ++ tailWord_1116583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116583).length < 2 ^ (prefixWord ++ tailWord_1116583).sum := by decide
  have hdescent : baseEnd_1116583 < baseStart_1116583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116656 : List Nat := [2, 1, 1, 1, 3, 3, 2, 4, 2, 3]
def baseStart_1116656 : Nat := 118140960795 + 1116656 * 2 ^ 59
def prefixEnd_1116656 : Nat := 4983230072969 + 3 ^ 40 * 1116656 * 2
def baseEnd_1116656 : Nat := 382254169151392207976399

theorem tailTrace_1116656 : CollatzResearch.WordTrace tailWord_1116656 prefixEnd_1116656 382254169151392207976399 := by
  unfold tailWord_1116656
  simp only [CollatzResearch.WordTrace]
  refine ⟨20363895121276748253368911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27151860161702331004491881 20363895121276748253368911)
  ·
    refine ⟨30545842681915122380053367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20363895121276748253368911 30545842681915122380053367)
    ·
      refine ⟨45818764022872683570080051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30545842681915122380053367 45818764022872683570080051)
      ·
        refine ⟨68728146034309025355120077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45818764022872683570080051 68728146034309025355120077)
        ·
          refine ⟨25773054762865884508170029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68728146034309025355120077 25773054762865884508170029)
          ·
            refine ⟨9664895536074706690563761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25773054762865884508170029 9664895536074706690563761)
            ·
              refine ⟨7248671652056030017922821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9664895536074706690563761 7248671652056030017922821)
              ·
                refine ⟨1359125934760505628360529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7248671652056030017922821 1359125934760505628360529)
                ·
                  refine ⟨1019344451070379221270397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1359125934760505628360529 1019344451070379221270397)
                  ·
                    refine ⟨382254169151392207976399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1019344451070379221270397 382254169151392207976399)
                    ·
                      rfl

theorem cell22_1116656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 2, 3].length) (baseStart_1116656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116656 prefixEnd_1116656 := by exact prefixLift 1116656
  have htrace : WordTrace (prefixWord ++ tailWord_1116656) baseStart_1116656 baseEnd_1116656 := by
    simpa [prefixWord, tailWord_1116656, baseEnd_1116656] using wordTrace_append hprefix tailTrace_1116656
  have hstable : (prefixWord ++ tailWord_1116656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116656).length < 2 ^ (prefixWord ++ tailWord_1116656).sum := by decide
  have hdescent : baseEnd_1116656 < baseStart_1116656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116658 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 6]
def baseStart_1116658 : Nat := 118140960795 + 1116658 * 2 ^ 59
def prefixEnd_1116658 : Nat := 4983230072969 + 3 ^ 40 * 1116658 * 2
def baseEnd_1116658 : Nat := 127418284597421623142131

theorem tailTrace_1116658 : CollatzResearch.WordTrace tailWord_1116658 prefixEnd_1116658 127418284597421623142131 := by
  unfold tailWord_1116658
  simp only [CollatzResearch.WordTrace]
  refine ⟨10181965797136562712077657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27151908792364167232207085 10181965797136562712077657)
  ·
    refine ⟨7636474347852422034058243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10181965797136562712077657 7636474347852422034058243)
    ·
      refine ⟨11454711521778633051087365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7636474347852422034058243 11454711521778633051087365)
      ·
        refine ⟨2147758410333493697078881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11454711521778633051087365 2147758410333493697078881)
        ·
          refine ⟨1610818807750120272809161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2147758410333493697078881 1610818807750120272809161)
          ·
            refine ⟨1208114105812590204606871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1610818807750120272809161 1208114105812590204606871)
            ·
              refine ⟨1812171158718885306910307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208114105812590204606871 1812171158718885306910307)
              ·
                refine ⟨2718256738078327960365461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1812171158718885306910307 2718256738078327960365461)
                ·
                  refine ⟨127418284597421623142131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2718256738078327960365461 127418284597421623142131)
                  ·
                    rfl

theorem cell22_1116658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_1116658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116658 prefixEnd_1116658 := by exact prefixLift 1116658
  have htrace : WordTrace (prefixWord ++ tailWord_1116658) baseStart_1116658 baseEnd_1116658 := by
    simpa [prefixWord, tailWord_1116658, baseEnd_1116658] using wordTrace_append hprefix tailTrace_1116658
  have hstable : (prefixWord ++ tailWord_1116658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116658).length < 2 ^ (prefixWord ++ tailWord_1116658).sum := by decide
  have hdescent : baseEnd_1116658 < baseStart_1116658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116669 : List Nat := [1, 4, 1, 1, 1, 3, 4, 7]
def baseStart_1116669 : Nat := 118140960795 + 1116669 * 2 ^ 59
def prefixEnd_1116669 : Nat := 4983230072969 + 3 ^ 40 * 1116669 * 2
def baseEnd_1116669 : Nat := 42473179924118278600151

theorem tailTrace_1116669 : CollatzResearch.WordTrace tailWord_1116669 prefixEnd_1116669 42473179924118278600151 := by
  unfold tailWord_1116669
  simp only [CollatzResearch.WordTrace]
  refine ⟨40728264391506399726961061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27152176261004266484640707 40728264391506399726961061)
  ·
    refine ⟨7636549573407449948805199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40728264391506399726961061 7636549573407449948805199)
    ·
      refine ⟨11454824360111174923207799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7636549573407449948805199 11454824360111174923207799)
      ·
        refine ⟨17182236540166762384811699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11454824360111174923207799 17182236540166762384811699)
        ·
          refine ⟨25773354810250143577217549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17182236540166762384811699 25773354810250143577217549)
          ·
            refine ⟨9665008053843803841456581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25773354810250143577217549 9665008053843803841456581)
            ·
              refine ⟨1812189010095713220273109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9665008053843803841456581 1812189010095713220273109)
              ·
                refine ⟨42473179924118278600151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1812189010095713220273109 42473179924118278600151)
                ·
                  rfl

theorem cell22_1116669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 7].length) (baseStart_1116669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116669 prefixEnd_1116669 := by exact prefixLift 1116669
  have htrace : WordTrace (prefixWord ++ tailWord_1116669) baseStart_1116669 baseEnd_1116669 := by
    simpa [prefixWord, tailWord_1116669, baseEnd_1116669] using wordTrace_append hprefix tailTrace_1116669
  have hstable : (prefixWord ++ tailWord_1116669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116669).length < 2 ^ (prefixWord ++ tailWord_1116669).sum := by decide
  have hdescent : baseEnd_1116669 < baseStart_1116669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116673 : List Nat := [1, 2, 4, 1, 3, 2, 1, 3, 2, 3]
def baseStart_1116673 : Nat := 118140960795 + 1116673 * 2 ^ 59
def prefixEnd_1116673 : Nat := 4983230072969 + 3 ^ 40 * 1116673 * 2
def baseEnd_1116673 : Nat := 382259988598809830301347

theorem tailTrace_1116673 : CollatzResearch.WordTrace tailWord_1116673 prefixEnd_1116673 382259988598809830301347 := by
  unfold tailWord_1116673
  simp only [CollatzResearch.WordTrace]
  refine ⟨40728410283491908410106673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27152273522327938940071115 40728410283491908410106673)
  ·
    refine ⟨30546307712618931307580005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40728410283491908410106673 30546307712618931307580005)
    ·
      refine ⟨5727432696116049620171251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30546307712618931307580005 5727432696116049620171251)
      ·
        refine ⟨8591149044174074430256877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5727432696116049620171251 8591149044174074430256877)
        ·
          refine ⟨3221680891565277911346329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8591149044174074430256877 3221680891565277911346329)
          ·
            refine ⟨2416260668673958433509747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3221680891565277911346329 2416260668673958433509747)
            ·
              refine ⟨3624391003010937650264621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2416260668673958433509747 3624391003010937650264621)
              ·
                refine ⟨1359146626129101618849233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3624391003010937650264621 1359146626129101618849233)
                ·
                  refine ⟨1019359969596826214136925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1359146626129101618849233 1019359969596826214136925)
                  ·
                    refine ⟨382259988598809830301347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1019359969596826214136925 382259988598809830301347)
                    ·
                      rfl

theorem cell22_1116673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_1116673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116673 prefixEnd_1116673 := by exact prefixLift 1116673
  have htrace : WordTrace (prefixWord ++ tailWord_1116673) baseStart_1116673 baseEnd_1116673 := by
    simpa [prefixWord, tailWord_1116673, baseEnd_1116673] using wordTrace_append hprefix tailTrace_1116673
  have hstable : (prefixWord ++ tailWord_1116673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116673).length < 2 ^ (prefixWord ++ tailWord_1116673).sum := by decide
  have hdescent : baseEnd_1116673 < baseStart_1116673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116759 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 8]
def baseStart_1116759 : Nat := 118140960795 + 1116759 * 2 ^ 59
def prefixEnd_1116759 : Nat := 4983230072969 + 3 ^ 40 * 1116759 * 2
def baseEnd_1116759 : Nat := 127429809385444757550361

theorem tailTrace_1116759 : CollatzResearch.WordTrace tailWord_1116759 prefixEnd_1116759 127429809385444757550361 := by
  unfold tailWord_1116759
  simp only [CollatzResearch.WordTrace]
  refine ⟨40731546961180345097737331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27154364640786896731824887 40731546961180345097737331)
  ·
    refine ⟨61097320441770517646605997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40731546961180345097737331 61097320441770517646605997)
    ·
      refine ⟨22911495165663944117477249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61097320441770517646605997 22911495165663944117477249)
      ·
        refine ⟨17183621374247958088107937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22911495165663944117477249 17183621374247958088107937)
        ·
          refine ⟨12887716030685968566080953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17183621374247958088107937 12887716030685968566080953)
          ·
            refine ⟨9665787023014476424560715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12887716030685968566080953 9665787023014476424560715)
            ·
              refine ⟨14498680534521714636841073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9665787023014476424560715 14498680534521714636841073)
              ·
                refine ⟨10874010400891285977630805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14498680534521714636841073 10874010400891285977630805)
                ·
                  refine ⟨127429809385444757550361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10874010400891285977630805 127429809385444757550361)
                  ·
                    rfl

theorem cell22_1116759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 8].length) (baseStart_1116759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116759 prefixEnd_1116759 := by exact prefixLift 1116759
  have htrace : WordTrace (prefixWord ++ tailWord_1116759) baseStart_1116759 baseEnd_1116759 := by
    simpa [prefixWord, tailWord_1116759, baseEnd_1116759] using wordTrace_append hprefix tailTrace_1116759
  have hstable : (prefixWord ++ tailWord_1116759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116759).length < 2 ^ (prefixWord ++ tailWord_1116759).sum := by decide
  have hdescent : baseEnd_1116759 < baseStart_1116759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116791 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 1, 5]
def baseStart_1116791 : Nat := 118140960795 + 1116791 * 2 ^ 59
def prefixEnd_1116791 : Nat := 4983230072969 + 3 ^ 40 * 1116791 * 2
def baseEnd_1116791 : Nat := 382300382410296855850985

theorem tailTrace_1116791 : CollatzResearch.WordTrace tailWord_1116791 prefixEnd_1116791 382300382410296855850985 := by
  unfold tailWord_1116791
  simp only [CollatzResearch.WordTrace]
  refine ⟨40732714097064414562902227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27155142731376276375268151 40732714097064414562902227)
  ·
    refine ⟨61099071145596621844353341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40732714097064414562902227 61099071145596621844353341)
    ·
      refine ⟨22912151679598733191632503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61099071145596621844353341 22912151679598733191632503)
      ·
        refine ⟨34368227519398099787448755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22912151679598733191632503 34368227519398099787448755)
        ·
          refine ⟨51552341279097149681173133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34368227519398099787448755 51552341279097149681173133)
          ·
            refine ⟨19332127979661431130439925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51552341279097149681173133 19332127979661431130439925)
            ·
              refine ⟨1812386998093259168478743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19332127979661431130439925 1812386998093259168478743)
              ·
                refine ⟨2718580497139888752718115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1812386998093259168478743 2718580497139888752718115)
                ·
                  refine ⟨4077870745709833129077173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718580497139888752718115 4077870745709833129077173)
                  ·
                    refine ⟨382300382410296855850985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4077870745709833129077173 382300382410296855850985)
                    ·
                      rfl

theorem cell22_1116791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_1116791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116791 prefixEnd_1116791 := by exact prefixLift 1116791
  have htrace : WordTrace (prefixWord ++ tailWord_1116791) baseStart_1116791 baseEnd_1116791 := by
    simpa [prefixWord, tailWord_1116791, baseEnd_1116791] using wordTrace_append hprefix tailTrace_1116791
  have hstable : (prefixWord ++ tailWord_1116791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116791).length < 2 ^ (prefixWord ++ tailWord_1116791).sum := by decide
  have hdescent : baseEnd_1116791 < baseStart_1116791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116819 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 1, 9]
def baseStart_1116819 : Nat := 118140960795 + 1116819 * 2 ^ 59
def prefixEnd_1116819 : Nat := 4983230072969 + 3 ^ 40 * 1116819 * 2
def baseEnd_1116819 : Nat := 382309967382514116150899

theorem tailTrace_1116819 : CollatzResearch.WordTrace tailWord_1116819 prefixEnd_1116819 382309967382514116150899 := by
  unfold tailWord_1116819
  simp only [CollatzResearch.WordTrace]
  refine ⟨40733735340962975344921511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27155823560641983563281007 40733735340962975344921511)
  ·
    refine ⟨61100603011444463017382267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40733735340962975344921511 61100603011444463017382267)
    ·
      refine ⟨91650904517166694526073401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61100603011444463017382267 91650904517166694526073401)
      ·
        refine ⟨68738178387875020894555051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91650904517166694526073401 68738178387875020894555051)
        ·
          refine ⟨103107267581812531341832577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68738178387875020894555051 103107267581812531341832577)
          ·
            refine ⟨77330450686359398506374433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103107267581812531341832577 77330450686359398506374433)
            ·
              refine ⟨57997838014769548879780825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77330450686359398506374433 57997838014769548879780825)
              ·
                refine ⟨43498378511077161659835619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57997838014769548879780825 43498378511077161659835619)
                ·
                  refine ⟨65247567766615742489753429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43498378511077161659835619 65247567766615742489753429)
                  ·
                    refine ⟨382309967382514116150899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 65247567766615742489753429 382309967382514116150899)
                    ·
                      rfl

theorem cell22_1116819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_1116819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116819 prefixEnd_1116819 := by exact prefixLift 1116819
  have htrace : WordTrace (prefixWord ++ tailWord_1116819) baseStart_1116819 baseEnd_1116819 := by
    simpa [prefixWord, tailWord_1116819, baseEnd_1116819] using wordTrace_append hprefix tailTrace_1116819
  have hstable : (prefixWord ++ tailWord_1116819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116819).length < 2 ^ (prefixWord ++ tailWord_1116819).sum := by decide
  have hdescent : baseEnd_1116819 < baseStart_1116819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116881 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 2, 5]
def baseStart_1116881 : Nat := 118140960795 + 1116881 * 2 ^ 59
def prefixEnd_1116881 : Nat := 4983230072969 + 3 ^ 40 * 1116881 * 2
def baseEnd_1116881 : Nat := 382331191249566621100709

theorem tailTrace_1116881 : CollatzResearch.WordTrace tailWord_1116881 prefixEnd_1116881 382331191249566621100709 := by
  unfold tailWord_1116881
  simp only [CollatzResearch.WordTrace]
  refine ⟨40735996666738359933678497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27157331111158906622452331 40735996666738359933678497)
  ·
    refine ⟨30551997500053769950258873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40735996666738359933678497 30551997500053769950258873)
    ·
      refine ⟨22913998125040327462694155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30551997500053769950258873 22913998125040327462694155)
      ·
        refine ⟨34370997187560491194041233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22913998125040327462694155 34370997187560491194041233)
        ·
          refine ⟨25778247890670368395530925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34370997187560491194041233 25778247890670368395530925)
          ·
            refine ⟨9666842959001388148324097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25778247890670368395530925 9666842959001388148324097)
            ·
              refine ⟨7250132219251041111243073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9666842959001388148324097 7250132219251041111243073)
              ·
                refine ⟨5437599164438280833432305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7250132219251041111243073 5437599164438280833432305)
                ·
                  refine ⟨4078199373328710625074229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5437599164438280833432305 4078199373328710625074229)
                  ·
                    refine ⟨382331191249566621100709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4078199373328710625074229 382331191249566621100709)
                    ·
                      rfl

theorem cell22_1116881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_1116881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116881 prefixEnd_1116881 := by exact prefixLift 1116881
  have htrace : WordTrace (prefixWord ++ tailWord_1116881) baseStart_1116881 baseEnd_1116881 := by
    simpa [prefixWord, tailWord_1116881, baseEnd_1116881] using wordTrace_append hprefix tailTrace_1116881
  have hstable : (prefixWord ++ tailWord_1116881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116881).length < 2 ^ (prefixWord ++ tailWord_1116881).sum := by decide
  have hdescent : baseEnd_1116881 < baseStart_1116881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116887 : List Nat := [1, 1, 3, 2, 1, 4, 4, 2, 1, 3]
def baseStart_1116887 : Nat := 118140960795 + 1116887 * 2 ^ 59
def prefixEnd_1116887 : Nat := 4983230072969 + 3 ^ 40 * 1116887 * 2
def baseEnd_1116887 : Nat := 382333245172184605450691

theorem tailTrace_1116887 : CollatzResearch.WordTrace tailWord_1116887 prefixEnd_1116887 382333245172184605450691 := by
  unfold tailWord_1116887
  simp only [CollatzResearch.WordTrace]
  refine ⟨40736215504716622958396915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27157477003144415305597943 40736215504716622958396915)
  ·
    refine ⟨61104323257074934437595373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40736215504716622958396915 61104323257074934437595373)
    ·
      refine ⟨22914121221403100414098265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61104323257074934437595373 22914121221403100414098265)
      ·
        refine ⟨17185590916052325310573699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22914121221403100414098265 17185590916052325310573699)
        ·
          refine ⟨25778386374078487965860549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17185590916052325310573699 25778386374078487965860549)
          ·
            refine ⟨4833447445139716493598853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25778386374078487965860549 4833447445139716493598853)
            ·
              refine ⟨906271395963696842549785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4833447445139716493598853 906271395963696842549785)
              ·
                refine ⟨679703546972772631912339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906271395963696842549785 679703546972772631912339)
                ·
                  refine ⟨1019555320459158947868509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 679703546972772631912339 1019555320459158947868509)
                  ·
                    refine ⟨382333245172184605450691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1019555320459158947868509 382333245172184605450691)
                    ·
                      rfl

theorem cell22_1116887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_1116887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116887 prefixEnd_1116887 := by exact prefixLift 1116887
  have htrace : WordTrace (prefixWord ++ tailWord_1116887) baseStart_1116887 baseEnd_1116887 := by
    simpa [prefixWord, tailWord_1116887, baseEnd_1116887] using wordTrace_append hprefix tailTrace_1116887
  have hstable : (prefixWord ++ tailWord_1116887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116887).length < 2 ^ (prefixWord ++ tailWord_1116887).sum := by decide
  have hdescent : baseEnd_1116887 < baseStart_1116887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116911 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 8]
def baseStart_1116911 : Nat := 118140960795 + 1116911 * 2 ^ 59
def prefixEnd_1116911 : Nat := 4983230072969 + 3 ^ 40 * 1116911 * 2
def baseEnd_1116911 : Nat := 127447153620885514283539

theorem tailTrace_1116911 : CollatzResearch.WordTrace tailWord_1116911 prefixEnd_1116911 127447153620885514283539 := by
  unfold tailWord_1116911
  simp only [CollatzResearch.WordTrace]
  refine ⟨40737090856629675057270587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27158060571086450038180391 40737090856629675057270587)
  ·
    refine ⟨61105636284944512585905881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40737090856629675057270587 61105636284944512585905881)
    ·
      refine ⟨45829227213708384439429411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61105636284944512585905881 45829227213708384439429411)
      ·
        refine ⟨68743840820562576659144117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45829227213708384439429411 68743840820562576659144117)
        ·
          refine ⟨6444735076927741561794761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68743840820562576659144117 6444735076927741561794761)
          ·
            refine ⟨4833551307695806171346071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6444735076927741561794761 4833551307695806171346071)
            ·
              refine ⟨7250326961543709257019107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4833551307695806171346071 7250326961543709257019107)
              ·
                refine ⟨10875490442315563885528661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7250326961543709257019107 10875490442315563885528661)
                ·
                  refine ⟨127447153620885514283539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10875490442315563885528661 127447153620885514283539)
                  ·
                    rfl

theorem cell22_1116911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 8].length) (baseStart_1116911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116911 prefixEnd_1116911 := by exact prefixLift 1116911
  have htrace : WordTrace (prefixWord ++ tailWord_1116911) baseStart_1116911 baseEnd_1116911 := by
    simpa [prefixWord, tailWord_1116911, baseEnd_1116911] using wordTrace_append hprefix tailTrace_1116911
  have hstable : (prefixWord ++ tailWord_1116911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116911).length < 2 ^ (prefixWord ++ tailWord_1116911).sum := by decide
  have hdescent : baseEnd_1116911 < baseStart_1116911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116913 : List Nat := [1, 2, 2, 2, 2, 2, 2, 4, 1, 4]
def baseStart_1116913 : Nat := 118140960795 + 1116913 * 2 ^ 59
def prefixEnd_1116913 : Nat := 4983230072969 + 3 ^ 40 * 1116913 * 2
def baseEnd_1116913 : Nat := 382342145503529204300611

theorem tailTrace_1116913 : CollatzResearch.WordTrace tailWord_1116913 prefixEnd_1116913 382342145503529204300611 := by
  unfold tailWord_1116913
  simp only [CollatzResearch.WordTrace]
  refine ⟨40737163802622429398843393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27158109201748286265895595 40737163802622429398843393)
  ·
    refine ⟨30552872851966822049132545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40737163802622429398843393 30552872851966822049132545)
    ·
      refine ⟨22914654638975116536849409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30552872851966822049132545 22914654638975116536849409)
      ·
        refine ⟨17185990979231337402637057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22914654638975116536849409 17185990979231337402637057)
        ·
          refine ⟨12889493234423503051977793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17185990979231337402637057 12889493234423503051977793)
          ·
            refine ⟨9667119925817627288983345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12889493234423503051977793 9667119925817627288983345)
            ·
              refine ⟨7250339944363220466737509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9667119925817627288983345 7250339944363220466737509)
              ·
                refine ⟨1359438739568103837513283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7250339944363220466737509 1359438739568103837513283)
                ·
                  refine ⟨2039158109352155756269925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359438739568103837513283 2039158109352155756269925)
                  ·
                    refine ⟨382342145503529204300611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2039158109352155756269925 382342145503529204300611)
                    ·
                      rfl

theorem cell22_1116913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_1116913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116913 prefixEnd_1116913 := by exact prefixLift 1116913
  have htrace : WordTrace (prefixWord ++ tailWord_1116913) baseStart_1116913 baseEnd_1116913 := by
    simpa [prefixWord, tailWord_1116913, baseEnd_1116913] using wordTrace_append hprefix tailTrace_1116913
  have hstable : (prefixWord ++ tailWord_1116913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116913).length < 2 ^ (prefixWord ++ tailWord_1116913).sum := by decide
  have hdescent : baseEnd_1116913 < baseStart_1116913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116943 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 4, 3]
def baseStart_1116943 : Nat := 118140960795 + 1116943 * 2 ^ 59
def prefixEnd_1116943 : Nat := 4983230072969 + 3 ^ 40 * 1116943 * 2
def baseEnd_1116943 : Nat := 382352415116619126050519

theorem tailTrace_1116943 : CollatzResearch.WordTrace tailWord_1116943 prefixEnd_1116943 382352415116619126050519 := by
  unfold tailWord_1116943
  simp only [CollatzResearch.WordTrace]
  refine ⟨40738257992513744522435483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27158838661675829681623655 40738257992513744522435483)
  ·
    refine ⟨61107386988770616783653225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40738257992513744522435483 61107386988770616783653225)
    ·
      refine ⟨45830540241577962587739919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61107386988770616783653225 45830540241577962587739919)
      ·
        refine ⟨68745810362366943881609879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45830540241577962587739919 68745810362366943881609879)
        ·
          refine ⟨103118715543550415822414819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68745810362366943881609879 103118715543550415822414819)
          ·
            refine ⟨154678073315325623733622229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103118715543550415822414819 154678073315325623733622229)
            ·
              refine ⟨3625267343327944306256771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 154678073315325623733622229 3625267343327944306256771)
              ·
                refine ⟨5437901014991916459385157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3625267343327944306256771 5437901014991916459385157)
                ·
                  refine ⟨1019606440310984336134717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5437901014991916459385157 1019606440310984336134717)
                  ·
                    refine ⟨382352415116619126050519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1019606440310984336134717 382352415116619126050519)
                    ·
                      rfl

theorem cell22_1116943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 3].length) (baseStart_1116943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116943 prefixEnd_1116943 := by exact prefixLift 1116943
  have htrace : WordTrace (prefixWord ++ tailWord_1116943) baseStart_1116943 baseEnd_1116943 := by
    simpa [prefixWord, tailWord_1116943, baseEnd_1116943] using wordTrace_append hprefix tailTrace_1116943
  have hstable : (prefixWord ++ tailWord_1116943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116943).length < 2 ^ (prefixWord ++ tailWord_1116943).sum := by decide
  have hdescent : baseEnd_1116943 < baseStart_1116943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116960 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 1, 5]
def baseStart_1116960 : Nat := 118140960795 + 1116960 * 2 ^ 59
def prefixEnd_1116960 : Nat := 4983230072969 + 3 ^ 40 * 1116960 * 2
def baseEnd_1116960 : Nat := 382358234564036748375467

theorem tailTrace_1116960 : CollatzResearch.WordTrace tailWord_1116960 prefixEnd_1116960 382358234564036748375467 := by
  unfold tailWord_1116960
  simp only [CollatzResearch.WordTrace]
  refine ⟨20369439016726078212902167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27159252022301437617202889 20369439016726078212902167)
  ·
    refine ⟨30554158525089117319353251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20369439016726078212902167 30554158525089117319353251)
    ·
      refine ⟨45831237787633675979029877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30554158525089117319353251 45831237787633675979029877)
      ·
        refine ⟨4296678542590657123034051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45831237787633675979029877 4296678542590657123034051)
        ·
          refine ⟨6445017813885985684551077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4296678542590657123034051 6445017813885985684551077)
          ·
            refine ⟨1208440840103622315853327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6445017813885985684551077 1208440840103622315853327)
            ·
              refine ⟨1812661260155433473779991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208440840103622315853327 1812661260155433473779991)
              ·
                refine ⟨2718991890233150210669987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1812661260155433473779991 2718991890233150210669987)
                ·
                  refine ⟨4078487835349725316004981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718991890233150210669987 4078487835349725316004981)
                  ·
                    refine ⟨382358234564036748375467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4078487835349725316004981 382358234564036748375467)
                    ·
                      rfl

theorem cell22_1116960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 1, 5].length) (baseStart_1116960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116960 prefixEnd_1116960 := by exact prefixLift 1116960
  have htrace : WordTrace (prefixWord ++ tailWord_1116960) baseStart_1116960 baseEnd_1116960 := by
    simpa [prefixWord, tailWord_1116960, baseEnd_1116960] using wordTrace_append hprefix tailTrace_1116960
  have hstable : (prefixWord ++ tailWord_1116960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116960).length < 2 ^ (prefixWord ++ tailWord_1116960).sum := by decide
  have hdescent : baseEnd_1116960 < baseStart_1116960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116990 : List Nat := [4, 2, 1, 2, 3, 2, 8]
def baseStart_1116990 : Nat := 118140960795 + 1116990 * 2 ^ 59
def prefixEnd_1116990 : Nat := 4983230072969 + 3 ^ 40 * 1116990 * 2
def baseEnd_1116990 : Nat := 14161796451004691486125

theorem tailTrace_1116990 : CollatzResearch.WordTrace tailWord_1116990 prefixEnd_1116990 14161796451004691486125 := by
  unfold tailWord_1116990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5092496527917933943674553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27159981482228981032930949 5092496527917933943674553)
  ·
    refine ⟨3819372395938450457755915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5092496527917933943674553 3819372395938450457755915)
    ·
      refine ⟨5729058593907675686633873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3819372395938450457755915 5729058593907675686633873)
      ·
        refine ⟨4296793945430756764975405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5729058593907675686633873 4296793945430756764975405)
        ·
          refine ⟨1611297729536533786865777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4296793945430756764975405 1611297729536533786865777)
          ·
            refine ⟨1208473297152400340149333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1611297729536533786865777 1208473297152400340149333)
            ·
              refine ⟨14161796451004691486125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1208473297152400340149333 14161796451004691486125)
              ·
                rfl

theorem cell22_1116990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 8].length) (baseStart_1116990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116990 prefixEnd_1116990 := by exact prefixLift 1116990
  have htrace : WordTrace (prefixWord ++ tailWord_1116990) baseStart_1116990 baseEnd_1116990 := by
    simpa [prefixWord, tailWord_1116990, baseEnd_1116990] using wordTrace_append hprefix tailTrace_1116990
  have hstable : (prefixWord ++ tailWord_1116990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116990).length < 2 ^ (prefixWord ++ tailWord_1116990).sum := by decide
  have hdescent : baseEnd_1116990 < baseStart_1116990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1116996 : List Nat := [2, 3, 4, 2, 1, 1, 3, 2, 4]
def baseStart_1116996 : Nat := 118140960795 + 1116996 * 2 ^ 59
def prefixEnd_1116996 : Nat := 4983230072969 + 3 ^ 40 * 1116996 * 2
def baseEnd_1116996 : Nat := 127456852699914884825119

theorem tailTrace_1116996 : CollatzResearch.WordTrace tailWord_1116996 prefixEnd_1116996 127456852699914884825119 := by
  unfold tailWord_1116996
  simp only [CollatzResearch.WordTrace]
  refine ⟨20370095530660867287057421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27160127374214489716076561 20370095530660867287057421)
  ·
    refine ⟨7638785823997825232646533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20370095530660867287057421 7638785823997825232646533)
    ·
      refine ⟨1432272341999592231121225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7638785823997825232646533 1432272341999592231121225)
      ·
        refine ⟨1074204256499694173340919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1432272341999592231121225 1074204256499694173340919)
        ·
          refine ⟨1611306384749541260011379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1074204256499694173340919 1611306384749541260011379)
          ·
            refine ⟨2416959577124311890017069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611306384749541260011379 2416959577124311890017069)
            ·
              refine ⟨906359841421616958756401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2416959577124311890017069 906359841421616958756401)
              ·
                refine ⟨679769881066212719067301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906359841421616958756401 679769881066212719067301)
                ·
                  refine ⟨127456852699914884825119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 679769881066212719067301 127456852699914884825119)
                  ·
                    rfl

theorem cell22_1116996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_1116996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1116996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1116996 prefixEnd_1116996 := by exact prefixLift 1116996
  have htrace : WordTrace (prefixWord ++ tailWord_1116996) baseStart_1116996 baseEnd_1116996 := by
    simpa [prefixWord, tailWord_1116996, baseEnd_1116996] using wordTrace_append hprefix tailTrace_1116996
  have hstable : (prefixWord ++ tailWord_1116996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1116996).length < 2 ^ (prefixWord ++ tailWord_1116996).sum := by decide
  have hdescent : baseEnd_1116996 < baseStart_1116996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1116996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117112 : List Nat := [2, 1, 2, 1, 2, 4, 3, 2, 2, 3]
def baseStart_1117112 : Nat := 118140960795 + 1117112 * 2 ^ 59
def prefixEnd_1117112 : Nat := 4983230072969 + 3 ^ 40 * 1117112 * 2
def baseEnd_1117112 : Nat := 382410267270359018575001

theorem tailTrace_1117112 : CollatzResearch.WordTrace tailWord_1117112 prefixEnd_1117112 382410267270359018575001 := by
  unfold tailWord_1117112
  simp only [CollatzResearch.WordTrace]
  refine ⟨20372210964450743192668795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27162947952600990923558393 20372210964450743192668795)
  ·
    refine ⟨30558316446676114789003193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20372210964450743192668795 30558316446676114789003193)
    ·
      refine ⟨22918737335007086091752395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30558316446676114789003193 22918737335007086091752395)
      ·
        refine ⟨34378106002510629137628593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22918737335007086091752395 34378106002510629137628593)
        ·
          refine ⟨25783579501882971853221445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34378106002510629137628593 25783579501882971853221445)
          ·
            refine ⟨4834421156603057222479021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25783579501882971853221445 4834421156603057222479021)
            ·
              refine ⟨1812907933726146458429633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4834421156603057222479021 1812907933726146458429633)
              ·
                refine ⟨1359680950294609843822225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1812907933726146458429633 1359680950294609843822225)
                ·
                  refine ⟨1019760712720957382866669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1359680950294609843822225 1019760712720957382866669)
                  ·
                    refine ⟨382410267270359018575001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1019760712720957382866669 382410267270359018575001)
                    ·
                      rfl

theorem cell22_1117112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_1117112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117112 prefixEnd_1117112 := by exact prefixLift 1117112
  have htrace : WordTrace (prefixWord ++ tailWord_1117112) baseStart_1117112 baseEnd_1117112 := by
    simpa [prefixWord, tailWord_1117112, baseEnd_1117112] using wordTrace_append hprefix tailTrace_1117112
  have hstable : (prefixWord ++ tailWord_1117112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117112).length < 2 ^ (prefixWord ++ tailWord_1117112).sum := by decide
  have hdescent : baseEnd_1117112 < baseStart_1117112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117133 : List Nat := [1, 6, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1117133 : Nat := 118140960795 + 1117133 * 2 ^ 59
def prefixEnd_1117133 : Nat := 4983230072969 + 3 ^ 40 * 1117133 * 2
def baseEnd_1117133 : Nat := 382417455999521963799937

theorem tailTrace_1117133 : CollatzResearch.WordTrace tailWord_1117133 prefixEnd_1117133 382417455999521963799937 := by
  unfold tailWord_1117133
  simp only [CollatzResearch.WordTrace]
  refine ⟨40745187861825406971852053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27163458574550271314568035 40745187861825406971852053)
  ·
    refine ⟨1909930681023065951805565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40745187861825406971852053 1909930681023065951805565)
    ·
      refine ⟨716224005383649731927087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1909930681023065951805565 716224005383649731927087)
      ·
        refine ⟨1074336008075474597890631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 716224005383649731927087 1074336008075474597890631)
        ·
          refine ⟨1611504012113211896835947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1074336008075474597890631 1611504012113211896835947)
          ·
            refine ⟨2417256018169817845253921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611504012113211896835947 2417256018169817845253921)
            ·
              refine ⟨1812942013627363383940441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2417256018169817845253921 1812942013627363383940441)
              ·
                refine ⟨1359706510220522537955331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1812942013627363383940441 1359706510220522537955331)
                ·
                  refine ⟨2039559765330783806932997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359706510220522537955331 2039559765330783806932997)
                  ·
                    refine ⟨382417455999521963799937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2039559765330783806932997 382417455999521963799937)
                    ·
                      rfl

theorem cell22_1117133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1117133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117133 prefixEnd_1117133 := by exact prefixLift 1117133
  have htrace : WordTrace (prefixWord ++ tailWord_1117133) baseStart_1117133 baseEnd_1117133 := by
    simpa [prefixWord, tailWord_1117133, baseEnd_1117133] using wordTrace_append hprefix tailTrace_1117133
  have hstable : (prefixWord ++ tailWord_1117133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117133).length < 2 ^ (prefixWord ++ tailWord_1117133).sum := by decide
  have hdescent : baseEnd_1117133 < baseStart_1117133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117142 : List Nat := [5, 2, 1, 1, 2, 2, 1, 8]
def baseStart_1117142 : Nat := 118140960795 + 1117142 * 2 ^ 59
def prefixEnd_1117142 : Nat := 4983230072969 + 3 ^ 40 * 1117142 * 2
def baseEnd_1117142 : Nat := 42491170764827660036101

theorem tailTrace_1117142 : CollatzResearch.WordTrace tailWord_1117142 prefixEnd_1117142 42491170764827660036101 := by
  unfold tailWord_1117142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2546594757424550094308105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27163677412528534339286453 2546594757424550094308105)
  ·
    refine ⟨1909946068068412570731079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2546594757424550094308105 1909946068068412570731079)
    ·
      refine ⟨2864919102102618856096619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1909946068068412570731079 2864919102102618856096619)
      ·
        refine ⟨4297378653153928284144929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2864919102102618856096619 4297378653153928284144929)
        ·
          refine ⟨3223033989865446213108697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4297378653153928284144929 3223033989865446213108697)
          ·
            refine ⟨2417275492399084659831523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3223033989865446213108697 2417275492399084659831523)
            ·
              refine ⟨3625913238598626989747285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2417275492399084659831523 3625913238598626989747285)
              ·
                refine ⟨42491170764827660036101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3625913238598626989747285 42491170764827660036101)
                ·
                  rfl

theorem cell22_1117142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_1117142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117142 prefixEnd_1117142 := by exact prefixLift 1117142
  have htrace : WordTrace (prefixWord ++ tailWord_1117142) baseStart_1117142 baseEnd_1117142 := by
    simpa [prefixWord, tailWord_1117142, baseEnd_1117142] using wordTrace_append hprefix tailTrace_1117142
  have hstable : (prefixWord ++ tailWord_1117142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117142).length < 2 ^ (prefixWord ++ tailWord_1117142).sum := by decide
  have hdescent : baseEnd_1117142 < baseStart_1117142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117174 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_1117174 : Nat := 118140960795 + 1117174 * 2 ^ 59
def prefixEnd_1117174 : Nat := 4983230072969 + 3 ^ 40 * 1117174 * 2
def baseEnd_1117174 : Nat := 382431491137411523524811

theorem tailTrace_1117174 : CollatzResearch.WordTrace tailWord_1117174 prefixEnd_1117174 382431491137411523524811 := by
  unfold tailWord_1117174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2546667703417304435880911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27164455503117913982729717 2546667703417304435880911)
  ·
    refine ⟨3820001555125956653821367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2546667703417304435880911 3820001555125956653821367)
    ·
      refine ⟨5730002332688934980732051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3820001555125956653821367 5730002332688934980732051)
      ·
        refine ⟨8595003499033402471098077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5730002332688934980732051 8595003499033402471098077)
        ·
          refine ⟨3223126312137525926661779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8595003499033402471098077 3223126312137525926661779)
          ·
            refine ⟨4834689468206288889992669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3223126312137525926661779 4834689468206288889992669)
            ·
              refine ⟨1813008550577358333747251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4834689468206288889992669 1813008550577358333747251)
              ·
                refine ⟨2719512825866037500620877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1813008550577358333747251 2719512825866037500620877)
                ·
                  refine ⟨1019817309699764062732829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2719512825866037500620877 1019817309699764062732829)
                  ·
                    refine ⟨382431491137411523524811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1019817309699764062732829 382431491137411523524811)
                    ·
                      rfl

theorem cell22_1117174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_1117174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117174 prefixEnd_1117174 := by exact prefixLift 1117174
  have htrace : WordTrace (prefixWord ++ tailWord_1117174) baseStart_1117174 baseEnd_1117174 := by
    simpa [prefixWord, tailWord_1117174, baseEnd_1117174] using wordTrace_append hprefix tailTrace_1117174
  have hstable : (prefixWord ++ tailWord_1117174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117174).length < 2 ^ (prefixWord ++ tailWord_1117174).sum := by decide
  have hdescent : baseEnd_1117174 < baseStart_1117174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117183 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 1, 10]
def baseStart_1117183 : Nat := 118140960795 + 1117183 * 2 ^ 59
def prefixEnd_1117183 : Nat := 4983230072969 + 3 ^ 40 * 1117183 * 2
def baseEnd_1117183 : Nat := 382434572021338500049783

theorem tailTrace_1117183 : CollatzResearch.WordTrace tailWord_1117183 prefixEnd_1117183 382434572021338500049783 := by
  unfold tailWord_1117183
  simp only [CollatzResearch.WordTrace]
  refine ⟨40747011511644265511172203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27164674341096177007448135 40747011511644265511172203)
  ·
    refine ⟨61120517267466398266758305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40747011511644265511172203 61120517267466398266758305)
    ·
      refine ⟨45840387950599798700068729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61120517267466398266758305 45840387950599798700068729)
      ·
        refine ⟨34380290962949849025051547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45840387950599798700068729 34380290962949849025051547)
        ·
          refine ⟨51570436444424773537577321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34380290962949849025051547 51570436444424773537577321)
          ·
            refine ⟨38677827333318580153182991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51570436444424773537577321 38677827333318580153182991)
            ·
              refine ⟨58016740999977870229774487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38677827333318580153182991 58016740999977870229774487)
              ·
                refine ⟨87025111499966805344661731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58016740999977870229774487 87025111499966805344661731)
                ·
                  refine ⟨130537667249950208016992597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87025111499966805344661731 130537667249950208016992597)
                  ·
                    refine ⟨382434572021338500049783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 130537667249950208016992597 382434572021338500049783)
                    ·
                      rfl

theorem cell22_1117183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_1117183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117183 prefixEnd_1117183 := by exact prefixLift 1117183
  have htrace : WordTrace (prefixWord ++ tailWord_1117183) baseStart_1117183 baseEnd_1117183 := by
    simpa [prefixWord, tailWord_1117183, baseEnd_1117183] using wordTrace_append hprefix tailTrace_1117183
  have hstable : (prefixWord ++ tailWord_1117183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117183).length < 2 ^ (prefixWord ++ tailWord_1117183).sum := by decide
  have hdescent : baseEnd_1117183 < baseStart_1117183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117232 : List Nat := [2, 1, 1, 1, 2, 4, 3, 4, 4]
def baseStart_1117232 : Nat := 118140960795 + 1117232 * 2 ^ 59
def prefixEnd_1117232 : Nat := 4983230072969 + 3 ^ 40 * 1117232 * 2
def baseEnd_1117232 : Nat := 127483781907572901858211

theorem tailTrace_1117232 : CollatzResearch.WordTrace tailWord_1117232 prefixEnd_1117232 127483781907572901858211 := by
  unfold tailWord_1117232
  simp only [CollatzResearch.WordTrace]
  refine ⟨20374399344233373439852975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27165865792311164586470633 20374399344233373439852975)
  ·
    refine ⟨30561599016350060159779463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20374399344233373439852975 30561599016350060159779463)
    ·
      refine ⟨45842398524525090239669195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30561599016350060159779463 45842398524525090239669195)
      ·
        refine ⟨68763597786787635359503793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45842398524525090239669195 68763597786787635359503793)
        ·
          refine ⟨51572698340090726519627845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68763597786787635359503793 51572698340090726519627845)
          ·
            refine ⟨9669880938767011222430221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51572698340090726519627845 9669880938767011222430221)
            ·
              refine ⟨3626205352037629208411333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9669880938767011222430221 3626205352037629208411333)
              ·
                refine ⟨679913503507055476577125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3626205352037629208411333 679913503507055476577125)
                ·
                  refine ⟨127483781907572901858211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 679913503507055476577125 127483781907572901858211)
                  ·
                    rfl

theorem cell22_1117232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 4].length) (baseStart_1117232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117232 prefixEnd_1117232 := by exact prefixLift 1117232
  have htrace : WordTrace (prefixWord ++ tailWord_1117232) baseStart_1117232 baseEnd_1117232 := by
    simpa [prefixWord, tailWord_1117232, baseEnd_1117232] using wordTrace_append hprefix tailTrace_1117232
  have hstable : (prefixWord ++ tailWord_1117232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117232).length < 2 ^ (prefixWord ++ tailWord_1117232).sum := by decide
  have hdescent : baseEnd_1117232 < baseStart_1117232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117343 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 3, 3]
def baseStart_1117343 : Nat := 118140960795 + 1117343 * 2 ^ 59
def prefixEnd_1117343 : Nat := 4983230072969 + 3 ^ 40 * 1117343 * 2
def baseEnd_1117343 : Nat := 382489343291151416049293

theorem tailTrace_1117343 : CollatzResearch.WordTrace tailWord_1117343 prefixEnd_1117343 382489343291151416049293 := by
  unfold tailWord_1117343
  simp only [CollatzResearch.WordTrace]
  refine ⟨40752847191064612836996683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27168564794043075224664455 40752847191064612836996683)
  ·
    refine ⟨61129270786596919255495025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40752847191064612836996683 61129270786596919255495025)
    ·
      refine ⟨45846953089947689441621269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61129270786596919255495025 45846953089947689441621269)
      ·
        refine ⟨2149075926091297942575997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45846953089947689441621269 2149075926091297942575997)
        ·
          refine ⟨805903472284236728465999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2149075926091297942575997 805903472284236728465999)
          ·
            refine ⟨1208855208426355092698999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805903472284236728465999 1208855208426355092698999)
            ·
              refine ⟨1813282812639532639048499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208855208426355092698999 1813282812639532639048499)
              ·
                refine ⟨2719924218959298958572749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1813282812639532639048499 2719924218959298958572749)
                ·
                  refine ⟨1019971582109737109464781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2719924218959298958572749 1019971582109737109464781)
                  ·
                    refine ⟨382489343291151416049293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1019971582109737109464781 382489343291151416049293)
                    ·
                      rfl

theorem cell22_1117343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 3, 3].length) (baseStart_1117343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117343 prefixEnd_1117343 := by exact prefixLift 1117343
  have htrace : WordTrace (prefixWord ++ tailWord_1117343) baseStart_1117343 baseEnd_1117343 := by
    simpa [prefixWord, tailWord_1117343, baseEnd_1117343] using wordTrace_append hprefix tailTrace_1117343
  have hstable : (prefixWord ++ tailWord_1117343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117343).length < 2 ^ (prefixWord ++ tailWord_1117343).sum := by decide
  have hdescent : baseEnd_1117343 < baseStart_1117343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117369 : List Nat := [1, 2, 1, 4, 1, 3, 3, 2, 1, 4]
def baseStart_1117369 : Nat := 118140960795 + 1117369 * 2 ^ 59
def prefixEnd_1117369 : Nat := 4983230072969 + 3 ^ 40 * 1117369 * 2
def baseEnd_1117369 : Nat := 382498243622496014899213

theorem tailTrace_1117369 : CollatzResearch.WordTrace tailWord_1117369 prefixEnd_1117369 382498243622496014899213 := by
  unfold tailWord_1117369
  simp only [CollatzResearch.WordTrace]
  refine ⟨40753795488970419277443161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27169196992646946184962107 40753795488970419277443161)
  ·
    refine ⟨30565346616727814458082371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40753795488970419277443161 30565346616727814458082371)
    ·
      refine ⟨45848019925091721687123557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30565346616727814458082371 45848019925091721687123557)
      ·
        refine ⟨8596503735954697816335667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45848019925091721687123557 8596503735954697816335667)
        ·
          refine ⟨12894755603932046724503501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8596503735954697816335667 12894755603932046724503501)
          ·
            refine ⟨4835533351474517521688813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12894755603932046724503501 4835533351474517521688813)
            ·
              refine ⟨1813325006802944070633305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4835533351474517521688813 1813325006802944070633305)
              ·
                refine ⟨1359993755102208052974979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1813325006802944070633305 1359993755102208052974979)
                ·
                  refine ⟨2039990632653312079462469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359993755102208052974979 2039990632653312079462469)
                  ·
                    refine ⟨382498243622496014899213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2039990632653312079462469 382498243622496014899213)
                    ·
                      rfl

theorem cell22_1117369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_1117369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117369 prefixEnd_1117369 := by exact prefixLift 1117369
  have htrace : WordTrace (prefixWord ++ tailWord_1117369) baseStart_1117369 baseEnd_1117369 := by
    simpa [prefixWord, tailWord_1117369, baseEnd_1117369] using wordTrace_append hprefix tailTrace_1117369
  have hstable : (prefixWord ++ tailWord_1117369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117369).length < 2 ^ (prefixWord ++ tailWord_1117369).sum := by decide
  have hdescent : baseEnd_1117369 < baseStart_1117369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117386 : List Nat := [3, 1, 2, 1, 3, 3, 3, 1, 1, 4]
def baseStart_1117386 : Nat := 118140960795 + 1117386 * 2 ^ 59
def prefixEnd_1117386 : Nat := 4983230072969 + 3 ^ 40 * 1117386 * 2
def baseEnd_1117386 : Nat := 382504063069913637224161

theorem tailTrace_1117386 : CollatzResearch.WordTrace tailWord_1117386 prefixEnd_1117386 382504063069913637224161 := by
  unfold tailWord_1117386
  simp only [CollatzResearch.WordTrace]
  refine ⟨10188603882477207795203003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27169610353272554120541341 10188603882477207795203003)
  ·
    refine ⟨15282905823715811692804505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10188603882477207795203003 15282905823715811692804505)
    ·
      refine ⟨11462179367786858769603379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15282905823715811692804505 11462179367786858769603379)
      ·
        refine ⟨17193269051680288154405069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11462179367786858769603379 17193269051680288154405069)
        ·
          refine ⟨6447475894380108057901901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17193269051680288154405069 6447475894380108057901901)
          ·
            refine ⟨2417803460392540521713213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6447475894380108057901901 2417803460392540521713213)
            ·
              refine ⟨906676297647202695642455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2417803460392540521713213 906676297647202695642455)
              ·
                refine ⟨1360014446470804043463683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906676297647202695642455 1360014446470804043463683)
                ·
                  refine ⟨2040021669706206065195525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360014446470804043463683 2040021669706206065195525)
                  ·
                    refine ⟨382504063069913637224161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2040021669706206065195525 382504063069913637224161)
                    ·
                      rfl

theorem cell22_1117386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_1117386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117386 prefixEnd_1117386 := by exact prefixLift 1117386
  have htrace : WordTrace (prefixWord ++ tailWord_1117386) baseStart_1117386 baseEnd_1117386 := by
    simpa [prefixWord, tailWord_1117386, baseEnd_1117386] using wordTrace_append hprefix tailTrace_1117386
  have hstable : (prefixWord ++ tailWord_1117386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117386).length < 2 ^ (prefixWord ++ tailWord_1117386).sum := by decide
  have hdescent : baseEnd_1117386 < baseStart_1117386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117399 : List Nat := [1, 1, 3, 2, 1, 2, 3, 4, 2, 3]
def baseStart_1117399 : Nat := 118140960795 + 1117399 * 2 ^ 59
def prefixEnd_1117399 : Nat := 4983230072969 + 3 ^ 40 * 1117399 * 2
def baseEnd_1117399 : Nat := 382508513235585936649121

theorem tailTrace_1117399 : CollatzResearch.WordTrace tailWord_1117399 prefixEnd_1117399 382508513235585936649121 := by
  unfold tailWord_1117399
  simp only [CollatzResearch.WordTrace]
  refine ⟨40754889678861734401035251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27169926452574489600690167 40754889678861734401035251)
  ·
    refine ⟨61132334518292601601552877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40754889678861734401035251 61132334518292601601552877)
    ·
      refine ⟨22924625444359725600582329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61132334518292601601552877 22924625444359725600582329)
      ·
        refine ⟨17193469083269794200436747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22924625444359725600582329 17193469083269794200436747)
        ·
          refine ⟨25790203624904691300655121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17193469083269794200436747 25790203624904691300655121)
          ·
            refine ⟨19342652718678518475491341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25790203624904691300655121 19342652718678518475491341)
            ·
              refine ⟨7253494769504444428309253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19342652718678518475491341 7253494769504444428309253)
              ·
                refine ⟨1360030269282083330307985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7253494769504444428309253 1360030269282083330307985)
                ·
                  refine ⟨1020022701961562497730989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1360030269282083330307985 1020022701961562497730989)
                  ·
                    refine ⟨382508513235585936649121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1020022701961562497730989 382508513235585936649121)
                    ·
                      rfl

theorem cell22_1117399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_1117399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117399 prefixEnd_1117399 := by exact prefixLift 1117399
  have htrace : WordTrace (prefixWord ++ tailWord_1117399) baseStart_1117399 baseEnd_1117399 := by
    simpa [prefixWord, tailWord_1117399, baseEnd_1117399] using wordTrace_append hprefix tailTrace_1117399
  have hstable : (prefixWord ++ tailWord_1117399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117399).length < 2 ^ (prefixWord ++ tailWord_1117399).sum := by decide
  have hdescent : baseEnd_1117399 < baseStart_1117399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117412 : List Nat := [2, 3, 1, 1, 1, 2, 5, 7]
def baseStart_1117412 : Nat := 118140960795 + 1117412 * 2 ^ 59
def prefixEnd_1117412 : Nat := 4983230072969 + 3 ^ 40 * 1117412 * 2
def baseEnd_1117412 : Nat := 42501440377917581786009

theorem tailTrace_1117412 : CollatzResearch.WordTrace tailWord_1117412 prefixEnd_1117412 42501440377917581786009 := by
  unfold tailWord_1117412
  simp only [CollatzResearch.WordTrace]
  refine ⟨20377681913907318810629245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27170242551876425080838993 20377681913907318810629245)
  ·
    refine ⟨7641630717715244553985967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20377681913907318810629245 7641630717715244553985967)
    ·
      refine ⟨11462446076572866830978951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7641630717715244553985967 11462446076572866830978951)
      ·
        refine ⟨17193669114859300246468427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11462446076572866830978951 17193669114859300246468427)
        ·
          refine ⟨25790503672288950369702641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17193669114859300246468427 25790503672288950369702641)
          ·
            refine ⟨19342877754216712777276981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25790503672288950369702641 19342877754216712777276981)
            ·
              refine ⟨1813394789457816822869717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19342877754216712777276981 1813394789457816822869717)
              ·
                refine ⟨42501440377917581786009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1813394789457816822869717 42501440377917581786009)
                ·
                  rfl

theorem cell22_1117412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 7].length) (baseStart_1117412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117412 prefixEnd_1117412 := by exact prefixLift 1117412
  have htrace : WordTrace (prefixWord ++ tailWord_1117412) baseStart_1117412 baseEnd_1117412 := by
    simpa [prefixWord, tailWord_1117412, baseEnd_1117412] using wordTrace_append hprefix tailTrace_1117412
  have hstable : (prefixWord ++ tailWord_1117412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117412).length < 2 ^ (prefixWord ++ tailWord_1117412).sum := by decide
  have hdescent : baseEnd_1117412 < baseStart_1117412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117457 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 7]
def baseStart_1117457 : Nat := 118140960795 + 1117457 * 2 ^ 59
def prefixEnd_1117457 : Nat := 4983230072969 + 3 ^ 40 * 1117457 * 2
def baseEnd_1117457 : Nat := 127509455940297706232981

theorem tailTrace_1117457 : CollatzResearch.WordTrace tailWord_1117457 prefixEnd_1117457 127509455940297706232981 := by
  unfold tailWord_1117457
  simp only [CollatzResearch.WordTrace]
  refine ⟨40757005112651610306646625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27171336741767740204431083 40757005112651610306646625)
  ·
    refine ⟨30567753834488707729984969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40757005112651610306646625 30567753834488707729984969)
    ·
      refine ⟨22925815375866530797488727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30567753834488707729984969 22925815375866530797488727)
      ·
        refine ⟨34388723063799796196233091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22925815375866530797488727 34388723063799796196233091)
        ·
          refine ⟨51583084595699694294349637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34388723063799796196233091 51583084595699694294349637)
          ·
            refine ⟨9671828361693692680190557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51583084595699694294349637 9671828361693692680190557)
            ·
              refine ⟨3626935635635134755071459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9671828361693692680190557 3626935635635134755071459)
              ·
                refine ⟨5440403453452702132607189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3626935635635134755071459 5440403453452702132607189)
                ·
                  refine ⟨127509455940297706232981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5440403453452702132607189 127509455940297706232981)
                  ·
                    rfl

theorem cell22_1117457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 7].length) (baseStart_1117457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117457 prefixEnd_1117457 := by exact prefixLift 1117457
  have htrace : WordTrace (prefixWord ++ tailWord_1117457) baseStart_1117457 baseEnd_1117457 := by
    simpa [prefixWord, tailWord_1117457, baseEnd_1117457] using wordTrace_append hprefix tailTrace_1117457
  have hstable : (prefixWord ++ tailWord_1117457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117457).length < 2 ^ (prefixWord ++ tailWord_1117457).sum := by decide
  have hdescent : baseEnd_1117457 < baseStart_1117457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117504 : List Nat := [2, 1, 1, 2, 2, 1, 3, 5, 1, 4]
def baseStart_1117504 : Nat := 118140960795 + 1117504 * 2 ^ 59
def prefixEnd_1117504 : Nat := 4983230072969 + 3 ^ 40 * 1117504 * 2
def baseEnd_1117504 : Nat := 382544456881400662773799

theorem tailTrace_1117504 : CollatzResearch.WordTrace tailWord_1117504 prefixEnd_1117504 382544456881400662773799 := by
  unfold tailWord_1117504
  simp only [CollatzResearch.WordTrace]
  refine ⟨20379359671740668666803783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27172479562320891555738377 20379359671740668666803783)
  ·
    refine ⟨30569039507611003000205675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20379359671740668666803783 30569039507611003000205675)
    ·
      refine ⟨45853559261416504500308513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30569039507611003000205675 45853559261416504500308513)
      ·
        refine ⟨34390169446062378375231385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45853559261416504500308513 34390169446062378375231385)
        ·
          refine ⟨25792627084546783781423539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34390169446062378375231385 25792627084546783781423539)
          ·
            refine ⟨38688940626820175672135309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25792627084546783781423539 38688940626820175672135309)
            ·
              refine ⟨14508352735057565877050741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38688940626820175672135309 14508352735057565877050741)
              ·
                refine ⟨1360158068911646800973507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14508352735057565877050741 1360158068911646800973507)
                ·
                  refine ⟨2040237103367470201460261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360158068911646800973507 2040237103367470201460261)
                  ·
                    refine ⟨382544456881400662773799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2040237103367470201460261 382544456881400662773799)
                    ·
                      rfl

theorem cell22_1117504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_1117504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117504 prefixEnd_1117504 := by exact prefixLift 1117504
  have htrace : WordTrace (prefixWord ++ tailWord_1117504) baseStart_1117504 baseEnd_1117504 := by
    simpa [prefixWord, tailWord_1117504, baseEnd_1117504] using wordTrace_append hprefix tailTrace_1117504
  have hstable : (prefixWord ++ tailWord_1117504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117504).length < 2 ^ (prefixWord ++ tailWord_1117504).sum := by decide
  have hdescent : baseEnd_1117504 < baseStart_1117504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117570 : List Nat := [3, 4, 2, 1, 1, 2, 1, 4, 4]
def baseStart_1117570 : Nat := 118140960795 + 1117570 * 2 ^ 59
def prefixEnd_1117570 : Nat := 4983230072969 + 3 ^ 40 * 1117570 * 2
def baseEnd_1117570 : Nat := 127522350010066163541199

theorem tailTrace_1117570 : CollatzResearch.WordTrace tailWord_1117570 prefixEnd_1117570 127522350010066163541199 := by
  unfold tailWord_1117570
  simp only [CollatzResearch.WordTrace]
  refine ⟨10190281640310557651377541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27174084374161487070340109 10190281640310557651377541)
  ·
    refine ⟨1910677807558229559633289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10190281640310557651377541 1910677807558229559633289)
    ·
      refine ⟨1433008355668672169724967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1910677807558229559633289 1433008355668672169724967)
      ·
        refine ⟨2149512533503008254587451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433008355668672169724967 2149512533503008254587451)
        ·
          refine ⟨3224268800254512381881177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2149512533503008254587451 3224268800254512381881177)
          ·
            refine ⟨2418201600190884286410883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3224268800254512381881177 2418201600190884286410883)
            ·
              refine ⟨3627302400286326429616325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2418201600190884286410883 3627302400286326429616325)
              ·
                refine ⟨680119200053686205553061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3627302400286326429616325 680119200053686205553061)
                ·
                  refine ⟨127522350010066163541199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 680119200053686205553061 127522350010066163541199)
                  ·
                    rfl

theorem cell22_1117570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_1117570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117570 prefixEnd_1117570 := by exact prefixLift 1117570
  have htrace : WordTrace (prefixWord ++ tailWord_1117570) baseStart_1117570 baseEnd_1117570 := by
    simpa [prefixWord, tailWord_1117570, baseEnd_1117570] using wordTrace_append hprefix tailTrace_1117570
  have hstable : (prefixWord ++ tailWord_1117570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117570).length < 2 ^ (prefixWord ++ tailWord_1117570).sum := by decide
  have hdescent : baseEnd_1117570 < baseStart_1117570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117594 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_1117594 : Nat := 118140960795 + 1117594 * 2 ^ 59
def prefixEnd_1117594 : Nat := 4983230072969 + 3 ^ 40 * 1117594 * 2
def baseEnd_1117594 : Nat := 382575265720670428023523

theorem tailTrace_1117594 : CollatzResearch.WordTrace tailWord_1117594 prefixEnd_1117594 382575265720670428023523 := by
  unfold tailWord_1117594
  simp only [CollatzResearch.WordTrace]
  refine ⟨10190500478288820676095959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27174667942103521802922557 10190500478288820676095959)
  ·
    refine ⟨15285750717433231014143939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10190500478288820676095959 15285750717433231014143939)
    ·
      refine ⟨22928626076149846521215909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15285750717433231014143939 22928626076149846521215909)
      ·
        refine ⟨4299117389278096222727983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22928626076149846521215909 4299117389278096222727983)
        ·
          refine ⟨6448676083917144334091975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4299117389278096222727983 6448676083917144334091975)
          ·
            refine ⟨9673014125875716501137963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6448676083917144334091975 9673014125875716501137963)
            ·
              refine ⟨14509521188813574751706945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9673014125875716501137963 14509521188813574751706945)
              ·
                refine ⟨10882140891610181063780209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14509521188813574751706945 10882140891610181063780209)
                ·
                  refine ⟨8161605668707635797835157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10882140891610181063780209 8161605668707635797835157)
                  ·
                    refine ⟨382575265720670428023523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8161605668707635797835157 382575265720670428023523)
                    ·
                      rfl

theorem cell22_1117594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_1117594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117594 prefixEnd_1117594 := by exact prefixLift 1117594
  have htrace : WordTrace (prefixWord ++ tailWord_1117594) baseStart_1117594 baseEnd_1117594 := by
    simpa [prefixWord, tailWord_1117594, baseEnd_1117594] using wordTrace_append hprefix tailTrace_1117594
  have hstable : (prefixWord ++ tailWord_1117594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117594).length < 2 ^ (prefixWord ++ tailWord_1117594).sum := by decide
  have hdescent : baseEnd_1117594 < baseStart_1117594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117624 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 2, 5]
def baseStart_1117624 : Nat := 118140960795 + 1117624 * 2 ^ 59
def prefixEnd_1117624 : Nat := 4983230072969 + 3 ^ 40 * 1117624 * 2
def baseEnd_1117624 : Nat := 382585535333760349773431

theorem tailTrace_1117624 : CollatzResearch.WordTrace tailWord_1117624 prefixEnd_1117624 382585535333760349773431 := by
  unfold tailWord_1117624
  simp only [CollatzResearch.WordTrace]
  refine ⟨20381548051523298913987963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27175397402031065218650617 20381548051523298913987963)
  ·
    refine ⟨30572322077284948370981945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20381548051523298913987963 30572322077284948370981945)
    ·
      refine ⟨22929241557963711278236459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30572322077284948370981945 22929241557963711278236459)
      ·
        refine ⟨34393862336945566917354689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22929241557963711278236459 34393862336945566917354689)
        ·
          refine ⟨25795396752709175188016017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34393862336945566917354689 25795396752709175188016017)
          ·
            refine ⟨19346547564531881391012013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25795396752709175188016017 19346547564531881391012013)
            ·
              refine ⟨7254955336699455521629505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19346547564531881391012013 7254955336699455521629505)
              ·
                refine ⟨5441216502524591641222129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7254955336699455521629505 5441216502524591641222129)
                ·
                  refine ⟨4080912376893443730916597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5441216502524591641222129 4080912376893443730916597)
                  ·
                    refine ⟨382585535333760349773431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4080912376893443730916597 382585535333760349773431)
                    ·
                      rfl

theorem cell22_1117624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_1117624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117624 prefixEnd_1117624 := by exact prefixLift 1117624
  have htrace : WordTrace (prefixWord ++ tailWord_1117624) baseStart_1117624 baseEnd_1117624 := by
    simpa [prefixWord, tailWord_1117624, baseEnd_1117624] using wordTrace_append hprefix tailTrace_1117624
  have hstable : (prefixWord ++ tailWord_1117624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117624).length < 2 ^ (prefixWord ++ tailWord_1117624).sum := by decide
  have hdescent : baseEnd_1117624 < baseStart_1117624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117656 : List Nat := [2, 1, 2, 2, 2, 1, 3, 4, 1, 4]
def baseStart_1117656 : Nat := 118140960795 + 1117656 * 2 ^ 59
def prefixEnd_1117656 : Nat := 4983230072969 + 3 ^ 40 * 1117656 * 2
def baseEnd_1117656 : Nat := 382596489587722932973333

theorem tailTrace_1117656 : CollatzResearch.WordTrace tailWord_1117656 prefixEnd_1117656 382596489587722932973333 := by
  unfold tailWord_1117656
  simp only [CollatzResearch.WordTrace]
  refine ⟨20382131619465333646570411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27176175492620444862093881 20382131619465333646570411)
  ·
    refine ⟨30573197429198000469855617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20382131619465333646570411 30573197429198000469855617)
    ·
      refine ⟨22929898071898500352391713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30573197429198000469855617 22929898071898500352391713)
      ·
        refine ⟨17197423553923875264293785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22929898071898500352391713 17197423553923875264293785)
        ·
          refine ⟨12898067665442906448220339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17197423553923875264293785 12898067665442906448220339)
          ·
            refine ⟨19347101498164359672330509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12898067665442906448220339 19347101498164359672330509)
            ·
              refine ⟨7255163061811634877123941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19347101498164359672330509 7255163061811634877123941)
              ·
                refine ⟨1360343074089681539460739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7255163061811634877123941 1360343074089681539460739)
                ·
                  refine ⟨2040514611134522309191109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360343074089681539460739 2040514611134522309191109)
                  ·
                    refine ⟨382596489587722932973333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2040514611134522309191109 382596489587722932973333)
                    ·
                      rfl

theorem cell22_1117656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_1117656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117656 prefixEnd_1117656 := by exact prefixLift 1117656
  have htrace : WordTrace (prefixWord ++ tailWord_1117656) baseStart_1117656 baseEnd_1117656 := by
    simpa [prefixWord, tailWord_1117656, baseEnd_1117656] using wordTrace_append hprefix tailTrace_1117656
  have hstable : (prefixWord ++ tailWord_1117656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117656).length < 2 ^ (prefixWord ++ tailWord_1117656).sum := by decide
  have hdescent : baseEnd_1117656 < baseStart_1117656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117694 : List Nat := [4, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_1117694 : Nat := 118140960795 + 1117694 * 2 ^ 59
def prefixEnd_1117694 : Nat := 4983230072969 + 3 ^ 40 * 1117694 * 2
def baseEnd_1117694 : Nat := 127536499254767833507739

theorem tailTrace_1117694 : CollatzResearch.WordTrace tailWord_1117694 prefixEnd_1117694 127536499254767833507739 := by
  unfold tailWord_1117694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5095706151599124972878017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27177099475195333188682757 5095706151599124972878017)
  ·
    refine ⟨3821779613699343729658513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5095706151599124972878017 3821779613699343729658513)
    ·
      refine ⟨2866334710274507797243885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3821779613699343729658513 2866334710274507797243885)
      ·
        refine ⟨1074875516352940423966457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2866334710274507797243885 1074875516352940423966457)
        ·
          refine ⟨806156637264705317974843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1074875516352940423966457 806156637264705317974843)
          ·
            refine ⟨1209234955897057976962265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806156637264705317974843 1209234955897057976962265)
            ·
              refine ⟨906926216922793482721699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1209234955897057976962265 906926216922793482721699)
              ·
                refine ⟨1360389325384190224082549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906926216922793482721699 1360389325384190224082549)
                ·
                  refine ⟨127536499254767833507739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1360389325384190224082549 127536499254767833507739)
                  ·
                    rfl

theorem cell22_1117694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_1117694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117694 prefixEnd_1117694 := by exact prefixLift 1117694
  have htrace : WordTrace (prefixWord ++ tailWord_1117694) baseStart_1117694 baseEnd_1117694 := by
    simpa [prefixWord, tailWord_1117694, baseEnd_1117694] using wordTrace_append hprefix tailTrace_1117694
  have hstable : (prefixWord ++ tailWord_1117694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117694).length < 2 ^ (prefixWord ++ tailWord_1117694).sum := by decide
  have hdescent : baseEnd_1117694 < baseStart_1117694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117750 : List Nat := [5, 1, 2, 1, 3, 2, 1, 7]
def baseStart_1117750 : Nat := 118140960795 + 1117750 * 2 ^ 59
def prefixEnd_1117750 : Nat := 4983230072969 + 3 ^ 40 * 1117750 * 2
def baseEnd_1117750 : Nat := 42514296412082002347005

theorem tailTrace_1117750 : CollatzResearch.WordTrace tailWord_1117750 prefixEnd_1117750 42514296412082002347005 := by
  unfold tailWord_1117750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2547980731286882584191419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27178461133726747564708469 2547980731286882584191419)
  ·
    refine ⟨3821971096930323876287129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2547980731286882584191419 3821971096930323876287129)
    ·
      refine ⟨2866478322697742907215347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3821971096930323876287129 2866478322697742907215347)
      ·
        refine ⟨4299717484046614360823021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2866478322697742907215347 4299717484046614360823021)
        ·
          refine ⟨1612394056517480385308633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4299717484046614360823021 1612394056517480385308633)
          ·
            refine ⟨1209295542388110288981475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1612394056517480385308633 1209295542388110288981475)
            ·
              refine ⟨1813943313582165433472213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209295542388110288981475 1813943313582165433472213)
              ·
                refine ⟨42514296412082002347005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1813943313582165433472213 42514296412082002347005)
                ·
                  rfl

theorem cell22_1117750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_1117750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117750 prefixEnd_1117750 := by exact prefixLift 1117750
  have htrace : WordTrace (prefixWord ++ tailWord_1117750) baseStart_1117750 baseEnd_1117750 := by
    simpa [prefixWord, tailWord_1117750, baseEnd_1117750] using wordTrace_append hprefix tailTrace_1117750
  have hstable : (prefixWord ++ tailWord_1117750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117750).length < 2 ^ (prefixWord ++ tailWord_1117750).sum := by decide
  have hdescent : baseEnd_1117750 < baseStart_1117750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117825 : List Nat := [1, 2, 4, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1117825 : Nat := 118140960795 + 1117825 * 2 ^ 59
def prefixEnd_1117825 : Nat := 4983230072969 + 3 ^ 40 * 1117825 * 2
def baseEnd_1117825 : Nat := 382654341741462825497815

theorem tailTrace_1117825 : CollatzResearch.WordTrace tailWord_1117825 prefixEnd_1117825 382654341741462825497815 := by
  unfold tailWord_1117825
  simp only [CollatzResearch.WordTrace]
  refine ⟨40770427175318409156042929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27180284783545606104028619 40770427175318409156042929)
  ·
    refine ⟨30577820381488806867032197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40770427175318409156042929 30577820381488806867032197)
    ·
      refine ⟨5733341321529151287568537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30577820381488806867032197 5733341321529151287568537)
      ·
        refine ⟨4300005991146863465676403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5733341321529151287568537 4300005991146863465676403)
        ·
          refine ⟨6450008986720295198514605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4300005991146863465676403 6450008986720295198514605)
          ·
            refine ⟨2418753370020110699442977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6450008986720295198514605 2418753370020110699442977)
            ·
              refine ⟨1814065027515083024582233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2418753370020110699442977 1814065027515083024582233)
              ·
                refine ⟨1360548770636312268436675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1814065027515083024582233 1360548770636312268436675)
                ·
                  refine ⟨2040823155954468402655013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360548770636312268436675 2040823155954468402655013)
                  ·
                    refine ⟨382654341741462825497815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2040823155954468402655013 382654341741462825497815)
                    ·
                      rfl

theorem cell22_1117825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1117825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117825 prefixEnd_1117825 := by exact prefixLift 1117825
  have htrace : WordTrace (prefixWord ++ tailWord_1117825) baseStart_1117825 baseEnd_1117825 := by
    simpa [prefixWord, tailWord_1117825, baseEnd_1117825] using wordTrace_append hprefix tailTrace_1117825
  have hstable : (prefixWord ++ tailWord_1117825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117825).length < 2 ^ (prefixWord ++ tailWord_1117825).sum := by decide
  have hdescent : baseEnd_1117825 < baseStart_1117825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117836 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_1117836 : Nat := 118140960795 + 1117836 * 2 ^ 59
def prefixEnd_1117836 : Nat := 4983230072969 + 3 ^ 40 * 1117836 * 2
def baseEnd_1117836 : Nat := 382658107266262463472781

theorem tailTrace_1117836 : CollatzResearch.WordTrace tailWord_1117836 prefixEnd_1117836 382658107266262463472781 := by
  unfold tailWord_1117836
  simp only [CollatzResearch.WordTrace]
  refine ⟨20385414189139279017346681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27180552252185705356462241 20385414189139279017346681)
  ·
    refine ⟨15289060641854459263010011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20385414189139279017346681 15289060641854459263010011)
    ·
      refine ⟨22933590962781688894515017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15289060641854459263010011 22933590962781688894515017)
      ·
        refine ⟨17200193222086266670886263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22933590962781688894515017 17200193222086266670886263)
        ·
          refine ⟨25800289833129400006329395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17200193222086266670886263 25800289833129400006329395)
          ·
            refine ⟨38700434749694100009494093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25800289833129400006329395 38700434749694100009494093)
            ·
              refine ⟨14512663031135287503560285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38700434749694100009494093 14512663031135287503560285)
              ·
                refine ⟨5442248636675732813835107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14512663031135287503560285 5442248636675732813835107)
                ·
                  refine ⟨8163372955013599220752661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5442248636675732813835107 8163372955013599220752661)
                  ·
                    refine ⟨382658107266262463472781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8163372955013599220752661 382658107266262463472781)
                    ·
                      rfl

theorem cell22_1117836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_1117836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117836 prefixEnd_1117836 := by exact prefixLift 1117836
  have htrace : WordTrace (prefixWord ++ tailWord_1117836) baseStart_1117836 baseEnd_1117836 := by
    simpa [prefixWord, tailWord_1117836, baseEnd_1117836] using wordTrace_append hprefix tailTrace_1117836
  have hstable : (prefixWord ++ tailWord_1117836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117836).length < 2 ^ (prefixWord ++ tailWord_1117836).sum := by decide
  have hdescent : baseEnd_1117836 < baseStart_1117836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117857 : List Nat := [1, 2, 3, 3, 2, 2, 3, 2, 4]
def baseStart_1117857 : Nat := 118140960795 + 1117857 * 2 ^ 59
def prefixEnd_1117857 : Nat := 4983230072969 + 3 ^ 40 * 1117857 * 2
def baseEnd_1117857 : Nat := 127555098665141802899239

theorem tailTrace_1117857 : CollatzResearch.WordTrace tailWord_1117857 prefixEnd_1117857 127555098665141802899239 := by
  unfold tailWord_1117857
  simp only [CollatzResearch.WordTrace]
  refine ⟨40771594311202478621207825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27181062874134985747471883 40771594311202478621207825)
  ·
    refine ⟨30578695733401858965905869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40771594311202478621207825 30578695733401858965905869)
    ·
      refine ⟨11467010900025697112214701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30578695733401858965905869 11467010900025697112214701)
      ·
        refine ⟨4300129087509636417080513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11467010900025697112214701 4300129087509636417080513)
        ·
          refine ⟨3225096815632227312810385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4300129087509636417080513 3225096815632227312810385)
          ·
            refine ⟨2418822611724170484607789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3225096815632227312810385 2418822611724170484607789)
            ·
              refine ⟨907058479396563931727921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2418822611724170484607789 907058479396563931727921)
              ·
                refine ⟨680293859547422948795941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 907058479396563931727921 680293859547422948795941)
                ·
                  refine ⟨127555098665141802899239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 680293859547422948795941 127555098665141802899239)
                  ·
                    rfl

theorem cell22_1117857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 4].length) (baseStart_1117857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117857 prefixEnd_1117857 := by exact prefixLift 1117857
  have htrace : WordTrace (prefixWord ++ tailWord_1117857) baseStart_1117857 baseEnd_1117857 := by
    simpa [prefixWord, tailWord_1117857, baseEnd_1117857] using wordTrace_append hprefix tailTrace_1117857
  have hstable : (prefixWord ++ tailWord_1117857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117857).length < 2 ^ (prefixWord ++ tailWord_1117857).sum := by decide
  have hdescent : baseEnd_1117857 < baseStart_1117857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117883 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 3, 3]
def baseStart_1117883 : Nat := 118140960795 + 1117883 * 2 ^ 59
def prefixEnd_1117883 : Nat := 4983230072969 + 3 ^ 40 * 1117883 * 2
def baseEnd_1117883 : Nat := 382674196326770007547637

theorem tailTrace_1117883 : CollatzResearch.WordTrace tailWord_1117883 prefixEnd_1117883 382674196326770007547637 := by
  unfold tailWord_1117883
  simp only [CollatzResearch.WordTrace]
  refine ⟨40772542609108285061654303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27181695072738856707769535 40772542609108285061654303)
  ·
    refine ⟨61158813913662427592481455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40772542609108285061654303 61158813913662427592481455)
    ·
      refine ⟨91738220870493641388722183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61158813913662427592481455 91738220870493641388722183)
      ·
        refine ⟨137607331305740462083083275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91738220870493641388722183 137607331305740462083083275)
        ·
          refine ⟨206410996958610693124624913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137607331305740462083083275 206410996958610693124624913)
          ·
            refine ⟨154808247718958019843468685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206410996958610693124624913 154808247718958019843468685)
            ·
              refine ⟨58053092894609257441300757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154808247718958019843468685 58053092894609257441300757)
              ·
                refine ⟨2721238729434808942560973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58053092894609257441300757 2721238729434808942560973)
                ·
                  refine ⟨1020464523538053353460365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2721238729434808942560973 1020464523538053353460365)
                  ·
                    refine ⟨382674196326770007547637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1020464523538053353460365 382674196326770007547637)
                    ·
                      rfl

theorem cell22_1117883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 3].length) (baseStart_1117883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117883 prefixEnd_1117883 := by exact prefixLift 1117883
  have htrace : WordTrace (prefixWord ++ tailWord_1117883) baseStart_1117883 baseEnd_1117883 := by
    simpa [prefixWord, tailWord_1117883, baseEnd_1117883] using wordTrace_append hprefix tailTrace_1117883
  have hstable : (prefixWord ++ tailWord_1117883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117883).length < 2 ^ (prefixWord ++ tailWord_1117883).sum := by decide
  have hdescent : baseEnd_1117883 < baseStart_1117883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117913 : List Nat := [1, 2, 1, 2, 3, 3, 1, 4, 5]
def baseStart_1117913 : Nat := 118140960795 + 1117913 * 2 ^ 59
def prefixEnd_1117913 : Nat := 4983230072969 + 3 ^ 40 * 1117913 * 2
def baseEnd_1117913 : Nat := 127561488646619976432515

theorem tailTrace_1117913 : CollatzResearch.WordTrace tailWord_1117913 prefixEnd_1117913 127561488646619976432515 := by
  unfold tailWord_1117913
  simp only [CollatzResearch.WordTrace]
  refine ⟨40773636798999600185246393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27182424532666400123497595 40773636798999600185246393)
  ·
    refine ⟨30580227599249700138934795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40773636798999600185246393 30580227599249700138934795)
    ·
      refine ⟨45870341398874550208402193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30580227599249700138934795 45870341398874550208402193)
      ·
        refine ⟨34402756049155912656301645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45870341398874550208402193 34402756049155912656301645)
        ·
          refine ⟨12901033518433467246113117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34402756049155912656301645 12901033518433467246113117)
          ·
            refine ⟨4837887569412550217292419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12901033518433467246113117 4837887569412550217292419)
            ·
              refine ⟨7256831354118825325938629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4837887569412550217292419 7256831354118825325938629)
              ·
                refine ⟨1360655878897279748613493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7256831354118825325938629 1360655878897279748613493)
                ·
                  refine ⟨127561488646619976432515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1360655878897279748613493 127561488646619976432515)
                  ·
                    rfl

theorem cell22_1117913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 5].length) (baseStart_1117913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117913 prefixEnd_1117913 := by exact prefixLift 1117913
  have htrace : WordTrace (prefixWord ++ tailWord_1117913) baseStart_1117913 baseEnd_1117913 := by
    simpa [prefixWord, tailWord_1117913, baseEnd_1117913] using wordTrace_append hprefix tailTrace_1117913
  have hstable : (prefixWord ++ tailWord_1117913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117913).length < 2 ^ (prefixWord ++ tailWord_1117913).sum := by decide
  have hdescent : baseEnd_1117913 < baseStart_1117913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117928 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1117928 : Nat := 118140960795 + 1117928 * 2 ^ 59
def prefixEnd_1117928 : Nat := 4983230072969 + 3 ^ 40 * 1117928 * 2
def baseEnd_1117928 : Nat := 382689600746404890172499

theorem tailTrace_1117928 : CollatzResearch.WordTrace tailWord_1117928 prefixEnd_1117928 382689600746404890172499 := by
  unfold tailWord_1117928
  simp only [CollatzResearch.WordTrace]
  refine ⟨20387091946972628873521219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27182789262630171831361625 20387091946972628873521219)
  ·
    refine ⟨30580637920458943310281829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20387091946972628873521219 30580637920458943310281829)
    ·
      refine ⟨5733869610086051870677843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30580637920458943310281829 5733869610086051870677843)
      ·
        refine ⟨8600804415129077806016765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5733869610086051870677843 8600804415129077806016765)
        ·
          refine ⟨3225301655673404177256287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8600804415129077806016765 3225301655673404177256287)
          ·
            refine ⟨4837952483510106265884431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3225301655673404177256287 4837952483510106265884431)
            ·
              refine ⟨7256928725265159398826647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4837952483510106265884431 7256928725265159398826647)
              ·
                refine ⟨10885393087897739098239971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7256928725265159398826647 10885393087897739098239971)
                ·
                  refine ⟨16328089631846608647359957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10885393087897739098239971 16328089631846608647359957)
                  ·
                    refine ⟨382689600746404890172499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16328089631846608647359957 382689600746404890172499)
                    ·
                      rfl

theorem cell22_1117928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1117928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117928 prefixEnd_1117928 := by exact prefixLift 1117928
  have htrace : WordTrace (prefixWord ++ tailWord_1117928) baseStart_1117928 baseEnd_1117928 := by
    simpa [prefixWord, tailWord_1117928, baseEnd_1117928] using wordTrace_append hprefix tailTrace_1117928
  have hstable : (prefixWord ++ tailWord_1117928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117928).length < 2 ^ (prefixWord ++ tailWord_1117928).sum := by decide
  have hdescent : baseEnd_1117928 < baseStart_1117928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117943 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 3, 4]
def baseStart_1117943 : Nat := 118140960795 + 1117943 * 2 ^ 59
def prefixEnd_1117943 : Nat := 4983230072969 + 3 ^ 40 * 1117943 * 2
def baseEnd_1117943 : Nat := 382694735552949851047453

theorem tailTrace_1117943 : CollatzResearch.WordTrace tailWord_1117943 prefixEnd_1117943 382694735552949851047453 := by
  unfold tailWord_1117943
  simp only [CollatzResearch.WordTrace]
  refine ⟨40774730988890915308838483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27183153992593943539225655 40774730988890915308838483)
  ·
    refine ⟨61162096483336372963257725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40774730988890915308838483 61162096483336372963257725)
    ·
      refine ⟨22935786181251139861221647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61162096483336372963257725 22935786181251139861221647)
      ·
        refine ⟨34403679271876709791832471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22935786181251139861221647 34403679271876709791832471)
        ·
          refine ⟨51605518907815064687748707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34403679271876709791832471 51605518907815064687748707)
          ·
            refine ⟨77408278361722597031623061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51605518907815064687748707 77408278361722597031623061)
            ·
              refine ⟨3628513048205746735857331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77408278361722597031623061 3628513048205746735857331)
              ·
                refine ⟨5442769572308620103785997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3628513048205746735857331 5442769572308620103785997)
                ·
                  refine ⟨2041038589615732538919749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5442769572308620103785997 2041038589615732538919749)
                  ·
                    refine ⟨382694735552949851047453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2041038589615732538919749 382694735552949851047453)
                    ·
                      rfl

theorem cell22_1117943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_1117943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117943 prefixEnd_1117943 := by exact prefixLift 1117943
  have htrace : WordTrace (prefixWord ++ tailWord_1117943) baseStart_1117943 baseEnd_1117943 := by
    simpa [prefixWord, tailWord_1117943, baseEnd_1117943] using wordTrace_append hprefix tailTrace_1117943
  have hstable : (prefixWord ++ tailWord_1117943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117943).length < 2 ^ (prefixWord ++ tailWord_1117943).sum := by decide
  have hdescent : baseEnd_1117943 < baseStart_1117943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117960 : List Nat := [2, 1, 3, 2, 2, 1, 3, 3, 1, 4]
def baseStart_1117960 : Nat := 118140960795 + 1117960 * 2 ^ 59
def prefixEnd_1117960 : Nat := 4983230072969 + 3 ^ 40 * 1117960 * 2
def baseEnd_1117960 : Nat := 382700555000367473372401

theorem tailTrace_1117960 : CollatzResearch.WordTrace tailWord_1117960 prefixEnd_1117960 382700555000367473372401 := by
  unfold tailWord_1117960
  simp only [CollatzResearch.WordTrace]
  refine ⟨20387675514914663606103667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27183567353219551474804889 20387675514914663606103667)
  ·
    refine ⟨30581513272371995409155501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20387675514914663606103667 30581513272371995409155501)
    ·
      refine ⟨11468067477139498278433313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30581513272371995409155501 11468067477139498278433313)
      ·
        refine ⟨8601050607854623708824985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11468067477139498278433313 8601050607854623708824985)
        ·
          refine ⟨6450787955890967781618739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8601050607854623708824985 6450787955890967781618739)
          ·
            refine ⟨9676181933836451672428109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6450787955890967781618739 9676181933836451672428109)
            ·
              refine ⟨3628568225188669377160541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9676181933836451672428109 3628568225188669377160541)
              ·
                refine ⟨1360713084445751016435203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3628568225188669377160541 1360713084445751016435203)
                ·
                  refine ⟨2041069626668626524652805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360713084445751016435203 2041069626668626524652805)
                  ·
                    refine ⟨382700555000367473372401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2041069626668626524652805 382700555000367473372401)
                    ·
                      rfl

theorem cell22_1117960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_1117960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117960 prefixEnd_1117960 := by exact prefixLift 1117960
  have htrace : WordTrace (prefixWord ++ tailWord_1117960) baseStart_1117960 baseEnd_1117960 := by
    simpa [prefixWord, tailWord_1117960, baseEnd_1117960] using wordTrace_append hprefix tailTrace_1117960
  have hstable : (prefixWord ++ tailWord_1117960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117960).length < 2 ^ (prefixWord ++ tailWord_1117960).sum := by decide
  have hdescent : baseEnd_1117960 < baseStart_1117960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1117975 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 6]
def baseStart_1117975 : Nat := 118140960795 + 1117975 * 2 ^ 59
def prefixEnd_1117975 : Nat := 4983230072969 + 3 ^ 40 * 1117975 * 2
def baseEnd_1117975 : Nat := 127568563268970811415785

theorem tailTrace_1117975 : CollatzResearch.WordTrace tailWord_1117975 prefixEnd_1117975 127568563268970811415785 := by
  unfold tailWord_1117975
  simp only [CollatzResearch.WordTrace]
  refine ⟨40775898124774984774003379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27183932083183323182668919 40775898124774984774003379)
  ·
    refine ⟨61163847187162477161005069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40775898124774984774003379 61163847187162477161005069)
    ·
      refine ⟨22936442695185928935376901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61163847187162477161005069 22936442695185928935376901)
      ·
        refine ⟨4300583005347361675383169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22936442695185928935376901 4300583005347361675383169)
        ·
          refine ⟨3225437254010521256537377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4300583005347361675383169 3225437254010521256537377)
          ·
            refine ⟨2419077940507890942403033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3225437254010521256537377 2419077940507890942403033)
            ·
              refine ⟨1814308455380918206802275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2419077940507890942403033 1814308455380918206802275)
              ·
                refine ⟨2721462683071377310203413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814308455380918206802275 2721462683071377310203413)
                ·
                  refine ⟨127568563268970811415785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2721462683071377310203413 127568563268970811415785)
                  ·
                    rfl

theorem cell22_1117975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 6].length) (baseStart_1117975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1117975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1117975 prefixEnd_1117975 := by exact prefixLift 1117975
  have htrace : WordTrace (prefixWord ++ tailWord_1117975) baseStart_1117975 baseEnd_1117975 := by
    simpa [prefixWord, tailWord_1117975, baseEnd_1117975] using wordTrace_append hprefix tailTrace_1117975
  have hstable : (prefixWord ++ tailWord_1117975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1117975).length < 2 ^ (prefixWord ++ tailWord_1117975).sum := by decide
  have hdescent : baseEnd_1117975 < baseStart_1117975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1117975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118063 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 6, 5]
def baseStart_1118063 : Nat := 118140960795 + 1118063 * 2 ^ 59
def prefixEnd_1118063 : Nat := 4983230072969 + 3 ^ 40 * 1118063 * 2
def baseEnd_1118063 : Nat := 382735814005309538047085

theorem tailTrace_1118063 : CollatzResearch.WordTrace tailWord_1118063 prefixEnd_1118063 382735814005309538047085 := by
  unfold tailWord_1118063
  simp only [CollatzResearch.WordTrace]
  refine ⟨40779107748456175803206843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27186071832304117202137895 40779107748456175803206843)
  ·
    refine ⟨61168661622684263704810265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40779107748456175803206843 61168661622684263704810265)
    ·
      refine ⟨45876496217013197778607699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61168661622684263704810265 45876496217013197778607699)
      ·
        refine ⟨68814744325519796667911549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45876496217013197778607699 68814744325519796667911549)
        ·
          refine ⟨25805529122069923750466831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68814744325519796667911549 25805529122069923750466831)
          ·
            refine ⟨38708293683104885625700247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25805529122069923750466831 38708293683104885625700247)
            ·
              refine ⟨58062440524657328438550371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38708293683104885625700247 58062440524657328438550371)
              ·
                refine ⟨87093660786985992657825557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58062440524657328438550371 87093660786985992657825557)
                ·
                  refine ⟨4082515349389968405835573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87093660786985992657825557 4082515349389968405835573)
                  ·
                    refine ⟨382735814005309538047085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4082515349389968405835573 382735814005309538047085)
                    ·
                      rfl

theorem cell22_1118063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_1118063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118063 prefixEnd_1118063 := by exact prefixLift 1118063
  have htrace : WordTrace (prefixWord ++ tailWord_1118063) baseStart_1118063 baseEnd_1118063 := by
    simpa [prefixWord, tailWord_1118063, baseEnd_1118063] using wordTrace_append hprefix tailTrace_1118063
  have hstable : (prefixWord ++ tailWord_1118063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118063).length < 2 ^ (prefixWord ++ tailWord_1118063).sum := by decide
  have hdescent : baseEnd_1118063 < baseStart_1118063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118069 : List Nat := [1, 3, 4, 1, 1, 1, 2, 5, 1, 3]
def baseStart_1118069 : Nat := 118140960795 + 1118069 * 2 ^ 59
def prefixEnd_1118069 : Nat := 4983230072969 + 3 ^ 40 * 1118069 * 2
def baseEnd_1118069 : Nat := 382737867927927522397067

theorem tailTrace_1118069 : CollatzResearch.WordTrace tailWord_1118069 prefixEnd_1118069 382737867927927522397067 := by
  unfold tailWord_1118069
  simp only [CollatzResearch.WordTrace]
  refine ⟨40779326586434438827925261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27186217724289625885283507 40779326586434438827925261)
  ·
    refine ⟨15292247469912914560471973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40779326586434438827925261 15292247469912914560471973)
    ·
      refine ⟨2867296400608671480088495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15292247469912914560471973 2867296400608671480088495)
      ·
        refine ⟨4300944600913007220132743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2867296400608671480088495 4300944600913007220132743)
        ·
          refine ⟨6451416901369510830199115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4300944600913007220132743 6451416901369510830199115)
          ·
            refine ⟨9677125352054266245298673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6451416901369510830199115 9677125352054266245298673)
            ·
              refine ⟨7257844014040699683974005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9677125352054266245298673 7257844014040699683974005)
              ·
                refine ⟨680422876316315595372563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7257844014040699683974005 680422876316315595372563)
                ·
                  refine ⟨1020634314474473393058845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680422876316315595372563 1020634314474473393058845)
                  ·
                    refine ⟨382737867927927522397067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1020634314474473393058845 382737867927927522397067)
                    ·
                      rfl

theorem cell22_1118069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_1118069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118069 prefixEnd_1118069 := by exact prefixLift 1118069
  have htrace : WordTrace (prefixWord ++ tailWord_1118069) baseStart_1118069 baseEnd_1118069 := by
    simpa [prefixWord, tailWord_1118069, baseEnd_1118069] using wordTrace_append hprefix tailTrace_1118069
  have hstable : (prefixWord ++ tailWord_1118069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118069).length < 2 ^ (prefixWord ++ tailWord_1118069).sum := by decide
  have hdescent : baseEnd_1118069 < baseStart_1118069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118127 : List Nat := [1, 1, 2, 1, 2, 2, 6, 3, 4]
def baseStart_1118127 : Nat := 118140960795 + 1118127 * 2 ^ 59
def prefixEnd_1118127 : Nat := 4983230072969 + 3 ^ 40 * 1118127 * 2
def baseEnd_1118127 : Nat := 127585907504411568148963

theorem tailTrace_1118127 : CollatzResearch.WordTrace tailWord_1118127 prefixEnd_1118127 127585907504411568148963 := by
  unfold tailWord_1118127
  simp only [CollatzResearch.WordTrace]
  refine ⟨40781442020224314733536635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27187628013482876489024423 40781442020224314733536635)
  ·
    refine ⟨61172163030336472100304953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40781442020224314733536635 61172163030336472100304953)
    ·
      refine ⟨45879122272752354075228715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61172163030336472100304953 45879122272752354075228715)
      ·
        refine ⟨68818683409128531112843073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45879122272752354075228715 68818683409128531112843073)
        ·
          refine ⟨51614012556846398334632305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68818683409128531112843073 51614012556846398334632305)
          ·
            refine ⟨38710509417634798750974229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51614012556846398334632305 38710509417634798750974229)
            ·
              refine ⟨1814555128951631191451917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38710509417634798750974229 1814555128951631191451917)
              ·
                refine ⟨680458173356861696794469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1814555128951631191451917 680458173356861696794469)
                ·
                  refine ⟨127585907504411568148963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 680458173356861696794469 127585907504411568148963)
                  ·
                    rfl

theorem cell22_1118127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 4].length) (baseStart_1118127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118127 prefixEnd_1118127 := by exact prefixLift 1118127
  have htrace : WordTrace (prefixWord ++ tailWord_1118127) baseStart_1118127 baseEnd_1118127 := by
    simpa [prefixWord, tailWord_1118127, baseEnd_1118127] using wordTrace_append hprefix tailTrace_1118127
  have hstable : (prefixWord ++ tailWord_1118127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118127).length < 2 ^ (prefixWord ++ tailWord_1118127).sum := by decide
  have hdescent : baseEnd_1118127 < baseStart_1118127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118129 : List Nat := [1, 2, 2, 4, 2, 1, 4, 1, 1, 4]
def baseStart_1118129 : Nat := 118140960795 + 1118129 * 2 ^ 59
def prefixEnd_1118129 : Nat := 4983230072969 + 3 ^ 40 * 1118129 * 2
def baseEnd_1118129 : Nat := 382758407154107365896883

theorem tailTrace_1118129 : CollatzResearch.WordTrace tailWord_1118129 prefixEnd_1118129 382758407154107365896883 := by
  unfold tailWord_1118129
  simp only [CollatzResearch.WordTrace]
  refine ⟨40781514966217069075109441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27187676644144712716739627 40781514966217069075109441)
  ·
    refine ⟨30586136224662801806332081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40781514966217069075109441 30586136224662801806332081)
    ·
      refine ⟨22939602168497101354749061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30586136224662801806332081 22939602168497101354749061)
      ·
        refine ⟨4301175406593206504015449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22939602168497101354749061 4301175406593206504015449)
        ·
          refine ⟨3225881554944904878011587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4301175406593206504015449 3225881554944904878011587)
          ·
            refine ⟨4838822332417357317017381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3225881554944904878011587 4838822332417357317017381)
            ·
              refine ⟨907279187328254496940759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4838822332417357317017381 907279187328254496940759)
              ·
                refine ⟨1360918780992381745411139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 907279187328254496940759 1360918780992381745411139)
                ·
                  refine ⟨2041378171488572618116709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1360918780992381745411139 2041378171488572618116709)
                  ·
                    refine ⟨382758407154107365896883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2041378171488572618116709 382758407154107365896883)
                    ·
                      rfl

theorem cell22_1118129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_1118129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118129 prefixEnd_1118129 := by exact prefixLift 1118129
  have htrace : WordTrace (prefixWord ++ tailWord_1118129) baseStart_1118129 baseEnd_1118129 := by
    simpa [prefixWord, tailWord_1118129, baseEnd_1118129] using wordTrace_append hprefix tailTrace_1118129
  have hstable : (prefixWord ++ tailWord_1118129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118129).length < 2 ^ (prefixWord ++ tailWord_1118129).sum := by decide
  have hdescent : baseEnd_1118129 < baseStart_1118129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118159 : List Nat := [1, 1, 2, 1, 1, 5, 5, 1, 2, 3]
def baseStart_1118159 : Nat := 118140960795 + 1118159 * 2 ^ 59
def prefixEnd_1118159 : Nat := 4983230072969 + 3 ^ 40 * 1118159 * 2
def baseEnd_1118159 : Nat := 382768676767197287646791

theorem tailTrace_1118159 : CollatzResearch.WordTrace tailWord_1118159 prefixEnd_1118159 382768676767197287646791 := by
  unfold tailWord_1118159
  simp only [CollatzResearch.WordTrace]
  refine ⟨40782609156108384198701531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27188406104072256132467687 40782609156108384198701531)
  ·
    refine ⟨61173913734162576298052297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40782609156108384198701531 61173913734162576298052297)
    ·
      refine ⟨45880435300621932223539223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61173913734162576298052297 45880435300621932223539223)
      ·
        refine ⟨68820652950932898335308835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45880435300621932223539223 68820652950932898335308835)
        ·
          refine ⟨103230979426399347502963253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68820652950932898335308835 103230979426399347502963253)
          ·
            refine ⟨9677904321224938828402805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103230979426399347502963253 9677904321224938828402805)
            ·
              refine ⟨907303530114838015162763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9677904321224938828402805 907303530114838015162763)
              ·
                refine ⟨1360955295172257022744145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 907303530114838015162763 1360955295172257022744145)
                ·
                  refine ⟨1020716471379192767058109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1360955295172257022744145 1020716471379192767058109)
                  ·
                    refine ⟨382768676767197287646791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1020716471379192767058109 382768676767197287646791)
                    ·
                      rfl

theorem cell22_1118159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 2, 3].length) (baseStart_1118159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118159 prefixEnd_1118159 := by exact prefixLift 1118159
  have htrace : WordTrace (prefixWord ++ tailWord_1118159) baseStart_1118159 baseEnd_1118159 := by
    simpa [prefixWord, tailWord_1118159, baseEnd_1118159] using wordTrace_append hprefix tailTrace_1118159
  have hstable : (prefixWord ++ tailWord_1118159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118159).length < 2 ^ (prefixWord ++ tailWord_1118159).sum := by decide
  have hdescent : baseEnd_1118159 < baseStart_1118159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118178 : List Nat := [3, 3, 3, 1, 2, 2, 1, 3, 4]
def baseStart_1118178 : Nat := 118140960795 + 1118178 * 2 ^ 59
def prefixEnd_1118178 : Nat := 4983230072969 + 3 ^ 40 * 1118178 * 2
def baseEnd_1118178 : Nat := 127591726951829190473911

theorem tailTrace_1118178 : CollatzResearch.WordTrace tailWord_1118178 prefixEnd_1118178 127591726951829190473911 := by
  unfold tailWord_1118178
  simp only [CollatzResearch.WordTrace]
  refine ⟨10195825535759887610910797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27188868095359700295762125 10195825535759887610910797)
  ·
    refine ⟨3823434575909957854091549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10195825535759887610910797 3823434575909957854091549)
    ·
      refine ⟨1433787965966234195284331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3823434575909957854091549 1433787965966234195284331)
      ·
        refine ⟨2150681948949351292926497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433787965966234195284331 2150681948949351292926497)
        ·
          refine ⟨1613011461712013469694873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2150681948949351292926497 1613011461712013469694873)
          ·
            refine ⟨1209758596284010102271155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1613011461712013469694873 1209758596284010102271155)
            ·
              refine ⟨1814637894426015153406733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1209758596284010102271155 1814637894426015153406733)
              ·
                refine ⟨680489210409755682527525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1814637894426015153406733 680489210409755682527525)
                ·
                  refine ⟨127591726951829190473911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 680489210409755682527525 127591726951829190473911)
                  ·
                    rfl

theorem cell22_1118178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_1118178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118178 prefixEnd_1118178 := by exact prefixLift 1118178
  have htrace : WordTrace (prefixWord ++ tailWord_1118178) baseStart_1118178 baseEnd_1118178 := by
    simpa [prefixWord, tailWord_1118178, baseEnd_1118178] using wordTrace_append hprefix tailTrace_1118178
  have hstable : (prefixWord ++ tailWord_1118178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118178).length < 2 ^ (prefixWord ++ tailWord_1118178).sum := by decide
  have hdescent : baseEnd_1118178 < baseStart_1118178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118189 : List Nat := [1, 5, 1, 4, 1, 2, 8]
def baseStart_1118189 : Nat := 118140960795 + 1118189 * 2 ^ 59
def prefixEnd_1118189 : Nat := 4983230072969 + 3 ^ 40 * 1118189 * 2
def baseEnd_1118189 : Nat := 14176998014084711459137

theorem tailTrace_1118189 : CollatzResearch.WordTrace tailWord_1118189 prefixEnd_1118189 14176998014084711459137 := by
  unfold tailWord_1118189
  simp only [CollatzResearch.WordTrace]
  refine ⟨40783703345999699322293621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27189135563999799548195747 40783703345999699322293621)
  ·
    refine ⟨3823472188687471811465027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40783703345999699322293621 3823472188687471811465027)
    ·
      refine ⟨5735208283031207717197541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3823472188687471811465027 5735208283031207717197541)
      ·
        refine ⟨1075351553068351446974539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5735208283031207717197541 1075351553068351446974539)
        ·
          refine ⟨1613027329602527170461809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075351553068351446974539 1613027329602527170461809)
          ·
            refine ⟨1209770497201895377846357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1613027329602527170461809 1209770497201895377846357)
            ·
              refine ⟨14176998014084711459137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1209770497201895377846357 14176998014084711459137)
              ·
                rfl

theorem cell22_1118189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 8].length) (baseStart_1118189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118189 prefixEnd_1118189 := by exact prefixLift 1118189
  have htrace : WordTrace (prefixWord ++ tailWord_1118189) baseStart_1118189 baseEnd_1118189 := by
    simpa [prefixWord, tailWord_1118189, baseEnd_1118189] using wordTrace_append hprefix tailTrace_1118189
  have hstable : (prefixWord ++ tailWord_1118189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118189).length < 2 ^ (prefixWord ++ tailWord_1118189).sum := by decide
  have hdescent : baseEnd_1118189 < baseStart_1118189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118200 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 7]
def baseStart_1118200 : Nat := 118140960795 + 1118200 * 2 ^ 59
def prefixEnd_1118200 : Nat := 4983230072969 + 3 ^ 40 * 1118200 * 2
def baseEnd_1118200 : Nat := 127594237301695615790555

theorem tailTrace_1118200 : CollatzResearch.WordTrace tailWord_1118200 prefixEnd_1118200 127594237301695615790555 := by
  unfold tailWord_1118200
  simp only [CollatzResearch.WordTrace]
  refine ⟨20392052274479924100472027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27189403032639898800629369 20392052274479924100472027)
  ·
    refine ⟨30588078411719886150708041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20392052274479924100472027 30588078411719886150708041)
    ·
      refine ⟨22941058808789914613031031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30588078411719886150708041 22941058808789914613031031)
      ·
        refine ⟨34411588213184871919546547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22941058808789914613031031 34411588213184871919546547)
        ·
          refine ⟨51617382319777307879319821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34411588213184871919546547 51617382319777307879319821)
          ·
            refine ⟨19356518369916490454744933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51617382319777307879319821 19356518369916490454744933)
            ·
              refine ⟨3629347194359341960264675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19356518369916490454744933 3629347194359341960264675)
              ·
                refine ⟨5444020791539012940397013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3629347194359341960264675 5444020791539012940397013)
                ·
                  refine ⟨127594237301695615790555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5444020791539012940397013 127594237301695615790555)
                  ·
                    rfl

theorem cell22_1118200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 7].length) (baseStart_1118200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118200 prefixEnd_1118200 := by exact prefixLift 1118200
  have htrace : WordTrace (prefixWord ++ tailWord_1118200) baseStart_1118200 baseEnd_1118200 := by
    simpa [prefixWord, tailWord_1118200, baseEnd_1118200] using wordTrace_append hprefix tailTrace_1118200
  have hstable : (prefixWord ++ tailWord_1118200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118200).length < 2 ^ (prefixWord ++ tailWord_1118200).sum := by decide
  have hdescent : baseEnd_1118200 < baseStart_1118200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118277 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 6, 3]
def baseStart_1118277 : Nat := 118140960795 + 1118277 * 2 ^ 59
def prefixEnd_1118277 : Nat := 4983230072969 + 3 ^ 40 * 1118277 * 2
def baseEnd_1118277 : Nat := 382809070578684313196429

theorem tailTrace_1118277 : CollatzResearch.WordTrace tailWord_1118277 prefixEnd_1118277 382809070578684313196429 := by
  unfold tailWord_1118277
  simp only [CollatzResearch.WordTrace]
  refine ⟨40786912969680890351497085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27191275313120593567664723 40786912969680890351497085)
  ·
    refine ⟨15295092363630333881811407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40786912969680890351497085 15295092363630333881811407)
    ·
      refine ⟨22942638545445500822717111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15295092363630333881811407 22942638545445500822717111)
      ·
        refine ⟨34413957818168251234075667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22942638545445500822717111 34413957818168251234075667)
        ·
          refine ⟨51620936727252376851113501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34413957818168251234075667 51620936727252376851113501)
          ·
            refine ⟨19357851272719641319167563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51620936727252376851113501 19357851272719641319167563)
            ·
              refine ⟨29036776909079461978751345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19357851272719641319167563 29036776909079461978751345)
              ·
                refine ⟨21777582681809596484063509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29036776909079461978751345 21777582681809596484063509)
                ·
                  refine ⟨1020824188209824835190477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21777582681809596484063509 1020824188209824835190477)
                  ·
                    refine ⟨382809070578684313196429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1020824188209824835190477 382809070578684313196429)
                    ·
                      rfl

theorem cell22_1118277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_1118277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118277 prefixEnd_1118277 := by exact prefixLift 1118277
  have htrace : WordTrace (prefixWord ++ tailWord_1118277) baseStart_1118277 baseEnd_1118277 := by
    simpa [prefixWord, tailWord_1118277, baseEnd_1118277] using wordTrace_append hprefix tailTrace_1118277
  have hstable : (prefixWord ++ tailWord_1118277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118277).length < 2 ^ (prefixWord ++ tailWord_1118277).sum := by decide
  have hdescent : baseEnd_1118277 < baseStart_1118277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118339 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 3, 3]
def baseStart_1118339 : Nat := 118140960795 + 1118339 * 2 ^ 59
def prefixEnd_1118339 : Nat := 4983230072969 + 3 ^ 40 * 1118339 * 2
def baseEnd_1118339 : Nat := 382830294445736818146239

theorem tailTrace_1118339 : CollatzResearch.WordTrace tailWord_1118339 prefixEnd_1118339 382830294445736818146239 := by
  unfold tailWord_1118339
  simp only [CollatzResearch.WordTrace]
  refine ⟨40789174295456274940254071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27192782863637516626836047 40789174295456274940254071)
  ·
    refine ⟨61183761443184412410381107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40789174295456274940254071 61183761443184412410381107)
    ·
      refine ⟨91775642164776618615571661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61183761443184412410381107 91775642164776618615571661)
      ·
        refine ⟨34415865811791231980839373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91775642164776618615571661 34415865811791231980839373)
        ·
          refine ⟨12905949679421711992814765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34415865811791231980839373 12905949679421711992814765)
          ·
            refine ⟨4839731129783141997305537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12905949679421711992814765 4839731129783141997305537)
            ·
              refine ⟨3629798347337356497979153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4839731129783141997305537 3629798347337356497979153)
              ·
                refine ⟨2722348760503017373484365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3629798347337356497979153 2722348760503017373484365)
                ·
                  refine ⟨1020880785188631515056637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2722348760503017373484365 1020880785188631515056637)
                  ·
                    refine ⟨382830294445736818146239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1020880785188631515056637 382830294445736818146239)
                    ·
                      rfl

theorem cell22_1118339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 3].length) (baseStart_1118339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118339 prefixEnd_1118339 := by exact prefixLift 1118339
  have htrace : WordTrace (prefixWord ++ tailWord_1118339) baseStart_1118339 baseEnd_1118339 := by
    simpa [prefixWord, tailWord_1118339, baseEnd_1118339] using wordTrace_append hprefix tailTrace_1118339
  have hstable : (prefixWord ++ tailWord_1118339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118339).length < 2 ^ (prefixWord ++ tailWord_1118339).sum := by decide
  have hdescent : baseEnd_1118339 < baseStart_1118339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118373 : List Nat := [1, 3, 1, 2, 1, 3, 5, 2, 1, 3]
def baseStart_1118373 : Nat := 118140960795 + 1118373 * 2 ^ 59
def prefixEnd_1118373 : Nat := 4983230072969 + 3 ^ 40 * 1118373 * 2
def baseEnd_1118373 : Nat := 382841933340572062796135

theorem tailTrace_1118373 : CollatzResearch.WordTrace tailWord_1118373 prefixEnd_1118373 382841933340572062796135 := by
  unfold tailWord_1118373
  simp only [CollatzResearch.WordTrace]
  refine ⟨40790414377333098746991773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27193609584888732497994515 40790414377333098746991773)
  ·
    refine ⟨15296405391499912030121915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40790414377333098746991773 15296405391499912030121915)
    ·
      refine ⟨22944608087249868045182873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15296405391499912030121915 22944608087249868045182873)
      ·
        refine ⟨17208456065437401033887155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22944608087249868045182873 17208456065437401033887155)
        ·
          refine ⟨25812684098156101550830733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17208456065437401033887155 25812684098156101550830733)
          ·
            refine ⟨9679756536808538081561525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25812684098156101550830733 9679756536808538081561525)
            ·
              refine ⟨907477175325800445146393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9679756536808538081561525 907477175325800445146393)
              ·
                refine ⟨680607881494350333859795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 907477175325800445146393 680607881494350333859795)
                ·
                  refine ⟨1020911822241525500789693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 680607881494350333859795 1020911822241525500789693)
                  ·
                    refine ⟨382841933340572062796135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1020911822241525500789693 382841933340572062796135)
                    ·
                      rfl

theorem cell22_1118373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_1118373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118373 prefixEnd_1118373 := by exact prefixLift 1118373
  have htrace : WordTrace (prefixWord ++ tailWord_1118373) baseStart_1118373 baseEnd_1118373 := by
    simpa [prefixWord, tailWord_1118373, baseEnd_1118373] using wordTrace_append hprefix tailTrace_1118373
  have hstable : (prefixWord ++ tailWord_1118373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118373).length < 2 ^ (prefixWord ++ tailWord_1118373).sum := by decide
  have hdescent : baseEnd_1118373 < baseStart_1118373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118397 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 8]
def baseStart_1118397 : Nat := 118140960795 + 1118397 * 2 ^ 59
def prefixEnd_1118397 : Nat := 4983230072969 + 3 ^ 40 * 1118397 * 2
def baseEnd_1118397 : Nat := 127616716343681333398687

theorem tailTrace_1118397 : CollatzResearch.WordTrace tailWord_1118397 prefixEnd_1118397 127616716343681333398687 := by
  unfold tailWord_1118397
  simp only [CollatzResearch.WordTrace]
  refine ⟨40791289729246150845865445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27194193152830767230576963 40791289729246150845865445)
  ·
    refine ⟨7648366824233653283599771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40791289729246150845865445 7648366824233653283599771)
    ·
      refine ⟨11472550236350479925399657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7648366824233653283599771 11472550236350479925399657)
      ·
        refine ⟨8604412677262859944049743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11472550236350479925399657 8604412677262859944049743)
        ·
          refine ⟨12906619015894289916074615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8604412677262859944049743 12906619015894289916074615)
          ·
            refine ⟨19359928523841434874111923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12906619015894289916074615 19359928523841434874111923)
            ·
              refine ⟨29039892785762152311167885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19359928523841434874111923 29039892785762152311167885)
              ·
                refine ⟨10889959794660807116687957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29039892785762152311167885 10889959794660807116687957)
                ·
                  refine ⟨127616716343681333398687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10889959794660807116687957 127616716343681333398687)
                  ·
                    rfl

theorem cell22_1118397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_1118397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118397 prefixEnd_1118397 := by exact prefixLift 1118397
  have htrace : WordTrace (prefixWord ++ tailWord_1118397) baseStart_1118397 baseEnd_1118397 := by
    simpa [prefixWord, tailWord_1118397, baseEnd_1118397] using wordTrace_append hprefix tailTrace_1118397
  have hstable : (prefixWord ++ tailWord_1118397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118397).length < 2 ^ (prefixWord ++ tailWord_1118397).sum := by decide
  have hdescent : baseEnd_1118397 < baseStart_1118397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118457 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 1, 9]
def baseStart_1118457 : Nat := 118140960795 + 1118457 * 2 ^ 59
def prefixEnd_1118457 : Nat := 4983230072969 + 3 ^ 40 * 1118457 * 2
def baseEnd_1118457 : Nat := 382870688257223843695877

theorem tailTrace_1118457 : CollatzResearch.WordTrace tailWord_1118457 prefixEnd_1118457 382870688257223843695877 := by
  unfold tailWord_1118457
  simp only [CollatzResearch.WordTrace]
  refine ⟨40793478109028781093049625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27195652072685854062033083 40793478109028781093049625)
  ·
    refine ⟨30595108581771585819787219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40793478109028781093049625 30595108581771585819787219)
    ·
      refine ⟨45892662872657378729680829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30595108581771585819787219 45892662872657378729680829)
      ·
        refine ⟨17209748577246517023630311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45892662872657378729680829 17209748577246517023630311)
        ·
          refine ⟨25814622865869775535445467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17209748577246517023630311 25814622865869775535445467)
          ·
            refine ⟨38721934298804663303168201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25814622865869775535445467 38721934298804663303168201)
            ·
              refine ⟨29041450724103497477376151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38721934298804663303168201 29041450724103497477376151)
              ·
                refine ⟨43562176086155246216064227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29041450724103497477376151 43562176086155246216064227)
                ·
                  refine ⟨65343264129232869324096341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43562176086155246216064227 65343264129232869324096341)
                  ·
                    refine ⟨382870688257223843695877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 65343264129232869324096341 382870688257223843695877)
                    ·
                      rfl

theorem cell22_1118457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_1118457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118457 prefixEnd_1118457 := by exact prefixLift 1118457
  have htrace : WordTrace (prefixWord ++ tailWord_1118457) baseStart_1118457 baseEnd_1118457 := by
    simpa [prefixWord, tailWord_1118457, baseEnd_1118457] using wordTrace_append hprefix tailTrace_1118457
  have hstable : (prefixWord ++ tailWord_1118457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118457).length < 2 ^ (prefixWord ++ tailWord_1118457).sum := by decide
  have hdescent : baseEnd_1118457 < baseStart_1118457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118510 : List Nat := [4, 1, 3, 3, 1, 2, 2, 6]
def baseStart_1118510 : Nat := 118140960795 + 1118510 * 2 ^ 59
def prefixEnd_1118510 : Nat := 4983230072969 + 3 ^ 40 * 1118510 * 2
def baseEnd_1118510 : Nat := 42543203471149930235635

theorem tailTrace_1118510 : CollatzResearch.WordTrace tailWord_1118510 prefixEnd_1118510 42543203471149930235635 := by
  unfold tailWord_1118510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5099426397229596393091123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27196940785224514096485989 5099426397229596393091123)
  ·
    refine ⟨7649139595844394589636685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5099426397229596393091123 7649139595844394589636685)
    ·
      refine ⟨2868427348441647971113757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7649139595844394589636685 2868427348441647971113757)
      ·
        refine ⟨1075660255665617989167659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2868427348441647971113757 1075660255665617989167659)
        ·
          refine ⟨1613490383498426983751489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075660255665617989167659 1613490383498426983751489)
          ·
            refine ⟨1210117787623820237813617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1613490383498426983751489 1210117787623820237813617)
            ·
              refine ⟨907588340717865178360213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1210117787623820237813617 907588340717865178360213)
              ·
                refine ⟨42543203471149930235635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 907588340717865178360213 42543203471149930235635)
                ·
                  rfl

theorem cell22_1118510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_1118510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118510 prefixEnd_1118510 := by exact prefixLift 1118510
  have htrace : WordTrace (prefixWord ++ tailWord_1118510) baseStart_1118510 baseEnd_1118510 := by
    simpa [prefixWord, tailWord_1118510, baseEnd_1118510] using wordTrace_append hprefix tailTrace_1118510
  have hstable : (prefixWord ++ tailWord_1118510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118510).length < 2 ^ (prefixWord ++ tailWord_1118510).sum := by decide
  have hdescent : baseEnd_1118510 < baseStart_1118510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118568 : List Nat := [2, 1, 4, 2, 2, 1, 3, 2, 1, 4]
def baseStart_1118568 : Nat := 118140960795 + 1118568 * 2 ^ 59
def prefixEnd_1118568 : Nat := 4983230072969 + 3 ^ 40 * 1118568 * 2
def baseEnd_1118568 : Nat := 382908685825656554170537

theorem tailTrace_1118568 : CollatzResearch.WordTrace tailWord_1118568 prefixEnd_1118568 382908685825656554170537 := by
  unfold tailWord_1118568
  simp only [CollatzResearch.WordTrace]
  refine ⟨20398763305813323525170179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27198351074417764700226905 20398763305813323525170179)
  ·
    refine ⟨30598144958719985287755269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20398763305813323525170179 30598144958719985287755269)
    ·
      refine ⟨5737152179759997241454113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30598144958719985287755269 5737152179759997241454113)
      ·
        refine ⟨4302864134819997931090585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5737152179759997241454113 4302864134819997931090585)
        ·
          refine ⟨3227148101114998448317939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4302864134819997931090585 3227148101114998448317939)
          ·
            refine ⟨4840722151672497672476909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3227148101114998448317939 4840722151672497672476909)
            ·
              refine ⟨1815270806877186627178841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4840722151672497672476909 1815270806877186627178841)
              ·
                refine ⟨1361453105157889970384131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1815270806877186627178841 1361453105157889970384131)
                ·
                  refine ⟨2042179657736834955576197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361453105157889970384131 2042179657736834955576197)
                  ·
                    refine ⟨382908685825656554170537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2042179657736834955576197 382908685825656554170537)
                    ·
                      rfl

theorem cell22_1118568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_1118568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118568 prefixEnd_1118568 := by exact prefixLift 1118568
  have htrace : WordTrace (prefixWord ++ tailWord_1118568) baseStart_1118568 baseEnd_1118568 := by
    simpa [prefixWord, tailWord_1118568, baseEnd_1118568] using wordTrace_append hprefix tailTrace_1118568
  have hstable : (prefixWord ++ tailWord_1118568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118568).length < 2 ^ (prefixWord ++ tailWord_1118568).sum := by decide
  have hdescent : baseEnd_1118568 < baseStart_1118568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118579 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 6, 4]
def baseStart_1118579 : Nat := 118140960795 + 1118579 * 2 ^ 59
def prefixEnd_1118579 : Nat := 4983230072969 + 3 ^ 40 * 1118579 * 2
def baseEnd_1118579 : Nat := 382912451350456192145503

theorem tailTrace_1118579 : CollatzResearch.WordTrace tailWord_1118579 prefixEnd_1118579 382912451350456192145503 := by
  unfold tailWord_1118579
  simp only [CollatzResearch.WordTrace]
  refine ⟨40797927814586795928990791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27198618543057863952660527 40797927814586795928990791)
  ·
    refine ⟨61196891721880193893486187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40797927814586795928990791 61196891721880193893486187)
    ·
      refine ⟨91795337582820290840229281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61196891721880193893486187 91795337582820290840229281)
      ·
        refine ⟨68846503187115218130171961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91795337582820290840229281 68846503187115218130171961)
        ·
          refine ⟨51634877390336413597628971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68846503187115218130171961 51634877390336413597628971)
          ·
            refine ⟨77452316085504620396443457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51634877390336413597628971 77452316085504620396443457)
            ·
              refine ⟨58089237064128465297332593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77452316085504620396443457 58089237064128465297332593)
              ·
                refine ⟨43566927798096348972999445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58089237064128465297332593 43566927798096348972999445)
                ·
                  refine ⟨2042199740535766358109349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43566927798096348972999445 2042199740535766358109349)
                  ·
                    refine ⟨382912451350456192145503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2042199740535766358109349 382912451350456192145503)
                    ·
                      rfl

theorem cell22_1118579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 4].length) (baseStart_1118579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118579 prefixEnd_1118579 := by exact prefixLift 1118579
  have htrace : WordTrace (prefixWord ++ tailWord_1118579) baseStart_1118579 baseEnd_1118579 := by
    simpa [prefixWord, tailWord_1118579, baseEnd_1118579] using wordTrace_append hprefix tailTrace_1118579
  have hstable : (prefixWord ++ tailWord_1118579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118579).length < 2 ^ (prefixWord ++ tailWord_1118579).sum := by decide
  have hdescent : baseEnd_1118579 < baseStart_1118579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
