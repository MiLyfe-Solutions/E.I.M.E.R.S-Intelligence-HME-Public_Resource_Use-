import V185TrunkScan23Chunk0937

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5552010 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_5552010 : Nat := 118140960795 + 5552010 * 2 ^ 59
def prefixEnd_5552010 : Nat := 4983230072969 + 3 ^ 40 * 5552010 * 2
def baseEnd_5552010 : Nat := 2850849728568927969041777

theorem tailTrace_5552010 : CollatzResearch.WordTrace tailWord_5552010 prefixEnd_5552010 2850849728568927969041777 := by
  unfold tailWord_5552010
  simp only [CollatzResearch.WordTrace]
  refine ⟨50624610154005863165607371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134998960410682301774952989 50624610154005863165607371)
  ·
    refine ⟨75936915231008794748411057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50624610154005863165607371 75936915231008794748411057)
    ·
      refine ⟨56952686423256596061308293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75936915231008794748411057 56952686423256596061308293)
      ·
        refine ⟨10678628704360611761495305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56952686423256596061308293 10678628704360611761495305)
        ·
          refine ⟨8008971528270458821121479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10678628704360611761495305 8008971528270458821121479)
          ·
            refine ⟨12013457292405688231682219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8008971528270458821121479 12013457292405688231682219)
            ·
              refine ⟨18020185938608532347523329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12013457292405688231682219 18020185938608532347523329)
              ·
                refine ⟨13515139453956399260642497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18020185938608532347523329 13515139453956399260642497)
                ·
                  refine ⟨10136354590467299445481873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13515139453956399260642497 10136354590467299445481873)
                  ·
                    refine ⟨7602265942850474584111405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10136354590467299445481873 7602265942850474584111405)
                    ·
                      refine ⟨2850849728568927969041777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7602265942850474584111405 2850849728568927969041777)
                      ·
                        rfl

theorem cell23_5552010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_5552010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552010 prefixEnd_5552010 := by exact prefixLift 5552010
  have htrace : WordTrace (prefixWord ++ tailWord_5552010) baseStart_5552010 baseEnd_5552010 := by
    simpa [prefixWord, tailWord_5552010, baseEnd_5552010] using wordTrace_append hprefix tailTrace_5552010
  have hstable : (prefixWord ++ tailWord_5552010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552010).length < 2 ^ (prefixWord ++ tailWord_5552010).sum := by decide
  have hdescent : baseEnd_5552010 < baseStart_5552010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552056 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 1, 6]
def baseStart_5552056 : Nat := 118140960795 + 5552056 * 2 ^ 59
def prefixEnd_5552056 : Nat := 4983230072969 + 3 ^ 40 * 5552056 * 2
def baseEnd_5552056 : Nat := 950291116226344929688855

theorem tailTrace_5552056 : CollatzResearch.WordTrace tailWord_5552056 prefixEnd_5552056 950291116226344929688855 := by
  unfold tailWord_5552056
  simp only [CollatzResearch.WordTrace]
  refine ⟨101250059186928401259302011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135000078915904535012402681 101250059186928401259302011)
  ·
    refine ⟨151875088780392601888953017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101250059186928401259302011 151875088780392601888953017)
    ·
      refine ⟨113906316585294451416714763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151875088780392601888953017 113906316585294451416714763)
      ·
        refine ⟨170859474877941677125072145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113906316585294451416714763 170859474877941677125072145)
        ·
          refine ⟨128144606158456257843804109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170859474877941677125072145 128144606158456257843804109)
          ·
            refine ⟨48054227309421096691426541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128144606158456257843804109 48054227309421096691426541)
            ·
              refine ⟨18020335241032911259284953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48054227309421096691426541 18020335241032911259284953)
              ·
                refine ⟨13515251430774683444463715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18020335241032911259284953 13515251430774683444463715)
                ·
                  refine ⟨20272877146162025166695573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13515251430774683444463715 20272877146162025166695573)
                  ·
                    refine ⟨950291116226344929688855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20272877146162025166695573 950291116226344929688855)
                    ·
                      rfl

theorem cell23_5552056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_5552056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552056 prefixEnd_5552056 := by exact prefixLift 5552056
  have htrace : WordTrace (prefixWord ++ tailWord_5552056) baseStart_5552056 baseEnd_5552056 := by
    simpa [prefixWord, tailWord_5552056, baseEnd_5552056] using wordTrace_append hprefix tailTrace_5552056
  have hstable : (prefixWord ++ tailWord_5552056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552056).length < 2 ^ (prefixWord ++ tailWord_5552056).sum := by decide
  have hdescent : baseEnd_5552056 < baseStart_5552056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552141 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_5552141 : Nat := 118140960795 + 5552141 * 2 ^ 59
def prefixEnd_5552141 : Nat := 4983230072969 + 3 ^ 40 * 5552141 * 2
def baseEnd_5552141 : Nat := 950305664844888985501225

theorem tailTrace_5552141 : CollatzResearch.WordTrace tailWord_5552141 prefixEnd_5552141 950305664844888985501225 := by
  unfold tailWord_5552141
  simp only [CollatzResearch.WordTrace]
  refine ⟨202503218578548862035448277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135002145719032574690298851 202503218578548862035448277)
  ·
    refine ⟨4746169185434738953955819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 202503218578548862035448277 4746169185434738953955819)
    ·
      refine ⟨7119253778152108430933729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4746169185434738953955819 7119253778152108430933729)
      ·
        refine ⟨5339440333614081323200297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7119253778152108430933729 5339440333614081323200297)
        ·
          refine ⟨4004580250210560992400223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5339440333614081323200297 4004580250210560992400223)
          ·
            refine ⟨6006870375315841488600335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4004580250210560992400223 6006870375315841488600335)
            ·
              refine ⟨9010305562973762232900503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6006870375315841488600335 9010305562973762232900503)
              ·
                refine ⟨13515458344460643349350755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9010305562973762232900503 13515458344460643349350755)
                ·
                  refine ⟨20273187516690965024026133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13515458344460643349350755 20273187516690965024026133)
                  ·
                    refine ⟨950305664844888985501225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20273187516690965024026133 950305664844888985501225)
                    ·
                      rfl

theorem cell23_5552141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_5552141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552141 prefixEnd_5552141 := by exact prefixLift 5552141
  have htrace : WordTrace (prefixWord ++ tailWord_5552141) baseStart_5552141 baseEnd_5552141 := by
    simpa [prefixWord, tailWord_5552141, baseEnd_5552141] using wordTrace_append hprefix tailTrace_5552141
  have hstable : (prefixWord ++ tailWord_5552141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552141).length < 2 ^ (prefixWord ++ tailWord_5552141).sum := by decide
  have hdescent : baseEnd_5552141 < baseStart_5552141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552157 : List Nat := [1, 4, 2, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_5552157 : Nat := 118140960795 + 5552157 * 2 ^ 59
def prefixEnd_5552157 : Nat := 4983230072969 + 3 ^ 40 * 5552157 * 2
def baseEnd_5552157 : Nat := 2850925210225138893903601

theorem tailTrace_5552157 : CollatzResearch.WordTrace tailWord_5552157 prefixEnd_5552157 2850925210225138893903601 := by
  unfold tailWord_5552157
  simp only [CollatzResearch.WordTrace]
  refine ⟨202503802146490896768030725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135002534764327264512020483 202503802146490896768030725)
  ·
    refine ⟨37969462902467043144005761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202503802146490896768030725 37969462902467043144005761)
    ·
      refine ⟨28477097176850282358004321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37969462902467043144005761 28477097176850282358004321)
      ·
        refine ⟨21357822882637711768503241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28477097176850282358004321 21357822882637711768503241)
        ·
          refine ⟨16018367161978283826377431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21357822882637711768503241 16018367161978283826377431)
          ·
            refine ⟨24027550742967425739566147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16018367161978283826377431 24027550742967425739566147)
            ·
              refine ⟨36041326114451138609349221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24027550742967425739566147 36041326114451138609349221)
              ·
                refine ⟨6757748646459588489252979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36041326114451138609349221 6757748646459588489252979)
                ·
                  refine ⟨10136622969689382733879469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6757748646459588489252979 10136622969689382733879469)
                  ·
                    refine ⟨3801233613633518525204801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10136622969689382733879469 3801233613633518525204801)
                    ·
                      refine ⟨2850925210225138893903601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801233613633518525204801 2850925210225138893903601)
                      ·
                        rfl

theorem cell23_5552157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_5552157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552157 prefixEnd_5552157 := by exact prefixLift 5552157
  have htrace : WordTrace (prefixWord ++ tailWord_5552157) baseStart_5552157 baseEnd_5552157 := by
    simpa [prefixWord, tailWord_5552157, baseEnd_5552157] using wordTrace_append hprefix tailTrace_5552157
  have hstable : (prefixWord ++ tailWord_5552157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552157).length < 2 ^ (prefixWord ++ tailWord_5552157).sum := by decide
  have hdescent : baseEnd_5552157 < baseStart_5552157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552186 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_5552186 : Nat := 118140960795 + 5552186 * 2 ^ 59
def prefixEnd_5552186 : Nat := 4983230072969 + 3 ^ 40 * 5552186 * 2
def baseEnd_5552186 : Nat := 2850940101164119280440967

theorem tailTrace_5552186 : CollatzResearch.WordTrace tailWord_5552186 prefixEnd_5552186 2850940101164119280440967 := by
  unfold tailWord_5552186
  simp only [CollatzResearch.WordTrace]
  refine ⟨50626214965846458680209103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135003239908923889813890941 50626214965846458680209103)
  ·
    refine ⟨75939322448769688020313655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50626214965846458680209103 75939322448769688020313655)
    ·
      refine ⟨113908983673154532030470483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75939322448769688020313655 113908983673154532030470483)
      ·
        refine ⟨170863475509731798045705725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113908983673154532030470483 170863475509731798045705725)
        ·
          refine ⟨64073803316149424267139647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170863475509731798045705725 64073803316149424267139647)
          ·
            refine ⟨96110704974224136400709471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64073803316149424267139647 96110704974224136400709471)
            ·
              refine ⟨144166057461336204601064207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96110704974224136400709471 144166057461336204601064207)
              ·
                refine ⟨216249086192004306901596311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144166057461336204601064207 216249086192004306901596311)
                ·
                  refine ⟨324373629288006460352394467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216249086192004306901596311 324373629288006460352394467)
                  ·
                    refine ⟨486560443932009690528591701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 324373629288006460352394467 486560443932009690528591701)
                    ·
                      refine ⟨2850940101164119280440967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 486560443932009690528591701 2850940101164119280440967)
                      ·
                        rfl

theorem cell23_5552186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_5552186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552186 prefixEnd_5552186 := by exact prefixLift 5552186
  have htrace : WordTrace (prefixWord ++ tailWord_5552186) baseStart_5552186 baseEnd_5552186 := by
    simpa [prefixWord, tailWord_5552186, baseEnd_5552186] using wordTrace_append hprefix tailTrace_5552186
  have hstable : (prefixWord ++ tailWord_5552186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552186).length < 2 ^ (prefixWord ++ tailWord_5552186).sum := by decide
  have hdescent : baseEnd_5552186 < baseStart_5552186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552204 : List Nat := [2, 2, 1, 3, 1, 1, 6, 1, 2, 2, 2]
def baseStart_5552204 : Nat := 118140960795 + 5552204 * 2 ^ 59
def prefixEnd_5552204 : Nat := 4983230072969 + 3 ^ 40 * 5552204 * 2
def baseEnd_5552204 : Nat := 2850949343815900210015885

theorem tailTrace_5552204 : CollatzResearch.WordTrace tailWord_5552204 prefixEnd_5552204 2850949343815900210015885 := by
  unfold tailWord_5552204
  simp only [CollatzResearch.WordTrace]
  refine ⟨101252758188660311897495833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135003677584880415863327777 101252758188660311897495833)
  ·
    refine ⟨75939568641495233923121875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101252758188660311897495833 75939568641495233923121875)
    ·
      refine ⟨113909352962242850884682813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75939568641495233923121875 113909352962242850884682813)
      ·
        refine ⟨42716007360841069081756055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113909352962242850884682813 42716007360841069081756055)
        ·
          refine ⟨64074011041261603622634083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42716007360841069081756055 64074011041261603622634083)
          ·
            refine ⟨96111016561892405433951125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64074011041261603622634083 96111016561892405433951125)
            ·
              refine ⟨4505203901338706504716459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96111016561892405433951125 4505203901338706504716459)
              ·
                refine ⟨6757805852008059757074689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4505203901338706504716459 6757805852008059757074689)
                ·
                  refine ⟨5068354389006044817806017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6757805852008059757074689 5068354389006044817806017)
                  ·
                    refine ⟨3801265791754533613354513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5068354389006044817806017 3801265791754533613354513)
                    ·
                      refine ⟨2850949343815900210015885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801265791754533613354513 2850949343815900210015885)
                      ·
                        rfl

theorem cell23_5552204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_5552204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552204 prefixEnd_5552204 := by exact prefixLift 5552204
  have htrace : WordTrace (prefixWord ++ tailWord_5552204) baseStart_5552204 baseEnd_5552204 := by
    simpa [prefixWord, tailWord_5552204, baseEnd_5552204] using wordTrace_append hprefix tailTrace_5552204
  have hstable : (prefixWord ++ tailWord_5552204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552204).length < 2 ^ (prefixWord ++ tailWord_5552204).sum := by decide
  have hdescent : baseEnd_5552204 < baseStart_5552204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552290 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_5552290 : Nat := 118140960795 + 5552290 * 2 ^ 59
def prefixEnd_5552290 : Nat := 4983230072969 + 3 ^ 40 * 5552290 * 2
def baseEnd_5552290 : Nat := 2850993503152186873540489

theorem tailTrace_5552290 : CollatzResearch.WordTrace tailWord_5552290 prefixEnd_5552290 2850993503152186873540489 := by
  unfold tailWord_5552290
  simp only [CollatzResearch.WordTrace]
  refine ⟨50627163263752265120655581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135005768703339373655081549 50627163263752265120655581)
  ·
    refine ⟨18985186223907099420245843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50627163263752265120655581 18985186223907099420245843)
    ·
      refine ⟨28477779335860649130368765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18985186223907099420245843 28477779335860649130368765)
      ·
        refine ⟨10679167250947743423888287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28477779335860649130368765 10679167250947743423888287)
        ·
          refine ⟨16018750876421615135832431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10679167250947743423888287 16018750876421615135832431)
          ·
            refine ⟨24028126314632422703748647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16018750876421615135832431 24028126314632422703748647)
            ·
              refine ⟨36042189471948634055622971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24028126314632422703748647 36042189471948634055622971)
              ·
                refine ⟨54063284207922951083434457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36042189471948634055622971 54063284207922951083434457)
                ·
                  refine ⟨40547463155942213312575843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54063284207922951083434457 40547463155942213312575843)
                  ·
                    refine ⟨60821194733913319968863765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40547463155942213312575843 60821194733913319968863765)
                    ·
                      refine ⟨2850993503152186873540489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60821194733913319968863765 2850993503152186873540489)
                      ·
                        rfl

theorem cell23_5552290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_5552290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552290 prefixEnd_5552290 := by exact prefixLift 5552290
  have htrace : WordTrace (prefixWord ++ tailWord_5552290) baseStart_5552290 baseEnd_5552290 := by
    simpa [prefixWord, tailWord_5552290, baseEnd_5552290] using wordTrace_append hprefix tailTrace_5552290
  have hstable : (prefixWord ++ tailWord_5552290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552290).length < 2 ^ (prefixWord ++ tailWord_5552290).sum := by decide
  have hdescent : baseEnd_5552290 < baseStart_5552290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552343 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 3, 6]
def baseStart_5552343 : Nat := 118140960795 + 5552343 * 2 ^ 59
def prefixEnd_5552343 : Nat := 4983230072969 + 3 ^ 40 * 5552343 * 2
def baseEnd_5552343 : Nat := 950340239208958388725915

theorem tailTrace_5552343 : CollatzResearch.WordTrace tailWord_5552343 prefixEnd_5552343 950340239208958388725915 := by
  unfold tailWord_5552343
  simp only [CollatzResearch.WordTrace]
  refine ⟨202510586123817050534301683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135007057415878033689534455 202510586123817050534301683)
  ·
    refine ⟨303765879185725575801452525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202510586123817050534301683 303765879185725575801452525)
    ·
      refine ⟨113912204694647090925544697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303765879185725575801452525 113912204694647090925544697)
      ·
        refine ⟨85434153520985318194158523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113912204694647090925544697 85434153520985318194158523)
        ·
          refine ⟨128151230281477977291237785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85434153520985318194158523 128151230281477977291237785)
          ·
            refine ⟨96113422711108482968428339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128151230281477977291237785 96113422711108482968428339)
            ·
              refine ⟨144170134066662724452642509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96113422711108482968428339 144170134066662724452642509)
              ·
                refine ⟨54063800274998521669740941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144170134066662724452642509 54063800274998521669740941)
                ·
                  refine ⟨20273925103124445626152853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54063800274998521669740941 20273925103124445626152853)
                  ·
                    refine ⟨950340239208958388725915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20273925103124445626152853 950340239208958388725915)
                    ·
                      rfl

theorem cell23_5552343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_5552343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552343 prefixEnd_5552343 := by exact prefixLift 5552343
  have htrace : WordTrace (prefixWord ++ tailWord_5552343) baseStart_5552343 baseEnd_5552343 := by
    simpa [prefixWord, tailWord_5552343, baseEnd_5552343] using wordTrace_append hprefix tailTrace_5552343
  have hstable : (prefixWord ++ tailWord_5552343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552343).length < 2 ^ (prefixWord ++ tailWord_5552343).sum := by decide
  have hdescent : baseEnd_5552343 < baseStart_5552343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552363 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 6]
def baseStart_5552363 : Nat := 118140960795 + 5552363 * 2 ^ 59
def prefixEnd_5552363 : Nat := 4983230072969 + 3 ^ 40 * 5552363 * 2
def baseEnd_5552363 : Nat := 2851030987239965087927653

theorem tailTrace_5552363 : CollatzResearch.WordTrace tailWord_5552363 prefixEnd_5552363 2851030987239965087927653 := by
  unfold tailWord_5552363
  simp only [CollatzResearch.WordTrace]
  refine ⟨202511315583744593950029743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135007543722496395966686495 202511315583744593950029743)
  ·
    refine ⟨303766973375616890925044615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202511315583744593950029743 303766973375616890925044615)
    ·
      refine ⟨455650460063425336387566923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303766973375616890925044615 455650460063425336387566923)
      ·
        refine ⟨683475690095138004581350385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455650460063425336387566923 683475690095138004581350385)
        ·
          refine ⟨512606767571353503436012789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683475690095138004581350385 512606767571353503436012789)
          ·
            refine ⟨48056884459814390947126199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 512606767571353503436012789 48056884459814390947126199)
            ·
              refine ⟨72085326689721586420689299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48056884459814390947126199 72085326689721586420689299)
              ·
                refine ⟨108127990034582379631033949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72085326689721586420689299 108127990034582379631033949)
                ·
                  refine ⟨40547996262968392361637731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108127990034582379631033949 40547996262968392361637731)
                  ·
                    refine ⟨60821994394452588542456597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40547996262968392361637731 60821994394452588542456597)
                    ·
                      refine ⟨2851030987239965087927653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60821994394452588542456597 2851030987239965087927653)
                      ·
                        rfl

theorem cell23_5552363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 6].length) (baseStart_5552363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552363 prefixEnd_5552363 := by exact prefixLift 5552363
  have htrace : WordTrace (prefixWord ++ tailWord_5552363) baseStart_5552363 baseEnd_5552363 := by
    simpa [prefixWord, tailWord_5552363, baseEnd_5552363] using wordTrace_append hprefix tailTrace_5552363
  have hstable : (prefixWord ++ tailWord_5552363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552363).length < 2 ^ (prefixWord ++ tailWord_5552363).sum := by decide
  have hdescent : baseEnd_5552363 < baseStart_5552363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552380 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_5552380 : Nat := 118140960795 + 5552380 * 2 ^ 59
def prefixEnd_5552380 : Nat := 4983230072969 + 3 ^ 40 * 5552380 * 2
def baseEnd_5552380 : Nat := 2851039716411091521415075

theorem tailTrace_5552380 : CollatzResearch.WordTrace tailWord_5552380 prefixEnd_5552380 2851039716411091521415075 := by
  unfold tailWord_5552380
  simp only [CollatzResearch.WordTrace]
  refine ⟨101255967812341502926699297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135007957083122003902265729 101255967812341502926699297)
  ·
    refine ⟨75941975859256127195024473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101255967812341502926699297 75941975859256127195024473)
    ·
      refine ⟨56956481894442095396268355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75941975859256127195024473 56956481894442095396268355)
      ·
        refine ⟨85434722841663143094402533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56956481894442095396268355 85434722841663143094402533)
        ·
          refine ⟨16019010532811839330200475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85434722841663143094402533 16019010532811839330200475)
          ·
            refine ⟨24028515799217758995300713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16019010532811839330200475 24028515799217758995300713)
            ·
              refine ⟨18021386849413319246475535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24028515799217758995300713 18021386849413319246475535)
              ·
                refine ⟨27032080274119978869713303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18021386849413319246475535 27032080274119978869713303)
                ·
                  refine ⟨40548120411179968304569955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27032080274119978869713303 40548120411179968304569955)
                  ·
                    refine ⟨60822180616769952456854933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40548120411179968304569955 60822180616769952456854933)
                    ·
                      refine ⟨2851039716411091521415075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60822180616769952456854933 2851039716411091521415075)
                      ·
                        rfl

theorem cell23_5552380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_5552380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552380 prefixEnd_5552380 := by exact prefixLift 5552380
  have htrace : WordTrace (prefixWord ++ tailWord_5552380) baseStart_5552380 baseEnd_5552380 := by
    simpa [prefixWord, tailWord_5552380, baseEnd_5552380] using wordTrace_append hprefix tailTrace_5552380
  have hstable : (prefixWord ++ tailWord_5552380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552380).length < 2 ^ (prefixWord ++ tailWord_5552380).sum := by decide
  have hdescent : baseEnd_5552380 < baseStart_5552380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552403 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 4, 7]
def baseStart_5552403 : Nat := 118140960795 + 5552403 * 2 ^ 59
def prefixEnd_5552403 : Nat := 4983230072969 + 3 ^ 40 * 5552403 * 2
def baseEnd_5552403 : Nat := 950350508822048310475823

theorem tailTrace_5552403 : CollatzResearch.WordTrace tailWord_5552403 prefixEnd_5552403 950350508822048310475823 := by
  unfold tailWord_5552403
  simp only [CollatzResearch.WordTrace]
  refine ⟨202512774503599680781485863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135008516335733120520990575 202512774503599680781485863)
  ·
    refine ⟨303769161755399521172228795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202512774503599680781485863 303769161755399521172228795)
    ·
      refine ⟨455653742633099281758343193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303769161755399521172228795 455653742633099281758343193)
      ·
        refine ⟨341740306974824461318757395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 455653742633099281758343193 341740306974824461318757395)
        ·
          refine ⟨512610460462236691978136093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341740306974824461318757395 512610460462236691978136093)
          ·
            refine ⟨192228922673338759491801035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 512610460462236691978136093 192228922673338759491801035)
            ·
              refine ⟨288343384010008139237701553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192228922673338759491801035 288343384010008139237701553)
              ·
                refine ⟨216257538007506104428276165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288343384010008139237701553 216257538007506104428276165)
                ·
                  refine ⟨40548288376407394580301781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 216257538007506104428276165 40548288376407394580301781)
                  ·
                    refine ⟨950350508822048310475823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40548288376407394580301781 950350508822048310475823)
                    ·
                      rfl

theorem cell23_5552403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 7].length) (baseStart_5552403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552403 prefixEnd_5552403 := by exact prefixLift 5552403
  have htrace : WordTrace (prefixWord ++ tailWord_5552403) baseStart_5552403 baseEnd_5552403 := by
    simpa [prefixWord, tailWord_5552403, baseEnd_5552403] using wordTrace_append hprefix tailTrace_5552403
  have hstable : (prefixWord ++ tailWord_5552403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552403).length < 2 ^ (prefixWord ++ tailWord_5552403).sum := by decide
  have hdescent : baseEnd_5552403 < baseStart_5552403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552417 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 4, 1, 3]
def baseStart_5552417 : Nat := 118140960795 + 5552417 * 2 ^ 59
def prefixEnd_5552417 : Nat := 4983230072969 + 3 ^ 40 * 5552417 * 2
def baseEnd_5552417 : Nat := 2851058715195307876652405

theorem tailTrace_5552417 : CollatzResearch.WordTrace tailWord_5552417 prefixEnd_5552417 2851058715195307876652405 := by
  unfold tailWord_5552417
  simp only [CollatzResearch.WordTrace]
  refine ⟨202513285125548961172495505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135008856750365974114997003 202513285125548961172495505)
  ·
    refine ⟨151884963844161720879371629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202513285125548961172495505 151884963844161720879371629)
    ·
      refine ⟨56956861441560645329764361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151884963844161720879371629 56956861441560645329764361)
      ·
        refine ⟨42717646081170483997323271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56956861441560645329764361 42717646081170483997323271)
        ·
          refine ⟨64076469121755725995984907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42717646081170483997323271 64076469121755725995984907)
          ·
            refine ⟨96114703682633588993977361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64076469121755725995984907 96114703682633588993977361)
            ·
              refine ⟨72086027761975191745483021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96114703682633588993977361 72086027761975191745483021)
              ·
                refine ⟨27032260410740696904556133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72086027761975191745483021 27032260410740696904556133)
                ·
                  refine ⟨5068548827013880669604275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27032260410740696904556133 5068548827013880669604275)
                  ·
                    refine ⟨7602823240520821004406413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5068548827013880669604275 7602823240520821004406413)
                    ·
                      refine ⟨2851058715195307876652405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7602823240520821004406413 2851058715195307876652405)
                      ·
                        rfl

theorem cell23_5552417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_5552417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552417 prefixEnd_5552417 := by exact prefixLift 5552417
  have htrace : WordTrace (prefixWord ++ tailWord_5552417) baseStart_5552417 baseEnd_5552417 := by
    simpa [prefixWord, tailWord_5552417, baseEnd_5552417] using wordTrace_append hprefix tailTrace_5552417
  have hstable : (prefixWord ++ tailWord_5552417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552417).length < 2 ^ (prefixWord ++ tailWord_5552417).sum := by decide
  have hdescent : baseEnd_5552417 < baseStart_5552417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552418 : List Nat := [3, 3, 1, 1, 3, 2, 1, 4, 1, 2, 2]
def baseStart_5552418 : Nat := 118140960795 + 5552418 * 2 ^ 59
def prefixEnd_5552418 : Nat := 4983230072969 + 3 ^ 40 * 5552418 * 2
def baseEnd_5552418 : Nat := 2851059228675962372739901

theorem tailTrace_5552418 : CollatzResearch.WordTrace tailWord_5552418 prefixEnd_5552418 2851059228675962372739901 := by
  unfold tailWord_5552418
  simp only [CollatzResearch.WordTrace]
  refine ⟨50628330399636334585820477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135008881065696892228854605 50628330399636334585820477)
  ·
    refine ⟨18985623899863625469682679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50628330399636334585820477 18985623899863625469682679)
    ·
      refine ⟨28478435849795438204524019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18985623899863625469682679 28478435849795438204524019)
      ·
        refine ⟨42717653774693157306786029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28478435849795438204524019 42717653774693157306786029)
        ·
          refine ⟨16019120165509933990044761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42717653774693157306786029 16019120165509933990044761)
          ·
            refine ⟨12014340124132450492533571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16019120165509933990044761 12014340124132450492533571)
            ·
              refine ⟨18021510186198675738800357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12014340124132450492533571 18021510186198675738800357)
              ·
                refine ⟨3379033159912251701025067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18021510186198675738800357 3379033159912251701025067)
                ·
                  refine ⟨5068549739868377551537601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3379033159912251701025067 5068549739868377551537601)
                  ·
                    refine ⟨3801412304901283163653201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5068549739868377551537601 3801412304901283163653201)
                    ·
                      refine ⟨2851059228675962372739901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801412304901283163653201 2851059228675962372739901)
                      ·
                        rfl

theorem cell23_5552418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_5552418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552418 prefixEnd_5552418 := by exact prefixLift 5552418
  have htrace : WordTrace (prefixWord ++ tailWord_5552418) baseStart_5552418 baseEnd_5552418 := by
    simpa [prefixWord, tailWord_5552418, baseEnd_5552418] using wordTrace_append hprefix tailTrace_5552418
  have hstable : (prefixWord ++ tailWord_5552418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552418).length < 2 ^ (prefixWord ++ tailWord_5552418).sum := by decide
  have hdescent : baseEnd_5552418 < baseStart_5552418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552420 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_5552420 : Nat := 118140960795 + 5552420 * 2 ^ 59
def prefixEnd_5552420 : Nat := 4983230072969 + 3 ^ 40 * 5552420 * 2
def baseEnd_5552420 : Nat := 950353418545757121638297

theorem tailTrace_5552420 : CollatzResearch.WordTrace tailWord_5552420 prefixEnd_5552420 950353418545757121638297 := by
  unfold tailWord_5552420
  simp only [CollatzResearch.WordTrace]
  refine ⟨101256697272269046342427357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135008929696358728456569809 101256697272269046342427357)
  ·
    refine ⟨37971261477100892378410259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101256697272269046342427357 37971261477100892378410259)
    ·
      refine ⟨56956892215651338567615389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37971261477100892378410259 56956892215651338567615389)
      ·
        refine ⟨21358834580869251962855771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56956892215651338567615389 21358834580869251962855771)
        ·
          refine ⟨32038251871303877944283657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21358834580869251962855771 32038251871303877944283657)
          ·
            refine ⟨24028688903477908458212743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32038251871303877944283657 24028688903477908458212743)
            ·
              refine ⟨36043033355216862687319115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24028688903477908458212743 36043033355216862687319115)
              ·
                refine ⟨54064550032825294030978673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36043033355216862687319115 54064550032825294030978673)
                ·
                  refine ⟨40548412524618970523234005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54064550032825294030978673 40548412524618970523234005)
                  ·
                    refine ⟨950353418545757121638297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40548412524618970523234005 950353418545757121638297)
                    ·
                      rfl

theorem cell23_5552420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_5552420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552420 prefixEnd_5552420 := by exact prefixLift 5552420
  have htrace : WordTrace (prefixWord ++ tailWord_5552420) baseStart_5552420 baseEnd_5552420 := by
    simpa [prefixWord, tailWord_5552420, baseEnd_5552420] using wordTrace_append hprefix tailTrace_5552420
  have hstable : (prefixWord ++ tailWord_5552420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552420).length < 2 ^ (prefixWord ++ tailWord_5552420).sum := by decide
  have hdescent : baseEnd_5552420 < baseStart_5552420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552424 : List Nat := [2, 1, 5, 1, 4, 1, 1, 8]
def baseStart_5552424 : Nat := 118140960795 + 5552424 * 2 ^ 59
def prefixEnd_5552424 : Nat := 4983230072969 + 3 ^ 40 * 5552424 * 2
def baseEnd_5552424 : Nat := 105594900354069975898699

theorem tailTrace_5552424 : CollatzResearch.WordTrace tailWord_5552424 prefixEnd_5552424 105594900354069975898699 := by
  unfold tailWord_5552424
  simp only [CollatzResearch.WordTrace]
  refine ⟨101256770218261800684000163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135009026957682400912000217 101256770218261800684000163)
  ·
    refine ⟨151885155327392701026000245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101256770218261800684000163 151885155327392701026000245)
    ·
      refine ⟨14239233311943065721187523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151885155327392701026000245 14239233311943065721187523)
      ·
        refine ⟨21358849967914598581781285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14239233311943065721187523 21358849967914598581781285)
        ·
          refine ⟨4004784368983987234083991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21358849967914598581781285 4004784368983987234083991)
          ·
            refine ⟨6007176553475980851125987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4004784368983987234083991 6007176553475980851125987)
            ·
              refine ⟨9010764830213971276688981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6007176553475980851125987 9010764830213971276688981)
              ·
                refine ⟨105594900354069975898699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9010764830213971276688981 105594900354069975898699)
                ·
                  rfl

theorem cell23_5552424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 8].length) (baseStart_5552424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552424 prefixEnd_5552424 := by exact prefixLift 5552424
  have htrace : WordTrace (prefixWord ++ tailWord_5552424) baseStart_5552424 baseEnd_5552424 := by
    simpa [prefixWord, tailWord_5552424, baseEnd_5552424] using wordTrace_append hprefix tailTrace_5552424
  have hstable : (prefixWord ++ tailWord_5552424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552424).length < 2 ^ (prefixWord ++ tailWord_5552424).sum := by decide
  have hdescent : baseEnd_5552424 < baseStart_5552424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552434 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_5552434 : Nat := 118140960795 + 5552434 * 2 ^ 59
def prefixEnd_5552434 : Nat := 4983230072969 + 3 ^ 40 * 5552434 * 2
def baseEnd_5552434 : Nat := 2851067444366434310139827

theorem tailTrace_5552434 : CollatzResearch.WordTrace tailWord_5552434 prefixEnd_5552434 2851067444366434310139827 := by
  unfold tailWord_5552434
  simp only [CollatzResearch.WordTrace]
  refine ⟨50628476291621843268966089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135009270110991582050576237 50628476291621843268966089)
  ·
    refine ⟨37971357218716382451724567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50628476291621843268966089 37971357218716382451724567)
    ·
      refine ⟨56957035828074573677586851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37971357218716382451724567 56957035828074573677586851)
      ·
        refine ⟨85435553742111860516380277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56957035828074573677586851 85435553742111860516380277)
        ·
          refine ⟨8009583163322986923410651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85435553742111860516380277 8009583163322986923410651)
          ·
            refine ⟨12014374744984480385115977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8009583163322986923410651 12014374744984480385115977)
            ·
              refine ⟨9010781058738360288836983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12014374744984480385115977 9010781058738360288836983)
              ·
                refine ⟨13516171588107540433255475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9010781058738360288836983 13516171588107540433255475)
                ·
                  refine ⟨20274257382161310649883213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13516171588107540433255475 20274257382161310649883213)
                  ·
                    refine ⟨7602846518310491493706205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20274257382161310649883213 7602846518310491493706205)
                    ·
                      refine ⟨2851067444366434310139827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7602846518310491493706205 2851067444366434310139827)
                      ·
                        rfl

theorem cell23_5552434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_5552434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552434 prefixEnd_5552434 := by exact prefixLift 5552434
  have htrace : WordTrace (prefixWord ++ tailWord_5552434) baseStart_5552434 baseEnd_5552434 := by
    simpa [prefixWord, tailWord_5552434, baseEnd_5552434] using wordTrace_append hprefix tailTrace_5552434
  have hstable : (prefixWord ++ tailWord_5552434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552434).length < 2 ^ (prefixWord ++ tailWord_5552434).sum := by decide
  have hdescent : baseEnd_5552434 < baseStart_5552434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552444 : List Nat := [2, 2, 2, 2, 1, 2, 2, 4, 1, 3, 2]
def baseStart_5552444 : Nat := 118140960795 + 5552444 * 2 ^ 59
def prefixEnd_5552444 : Nat := 4983230072969 + 3 ^ 40 * 5552444 * 2
def baseEnd_5552444 : Nat := 2851072579172979271014781

theorem tailTrace_5552444 : CollatzResearch.WordTrace tailWord_5552444 prefixEnd_5552444 2851072579172979271014781 := by
  unfold tailWord_5552444
  simp only [CollatzResearch.WordTrace]
  refine ⟨101257134948225572391864193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135009513264300763189152257 101257134948225572391864193)
  ·
    refine ⟨75942851211169179293898145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101257134948225572391864193 75942851211169179293898145)
    ·
      refine ⟨56957138408376884470423609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75942851211169179293898145 56957138408376884470423609)
      ·
        refine ⟨42717853806282663352817707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56957138408376884470423609 42717853806282663352817707)
        ·
          refine ⟨64076780709423995029226561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42717853806282663352817707 64076780709423995029226561)
          ·
            refine ⟨48057585532067996271919921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64076780709423995029226561 48057585532067996271919921)
            ·
              refine ⟨36043189149050997203939941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48057585532067996271919921 36043189149050997203939941)
              ·
                refine ⟨6758097965447061975738739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36043189149050997203939941 6758097965447061975738739)
                ·
                  refine ⟨10137146948170592963608109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6758097965447061975738739 10137146948170592963608109)
                  ·
                    refine ⟨3801430105563972361353041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10137146948170592963608109 3801430105563972361353041)
                    ·
                      refine ⟨2851072579172979271014781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801430105563972361353041 2851072579172979271014781)
                      ·
                        rfl

theorem cell23_5552444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_5552444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552444 prefixEnd_5552444 := by exact prefixLift 5552444
  have htrace : WordTrace (prefixWord ++ tailWord_5552444) baseStart_5552444 baseEnd_5552444 := by
    simpa [prefixWord, tailWord_5552444, baseEnd_5552444] using wordTrace_append hprefix tailTrace_5552444
  have hstable : (prefixWord ++ tailWord_5552444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552444).length < 2 ^ (prefixWord ++ tailWord_5552444).sum := by decide
  have hdescent : baseEnd_5552444 < baseStart_5552444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552460 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_5552460 : Nat := 118140960795 + 5552460 * 2 ^ 59
def prefixEnd_5552460 : Nat := 4983230072969 + 3 ^ 40 * 5552460 * 2
def baseEnd_5552460 : Nat := 2851080794863451208414707

theorem tailTrace_5552460 : CollatzResearch.WordTrace tailWord_5552460 prefixEnd_5552460 2851080794863451208414707 := by
  unfold tailWord_5552460
  simp only [CollatzResearch.WordTrace]
  refine ⟨101257426732196589758155417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135009902309595453010873889 101257426732196589758155417)
  ·
    refine ⟨75943070049147442318616563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101257426732196589758155417 75943070049147442318616563)
    ·
      refine ⟨113914605073721163477924845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75943070049147442318616563 113914605073721163477924845)
      ·
        refine ⟨42717976902645436304221817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113914605073721163477924845 42717976902645436304221817)
        ·
          refine ⟨32038482676984077228166363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42717976902645436304221817 32038482676984077228166363)
          ·
            refine ⟨48057724015476115842249545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32038482676984077228166363 48057724015476115842249545)
            ·
              refine ⟨36043293011607086881687159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48057724015476115842249545 36043293011607086881687159)
              ·
                refine ⟨54064939517410630322530739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36043293011607086881687159 54064939517410630322530739)
                ·
                  refine ⟨81097409276115945483796109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54064939517410630322530739 81097409276115945483796109)
                  ·
                    refine ⟨30411528478543479556423541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81097409276115945483796109 30411528478543479556423541)
                    ·
                      refine ⟨2851080794863451208414707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30411528478543479556423541 2851080794863451208414707)
                      ·
                        rfl

theorem cell23_5552460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_5552460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552460 prefixEnd_5552460 := by exact prefixLift 5552460
  have htrace : WordTrace (prefixWord ++ tailWord_5552460) baseStart_5552460 baseEnd_5552460 := by
    simpa [prefixWord, tailWord_5552460, baseEnd_5552460] using wordTrace_append hprefix tailTrace_5552460
  have hstable : (prefixWord ++ tailWord_5552460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552460).length < 2 ^ (prefixWord ++ tailWord_5552460).sum := by decide
  have hdescent : baseEnd_5552460 < baseStart_5552460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552487 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_5552487 : Nat := 118140960795 + 5552487 * 2 ^ 59
def prefixEnd_5552487 : Nat := 4983230072969 + 3 ^ 40 * 5552487 * 2
def baseEnd_5552487 : Nat := 2851094658841122602777083

theorem tailTrace_5552487 : CollatzResearch.WordTrace tailWord_5552487 prefixEnd_5552487 2851094658841122602777083 := by
  unfold tailWord_5552487
  simp only [CollatzResearch.WordTrace]
  refine ⟨202515838235295363127543715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135010558823530242085029143 202515838235295363127543715)
  ·
    refine ⟨303773757352943044691315573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202515838235295363127543715 303773757352943044691315573)
    ·
      refine ⟨28478789751838410439810835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 303773757352943044691315573 28478789751838410439810835)
      ·
        refine ⟨42718184627757615659716253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28478789751838410439810835 42718184627757615659716253)
        ·
          refine ⟨16019319235409105872393595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42718184627757615659716253 16019319235409105872393595)
          ·
            refine ⟨24028978853113658808590393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16019319235409105872393595 24028978853113658808590393)
            ·
              refine ⟨18021734139835244106442795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24028978853113658808590393 18021734139835244106442795)
              ·
                refine ⟨27032601209752866159664193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18021734139835244106442795 27032601209752866159664193)
                ·
                  refine ⟨20274450907314649619748145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27032601209752866159664193 20274450907314649619748145)
                  ·
                    refine ⟨15205838180485987214811109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20274450907314649619748145 15205838180485987214811109)
                    ·
                      refine ⟨2851094658841122602777083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15205838180485987214811109 2851094658841122602777083)
                      ·
                        rfl

theorem cell23_5552487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_5552487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552487 prefixEnd_5552487 := by exact prefixLift 5552487
  have htrace : WordTrace (prefixWord ++ tailWord_5552487) baseStart_5552487 baseEnd_5552487 := by
    simpa [prefixWord, tailWord_5552487, baseEnd_5552487] using wordTrace_append hprefix tailTrace_5552487
  have hstable : (prefixWord ++ tailWord_5552487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552487).length < 2 ^ (prefixWord ++ tailWord_5552487).sum := by decide
  have hdescent : baseEnd_5552487 < baseStart_5552487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552517 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 1, 7, 2]
def baseStart_5552517 : Nat := 118140960795 + 5552517 * 2 ^ 59
def prefixEnd_5552517 : Nat := 4983230072969 + 3 ^ 40 * 5552517 * 2
def baseEnd_5552517 : Nat := 2851110063260757485401945

theorem tailTrace_5552517 : CollatzResearch.WordTrace tailWord_5552517 prefixEnd_5552517 2851110063260757485401945 := by
  unfold tailWord_5552517
  simp only [CollatzResearch.WordTrace]
  refine ⟨202516932425186678251135805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135011288283457785500757203 202516932425186678251135805)
  ·
    refine ⟨75943849659445004344175927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202516932425186678251135805 75943849659445004344175927)
    ·
      refine ⟨113915774489167506516263891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75943849659445004344175927 113915774489167506516263891)
      ·
        refine ⟨170873661733751259774395837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113915774489167506516263891 170873661733751259774395837)
        ·
          refine ⟨64077623150156722415398439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170873661733751259774395837 64077623150156722415398439)
          ·
            refine ⟨96116434725235083623097659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64077623150156722415398439 96116434725235083623097659)
            ·
              refine ⟨144174652087852625434646489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96116434725235083623097659 144174652087852625434646489)
              ·
                refine ⟨108130989065889469075984867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144174652087852625434646489 108130989065889469075984867)
                ·
                  refine ⟨162196483598834203613977301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108130989065889469075984867 162196483598834203613977301)
                  ·
                    refine ⟨3801480084347676647202593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 162196483598834203613977301 3801480084347676647202593)
                    ·
                      refine ⟨2851110063260757485401945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801480084347676647202593 2851110063260757485401945)
                      ·
                        rfl

theorem cell23_5552517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 7, 2].length) (baseStart_5552517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552517 prefixEnd_5552517 := by exact prefixLift 5552517
  have htrace : WordTrace (prefixWord ++ tailWord_5552517) baseStart_5552517 baseEnd_5552517 := by
    simpa [prefixWord, tailWord_5552517, baseEnd_5552517] using wordTrace_append hprefix tailTrace_5552517
  have hstable : (prefixWord ++ tailWord_5552517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552517).length < 2 ^ (prefixWord ++ tailWord_5552517).sum := by decide
  have hdescent : baseEnd_5552517 < baseStart_5552517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552542 : List Nat := [4, 3, 1, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_5552542 : Nat := 118140960795 + 5552542 * 2 ^ 59
def prefixEnd_5552542 : Nat := 4983230072969 + 3 ^ 40 * 5552542 * 2
def baseEnd_5552542 : Nat := 2851122900277119887589331

theorem tailTrace_5552542 : CollatzResearch.WordTrace tailWord_5552542 prefixEnd_5552542 2851122900277119887589331 := by
  unfold tailWord_5552542
  simp only [CollatzResearch.WordTrace]
  refine ⟨25314730531262013440099485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135011896166730738347197253 25314730531262013440099485)
  ·
    refine ⟨9493023949223255040037307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25314730531262013440099485 9493023949223255040037307)
    ·
      refine ⟨14239535923834882560055961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9493023949223255040037307 14239535923834882560055961)
      ·
        refine ⟨10679651942876161920041971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14239535923834882560055961 10679651942876161920041971)
        ·
          refine ⟨16019477914314242880062957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10679651942876161920041971 16019477914314242880062957)
          ·
            refine ⟨6007304217867841080023609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16019477914314242880062957 6007304217867841080023609)
            ·
              refine ⟨4505478163400880810017707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6007304217867841080023609 4505478163400880810017707)
              ·
                refine ⟨6758217245101321215026561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4505478163400880810017707 6758217245101321215026561)
                ·
                  refine ⟨5068662933825990911269921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6758217245101321215026561 5068662933825990911269921)
                  ·
                    refine ⟨3801497200369493183452441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5068662933825990911269921 3801497200369493183452441)
                    ·
                      refine ⟨2851122900277119887589331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801497200369493183452441 2851122900277119887589331)
                      ·
                        rfl

theorem cell23_5552542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_5552542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552542 prefixEnd_5552542 := by exact prefixLift 5552542
  have htrace : WordTrace (prefixWord ++ tailWord_5552542) baseStart_5552542 baseEnd_5552542 := by
    simpa [prefixWord, tailWord_5552542, baseEnd_5552542] using wordTrace_append hprefix tailTrace_5552542
  have hstable : (prefixWord ++ tailWord_5552542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552542).length < 2 ^ (prefixWord ++ tailWord_5552542).sum := by decide
  have hdescent : baseEnd_5552542 < baseStart_5552542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552570 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 10]
def baseStart_5552570 : Nat := 118140960795 + 5552570 * 2 ^ 59
def prefixEnd_5552570 : Nat := 4983230072969 + 3 ^ 40 * 5552570 * 2
def baseEnd_5552570 : Nat := 316793030859493975337689

theorem tailTrace_5552570 : CollatzResearch.WordTrace tailWord_5552570 prefixEnd_5552570 316793030859493975337689 := by
  unfold tailWord_5552570
  simp only [CollatzResearch.WordTrace]
  refine ⟨50629716373498667075703791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135012576995996445535210109 50629716373498667075703791)
  ·
    refine ⟨75944574560248000613555687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50629716373498667075703791 75944574560248000613555687)
    ·
      refine ⟨113916861840372000920333531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75944574560248000613555687 113916861840372000920333531)
      ·
        refine ⟨170875292760558001380500297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113916861840372000920333531 170875292760558001380500297)
        ·
          refine ⟨128156469570418501035375223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170875292760558001380500297 128156469570418501035375223)
          ·
            refine ⟨192234704355627751553062835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128156469570418501035375223 192234704355627751553062835)
            ·
              refine ⟨288352056533441627329594253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192234704355627751553062835 288352056533441627329594253)
              ·
                refine ⟨108132021200040610248597845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288352056533441627329594253 108132021200040610248597845)
                ·
                  refine ⟨316793030859493975337689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 108132021200040610248597845 316793030859493975337689)
                  ·
                    rfl

theorem cell23_5552570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_5552570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552570 prefixEnd_5552570 := by exact prefixLift 5552570
  have htrace : WordTrace (prefixWord ++ tailWord_5552570) baseStart_5552570 baseEnd_5552570 := by
    simpa [prefixWord, tailWord_5552570, baseEnd_5552570] using wordTrace_append hprefix tailTrace_5552570
  have hstable : (prefixWord ++ tailWord_5552570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552570).length < 2 ^ (prefixWord ++ tailWord_5552570).sum := by decide
  have hdescent : baseEnd_5552570 < baseStart_5552570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552584 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_5552584 : Nat := 118140960795 + 5552584 * 2 ^ 59
def prefixEnd_5552584 : Nat := 4983230072969 + 3 ^ 40 * 5552584 * 2
def baseEnd_5552584 : Nat := 2851144466464608723264137

theorem tailTrace_5552584 : CollatzResearch.WordTrace tailWord_5552584 prefixEnd_5552584 2851144466464608723264137 := by
  unfold tailWord_5552584
  simp only [CollatzResearch.WordTrace]
  refine ⟨101259688057971974346912403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135012917410629299129216537 101259688057971974346912403)
  ·
    refine ⟨151889532086957961520368605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101259688057971974346912403 151889532086957961520368605)
    ·
      refine ⟨56958574532609235570138227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151889532086957961520368605 56958574532609235570138227)
      ·
        refine ⟨85437861798913853355207341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56958574532609235570138227 85437861798913853355207341)
        ·
          refine ⟨32039198174592695008202753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85437861798913853355207341 32039198174592695008202753)
          ·
            refine ⟨24029398630944521256152065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32039198174592695008202753 24029398630944521256152065)
            ·
              refine ⟨18022048973208390942114049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24029398630944521256152065 18022048973208390942114049)
              ·
                refine ⟨13516536729906293206585537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18022048973208390942114049 13516536729906293206585537)
                ·
                  refine ⟨10137402547429719904939153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13516536729906293206585537 10137402547429719904939153)
                  ·
                    refine ⟨7603051910572289928704365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10137402547429719904939153 7603051910572289928704365)
                    ·
                      refine ⟨2851144466464608723264137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7603051910572289928704365 2851144466464608723264137)
                      ·
                        rfl

theorem cell23_5552584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_5552584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552584 prefixEnd_5552584 := by exact prefixLift 5552584
  have htrace : WordTrace (prefixWord ++ tailWord_5552584) baseStart_5552584 baseEnd_5552584 := by
    simpa [prefixWord, tailWord_5552584, baseEnd_5552584] using wordTrace_append hprefix tailTrace_5552584
  have hstable : (prefixWord ++ tailWord_5552584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552584).length < 2 ^ (prefixWord ++ tailWord_5552584).sum := by decide
  have hdescent : baseEnd_5552584 < baseStart_5552584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552624 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 1, 5, 2]
def baseStart_5552624 : Nat := 118140960795 + 5552624 * 2 ^ 59
def prefixEnd_5552624 : Nat := 4983230072969 + 3 ^ 40 * 5552624 * 2
def baseEnd_5552624 : Nat := 2851165005690788566763953

theorem tailTrace_5552624 : CollatzResearch.WordTrace tailWord_5552624 prefixEnd_5552624 2851165005690788566763953 := by
  unfold tailWord_5552624
  simp only [CollatzResearch.WordTrace]
  refine ⟨101260417517899517762640463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135013890023866023683520617 101260417517899517762640463)
  ·
    refine ⟨151890626276849276643960695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101260417517899517762640463 151890626276849276643960695)
    ·
      refine ⟨227835939415273914965941043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151890626276849276643960695 227835939415273914965941043)
      ·
        refine ⟨341753909122910872448911565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227835939415273914965941043 341753909122910872448911565)
        ·
          refine ⟨128157715921091577168341837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341753909122910872448911565 128157715921091577168341837)
          ·
            refine ⟨48059143470409341438128189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128157715921091577168341837 48059143470409341438128189)
            ·
              refine ⟨18022178801403503039298071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48059143470409341438128189 18022178801403503039298071)
              ·
                refine ⟨27033268202105254558947107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18022178801403503039298071 27033268202105254558947107)
                ·
                  refine ⟨40549902303157881838420661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27033268202105254558947107 40549902303157881838420661)
                  ·
                    refine ⟨3801553340921051422351937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40549902303157881838420661 3801553340921051422351937)
                    ·
                      refine ⟨2851165005690788566763953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801553340921051422351937 2851165005690788566763953)
                      ·
                        rfl

theorem cell23_5552624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 5, 2].length) (baseStart_5552624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552624 prefixEnd_5552624 := by exact prefixLift 5552624
  have htrace : WordTrace (prefixWord ++ tailWord_5552624) baseStart_5552624 baseEnd_5552624 := by
    simpa [prefixWord, tailWord_5552624, baseEnd_5552624] using wordTrace_append hprefix tailTrace_5552624
  have hstable : (prefixWord ++ tailWord_5552624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552624).length < 2 ^ (prefixWord ++ tailWord_5552624).sum := by decide
  have hdescent : baseEnd_5552624 < baseStart_5552624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552657 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 3]
def baseStart_5552657 : Nat := 118140960795 + 5552657 * 2 ^ 59
def prefixEnd_5552657 : Nat := 4983230072969 + 3 ^ 40 * 5552657 * 2
def baseEnd_5552657 : Nat := 2851181950552386937651301

theorem tailTrace_5552657 : CollatzResearch.WordTrace tailWord_5552657 prefixEnd_5552657 2851181950552386937651301 := by
  unfold tailWord_5552657
  simp only [CollatzResearch.WordTrace]
  refine ⟨202522038644679482161232225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135014692429786321440821483 202522038644679482161232225)
  ·
    refine ⟨151891528983509611620924169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202522038644679482161232225 151891528983509611620924169)
    ·
      refine ⟨113918646737632208715693127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151891528983509611620924169 113918646737632208715693127)
      ·
        refine ⟨170877970106448313073539691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113918646737632208715693127 170877970106448313073539691)
        ·
          refine ⟨256316955159672469610309537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170877970106448313073539691 256316955159672469610309537)
          ·
            refine ⟨192237716369754352207732153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256316955159672469610309537 192237716369754352207732153)
            ·
              refine ⟨144178287277315764155799115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192237716369754352207732153 144178287277315764155799115)
              ·
                refine ⟨216267430915973646233698673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144178287277315764155799115 216267430915973646233698673)
                ·
                  refine ⟨162200573186980234675274005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216267430915973646233698673 162200573186980234675274005)
                  ·
                    refine ⟨7603151868139698500403469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 162200573186980234675274005 7603151868139698500403469)
                    ·
                      refine ⟨2851181950552386937651301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7603151868139698500403469 2851181950552386937651301)
                      ·
                        rfl

theorem cell23_5552657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_5552657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552657 prefixEnd_5552657 := by exact prefixLift 5552657
  have htrace : WordTrace (prefixWord ++ tailWord_5552657) baseStart_5552657 baseEnd_5552657 := by
    simpa [prefixWord, tailWord_5552657, baseEnd_5552657] using wordTrace_append hprefix tailTrace_5552657
  have hstable : (prefixWord ++ tailWord_5552657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552657).length < 2 ^ (prefixWord ++ tailWord_5552657).sum := by decide
  have hdescent : baseEnd_5552657 < baseStart_5552657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552664 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 1, 6]
def baseStart_5552664 : Nat := 118140960795 + 5552664 * 2 ^ 59
def prefixEnd_5552664 : Nat := 4983230072969 + 3 ^ 40 * 5552664 * 2
def baseEnd_5552664 : Nat := 950395181638989470087923

theorem tailTrace_5552664 : CollatzResearch.WordTrace tailWord_5552664 prefixEnd_5552664 950395181638989470087923 := by
  unfold tailWord_5552664
  simp only [CollatzResearch.WordTrace]
  refine ⟨101261146977827061178368523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135014862637102748237824697 101261146977827061178368523)
  ·
    refine ⟨151891720466740591767552785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101261146977827061178368523 151891720466740591767552785)
    ·
      refine ⟨113918790350055443825664589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151891720466740591767552785 113918790350055443825664589)
      ·
        refine ⟨42719546381270791434624221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113918790350055443825664589 42719546381270791434624221)
        ·
          refine ⟨16019829892976546787984083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42719546381270791434624221 16019829892976546787984083)
          ·
            refine ⟨24029744839464820181976125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16019829892976546787984083 24029744839464820181976125)
            ·
              refine ⟨9011154314799307568241047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24029744839464820181976125 9011154314799307568241047)
              ·
                refine ⟨13516731472198961352361571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9011154314799307568241047 13516731472198961352361571)
                ·
                  refine ⟨20275097208298442028542357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13516731472198961352361571 20275097208298442028542357)
                  ·
                    refine ⟨950395181638989470087923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20275097208298442028542357 950395181638989470087923)
                    ·
                      rfl

theorem cell23_5552664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_5552664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552664 prefixEnd_5552664 := by exact prefixLift 5552664
  have htrace : WordTrace (prefixWord ++ tailWord_5552664) baseStart_5552664 baseEnd_5552664 := by
    simpa [prefixWord, tailWord_5552664, baseEnd_5552664] using wordTrace_append hprefix tailTrace_5552664
  have hstable : (prefixWord ++ tailWord_5552664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552664).length < 2 ^ (prefixWord ++ tailWord_5552664).sum := by decide
  have hdescent : baseEnd_5552664 < baseStart_5552664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552694 : List Nat := [5, 1, 2, 1, 2, 1, 11]
def baseStart_5552694 : Nat := 118140960795 + 5552694 * 2 ^ 59
def prefixEnd_5552694 : Nat := 4983230072969 + 3 ^ 40 * 5552694 * 2
def baseEnd_5552694 : Nat := 35200011720204978924551

theorem tailTrace_5552694 : CollatzResearch.WordTrace tailWord_5552694 prefixEnd_5552694 35200011720204978924551 := by
  unfold tailWord_5552694
  simp only [CollatzResearch.WordTrace]
  refine ⟨12657711759096589842520571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135015592097030291653552757 12657711759096589842520571)
  ·
    refine ⟨18986567638644884763780857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12657711759096589842520571 18986567638644884763780857)
    ·
      refine ⟨14239925728983663572835643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18986567638644884763780857 14239925728983663572835643)
      ·
        refine ⟨21359888593475495359253465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14239925728983663572835643 21359888593475495359253465)
        ·
          refine ⟨16019916445106621519440099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21359888593475495359253465 16019916445106621519440099)
          ·
            refine ⟨24029874667659932279160149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16019916445106621519440099 24029874667659932279160149)
            ·
              refine ⟨35200011720204978924551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24029874667659932279160149 35200011720204978924551)
              ·
                rfl

theorem cell23_5552694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 11].length) (baseStart_5552694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552694 prefixEnd_5552694 := by exact prefixLift 5552694
  have htrace : WordTrace (prefixWord ++ tailWord_5552694) baseStart_5552694 baseEnd_5552694 := by
    simpa [prefixWord, tailWord_5552694, baseEnd_5552694] using wordTrace_append hprefix tailTrace_5552694
  have hstable : (prefixWord ++ tailWord_5552694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552694).length < 2 ^ (prefixWord ++ tailWord_5552694).sum := by decide
  have hdescent : baseEnd_5552694 < baseStart_5552694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552705 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_5552705 : Nat := 118140960795 + 5552705 * 2 ^ 59
def prefixEnd_5552705 : Nat := 4983230072969 + 3 ^ 40 * 5552705 * 2
def baseEnd_5552705 : Nat := 2851206597623802749851081

theorem tailTrace_5552705 : CollatzResearch.WordTrace tailWord_5552705 prefixEnd_5552705 2851206597623802749851081 := by
  unfold tailWord_5552705
  simp only [CollatzResearch.WordTrace]
  refine ⟨202523789348505586358979569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135015859565670390905986379 202523789348505586358979569)
  ·
    refine ⟨151892842011379189769234677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202523789348505586358979569 151892842011379189769234677)
    ·
      refine ⟨14239953938566799040865751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151892842011379189769234677 14239953938566799040865751)
      ·
        refine ⟨21359930907850198561298627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14239953938566799040865751 21359930907850198561298627)
        ·
          refine ⟨32039896361775297841947941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21359930907850198561298627 32039896361775297841947941)
          ·
            refine ⟨6007480567832868345365239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32039896361775297841947941 6007480567832868345365239)
            ·
              refine ⟨9011220851749302518047859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6007480567832868345365239 9011220851749302518047859)
              ·
                refine ⟨13516831277623953777071789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9011220851749302518047859 13516831277623953777071789)
                ·
                  refine ⟨5068811729108982666401921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13516831277623953777071789 5068811729108982666401921)
                  ·
                    refine ⟨3801608796831736999801441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5068811729108982666401921 3801608796831736999801441)
                    ·
                      refine ⟨2851206597623802749851081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801608796831736999801441 2851206597623802749851081)
                      ·
                        rfl

theorem cell23_5552705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_5552705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552705 prefixEnd_5552705 := by exact prefixLift 5552705
  have htrace : WordTrace (prefixWord ++ tailWord_5552705) baseStart_5552705 baseEnd_5552705 := by
    simpa [prefixWord, tailWord_5552705, baseEnd_5552705] using wordTrace_append hprefix tailTrace_5552705
  have hstable : (prefixWord ++ tailWord_5552705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552705).length < 2 ^ (prefixWord ++ tailWord_5552705).sum := by decide
  have hdescent : baseEnd_5552705 < baseStart_5552705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552747 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 5]
def baseStart_5552747 : Nat := 118140960795 + 5552747 * 2 ^ 59
def prefixEnd_5552747 : Nat := 4983230072969 + 3 ^ 40 * 5552747 * 2
def baseEnd_5552747 : Nat := 2851228163811291585525887

theorem tailTrace_5552747 : CollatzResearch.WordTrace tailWord_5552747 prefixEnd_5552747 2851228163811291585525887 := by
  unfold tailWord_5552747
  simp only [CollatzResearch.WordTrace]
  refine ⟨202525321214353427532008495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135016880809568951688005663 202525321214353427532008495)
  ·
    refine ⟨303787981821530141298012743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202525321214353427532008495 303787981821530141298012743)
    ·
      refine ⟨455681972732295211947019115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303787981821530141298012743 455681972732295211947019115)
      ·
        refine ⟨683522959098442817920528673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455681972732295211947019115 683522959098442817920528673)
        ·
          refine ⟨512642219323832113440396505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683522959098442817920528673 512642219323832113440396505)
          ·
            refine ⟨384481664492874085080297379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512642219323832113440396505 384481664492874085080297379)
            ·
              refine ⟨576722496739311127620446069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384481664492874085080297379 576722496739311127620446069)
              ·
                refine ⟨54067734069310418214416819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 576722496739311127620446069 54067734069310418214416819)
                ·
                  refine ⟨81101601103965627321625229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54067734069310418214416819 81101601103965627321625229)
                  ·
                    refine ⟨30413100413987110245609461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81101601103965627321625229 30413100413987110245609461)
                    ·
                      refine ⟨2851228163811291585525887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30413100413987110245609461 2851228163811291585525887)
                      ·
                        rfl

theorem cell23_5552747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 5].length) (baseStart_5552747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552747 prefixEnd_5552747 := by exact prefixLift 5552747
  have htrace : WordTrace (prefixWord ++ tailWord_5552747) baseStart_5552747 baseEnd_5552747 := by
    simpa [prefixWord, tailWord_5552747, baseEnd_5552747] using wordTrace_append hprefix tailTrace_5552747
  have hstable : (prefixWord ++ tailWord_5552747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552747).length < 2 ^ (prefixWord ++ tailWord_5552747).sum := by decide
  have hdescent : baseEnd_5552747 < baseStart_5552747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552764 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_5552764 : Nat := 118140960795 + 5552764 * 2 ^ 59
def prefixEnd_5552764 : Nat := 4983230072969 + 3 ^ 40 * 5552764 * 2
def baseEnd_5552764 : Nat := 2851236892982418019013309

theorem tailTrace_5552764 : CollatzResearch.WordTrace tailWord_5552764 prefixEnd_5552764 2851236892982418019013309 := by
  unfold tailWord_5552764
  simp only [CollatzResearch.WordTrace]
  refine ⟨101262970627645919717688673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135017294170194559623584897 101262970627645919717688673)
  ·
    refine ⟨75947227970734439788266505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101262970627645919717688673 75947227970734439788266505)
    ·
      refine ⟨56960420978050829841199879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75947227970734439788266505 56960420978050829841199879)
      ·
        refine ⟨85440631467076244761799819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56960420978050829841199879 85440631467076244761799819)
        ·
          refine ⟨128160947200614367142699729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85440631467076244761799819 128160947200614367142699729)
          ·
            refine ⟨96120710400460775357024797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128160947200614367142699729 96120710400460775357024797)
            ·
              refine ⟨36045266400172790758884299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96120710400460775357024797 36045266400172790758884299)
              ·
                refine ⟨54067899600259186138326449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36045266400172790758884299 54067899600259186138326449)
                ·
                  refine ⟨40550924700194389603744837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54067899600259186138326449 40550924700194389603744837)
                  ·
                    refine ⟨7603298381286448050702157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40550924700194389603744837 7603298381286448050702157)
                    ·
                      refine ⟨2851236892982418019013309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7603298381286448050702157 2851236892982418019013309)
                      ·
                        rfl

theorem cell23_5552764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_5552764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552764 prefixEnd_5552764 := by exact prefixLift 5552764
  have htrace : WordTrace (prefixWord ++ tailWord_5552764) baseStart_5552764 baseEnd_5552764 := by
    simpa [prefixWord, tailWord_5552764, baseEnd_5552764] using wordTrace_append hprefix tailTrace_5552764
  have hstable : (prefixWord ++ tailWord_5552764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552764).length < 2 ^ (prefixWord ++ tailWord_5552764).sum := by decide
  have hdescent : baseEnd_5552764 < baseStart_5552764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552787 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 8]
def baseStart_5552787 : Nat := 118140960795 + 5552787 * 2 ^ 59
def prefixEnd_5552787 : Nat := 4983230072969 + 3 ^ 40 * 5552787 * 2
def baseEnd_5552787 : Nat := 2851248703037471429025703

theorem tailTrace_5552787 : CollatzResearch.WordTrace tailWord_5552787 prefixEnd_5552787 2851248703037471429025703 := by
  unfold tailWord_5552787
  simp only [CollatzResearch.WordTrace]
  refine ⟨202526780134208514363464615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135017853422805676242309743 202526780134208514363464615)
  ·
    refine ⟨303790170201312771545196923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202526780134208514363464615 303790170201312771545196923)
    ·
      refine ⟨455685255301969157317795385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303790170201312771545196923 455685255301969157317795385)
      ·
        refine ⟨341763941476476867988346539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 455685255301969157317795385 341763941476476867988346539)
        ·
          refine ⟨512645912214715301982519809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341763941476476867988346539 512645912214715301982519809)
          ·
            refine ⟨384484434161036476486889857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512645912214715301982519809 384484434161036476486889857)
            ·
              refine ⟨288363325620777357365167393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384484434161036476486889857 288363325620777357365167393)
              ·
                refine ⟨216272494215583018023875545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288363325620777357365167393 216272494215583018023875545)
                ·
                  refine ⟨162204370661687263517906659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216272494215583018023875545 162204370661687263517906659)
                  ·
                    refine ⟨243306555992530895276859989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162204370661687263517906659 243306555992530895276859989)
                    ·
                      refine ⟨2851248703037471429025703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 243306555992530895276859989 2851248703037471429025703)
                      ·
                        rfl

theorem cell23_5552787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_5552787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552787 prefixEnd_5552787 := by exact prefixLift 5552787
  have htrace : WordTrace (prefixWord ++ tailWord_5552787) baseStart_5552787 baseEnd_5552787 := by
    simpa [prefixWord, tailWord_5552787, baseEnd_5552787] using wordTrace_append hprefix tailTrace_5552787
  have hstable : (prefixWord ++ tailWord_5552787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552787).length < 2 ^ (prefixWord ++ tailWord_5552787).sum := by decide
  have hdescent : baseEnd_5552787 < baseStart_5552787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552852 : List Nat := [2, 4, 1, 3, 3, 1, 1, 3, 5]
def baseStart_5552852 : Nat := 118140960795 + 5552852 * 2 ^ 59
def prefixEnd_5552852 : Nat := 4983230072969 + 3 ^ 40 * 5552852 * 2
def baseEnd_5552852 : Nat := 316809119920001519412545

theorem tailTrace_5552852 : CollatzResearch.WordTrace tailWord_5552852 prefixEnd_5552852 316809119920001519412545 := by
  unfold tailWord_5552852
  simp only [CollatzResearch.WordTrace]
  refine ⟨101264575439486515232290405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135019433919315353643053873 101264575439486515232290405)
  ·
    refine ⟨18987107894903721606054451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101264575439486515232290405 18987107894903721606054451)
    ·
      refine ⟨28480661842355582409081677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18987107894903721606054451 28480661842355582409081677)
      ·
        refine ⟨10680248190883343403405629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28480661842355582409081677 10680248190883343403405629)
        ·
          refine ⟨4005093071581253776277111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10680248190883343403405629 4005093071581253776277111)
          ·
            refine ⟨6007639607371880664415667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4005093071581253776277111 6007639607371880664415667)
            ·
              refine ⟨9011459411057820996623501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6007639607371880664415667 9011459411057820996623501)
              ·
                refine ⟨3379297279146682873733813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9011459411057820996623501 3379297279146682873733813)
                ·
                  refine ⟨316809119920001519412545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3379297279146682873733813 316809119920001519412545)
                  ·
                    rfl

theorem cell23_5552852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_5552852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552852 prefixEnd_5552852 := by exact prefixLift 5552852
  have htrace : WordTrace (prefixWord ++ tailWord_5552852) baseStart_5552852 baseEnd_5552852 := by
    simpa [prefixWord, tailWord_5552852, baseEnd_5552852] using wordTrace_append hprefix tailTrace_5552852
  have hstable : (prefixWord ++ tailWord_5552852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552852).length < 2 ^ (prefixWord ++ tailWord_5552852).sum := by decide
  have hdescent : baseEnd_5552852 < baseStart_5552852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552878 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_5552878 : Nat := 118140960795 + 5552878 * 2 ^ 59
def prefixEnd_5552878 : Nat := 4983230072969 + 3 ^ 40 * 5552878 * 2
def baseEnd_5552878 : Nat := 950431809925676857662595

theorem tailTrace_5552878 : CollatzResearch.WordTrace tailWord_5552878 prefixEnd_5552878 950431809925676857662595 := by
  unfold tailWord_5552878
  simp only [CollatzResearch.WordTrace]
  refine ⟨25316262397109854613128411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135020066117919224603351525 25316262397109854613128411)
  ·
    refine ⟨37974393595664781919692617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25316262397109854613128411 37974393595664781919692617)
    ·
      refine ⟨28480795196748586439769463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37974393595664781919692617 28480795196748586439769463)
      ·
        refine ⟨42721192795122879659654195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28480795196748586439769463 42721192795122879659654195)
        ·
          refine ⟨64081789192684319489481293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42721192795122879659654195 64081789192684319489481293)
          ·
            refine ⟨24030670947256619808555485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64081789192684319489481293 24030670947256619808555485)
            ·
              refine ⟨9011501605221232428208307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24030670947256619808555485 9011501605221232428208307)
              ·
                refine ⟨13517252407831848642312461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9011501605221232428208307 13517252407831848642312461)
                ·
                  refine ⟨5068969652936943240867173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13517252407831848642312461 5068969652936943240867173)
                  ·
                    refine ⟨950431809925676857662595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5068969652936943240867173 950431809925676857662595)
                    ·
                      rfl

theorem cell23_5552878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_5552878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552878 prefixEnd_5552878 := by exact prefixLift 5552878
  have htrace : WordTrace (prefixWord ++ tailWord_5552878) baseStart_5552878 baseEnd_5552878 := by
    simpa [prefixWord, tailWord_5552878, baseEnd_5552878] using wordTrace_append hprefix tailTrace_5552878
  have hstable : (prefixWord ++ tailWord_5552878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552878).length < 2 ^ (prefixWord ++ tailWord_5552878).sum := by decide
  have hdescent : baseEnd_5552878 < baseStart_5552878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552925 : List Nat := [1, 4, 2, 4, 1, 1, 2, 2, 6]
def baseStart_5552925 : Nat := 118140960795 + 5552925 * 2 ^ 59
def prefixEnd_5552925 : Nat := 4983230072969 + 3 ^ 40 * 5552925 * 2
def baseEnd_5552925 : Nat := 316813284818643543233341

theorem tailTrace_5552925 : CollatzResearch.WordTrace tailWord_5552925 prefixEnd_5552925 316813284818643543233341 := by
  unfold tailWord_5552925
  simp only [CollatzResearch.WordTrace]
  refine ⟨202531813407708563931988229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135021208938472375954658819 202531813407708563931988229)
  ·
    refine ⟨37974715013945355737247793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202531813407708563931988229 37974715013945355737247793)
    ·
      refine ⟨28481036260459016802935845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37974715013945355737247793 28481036260459016802935845)
      ·
        refine ⟨5340194298836065650550471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28481036260459016802935845 5340194298836065650550471)
        ·
          refine ⟨8010291448254098475825707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5340194298836065650550471 8010291448254098475825707)
          ·
            refine ⟨12015437172381147713738561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8010291448254098475825707 12015437172381147713738561)
            ·
              refine ⟨9011577879285860785303921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12015437172381147713738561 9011577879285860785303921)
              ·
                refine ⟨6758683409464395588977941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9011577879285860785303921 6758683409464395588977941)
                ·
                  refine ⟨316813284818643543233341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6758683409464395588977941 316813284818643543233341)
                  ·
                    rfl

theorem cell23_5552925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_5552925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552925 prefixEnd_5552925 := by exact prefixLift 5552925
  have htrace : WordTrace (prefixWord ++ tailWord_5552925) baseStart_5552925 baseEnd_5552925 := by
    simpa [prefixWord, tailWord_5552925, baseEnd_5552925] using wordTrace_append hprefix tailTrace_5552925
  have hstable : (prefixWord ++ tailWord_5552925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552925).length < 2 ^ (prefixWord ++ tailWord_5552925).sum := by decide
  have hdescent : baseEnd_5552925 < baseStart_5552925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552951 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 1, 6]
def baseStart_5552951 : Nat := 118140960795 + 5552951 * 2 ^ 59
def prefixEnd_5552951 : Nat := 4983230072969 + 3 ^ 40 * 5552951 * 2
def baseEnd_5552951 : Nat := 950444304621602929124983

theorem tailTrace_5552951 : CollatzResearch.WordTrace tailWord_5552951 prefixEnd_5552951 950444304621602929124983 := by
  unfold tailWord_5552951
  simp only [CollatzResearch.WordTrace]
  refine ⟨202532761705614370372434707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135021841137076246914956471 202532761705614370372434707)
  ·
    refine ⟨303799142558421555558652061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202532761705614370372434707 303799142558421555558652061)
    ·
      refine ⟨113924678459408083334494523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303799142558421555558652061 113924678459408083334494523)
      ·
        refine ⟨170887017689112125001741785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113924678459408083334494523 170887017689112125001741785)
        ·
          refine ⟨128165263266834093751306339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170887017689112125001741785 128165263266834093751306339)
          ·
            refine ⟨192247894900251140626959509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128165263266834093751306339 192247894900251140626959509)
            ·
              refine ⟨9011620073449272216888727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 192247894900251140626959509 9011620073449272216888727)
              ·
                refine ⟨13517430110173908325333091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9011620073449272216888727 13517430110173908325333091)
                ·
                  refine ⟨20276145165260862487999637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13517430110173908325333091 20276145165260862487999637)
                  ·
                    refine ⟨950444304621602929124983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20276145165260862487999637 950444304621602929124983)
                    ·
                      rfl

theorem cell23_5552951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_5552951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552951 prefixEnd_5552951 := by exact prefixLift 5552951
  have htrace : WordTrace (prefixWord ++ tailWord_5552951) baseStart_5552951 baseEnd_5552951 := by
    simpa [prefixWord, tailWord_5552951, baseEnd_5552951] using wordTrace_append hprefix tailTrace_5552951
  have hstable : (prefixWord ++ tailWord_5552951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552951).length < 2 ^ (prefixWord ++ tailWord_5552951).sum := by decide
  have hdescent : baseEnd_5552951 < baseStart_5552951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552985 : List Nat := [1, 2, 1, 2, 2, 6, 1, 2, 2, 4]
def baseStart_5552985 : Nat := 118140960795 + 5552985 * 2 ^ 59
def prefixEnd_5552985 : Nat := 4983230072969 + 3 ^ 40 * 5552985 * 2
def baseEnd_5552985 : Nat := 950450124069020551449931

theorem tailTrace_5552985 : CollatzResearch.WordTrace tailWord_5552985 prefixEnd_5552985 950450124069020551449931 := by
  unfold tailWord_5552985
  simp only [CollatzResearch.WordTrace]
  refine ⟨202534001787491194179172409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135022667858327462786114939 202534001787491194179172409)
  ·
    refine ⟨151900501340618395634379307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202534001787491194179172409 151900501340618395634379307)
    ·
      refine ⟨227850752010927593451568961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151900501340618395634379307 227850752010927593451568961)
      ·
        refine ⟨170888064008195695088676721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227850752010927593451568961 170888064008195695088676721)
        ·
          refine ⟨128166048006146771316507541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170888064008195695088676721 128166048006146771316507541)
          ·
            refine ⟨6007783500288129905461291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128166048006146771316507541 6007783500288129905461291)
            ·
              refine ⟨9011675250432194858191937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6007783500288129905461291 9011675250432194858191937)
              ·
                refine ⟨6758756437824146143643953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9011675250432194858191937 6758756437824146143643953)
                ·
                  refine ⟨5069067328368109607732965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6758756437824146143643953 5069067328368109607732965)
                  ·
                    refine ⟨950450124069020551449931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5069067328368109607732965 950450124069020551449931)
                    ·
                      rfl

theorem cell23_5552985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 4].length) (baseStart_5552985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552985 prefixEnd_5552985 := by exact prefixLift 5552985
  have htrace : WordTrace (prefixWord ++ tailWord_5552985) baseStart_5552985 baseEnd_5552985 := by
    simpa [prefixWord, tailWord_5552985, baseEnd_5552985] using wordTrace_append hprefix tailTrace_5552985
  have hstable : (prefixWord ++ tailWord_5552985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552985).length < 2 ^ (prefixWord ++ tailWord_5552985).sum := by decide
  have hdescent : baseEnd_5552985 < baseStart_5552985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5552992 : List Nat := [2, 1, 1, 3, 3, 1, 1, 6, 1, 2, 2]
def baseStart_5552992 : Nat := 118140960795 + 5552992 * 2 ^ 59
def prefixEnd_5552992 : Nat := 4983230072969 + 3 ^ 40 * 5552992 * 2
def baseEnd_5552992 : Nat := 2851353966571643126962261

theorem tailTrace_5552992 : CollatzResearch.WordTrace tailWord_5552992 prefixEnd_5552992 2851353966571643126962261 := by
  unfold tailWord_5552992
  simp only [CollatzResearch.WordTrace]
  refine ⟨101267128549232917187338615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135022838065643889583118153 101267128549232917187338615)
  ·
    refine ⟨151900692823849375781007923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101267128549232917187338615 151900692823849375781007923)
    ·
      refine ⟨227851039235774063671511885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151900692823849375781007923 227851039235774063671511885)
      ·
        refine ⟨85444139713415273876816957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227851039235774063671511885 85444139713415273876816957)
        ·
          refine ⟨32041552392530727703806359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85444139713415273876816957 32041552392530727703806359)
          ·
            refine ⟨48062328588796091555709539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32041552392530727703806359 48062328588796091555709539)
            ·
              refine ⟨72093492883194137333564309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48062328588796091555709539 72093492883194137333564309)
              ·
                refine ⟨3379382478899725187510827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72093492883194137333564309 3379382478899725187510827)
                ·
                  refine ⟨5069073718349587781266241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3379382478899725187510827 5069073718349587781266241)
                  ·
                    refine ⟨3801805288762190835949681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5069073718349587781266241 3801805288762190835949681)
                    ·
                      refine ⟨2851353966571643126962261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801805288762190835949681 2851353966571643126962261)
                      ·
                        rfl

theorem cell23_5552992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_5552992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5552992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5552992 prefixEnd_5552992 := by exact prefixLift 5552992
  have htrace : WordTrace (prefixWord ++ tailWord_5552992) baseStart_5552992 baseEnd_5552992 := by
    simpa [prefixWord, tailWord_5552992, baseEnd_5552992] using wordTrace_append hprefix tailTrace_5552992
  have hstable : (prefixWord ++ tailWord_5552992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5552992).length < 2 ^ (prefixWord ++ tailWord_5552992).sum := by decide
  have hdescent : baseEnd_5552992 < baseStart_5552992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5552992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553008 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 3]
def baseStart_5553008 : Nat := 118140960795 + 5553008 * 2 ^ 59
def prefixEnd_5553008 : Nat := 4983230072969 + 3 ^ 40 * 5553008 * 2
def baseEnd_5553008 : Nat := 2851362182262115064362187

theorem tailTrace_5553008 : CollatzResearch.WordTrace tailWord_5553008 prefixEnd_5553008 2851362182262115064362187 := by
  unfold tailWord_5553008
  simp only [CollatzResearch.WordTrace]
  refine ⟨101267420333203934553629839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135023227110938579404839785 101267420333203934553629839)
  ·
    refine ⟨151901130499805901830444759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101267420333203934553629839 151901130499805901830444759)
    ·
      refine ⟨227851695749708852745667139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151901130499805901830444759 227851695749708852745667139)
      ·
        refine ⟨341777543624563279118500709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227851695749708852745667139 341777543624563279118500709)
        ·
          refine ⟨64083289429605614834718883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 341777543624563279118500709 64083289429605614834718883)
          ·
            refine ⟨96124934144408422252078325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64083289429605614834718883 96124934144408422252078325)
            ·
              refine ⟨9011712576038289586132343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96124934144408422252078325 9011712576038289586132343)
              ·
                refine ⟨13517568864057434379198515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9011712576038289586132343 13517568864057434379198515)
                ·
                  refine ⟨20276353296086151568797773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13517568864057434379198515 20276353296086151568797773)
                  ·
                    refine ⟨7603632486032306838299165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20276353296086151568797773 7603632486032306838299165)
                    ·
                      refine ⟨2851362182262115064362187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7603632486032306838299165 2851362182262115064362187)
                      ·
                        rfl

theorem cell23_5553008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 3].length) (baseStart_5553008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553008 prefixEnd_5553008 := by exact prefixLift 5553008
  have htrace : WordTrace (prefixWord ++ tailWord_5553008) baseStart_5553008 baseEnd_5553008 := by
    simpa [prefixWord, tailWord_5553008, baseEnd_5553008] using wordTrace_append hprefix tailTrace_5553008
  have hstable : (prefixWord ++ tailWord_5553008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553008).length < 2 ^ (prefixWord ++ tailWord_5553008).sum := by decide
  have hdescent : baseEnd_5553008 < baseStart_5553008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553021 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_5553021 : Nat := 118140960795 + 5553021 * 2 ^ 59
def prefixEnd_5553021 : Nat := 4983230072969 + 3 ^ 40 * 5553021 * 2
def baseEnd_5553021 : Nat := 2851368857510623513499627

theorem tailTrace_5553021 : CollatzResearch.WordTrace tailWord_5553021 prefixEnd_5553021 2851368857510623513499627 := by
  unfold tailWord_5553021
  simp only [CollatzResearch.WordTrace]
  refine ⟨202535314815360772327482917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135023543210240514884988611 202535314815360772327482917)
  ·
    refine ⟨37975371527880144811403047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202535314815360772327482917 37975371527880144811403047)
    ·
      refine ⟨56963057291820217217104571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37975371527880144811403047 56963057291820217217104571)
      ·
        refine ⟨85444585937730325825656857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56963057291820217217104571 85444585937730325825656857)
        ·
          refine ⟨64083439453297744369242643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85444585937730325825656857 64083439453297744369242643)
          ·
            refine ⟨96125159179946616553863965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64083439453297744369242643 96125159179946616553863965)
            ·
              refine ⟨36046934692479981207698987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96125159179946616553863965 36046934692479981207698987)
              ·
                refine ⟨54070402038719971811548481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36046934692479981207698987 54070402038719971811548481)
                ·
                  refine ⟨40552801529039978858661361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54070402038719971811548481 40552801529039978858661361)
                  ·
                    refine ⟨30414601146779984143996021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40552801529039978858661361 30414601146779984143996021)
                    ·
                      refine ⟨2851368857510623513499627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30414601146779984143996021 2851368857510623513499627)
                      ·
                        rfl

theorem cell23_5553021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_5553021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553021 prefixEnd_5553021 := by exact prefixLift 5553021
  have htrace : WordTrace (prefixWord ++ tailWord_5553021) baseStart_5553021 baseEnd_5553021 := by
    simpa [prefixWord, tailWord_5553021, baseEnd_5553021] using wordTrace_append hprefix tailTrace_5553021
  have hstable : (prefixWord ++ tailWord_5553021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553021).length < 2 ^ (prefixWord ++ tailWord_5553021).sum := by decide
  have hdescent : baseEnd_5553021 < baseStart_5553021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553035 : List Nat := [1, 1, 1, 1, 4, 2, 4, 3, 1, 3, 2]
def baseStart_5553035 : Nat := 118140960795 + 5553035 * 2 ^ 59
def prefixEnd_5553035 : Nat := 4983230072969 + 3 ^ 40 * 5553035 * 2
def baseEnd_5553035 : Nat := 2851376046239786458724563

theorem tailTrace_5553035 : CollatzResearch.WordTrace tailWord_5553035 prefixEnd_5553035 2851376046239786458724563 := by
  unfold tailWord_5553035
  simp only [CollatzResearch.WordTrace]
  refine ⟨202535825437310052718492559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135023883624873368478995039 202535825437310052718492559)
  ·
    refine ⟨303803738155965079077738839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202535825437310052718492559 303803738155965079077738839)
    ·
      refine ⟨455705607233947618616608259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303803738155965079077738839 455705607233947618616608259)
      ·
        refine ⟨683558410850921427924912389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455705607233947618616608259 683558410850921427924912389)
        ·
          refine ⟨128167202034547767735921073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 683558410850921427924912389 128167202034547767735921073)
          ·
            refine ⟨96125401525910825801940805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128167202034547767735921073 96125401525910825801940805)
            ·
              refine ⟨18023512786108279837863901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96125401525910825801940805 18023512786108279837863901)
              ·
                refine ⟨6758817294790604939198963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18023512786108279837863901 6758817294790604939198963)
                ·
                  refine ⟨10138225942185907408798445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6758817294790604939198963 10138225942185907408798445)
                  ·
                    refine ⟨3801834728319715278299417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10138225942185907408798445 3801834728319715278299417)
                    ·
                      refine ⟨2851376046239786458724563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801834728319715278299417 2851376046239786458724563)
                      ·
                        rfl

theorem cell23_5553035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 3, 2].length) (baseStart_5553035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553035 prefixEnd_5553035 := by exact prefixLift 5553035
  have htrace : WordTrace (prefixWord ++ tailWord_5553035) baseStart_5553035 baseEnd_5553035 := by
    simpa [prefixWord, tailWord_5553035, baseEnd_5553035] using wordTrace_append hprefix tailTrace_5553035
  have hstable : (prefixWord ++ tailWord_5553035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553035).length < 2 ^ (prefixWord ++ tailWord_5553035).sum := by decide
  have hdescent : baseEnd_5553035 < baseStart_5553035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553069 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_5553069 : Nat := 118140960795 + 5553069 * 2 ^ 59
def prefixEnd_5553069 : Nat := 4983230072969 + 3 ^ 40 * 5553069 * 2
def baseEnd_5553069 : Nat := 2851393504582039325699407

theorem tailTrace_5553069 : CollatzResearch.WordTrace tailWord_5553069 prefixEnd_5553069 2851393504582039325699407 := by
  unfold tailWord_5553069
  simp only [CollatzResearch.WordTrace]
  refine ⟨202537065519186876525230261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135024710346124584350153507 202537065519186876525230261)
  ·
    refine ⟨18987849892423769674240337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202537065519186876525230261 18987849892423769674240337)
    ·
      refine ⟨14240887419317827255680253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18987849892423769674240337 14240887419317827255680253)
      ·
        refine ⟨5340332782244185220880095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14240887419317827255680253 5340332782244185220880095)
        ·
          refine ⟨8010499173366277831320143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5340332782244185220880095 8010499173366277831320143)
          ·
            refine ⟨12015748760049416746980215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8010499173366277831320143 12015748760049416746980215)
            ·
              refine ⟨18023623140074125120470323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12015748760049416746980215 18023623140074125120470323)
              ·
                refine ⟨27035434710111187680705485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18023623140074125120470323 27035434710111187680705485)
                ·
                  refine ⟨10138288016291695380264557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27035434710111187680705485 10138288016291695380264557)
                  ·
                    refine ⟨3801858006109385767599209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10138288016291695380264557 3801858006109385767599209)
                    ·
                      refine ⟨2851393504582039325699407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801858006109385767599209 2851393504582039325699407)
                      ·
                        rfl

theorem cell23_5553069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_5553069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553069 prefixEnd_5553069 := by exact prefixLift 5553069
  have htrace : WordTrace (prefixWord ++ tailWord_5553069) baseStart_5553069 baseEnd_5553069 := by
    simpa [prefixWord, tailWord_5553069, baseEnd_5553069] using wordTrace_append hprefix tailTrace_5553069
  have hstable : (prefixWord ++ tailWord_5553069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553069).length < 2 ^ (prefixWord ++ tailWord_5553069).sum := by decide
  have hdescent : baseEnd_5553069 < baseStart_5553069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553094 : List Nat := [6, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_5553094 : Nat := 118140960795 + 5553094 * 2 ^ 59
def prefixEnd_5553094 : Nat := 4983230072969 + 3 ^ 40 * 5553094 * 2
def baseEnd_5553094 : Nat := 2851406341598401727886793

theorem tailTrace_5553094 : CollatzResearch.WordTrace tailWord_5553094 prefixEnd_5553094 2851406341598401727886793 := by
  unfold tailWord_5553094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6329311792003009556090323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135025318229397537196593557 6329311792003009556090323)
  ·
    refine ⟨9493967688004514334135485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6329311792003009556090323 9493967688004514334135485)
    ·
      refine ⟨3560237883001692875300807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9493967688004514334135485 3560237883001692875300807)
      ·
        refine ⟨5340356824502539312951211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3560237883001692875300807 5340356824502539312951211)
        ·
          refine ⟨8010535236753808969426817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5340356824502539312951211 8010535236753808969426817)
          ·
            refine ⟨6007901427565356727070113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8010535236753808969426817 6007901427565356727070113)
            ·
              refine ⟨4505926070674017545302585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6007901427565356727070113 4505926070674017545302585)
              ·
                refine ⟨3379444553005513158976939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4505926070674017545302585 3379444553005513158976939)
                ·
                  refine ⟨5069166829508269738465409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3379444553005513158976939 5069166829508269738465409)
                  ·
                    refine ⟨3801875122131202303849057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5069166829508269738465409 3801875122131202303849057)
                    ·
                      refine ⟨2851406341598401727886793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3801875122131202303849057 2851406341598401727886793)
                      ·
                        rfl

theorem cell23_5553094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_5553094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553094 prefixEnd_5553094 := by exact prefixLift 5553094
  have htrace : WordTrace (prefixWord ++ tailWord_5553094) baseStart_5553094 baseEnd_5553094 := by
    simpa [prefixWord, tailWord_5553094, baseEnd_5553094] using wordTrace_append hprefix tailTrace_5553094
  have hstable : (prefixWord ++ tailWord_5553094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553094).length < 2 ^ (prefixWord ++ tailWord_5553094).sum := by decide
  have hdescent : baseEnd_5553094 < baseStart_5553094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553098 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_5553098 : Nat := 118140960795 + 5553098 * 2 ^ 59
def prefixEnd_5553098 : Nat := 4983230072969 + 3 ^ 40 * 5553098 * 2
def baseEnd_5553098 : Nat := 2851408395521019712236773

theorem tailTrace_5553098 : CollatzResearch.WordTrace tailWord_5553098 prefixEnd_5553098 2851408395521019712236773 := by
  unfold tailWord_5553098
  simp only [CollatzResearch.WordTrace]
  refine ⟨50634530809020453619508987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135025415490721209652023965 50634530809020453619508987)
  ·
    refine ⟨75951796213530680429263481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50634530809020453619508987 75951796213530680429263481)
    ·
      refine ⟨56963847160148010321947611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75951796213530680429263481 56963847160148010321947611)
      ·
        refine ⟨85445770740222015482921417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56963847160148010321947611 85445770740222015482921417)
        ·
          refine ⟨64084328055166511612191063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85445770740222015482921417 64084328055166511612191063)
          ·
            refine ⟨96126492082749767418286595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64084328055166511612191063 96126492082749767418286595)
            ·
              refine ⟨144189738124124651127429893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96126492082749767418286595 144189738124124651127429893)
              ·
                refine ⟨27035575898273372086393105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144189738124124651127429893 27035575898273372086393105)
                ·
                  refine ⟨20276681923705029064794829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27035575898273372086393105 20276681923705029064794829)
                  ·
                    refine ⟨7603755721389385899298061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20276681923705029064794829 7603755721389385899298061)
                    ·
                      refine ⟨2851408395521019712236773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7603755721389385899298061 2851408395521019712236773)
                      ·
                        rfl

theorem cell23_5553098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_5553098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553098 prefixEnd_5553098 := by exact prefixLift 5553098
  have htrace : WordTrace (prefixWord ++ tailWord_5553098) baseStart_5553098 baseEnd_5553098 := by
    simpa [prefixWord, tailWord_5553098, baseEnd_5553098] using wordTrace_append hprefix tailTrace_5553098
  have hstable : (prefixWord ++ tailWord_5553098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553098).length < 2 ^ (prefixWord ++ tailWord_5553098).sum := by decide
  have hdescent : baseEnd_5553098 < baseStart_5553098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553111 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_5553111 : Nat := 118140960795 + 5553111 * 2 ^ 59
def prefixEnd_5553111 : Nat := 4983230072969 + 3 ^ 40 * 5553111 * 2
def baseEnd_5553111 : Nat := 2851415070769528161374213

theorem tailTrace_5553111 : CollatzResearch.WordTrace tailWord_5553111 prefixEnd_5553111 2851415070769528161374213 := by
  unfold tailWord_5553111
  simp only [CollatzResearch.WordTrace]
  refine ⟨202538597385034717698259187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135025731590023145132172791 202538597385034717698259187)
  ·
    refine ⟨303807896077552076547388781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202538597385034717698259187 303807896077552076547388781)
    ·
      refine ⟨113927961029082028705270793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303807896077552076547388781 113927961029082028705270793)
      ·
        refine ⟨85445970771811521528953095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113927961029082028705270793 85445970771811521528953095)
        ·
          refine ⟨128168956157717282293429643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85445970771811521528953095 128168956157717282293429643)
          ·
            refine ⟨192253434236575923440144465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128168956157717282293429643 192253434236575923440144465)
            ·
              refine ⟨144190075677431942580108349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192253434236575923440144465 144190075677431942580108349)
              ·
                refine ⟨54071278379036978467540631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144190075677431942580108349 54071278379036978467540631)
                ·
                  refine ⟨81106917568555467701310947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54071278379036978467540631 81106917568555467701310947)
                  ·
                    refine ⟨121660376352833201551966421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81106917568555467701310947 121660376352833201551966421)
                    ·
                      refine ⟨2851415070769528161374213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121660376352833201551966421 2851415070769528161374213)
                      ·
                        rfl

theorem cell23_5553111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_5553111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553111 prefixEnd_5553111 := by exact prefixLift 5553111
  have htrace : WordTrace (prefixWord ++ tailWord_5553111) baseStart_5553111 baseEnd_5553111 := by
    simpa [prefixWord, tailWord_5553111, baseEnd_5553111] using wordTrace_append hprefix tailTrace_5553111
  have hstable : (prefixWord ++ tailWord_5553111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553111).length < 2 ^ (prefixWord ++ tailWord_5553111).sum := by decide
  have hdescent : baseEnd_5553111 < baseStart_5553111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553135 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 2, 5]
def baseStart_5553135 : Nat := 118140960795 + 5553135 * 2 ^ 59
def prefixEnd_5553135 : Nat := 4983230072969 + 3 ^ 40 * 5553135 * 2
def baseEnd_5553135 : Nat := 950475798101745355824701

theorem tailTrace_5553135 : CollatzResearch.WordTrace tailWord_5553135 prefixEnd_5553135 950475798101745355824701 := by
  unfold tailWord_5553135
  simp only [CollatzResearch.WordTrace]
  refine ⟨202539472736947769797132859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135026315157965179864755239 202539472736947769797132859)
  ·
    refine ⟨303809209105421654695699289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202539472736947769797132859 303809209105421654695699289)
    ·
      refine ⟨227856906829066241021774467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303809209105421654695699289 227856906829066241021774467)
      ·
        refine ⟨341785360243599361532661701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227856906829066241021774467 341785360243599361532661701)
        ·
          refine ⟨64084755045674880287374069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 341785360243599361532661701 64084755045674880287374069)
          ·
            refine ⟨6007945785532020026941319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64084755045674880287374069 6007945785532020026941319)
            ·
              refine ⟨9011918678298030040411979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6007945785532020026941319 9011918678298030040411979)
              ·
                refine ⟨13517878017447045060617969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9011918678298030040411979 13517878017447045060617969)
                ·
                  refine ⟨10138408513085283795463477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13517878017447045060617969 10138408513085283795463477)
                  ·
                    refine ⟨950475798101745355824701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10138408513085283795463477 950475798101745355824701)
                    ·
                      rfl

theorem cell23_5553135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 5].length) (baseStart_5553135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553135 prefixEnd_5553135 := by exact prefixLift 5553135
  have htrace : WordTrace (prefixWord ++ tailWord_5553135) baseStart_5553135 baseEnd_5553135 := by
    simpa [prefixWord, tailWord_5553135, baseEnd_5553135] using wordTrace_append hprefix tailTrace_5553135
  have hstable : (prefixWord ++ tailWord_5553135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553135).length < 2 ^ (prefixWord ++ tailWord_5553135).sum := by decide
  have hdescent : baseEnd_5553135 < baseStart_5553135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553175 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 3]
def baseStart_5553175 : Nat := 118140960795 + 5553175 * 2 ^ 59
def prefixEnd_5553175 : Nat := 4983230072969 + 3 ^ 40 * 5553175 * 2
def baseEnd_5553175 : Nat := 2851447933531415910973919

theorem tailTrace_5553175 : CollatzResearch.WordTrace tailWord_5553175 prefixEnd_5553175 2851447933531415910973919 := by
  unfold tailWord_5553175
  simp only [CollatzResearch.WordTrace]
  refine ⟨202540931656802856628588979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135027287771201904419059319 202540931656802856628588979)
  ·
    refine ⟨303811397485204284942883469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202540931656802856628588979 303811397485204284942883469)
    ·
      refine ⟨113929274056951606853581301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303811397485204284942883469 113929274056951606853581301)
      ·
        refine ⟨10680869442839213142523247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113929274056951606853581301 10680869442839213142523247)
        ·
          refine ⟨16021304164258819713784871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10680869442839213142523247 16021304164258819713784871)
          ·
            refine ⟨24031956246388229570677307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16021304164258819713784871 24031956246388229570677307)
            ·
              refine ⟨36047934369582344356015961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24031956246388229570677307 36047934369582344356015961)
              ·
                refine ⟨27035950777186758267011971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36047934369582344356015961 27035950777186758267011971)
                ·
                  refine ⟨40553926165780137400517957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27035950777186758267011971 40553926165780137400517957)
                  ·
                    refine ⟨7603861156083775762597117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40553926165780137400517957 7603861156083775762597117)
                    ·
                      refine ⟨2851447933531415910973919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7603861156083775762597117 2851447933531415910973919)
                      ·
                        rfl

theorem cell23_5553175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_5553175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553175 prefixEnd_5553175 := by exact prefixLift 5553175
  have htrace : WordTrace (prefixWord ++ tailWord_5553175) baseStart_5553175 baseEnd_5553175 := by
    simpa [prefixWord, tailWord_5553175, baseEnd_5553175] using wordTrace_append hprefix tailTrace_5553175
  have hstable : (prefixWord ++ tailWord_5553175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553175).length < 2 ^ (prefixWord ++ tailWord_5553175).sum := by decide
  have hdescent : baseEnd_5553175 < baseStart_5553175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553228 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_5553228 : Nat := 118140960795 + 5553228 * 2 ^ 59
def prefixEnd_5553228 : Nat := 4983230072969 + 3 ^ 40 * 5553228 * 2
def baseEnd_5553228 : Nat := 2851475148006104203611175

theorem tailTrace_5553228 : CollatzResearch.WordTrace tailWord_5553228 prefixEnd_5553228 2851475148006104203611175 := by
  unfold tailWord_5553228
  simp only [CollatzResearch.WordTrace]
  refine ⟨101271432362805423340134169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135028576483740564453512225 101271432362805423340134169)
  ·
    refine ⟨75953574272104067505100627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101271432362805423340134169 75953574272104067505100627)
    ·
      refine ⟨113930361408156101257650941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75953574272104067505100627 113930361408156101257650941)
      ·
        refine ⟨42723885528058537971619103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113930361408156101257650941 42723885528058537971619103)
        ·
          refine ⟨64085828292087806957428655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42723885528058537971619103 64085828292087806957428655)
          ·
            refine ⟨96128742438131710436142983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64085828292087806957428655 96128742438131710436142983)
            ·
              refine ⟨144193113657197565654214475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96128742438131710436142983 144193113657197565654214475)
              ·
                refine ⟨216289670485796348481321713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144193113657197565654214475 216289670485796348481321713)
                ·
                  refine ⟨162217252864347261360991285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216289670485796348481321713 162217252864347261360991285)
                  ·
                    refine ⟨15207867456032555752592933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 162217252864347261360991285 15207867456032555752592933)
                    ·
                      refine ⟨2851475148006104203611175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15207867456032555752592933 2851475148006104203611175)
                      ·
                        rfl

theorem cell23_5553228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_5553228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553228 prefixEnd_5553228 := by exact prefixLift 5553228
  have htrace : WordTrace (prefixWord ++ tailWord_5553228) baseStart_5553228 baseEnd_5553228 := by
    simpa [prefixWord, tailWord_5553228, baseEnd_5553228] using wordTrace_append hprefix tailTrace_5553228
  have hstable : (prefixWord ++ tailWord_5553228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553228).length < 2 ^ (prefixWord ++ tailWord_5553228).sum := by decide
  have hdescent : baseEnd_5553228 < baseStart_5553228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553229 : List Nat := [1, 6, 1, 1, 1, 4, 2, 1, 6]
def baseStart_5553229 : Nat := 118140960795 + 5553229 * 2 ^ 59
def prefixEnd_5553229 : Nat := 4983230072969 + 3 ^ 40 * 5553229 * 2
def baseEnd_5553229 : Nat := 316830629054084299966519

theorem tailTrace_5553229 : CollatzResearch.WordTrace tailWord_5553229 prefixEnd_5553229 316830629054084299966519 := by
  unfold tailWord_5553229
  simp only [CollatzResearch.WordTrace]
  refine ⟨202542901198607223851054741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135028600799071482567369827 202542901198607223851054741)
  ·
    refine ⟨9494198493684713618018191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 202542901198607223851054741 9494198493684713618018191)
    ·
      refine ⟨14241297740527070427027287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9494198493684713618018191 14241297740527070427027287)
      ·
        refine ⟨21361946610790605640540931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14241297740527070427027287 21361946610790605640540931)
        ·
          refine ⟨32042919916185908460811397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21361946610790605640540931 32042919916185908460811397)
          ·
            refine ⟨6008047484284857836402137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32042919916185908460811397 6008047484284857836402137)
            ·
              refine ⟨4506035613213643377301603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6008047484284857836402137 4506035613213643377301603)
              ·
                refine ⟨6759053419820465065952405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4506035613213643377301603 6759053419820465065952405)
                ·
                  refine ⟨316830629054084299966519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6759053419820465065952405 316830629054084299966519)
                  ·
                    rfl

theorem cell23_5553229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_5553229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553229 prefixEnd_5553229 := by exact prefixLift 5553229
  have htrace : WordTrace (prefixWord ++ tailWord_5553229) baseStart_5553229 baseEnd_5553229 := by
    simpa [prefixWord, tailWord_5553229, baseEnd_5553229] using wordTrace_append hprefix tailTrace_5553229
  have hstable : (prefixWord ++ tailWord_5553229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553229).length < 2 ^ (prefixWord ++ tailWord_5553229).sum := by decide
  have hdescent : baseEnd_5553229 < baseStart_5553229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553255 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 1, 6]
def baseStart_5553255 : Nat := 118140960795 + 5553255 * 2 ^ 59
def prefixEnd_5553255 : Nat := 4983230072969 + 3 ^ 40 * 5553255 * 2
def baseEnd_5553255 : Nat := 950496337327925199324517

theorem tailTrace_5553255 : CollatzResearch.WordTrace tailWord_5553255 prefixEnd_5553255 950496337327925199324517 := by
  unfold tailWord_5553255
  simp only [CollatzResearch.WordTrace]
  refine ⟨202543849496513030291501219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135029232997675353527667479 202543849496513030291501219)
  ·
    refine ⟨303815774244769545437251829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202543849496513030291501219 303815774244769545437251829)
    ·
      refine ⟨28482728835447144884742359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 303815774244769545437251829 28482728835447144884742359)
      ·
        refine ⟨42724093253170717327113539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28482728835447144884742359 42724093253170717327113539)
        ·
          refine ⟨64086139879756075990670309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42724093253170717327113539 64086139879756075990670309)
          ·
            refine ⟨12016151227454264248250683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64086139879756075990670309 12016151227454264248250683)
            ·
              refine ⟨18024226841181396372376025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12016151227454264248250683 18024226841181396372376025)
              ·
                refine ⟨13518170130886047279282019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18024226841181396372376025 13518170130886047279282019)
                ·
                  refine ⟨20277255196329070918923029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13518170130886047279282019 20277255196329070918923029)
                  ·
                    refine ⟨950496337327925199324517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20277255196329070918923029 950496337327925199324517)
                    ·
                      rfl

theorem cell23_5553255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_5553255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553255 prefixEnd_5553255 := by exact prefixLift 5553255
  have htrace : WordTrace (prefixWord ++ tailWord_5553255) baseStart_5553255 baseEnd_5553255 := by
    simpa [prefixWord, tailWord_5553255, baseEnd_5553255] using wordTrace_append hprefix tailTrace_5553255
  have hstable : (prefixWord ++ tailWord_5553255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553255).length < 2 ^ (prefixWord ++ tailWord_5553255).sum := by decide
  have hdescent : baseEnd_5553255 < baseStart_5553255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553273 : List Nat := [1, 2, 1, 3, 5, 2, 2, 2, 1, 1, 3]
def baseStart_5553273 : Nat := 118140960795 + 5553273 * 2 ^ 59
def prefixEnd_5553273 : Nat := 4983230072969 + 3 ^ 40 * 5553273 * 2
def baseEnd_5553273 : Nat := 2851498254635556527548469

theorem tailTrace_5553273 : CollatzResearch.WordTrace tailWord_5553273 prefixEnd_5553273 2851498254635556527548469 := by
  unfold tailWord_5553273
  simp only [CollatzResearch.WordTrace]
  refine ⟨202544506010447819365656473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135029670673631879577104315 202544506010447819365656473)
  ·
    refine ⟨151908379507835864524242355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202544506010447819365656473 151908379507835864524242355)
    ·
      refine ⟨227862569261753796786363533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151908379507835864524242355 227862569261753796786363533)
      ·
        refine ⟨85448463473157673794886325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227862569261753796786363533 85448463473157673794886325)
        ·
          refine ⟨8010793450608531918270593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85448463473157673794886325 8010793450608531918270593)
          ·
            refine ⟨6008095087956398938702945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8010793450608531918270593 6008095087956398938702945)
            ·
              refine ⟨4506071315967299204027209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6008095087956398938702945 4506071315967299204027209)
              ·
                refine ⟨3379553486975474403020407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4506071315967299204027209 3379553486975474403020407)
                ·
                  refine ⟨5069330230463211604530611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3379553486975474403020407 5069330230463211604530611)
                  ·
                    refine ⟨7603995345694817406795917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5069330230463211604530611 7603995345694817406795917)
                    ·
                      refine ⟨2851498254635556527548469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7603995345694817406795917 2851498254635556527548469)
                      ·
                        rfl

theorem cell23_5553273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_5553273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553273 prefixEnd_5553273 := by exact prefixLift 5553273
  have htrace : WordTrace (prefixWord ++ tailWord_5553273) baseStart_5553273 baseEnd_5553273 := by
    simpa [prefixWord, tailWord_5553273, baseEnd_5553273] using wordTrace_append hprefix tailTrace_5553273
  have hstable : (prefixWord ++ tailWord_5553273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553273).length < 2 ^ (prefixWord ++ tailWord_5553273).sum := by decide
  have hdescent : baseEnd_5553273 < baseStart_5553273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553312 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 4, 1, 3]
def baseStart_5553312 : Nat := 118140960795 + 5553312 * 2 ^ 59
def prefixEnd_5553312 : Nat := 4983230072969 + 3 ^ 40 * 5553312 * 2
def baseEnd_5553312 : Nat := 2851518280381081874960789

theorem tailTrace_5553312 : CollatzResearch.WordTrace tailWord_5553312 prefixEnd_5553312 2851518280381081874960789 := by
  unfold tailWord_5553312
  simp only [CollatzResearch.WordTrace]
  refine ⟨101272964228653264513163095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135030618971537686017550793 101272964228653264513163095)
  ·
    refine ⟨151909446342979896769744643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101272964228653264513163095 151909446342979896769744643)
    ·
      refine ⟨227864169514469845154616965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151909446342979896769744643 227864169514469845154616965)
      ·
        refine ⟨42724531783963095966490681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227864169514469845154616965 42724531783963095966490681)
        ·
          refine ⟨32043398837972321974868011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42724531783963095966490681 32043398837972321974868011)
          ·
            refine ⟨48065098256958482962302017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32043398837972321974868011 48065098256958482962302017)
            ·
              refine ⟨36048823692718862221726513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48065098256958482962302017 36048823692718862221726513)
              ·
                refine ⟨27036617769539146666294885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36048823692718862221726513 27036617769539146666294885)
                ·
                  refine ⟨5069365831788589999930291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27036617769539146666294885 5069365831788589999930291)
                  ·
                    refine ⟨7604048747682884999895437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5069365831788589999930291 7604048747682884999895437)
                    ·
                      refine ⟨2851518280381081874960789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7604048747682884999895437 2851518280381081874960789)
                      ·
                        rfl

theorem cell23_5553312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_5553312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553312 prefixEnd_5553312 := by exact prefixLift 5553312
  have htrace : WordTrace (prefixWord ++ tailWord_5553312) baseStart_5553312 baseEnd_5553312 := by
    simpa [prefixWord, tailWord_5553312, baseEnd_5553312] using wordTrace_append hprefix tailTrace_5553312
  have hstable : (prefixWord ++ tailWord_5553312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553312).length < 2 ^ (prefixWord ++ tailWord_5553312).sum := by decide
  have hdescent : baseEnd_5553312 < baseStart_5553312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553316 : List Nat := [2, 3, 1, 2, 3, 3, 2, 1, 1, 2, 3]
def baseStart_5553316 : Nat := 118140960795 + 5553316 * 2 ^ 59
def prefixEnd_5553316 : Nat := 4983230072969 + 3 ^ 40 * 5553316 * 2
def baseEnd_5553316 : Nat := 2851520334303699859310771

theorem tailTrace_5553316 : CollatzResearch.WordTrace tailWord_5553316 prefixEnd_5553316 2851520334303699859310771 := by
  unfold tailWord_5553316
  simp only [CollatzResearch.WordTrace]
  refine ⟨101273037174646018854735901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135030716232861358472981201 101273037174646018854735901)
  ·
    refine ⟨37977388940492257070525963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101273037174646018854735901 37977388940492257070525963)
    ·
      refine ⟨56966083410738385605788945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37977388940492257070525963 56966083410738385605788945)
      ·
        refine ⟨42724562558053789204341709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56966083410738385605788945 42724562558053789204341709)
        ·
          refine ⟨16021710959270170951628141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42724562558053789204341709 16021710959270170951628141)
          ·
            refine ⟨6008141609726314106860553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16021710959270170951628141 6008141609726314106860553)
            ·
              refine ⟨4506106207294735580145415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6008141609726314106860553 4506106207294735580145415)
              ·
                refine ⟨6759159310942103370218123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4506106207294735580145415 6759159310942103370218123)
                ·
                  refine ⟨10138738966413155055327185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6759159310942103370218123 10138738966413155055327185)
                  ·
                    refine ⟨7604054224809866291495389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10138738966413155055327185 7604054224809866291495389)
                    ·
                      refine ⟨2851520334303699859310771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7604054224809866291495389 2851520334303699859310771)
                      ·
                        rfl

theorem cell23_5553316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_5553316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553316 prefixEnd_5553316 := by exact prefixLift 5553316
  have htrace : WordTrace (prefixWord ++ tailWord_5553316) baseStart_5553316 baseEnd_5553316 := by
    simpa [prefixWord, tailWord_5553316, baseEnd_5553316] using wordTrace_append hprefix tailTrace_5553316
  have hstable : (prefixWord ++ tailWord_5553316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553316).length < 2 ^ (prefixWord ++ tailWord_5553316).sum := by decide
  have hdescent : baseEnd_5553316 < baseStart_5553316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553328 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 3, 8]
def baseStart_5553328 : Nat := 118140960795 + 5553328 * 2 ^ 59
def prefixEnd_5553328 : Nat := 4983230072969 + 3 ^ 40 * 5553328 * 2
def baseEnd_5553328 : Nat := 950508832023851270786905

theorem tailTrace_5553328 : CollatzResearch.WordTrace tailWord_5553328 prefixEnd_5553328 950508832023851270786905 := by
  unfold tailWord_5553328
  simp only [CollatzResearch.WordTrace]
  refine ⟨101273256012624281879454319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135031008016832375839272425 101273256012624281879454319)
  ·
    refine ⟨151909884018936422819181479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101273256012624281879454319 151909884018936422819181479)
    ·
      refine ⟨227864826028404634228772219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151909884018936422819181479 227864826028404634228772219)
      ·
        refine ⟨341797239042606951343158329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227864826028404634228772219 341797239042606951343158329)
        ·
          refine ⟨256347929281955213507368747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341797239042606951343158329 256347929281955213507368747)
          ·
            refine ⟨384521893922932820261053121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256347929281955213507368747 384521893922932820261053121)
            ·
              refine ⟨288391420442199615195789841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384521893922932820261053121 288391420442199615195789841)
              ·
                refine ⟨216293565331649711396842381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288391420442199615195789841 216293565331649711396842381)
                ·
                  refine ⟨81110086999368641773815893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216293565331649711396842381 81110086999368641773815893)
                  ·
                    refine ⟨950508832023851270786905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81110086999368641773815893 950508832023851270786905)
                    ·
                      rfl

theorem cell23_5553328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_5553328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553328 prefixEnd_5553328 := by exact prefixLift 5553328
  have htrace : WordTrace (prefixWord ++ tailWord_5553328) baseStart_5553328 baseEnd_5553328 := by
    simpa [prefixWord, tailWord_5553328, baseEnd_5553328] using wordTrace_append hprefix tailTrace_5553328
  have hstable : (prefixWord ++ tailWord_5553328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553328).length < 2 ^ (prefixWord ++ tailWord_5553328).sum := by decide
  have hdescent : baseEnd_5553328 < baseStart_5553328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553329 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 4, 1, 3]
def baseStart_5553329 : Nat := 118140960795 + 5553329 * 2 ^ 59
def prefixEnd_5553329 : Nat := 4983230072969 + 3 ^ 40 * 5553329 * 2
def baseEnd_5553329 : Nat := 2851527009552208308448211

theorem tailTrace_5553329 : CollatzResearch.WordTrace tailWord_5553329 prefixEnd_5553329 2851527009552208308448211 := by
  unfold tailWord_5553329
  simp only [CollatzResearch.WordTrace]
  refine ⟨202546548498244940929695041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135031032332163293953130027 202546548498244940929695041)
  ·
    refine ⟨151909911373683705697271281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202546548498244940929695041 151909911373683705697271281)
    ·
      refine ⟨113932433530262779272953461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151909911373683705697271281 113932433530262779272953461)
      ·
        refine ⟨10681165643462135556839387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113932433530262779272953461 10681165643462135556839387)
        ·
          refine ⟨16021748465193203335259081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10681165643462135556839387 16021748465193203335259081)
          ·
            refine ⟨12016311348894902501444311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16021748465193203335259081 12016311348894902501444311)
            ·
              refine ⟨18024467023342353752166467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12016311348894902501444311 18024467023342353752166467)
              ·
                refine ⟨27036700535013530628249701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18024467023342353752166467 27036700535013530628249701)
                ·
                  refine ⟨5069381350315036992796819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27036700535013530628249701 5069381350315036992796819)
                  ·
                    refine ⟨7604072025472555489195229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5069381350315036992796819 7604072025472555489195229)
                    ·
                      refine ⟨2851527009552208308448211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7604072025472555489195229 2851527009552208308448211)
                      ·
                        rfl

theorem cell23_5553329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_5553329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553329 prefixEnd_5553329 := by exact prefixLift 5553329
  have htrace : WordTrace (prefixWord ++ tailWord_5553329) baseStart_5553329 baseEnd_5553329 := by
    simpa [prefixWord, tailWord_5553329, baseEnd_5553329] using wordTrace_append hprefix tailTrace_5553329
  have hstable : (prefixWord ++ tailWord_5553329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553329).length < 2 ^ (prefixWord ++ tailWord_5553329).sum := by decide
  have hdescent : baseEnd_5553329 < baseStart_5553329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553350 : List Nat := [6, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_5553350 : Nat := 118140960795 + 5553350 * 2 ^ 59
def prefixEnd_5553350 : Nat := 4983230072969 + 3 ^ 40 * 5553350 * 2
def baseEnd_5553350 : Nat := 2851537792645952726285615

theorem tailTrace_5553350 : CollatzResearch.WordTrace tailWord_5553350 prefixEnd_5553350 2851537792645952726285615 := by
  unfold tailWord_5553350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6329603575974026922381547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135031542954112574344139669 6329603575974026922381547)
  ·
    refine ⟨9494405363961040383572321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6329603575974026922381547 9494405363961040383572321)
    ·
      refine ⟨7120804022970780287679241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9494405363961040383572321 7120804022970780287679241)
      ·
        refine ⟨5340603017228085215759431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7120804022970780287679241 5340603017228085215759431)
        ·
          refine ⟨8010904525842127823639147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5340603017228085215759431 8010904525842127823639147)
          ·
            refine ⟨12016356788763191735458721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8010904525842127823639147 12016356788763191735458721)
            ·
              refine ⟨9012267591572393801594041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12016356788763191735458721 9012267591572393801594041)
              ·
                refine ⟨6759200693679295351195531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9012267591572393801594041 6759200693679295351195531)
                ·
                  refine ⟨10138801040518943026793297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6759200693679295351195531 10138801040518943026793297)
                  ·
                    refine ⟨7604100780389207270094973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10138801040518943026793297 7604100780389207270094973)
                    ·
                      refine ⟨2851537792645952726285615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7604100780389207270094973 2851537792645952726285615)
                      ·
                        rfl

theorem cell23_5553350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_5553350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553350 prefixEnd_5553350 := by exact prefixLift 5553350
  have htrace : WordTrace (prefixWord ++ tailWord_5553350) baseStart_5553350 baseEnd_5553350 := by
    simpa [prefixWord, tailWord_5553350, baseEnd_5553350] using wordTrace_append hprefix tailTrace_5553350
  have hstable : (prefixWord ++ tailWord_5553350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553350).length < 2 ^ (prefixWord ++ tailWord_5553350).sum := by decide
  have hdescent : baseEnd_5553350 < baseStart_5553350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553422 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_5553422 : Nat := 118140960795 + 5553422 * 2 ^ 59
def prefixEnd_5553422 : Nat := 4983230072969 + 3 ^ 40 * 5553422 * 2
def baseEnd_5553422 : Nat := 950524921084358814861761

theorem tailTrace_5553422 : CollatzResearch.WordTrace tailWord_5553422 prefixEnd_5553422 950524921084358814861761 := by
  unfold tailWord_5553422
  simp only [CollatzResearch.WordTrace]
  refine ⟨25318742560863502226603815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135033293657938678541887013 25318742560863502226603815)
  ·
    refine ⟨37978113841295253339905723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25318742560863502226603815 37978113841295253339905723)
    ·
      refine ⟨56967170761942880009858585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37978113841295253339905723 56967170761942880009858585)
      ·
        refine ⟨42725378071457160007393939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56967170761942880009858585 42725378071457160007393939)
        ·
          refine ⟨64088067107185740011090909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42725378071457160007393939 64088067107185740011090909)
          ·
            refine ⟨24033025165194652504159091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64088067107185740011090909 24033025165194652504159091)
            ·
              refine ⟨36049537747791978756238637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24033025165194652504159091 36049537747791978756238637)
              ·
                refine ⟨13518576655421992033589489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36049537747791978756238637 13518576655421992033589489)
                ·
                  refine ⟨10138932491566494025192117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13518576655421992033589489 10138932491566494025192117)
                  ·
                    refine ⟨950524921084358814861761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10138932491566494025192117 950524921084358814861761)
                    ·
                      rfl

theorem cell23_5553422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_5553422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553422 prefixEnd_5553422 := by exact prefixLift 5553422
  have htrace : WordTrace (prefixWord ++ tailWord_5553422) baseStart_5553422 baseEnd_5553422 := by
    simpa [prefixWord, tailWord_5553422, baseEnd_5553422] using wordTrace_append hprefix tailTrace_5553422
  have hstable : (prefixWord ++ tailWord_5553422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553422).length < 2 ^ (prefixWord ++ tailWord_5553422).sum := by decide
  have hdescent : baseEnd_5553422 < baseStart_5553422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553452 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 3, 4]
def baseStart_5553452 : Nat := 118140960795 + 5553452 * 2 ^ 59
def prefixEnd_5553452 : Nat := 4983230072969 + 3 ^ 40 * 5553452 * 2
def baseEnd_5553452 : Nat := 950530055890903775736715

theorem tailTrace_5553452 : CollatzResearch.WordTrace tailWord_5553452 prefixEnd_5553452 950530055890903775736715 := by
  unfold tailWord_5553452
  simp only [CollatzResearch.WordTrace]
  refine ⟨101275517338399666468211305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135034023117866221957615073 101275517338399666468211305)
  ·
    refine ⟨75956638003799749851158479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101275517338399666468211305 75956638003799749851158479)
    ·
      refine ⟨113934957005699624776737719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75956638003799749851158479 113934957005699624776737719)
      ·
        refine ⟨170902435508549437165106579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113934957005699624776737719 170902435508549437165106579)
        ·
          refine ⟨256353653262824155747659869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170902435508549437165106579 256353653262824155747659869)
          ·
            refine ⟨96132619973559058405372451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256353653262824155747659869 96132619973559058405372451)
            ·
              refine ⟨144198929960338587608058677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96132619973559058405372451 144198929960338587608058677)
              ·
                refine ⟨13518649683781742588255501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144198929960338587608058677 13518649683781742588255501)
                ·
                  refine ⟨5069493631418153470595813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13518649683781742588255501 5069493631418153470595813)
                  ·
                    refine ⟨950530055890903775736715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5069493631418153470595813 950530055890903775736715)
                    ·
                      rfl

theorem cell23_5553452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_5553452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553452 prefixEnd_5553452 := by exact prefixLift 5553452
  have htrace : WordTrace (prefixWord ++ tailWord_5553452) baseStart_5553452 baseEnd_5553452 := by
    simpa [prefixWord, tailWord_5553452, baseEnd_5553452] using wordTrace_append hprefix tailTrace_5553452
  have hstable : (prefixWord ++ tailWord_5553452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553452).length < 2 ^ (prefixWord ++ tailWord_5553452).sum := by decide
  have hdescent : baseEnd_5553452 < baseStart_5553452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553455 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 4]
def baseStart_5553455 : Nat := 118140960795 + 5553455 * 2 ^ 59
def prefixEnd_5553455 : Nat := 4983230072969 + 3 ^ 40 * 5553455 * 2
def baseEnd_5553455 : Nat := 2851591708114674815472631

theorem tailTrace_5553455 : CollatzResearch.WordTrace tailWord_5553455 prefixEnd_5553455 2851591708114674815472631 := by
  unfold tailWord_5553455
  simp only [CollatzResearch.WordTrace]
  refine ⟨202551144095788464448781819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135034096063858976299187879 202551144095788464448781819)
  ·
    refine ⟨303826716143682696673172729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202551144095788464448781819 303826716143682696673172729)
    ·
      refine ⟨227870037107762022504879547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303826716143682696673172729 227870037107762022504879547)
      ·
        refine ⟨341805055661643033757319321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227870037107762022504879547 341805055661643033757319321)
        ·
          refine ⟨256353791746232275317989491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341805055661643033757319321 256353791746232275317989491)
          ·
            refine ⟨384530687619348412976984237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256353791746232275317989491 384530687619348412976984237)
            ·
              refine ⟨144199007857255654866369089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 384530687619348412976984237 144199007857255654866369089)
              ·
                refine ⟨108149255892941741149776817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144199007857255654866369089 108149255892941741149776817)
                ·
                  refine ⟨81111941919706305862332613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108149255892941741149776817 81111941919706305862332613)
                  ·
                    refine ⟨15208489109944932349187365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81111941919706305862332613 15208489109944932349187365)
                    ·
                      refine ⟨2851591708114674815472631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15208489109944932349187365 2851591708114674815472631)
                      ·
                        rfl

theorem cell23_5553455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_5553455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553455 prefixEnd_5553455 := by exact prefixLift 5553455
  have htrace : WordTrace (prefixWord ++ tailWord_5553455) baseStart_5553455 baseEnd_5553455 := by
    simpa [prefixWord, tailWord_5553455, baseEnd_5553455] using wordTrace_append hprefix tailTrace_5553455
  have hstable : (prefixWord ++ tailWord_5553455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553455).length < 2 ^ (prefixWord ++ tailWord_5553455).sum := by decide
  have hdescent : baseEnd_5553455 < baseStart_5553455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553459 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 2, 4, 2]
def baseStart_5553459 : Nat := 118140960795 + 5553459 * 2 ^ 59
def prefixEnd_5553459 : Nat := 4983230072969 + 3 ^ 40 * 5553459 * 2
def baseEnd_5553459 : Nat := 2851593762037292799822613

theorem tailTrace_5553459 : CollatzResearch.WordTrace tailWord_5553459 prefixEnd_5553459 2851593762037292799822613 := by
  unfold tailWord_5553459
  simp only [CollatzResearch.WordTrace]
  refine ⟨202551289987773973131927431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135034193325182648754618287 202551289987773973131927431)
  ·
    refine ⟨303826934981660959697891147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202551289987773973131927431 303826934981660959697891147)
    ·
      refine ⟨455740402472491439546836721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303826934981660959697891147 455740402472491439546836721)
      ·
        refine ⟨341805301854368579660127541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 455740402472491439546836721 341805301854368579660127541)
        ·
          refine ⟨32044247048847054343136957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 341805301854368579660127541 32044247048847054343136957)
          ·
            refine ⟨12016592643317645378676359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32044247048847054343136957 12016592643317645378676359)
            ·
              refine ⟨18024888964976468068014539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12016592643317645378676359 18024888964976468068014539)
              ·
                refine ⟨27037333447464702102021809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18024888964976468068014539 27037333447464702102021809)
                ·
                  refine ⟨20278000085598526576516357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27037333447464702102021809 20278000085598526576516357)
                  ·
                    refine ⟨3802125016049723733096817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20278000085598526576516357 3802125016049723733096817)
                    ·
                      refine ⟨2851593762037292799822613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3802125016049723733096817 2851593762037292799822613)
                      ·
                        rfl

theorem cell23_5553459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 4, 2].length) (baseStart_5553459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553459 prefixEnd_5553459 := by exact prefixLift 5553459
  have htrace : WordTrace (prefixWord ++ tailWord_5553459) baseStart_5553459 baseEnd_5553459 := by
    simpa [prefixWord, tailWord_5553459, baseEnd_5553459] using wordTrace_append hprefix tailTrace_5553459
  have hstable : (prefixWord ++ tailWord_5553459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553459).length < 2 ^ (prefixWord ++ tailWord_5553459).sum := by decide
  have hdescent : baseEnd_5553459 < baseStart_5553459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553476 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_5553476 : Nat := 118140960795 + 5553476 * 2 ^ 59
def prefixEnd_5553476 : Nat := 4983230072969 + 3 ^ 40 * 5553476 * 2
def baseEnd_5553476 : Nat := 2851602491208419233310035

theorem tailTrace_5553476 : CollatzResearch.WordTrace tailWord_5553476 prefixEnd_5553476 2851602491208419233310035 := by
  unfold tailWord_5553476
  simp only [CollatzResearch.WordTrace]
  refine ⟨101275955014356192517648141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135034606685808256690197521 101275955014356192517648141)
  ·
    refine ⟨37978483130383572194118053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101275955014356192517648141 37978483130383572194118053)
    ·
      refine ⟨7120965586946919786397135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37978483130383572194118053 7120965586946919786397135)
      ·
        refine ⟨10681448380420379679595703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7120965586946919786397135 10681448380420379679595703)
        ·
          refine ⟨16022172570630569519393555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10681448380420379679595703 16022172570630569519393555)
          ·
            refine ⟨24033258855945854279090333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16022172570630569519393555 24033258855945854279090333)
            ·
              refine ⟨9012472070979695354658875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24033258855945854279090333 9012472070979695354658875)
              ·
                refine ⟨13518708106469543031988313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9012472070979695354658875 13518708106469543031988313)
                ·
                  refine ⟨10139031079852157273991235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13518708106469543031988313 10139031079852157273991235)
                  ·
                    refine ⟨15208546619778235910986853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10139031079852157273991235 15208546619778235910986853)
                    ·
                      refine ⟨2851602491208419233310035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15208546619778235910986853 2851602491208419233310035)
                      ·
                        rfl

theorem cell23_5553476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_5553476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553476 prefixEnd_5553476 := by exact prefixLift 5553476
  have htrace : WordTrace (prefixWord ++ tailWord_5553476) baseStart_5553476 baseEnd_5553476 := by
    simpa [prefixWord, tailWord_5553476, baseEnd_5553476] using wordTrace_append hprefix tailTrace_5553476
  have hstable : (prefixWord ++ tailWord_5553476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553476).length < 2 ^ (prefixWord ++ tailWord_5553476).sum := by decide
  have hdescent : baseEnd_5553476 < baseStart_5553476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553479 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_5553479 : Nat := 118140960795 + 5553479 * 2 ^ 59
def prefixEnd_5553479 : Nat := 4983230072969 + 3 ^ 40 * 5553479 * 2
def baseEnd_5553479 : Nat := 2851604031650382721572521

theorem tailTrace_5553479 : CollatzResearch.WordTrace tailWord_5553479 prefixEnd_5553479 2851604031650382721572521 := by
  unfold tailWord_5553479
  simp only [CollatzResearch.WordTrace]
  refine ⟨202552019447701516547655491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135034679631801011031770327 202552019447701516547655491)
  ·
    refine ⟨303828029171552274821483237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202552019447701516547655491 303828029171552274821483237)
    ·
      refine ⟨56967755469666051529028107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303828029171552274821483237 56967755469666051529028107)
      ·
        refine ⟨85451633204499077293542161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56967755469666051529028107 85451633204499077293542161)
        ·
          refine ⟨64088724903374307970156621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85451633204499077293542161 64088724903374307970156621)
          ·
            refine ⟨24033271838765365488808733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64088724903374307970156621 24033271838765365488808733)
            ·
              refine ⟨9012476939537012058303275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24033271838765365488808733 9012476939537012058303275)
              ·
                refine ⟨13518715409305518087454913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9012476939537012058303275 13518715409305518087454913)
                ·
                  refine ⟨10139036556979138565591185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13518715409305518087454913 10139036556979138565591185)
                  ·
                    refine ⟨7604277417734353924193389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10139036556979138565591185 7604277417734353924193389)
                    ·
                      refine ⟨2851604031650382721572521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7604277417734353924193389 2851604031650382721572521)
                      ·
                        rfl

theorem cell23_5553479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_5553479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553479 prefixEnd_5553479 := by exact prefixLift 5553479
  have htrace : WordTrace (prefixWord ++ tailWord_5553479) baseStart_5553479 baseEnd_5553479 := by
    simpa [prefixWord, tailWord_5553479, baseEnd_5553479] using wordTrace_append hprefix tailTrace_5553479
  have hstable : (prefixWord ++ tailWord_5553479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553479).length < 2 ^ (prefixWord ++ tailWord_5553479).sum := by decide
  have hdescent : baseEnd_5553479 < baseStart_5553479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553486 : List Nat := [4, 1, 1, 1, 1, 1, 6, 3, 1, 4]
def baseStart_5553486 : Nat := 118140960795 + 5553486 * 2 ^ 59
def prefixEnd_5553486 : Nat := 4983230072969 + 3 ^ 40 * 5553486 * 2
def baseEnd_5553486 : Nat := 950535875338321398061663

theorem tailTrace_5553486 : CollatzResearch.WordTrace tailWord_5553486 prefixEnd_5553486 950535875338321398061663 := by
  unfold tailWord_5553486
  simp only [CollatzResearch.WordTrace]
  refine ⟨25319034344834519592895039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135034849839117437828773541 25319034344834519592895039)
  ·
    refine ⟨37978551517251779389342559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25319034344834519592895039 37978551517251779389342559)
    ·
      refine ⟨56967827275877669084013839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37978551517251779389342559 56967827275877669084013839)
      ·
        refine ⟨85451740913816503626020759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56967827275877669084013839 85451740913816503626020759)
        ·
          refine ⟨128177611370724755439031139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85451740913816503626020759 128177611370724755439031139)
          ·
            refine ⟨192266417056087133158546709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128177611370724755439031139 192266417056087133158546709)
            ·
              refine ⟨9012488299504084366806877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 192266417056087133158546709 9012488299504084366806877)
              ·
                refine ⟨3379683112314031637552579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9012488299504084366806877 3379683112314031637552579)
                ·
                  refine ⟨5069524668471047456328869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3379683112314031637552579 5069524668471047456328869)
                  ·
                    refine ⟨950535875338321398061663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5069524668471047456328869 950535875338321398061663)
                    ·
                      rfl

theorem cell23_5553486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_5553486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553486 prefixEnd_5553486 := by exact prefixLift 5553486
  have htrace : WordTrace (prefixWord ++ tailWord_5553486) baseStart_5553486 baseEnd_5553486 := by
    simpa [prefixWord, tailWord_5553486, baseEnd_5553486] using wordTrace_append hprefix tailTrace_5553486
  have hstable : (prefixWord ++ tailWord_5553486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553486).length < 2 ^ (prefixWord ++ tailWord_5553486).sum := by decide
  have hdescent : baseEnd_5553486 < baseStart_5553486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553543 : List Nat := [1, 1, 4, 2, 2, 2, 3, 3, 1, 1, 3]
def baseStart_5553543 : Nat := 118140960795 + 5553543 * 2 ^ 59
def prefixEnd_5553543 : Nat := 4983230072969 + 3 ^ 40 * 5553543 * 2
def baseEnd_5553543 : Nat := 2851636894412270471172227

theorem tailTrace_5553543 : CollatzResearch.WordTrace tailWord_5553543 prefixEnd_5553543 2851636894412270471172227 := by
  unfold tailWord_5553543
  simp only [CollatzResearch.WordTrace]
  refine ⟨202554353719469655477985283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135036235812979770318656855 202554353719469655477985283)
  ·
    refine ⟨303831530579204483216977925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202554353719469655477985283 303831530579204483216977925)
    ·
      refine ⟨56968411983600840603183361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303831530579204483216977925 56968411983600840603183361)
      ·
        refine ⟨42726308987700630452387521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56968411983600840603183361 42726308987700630452387521)
        ·
          refine ⟨32044731740775472839290641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42726308987700630452387521 32044731740775472839290641)
          ·
            refine ⟨24033548805581604629467981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32044731740775472839290641 24033548805581604629467981)
            ·
              refine ⟨9012580802093101736050493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24033548805581604629467981 9012580802093101736050493)
              ·
                refine ⟨3379717800784913151018935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9012580802093101736050493 3379717800784913151018935)
                ·
                  refine ⟨5069576701177369726528403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3379717800784913151018935 5069576701177369726528403)
                  ·
                    refine ⟨7604365051766054589792605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5069576701177369726528403 7604365051766054589792605)
                    ·
                      refine ⟨2851636894412270471172227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7604365051766054589792605 2851636894412270471172227)
                      ·
                        rfl

theorem cell23_5553543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_5553543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553543 prefixEnd_5553543 := by exact prefixLift 5553543
  have htrace : WordTrace (prefixWord ++ tailWord_5553543) baseStart_5553543 baseEnd_5553543 := by
    simpa [prefixWord, tailWord_5553543, baseEnd_5553543] using wordTrace_append hprefix tailTrace_5553543
  have hstable : (prefixWord ++ tailWord_5553543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553543).length < 2 ^ (prefixWord ++ tailWord_5553543).sum := by decide
  have hdescent : baseEnd_5553543 < baseStart_5553543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553559 : List Nat := [1, 1, 3, 3, 1, 1, 1, 6, 2, 4]
def baseStart_5553559 : Nat := 118140960795 + 5553559 * 2 ^ 59
def prefixEnd_5553559 : Nat := 4983230072969 + 3 ^ 40 * 5553559 * 2
def baseEnd_5553559 : Nat := 950548370034247469524051

theorem tailTrace_5553559 : CollatzResearch.WordTrace tailWord_5553559 prefixEnd_5553559 950548370034247469524051 := by
  unfold tailWord_5553559
  simp only [CollatzResearch.WordTrace]
  refine ⟨202554937287411690210567731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135036624858274460140378487 202554937287411690210567731)
  ·
    refine ⟨303832405931117535315851597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202554937287411690210567731 303832405931117535315851597)
    ·
      refine ⟨113937152224169075743444349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303832405931117535315851597 113937152224169075743444349)
      ·
        refine ⟨42726432084063403403791631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113937152224169075743444349 42726432084063403403791631)
        ·
          refine ⟨64089648126095105105687447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42726432084063403403791631 64089648126095105105687447)
          ·
            refine ⟨96134472189142657658531171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64089648126095105105687447 96134472189142657658531171)
            ·
              refine ⟨144201708283713986487796757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96134472189142657658531171 144201708283713986487796757)
              ·
                refine ⟨6759455075799093116615473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 144201708283713986487796757 6759455075799093116615473)
                ·
                  refine ⟨5069591306849319837461605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6759455075799093116615473 5069591306849319837461605)
                  ·
                    refine ⟨950548370034247469524051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5069591306849319837461605 950548370034247469524051)
                    ·
                      rfl

theorem cell23_5553559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_5553559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553559 prefixEnd_5553559 := by exact prefixLift 5553559
  have htrace : WordTrace (prefixWord ++ tailWord_5553559) baseStart_5553559 baseEnd_5553559 := by
    simpa [prefixWord, tailWord_5553559, baseEnd_5553559] using wordTrace_append hprefix tailTrace_5553559
  have hstable : (prefixWord ++ tailWord_5553559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553559).length < 2 ^ (prefixWord ++ tailWord_5553559).sum := by decide
  have hdescent : baseEnd_5553559 < baseStart_5553559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553560 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 3, 1, 3]
def baseStart_5553560 : Nat := 118140960795 + 5553560 * 2 ^ 59
def prefixEnd_5553560 : Nat := 4983230072969 + 3 ^ 40 * 5553560 * 2
def baseEnd_5553560 : Nat := 2851645623583396904659649

theorem tailTrace_5553560 : CollatzResearch.WordTrace tailWord_5553560 prefixEnd_5553560 2851645623583396904659649 := by
  unfold tailWord_5553560
  simp only [CollatzResearch.WordTrace]
  refine ⟨101277486880204033690677067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135036649173605378254236089 101277486880204033690677067)
  ·
    refine ⟨151916230320306050536015601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101277486880204033690677067 151916230320306050536015601)
    ·
      refine ⟨113937172740229537902011701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151916230320306050536015601 113937172740229537902011701)
      ·
        refine ⟨10681609944396519178313597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113937172740229537902011701 10681609944396519178313597)
        ·
          refine ⟨4005603729148694691867599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10681609944396519178313597 4005603729148694691867599)
          ·
            refine ⟨6008405593723042037801399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4005603729148694691867599 6008405593723042037801399)
            ·
              refine ⟨9012608390584563056702099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6008405593723042037801399 9012608390584563056702099)
              ·
                refine ⟨13518912585876844585053149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9012608390584563056702099 13518912585876844585053149)
                ·
                  refine ⟨5069592219703816719394931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13518912585876844585053149 5069592219703816719394931)
                  ·
                    refine ⟨7604388329555725079092397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5069592219703816719394931 7604388329555725079092397)
                    ·
                      refine ⟨2851645623583396904659649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7604388329555725079092397 2851645623583396904659649)
                      ·
                        rfl

theorem cell23_5553560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_5553560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553560 prefixEnd_5553560 := by exact prefixLift 5553560
  have htrace : WordTrace (prefixWord ++ tailWord_5553560) baseStart_5553560 baseEnd_5553560 := by
    simpa [prefixWord, tailWord_5553560, baseEnd_5553560] using wordTrace_append hprefix tailTrace_5553560
  have hstable : (prefixWord ++ tailWord_5553560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553560).length < 2 ^ (prefixWord ++ tailWord_5553560).sum := by decide
  have hdescent : baseEnd_5553560 < baseStart_5553560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553562 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_5553562 : Nat := 118140960795 + 5553562 * 2 ^ 59
def prefixEnd_5553562 : Nat := 4983230072969 + 3 ^ 40 * 5553562 * 2
def baseEnd_5553562 : Nat := 2851646650544705896834639

theorem tailTrace_5553562 : CollatzResearch.WordTrace tailWord_5553562 prefixEnd_5553562 2851646650544705896834639 := by
  unfold tailWord_5553562
  simp only [CollatzResearch.WordTrace]
  refine ⟨50638761676600205430731735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135036697804267214481951293 50638761676600205430731735)
  ·
    refine ⟨75958142514900308146097603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50638761676600205430731735 75958142514900308146097603)
    ·
      refine ⟨113937213772350462219146405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75958142514900308146097603 113937213772350462219146405)
      ·
        refine ⟨21363227582315711666089951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113937213772350462219146405 21363227582315711666089951)
        ·
          refine ⟨32044841373473567499134927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21363227582315711666089951 32044841373473567499134927)
          ·
            refine ⟨48067262060210351248702391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32044841373473567499134927 48067262060210351248702391)
            ·
              refine ⟨72100893090315526873053587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48067262060210351248702391 72100893090315526873053587)
              ·
                refine ⟨108151339635473290309580381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72100893090315526873053587 108151339635473290309580381)
                ·
                  refine ⟨40556752363302483866092643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108151339635473290309580381 40556752363302483866092643)
                  ·
                    refine ⟨60835128544953725799138965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40556752363302483866092643 60835128544953725799138965)
                    ·
                      refine ⟨2851646650544705896834639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60835128544953725799138965 2851646650544705896834639)
                      ·
                        rfl

theorem cell23_5553562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_5553562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553562 prefixEnd_5553562 := by exact prefixLift 5553562
  have htrace : WordTrace (prefixWord ++ tailWord_5553562) baseStart_5553562 baseEnd_5553562 := by
    simpa [prefixWord, tailWord_5553562, baseEnd_5553562] using wordTrace_append hprefix tailTrace_5553562
  have hstable : (prefixWord ++ tailWord_5553562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553562).length < 2 ^ (prefixWord ++ tailWord_5553562).sum := by decide
  have hdescent : baseEnd_5553562 < baseStart_5553562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553596 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_5553596 : Nat := 118140960795 + 5553596 * 2 ^ 59
def prefixEnd_5553596 : Nat := 4983230072969 + 3 ^ 40 * 5553596 * 2
def baseEnd_5553596 : Nat := 2851664108886958763809483

theorem tailTrace_5553596 : CollatzResearch.WordTrace tailWord_5553596 prefixEnd_5553596 2851664108886958763809483 := by
  unfold tailWord_5553596
  simp only [CollatzResearch.WordTrace]
  refine ⟨101278143394138822764832321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135037524525518430353109761 101278143394138822764832321)
  ·
    refine ⟨75958607545604117073624241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101278143394138822764832321 75958607545604117073624241)
    ·
      refine ⟨56968955659203087805218181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75958607545604117073624241 56968955659203087805218181)
      ·
        refine ⟨10681679186100578963478409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56968955659203087805218181 10681679186100578963478409)
        ·
          refine ⟨8011259389575434222608807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10681679186100578963478409 8011259389575434222608807)
          ·
            refine ⟨12016889084363151333913211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8011259389575434222608807 12016889084363151333913211)
            ·
              refine ⟨18025333626544727000869817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12016889084363151333913211 18025333626544727000869817)
              ·
                refine ⟨13519000219908545250652363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18025333626544727000869817 13519000219908545250652363)
                ·
                  refine ⟨20278500329862817875978545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13519000219908545250652363 20278500329862817875978545)
                  ·
                    refine ⟨15208875247397113406983909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20278500329862817875978545 15208875247397113406983909)
                    ·
                      refine ⟨2851664108886958763809483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15208875247397113406983909 2851664108886958763809483)
                      ·
                        rfl

theorem cell23_5553596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_5553596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553596 prefixEnd_5553596 := by exact prefixLift 5553596
  have htrace : WordTrace (prefixWord ++ tailWord_5553596) baseStart_5553596 baseEnd_5553596 := by
    simpa [prefixWord, tailWord_5553596, baseEnd_5553596] using wordTrace_append hprefix tailTrace_5553596
  have hstable : (prefixWord ++ tailWord_5553596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553596).length < 2 ^ (prefixWord ++ tailWord_5553596).sum := by decide
  have hdescent : baseEnd_5553596 < baseStart_5553596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553599 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 6, 1, 3]
def baseStart_5553599 : Nat := 118140960795 + 5553599 * 2 ^ 59
def prefixEnd_5553599 : Nat := 4983230072969 + 3 ^ 40 * 5553599 * 2
def baseEnd_5553599 : Nat := 2851665649328922252071969

theorem tailTrace_5553599 : CollatzResearch.WordTrace tailWord_5553599 prefixEnd_5553599 2851665649328922252071969 := by
  unfold tailWord_5553599
  simp only [CollatzResearch.WordTrace]
  refine ⟨202556396207266777042023851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135037597471511184694682567 202556396207266777042023851)
  ·
    refine ⟨303834594310900165563035777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202556396207266777042023851 303834594310900165563035777)
    ·
      refine ⟨227875945733175124172276833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303834594310900165563035777 227875945733175124172276833)
      ·
        refine ⟨170906959299881343129207625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227875945733175124172276833 170906959299881343129207625)
        ·
          refine ⟨128180219474911007346905719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170906959299881343129207625 128180219474911007346905719)
          ·
            refine ⟨192270329212366511020358579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128180219474911007346905719 192270329212366511020358579)
            ·
              refine ⟨288405493818549766530537869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192270329212366511020358579 288405493818549766530537869)
              ·
                refine ⟨108152060181956162448951701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288405493818549766530537869 108152060181956162448951701)
                ·
                  refine ⟨5069627821029195114794611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108152060181956162448951701 5069627821029195114794611)
                  ·
                    refine ⟨7604441731543792672191917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5069627821029195114794611 7604441731543792672191917)
                    ·
                      refine ⟨2851665649328922252071969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7604441731543792672191917 2851665649328922252071969)
                      ·
                        rfl

theorem cell23_5553599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_5553599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553599 prefixEnd_5553599 := by exact prefixLift 5553599
  have htrace : WordTrace (prefixWord ++ tailWord_5553599) baseStart_5553599 baseEnd_5553599 := by
    simpa [prefixWord, tailWord_5553599, baseEnd_5553599] using wordTrace_append hprefix tailTrace_5553599
  have hstable : (prefixWord ++ tailWord_5553599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553599).length < 2 ^ (prefixWord ++ tailWord_5553599).sum := by decide
  have hdescent : baseEnd_5553599 < baseStart_5553599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553626 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2]
def baseStart_5553626 : Nat := 118140960795 + 5553626 * 2 ^ 59
def prefixEnd_5553626 : Nat := 4983230072969 + 3 ^ 40 * 5553626 * 2
def baseEnd_5553626 : Nat := 2851679513306593646434345

theorem tailTrace_5553626 : CollatzResearch.WordTrace tailWord_5553626 prefixEnd_5553626 2851679513306593646434345 := by
  unfold tailWord_5553626
  simp only [CollatzResearch.WordTrace]
  refine ⟨50639345244542240163314183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135038253985445973768837821 50639345244542240163314183)
  ·
    refine ⟨75959017866813360244971275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50639345244542240163314183 75959017866813360244971275)
    ·
      refine ⟨113938526800220040367456913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75959017866813360244971275 113938526800220040367456913)
      ·
        refine ⟨85453895100165030275592685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113938526800220040367456913 85453895100165030275592685)
        ·
          refine ⟨32045210662561886353347257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85453895100165030275592685 32045210662561886353347257)
          ·
            refine ⟨24033907996921414765010443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32045210662561886353347257 24033907996921414765010443)
            ·
              refine ⟨36050861995382122147515665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24033907996921414765010443 36050861995382122147515665)
              ·
                refine ⟨27038146496536591610636749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36050861995382122147515665 27038146496536591610636749)
                ·
                  refine ⟨10139304936201221853988781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27038146496536591610636749 10139304936201221853988781)
                  ·
                    refine ⟨3802239351075458195245793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10139304936201221853988781 3802239351075458195245793)
                    ·
                      refine ⟨2851679513306593646434345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3802239351075458195245793 2851679513306593646434345)
                      ·
                        rfl

theorem cell23_5553626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_5553626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553626 prefixEnd_5553626 := by exact prefixLift 5553626
  have htrace : WordTrace (prefixWord ++ tailWord_5553626) baseStart_5553626 baseEnd_5553626 := by
    simpa [prefixWord, tailWord_5553626, baseEnd_5553626] using wordTrace_append hprefix tailTrace_5553626
  have hstable : (prefixWord ++ tailWord_5553626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553626).length < 2 ^ (prefixWord ++ tailWord_5553626).sum := by decide
  have hdescent : baseEnd_5553626 < baseStart_5553626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553656 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 1, 4, 2]
def baseStart_5553656 : Nat := 118140960795 + 5553656 * 2 ^ 59
def prefixEnd_5553656 : Nat := 4983230072969 + 3 ^ 40 * 5553656 * 2
def baseEnd_5553656 : Nat := 2851694917726228529059207

theorem tailTrace_5553656 : CollatzResearch.WordTrace tailWord_5553656 prefixEnd_5553656 2851694917726228529059207 := by
  unfold tailWord_5553656
  simp only [CollatzResearch.WordTrace]
  refine ⟨101279237584030137888424411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135038983445373517184565881 101279237584030137888424411)
  ·
    refine ⟨151918856376045206832636617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101279237584030137888424411 151918856376045206832636617)
    ·
      refine ⟨113939142282033905124477463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151918856376045206832636617 113939142282033905124477463)
      ·
        refine ⟨170908713423050857686716195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113939142282033905124477463 170908713423050857686716195)
        ·
          refine ⟨256363070134576286530074293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170908713423050857686716195 256363070134576286530074293)
          ·
            refine ⟨24034037825116526862194465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 256363070134576286530074293 24034037825116526862194465)
            ·
              refine ⟨18025528368837395146645849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24034037825116526862194465 18025528368837395146645849)
              ·
                refine ⟨13519146276628046359984387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18025528368837395146645849 13519146276628046359984387)
                ·
                  refine ⟨20278719414942069539976581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13519146276628046359984387 20278719414942069539976581)
                  ·
                    refine ⟨3802259890301638038745609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20278719414942069539976581 3802259890301638038745609)
                    ·
                      refine ⟨2851694917726228529059207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3802259890301638038745609 2851694917726228529059207)
                      ·
                        rfl

theorem cell23_5553656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 1, 4, 2].length) (baseStart_5553656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553656 prefixEnd_5553656 := by exact prefixLift 5553656
  have htrace : WordTrace (prefixWord ++ tailWord_5553656) baseStart_5553656 baseEnd_5553656 := by
    simpa [prefixWord, tailWord_5553656, baseEnd_5553656] using wordTrace_append hprefix tailTrace_5553656
  have hstable : (prefixWord ++ tailWord_5553656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553656).length < 2 ^ (prefixWord ++ tailWord_5553656).sum := by decide
  have hdescent : baseEnd_5553656 < baseStart_5553656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553666 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_5553666 : Nat := 118140960795 + 5553666 * 2 ^ 59
def prefixEnd_5553666 : Nat := 4983230072969 + 3 ^ 40 * 5553666 * 2
def baseEnd_5553666 : Nat := 950566684177591163311387

theorem tailTrace_5553666 : CollatzResearch.WordTrace tailWord_5553666 prefixEnd_5553666 950566684177591163311387 := by
  unfold tailWord_5553666
  simp only [CollatzResearch.WordTrace]
  refine ⟨50639709974506011871178213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135039226598682698323141901 50639709974506011871178213)
  ·
    refine ⟨9494945620219877225845915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50639709974506011871178213 9494945620219877225845915)
    ·
      refine ⟨14242418430329815838768873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9494945620219877225845915 14242418430329815838768873)
      ·
        refine ⟨10681813822747361879076655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14242418430329815838768873 10681813822747361879076655)
        ·
          refine ⟨16022720734121042818614983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10681813822747361879076655 16022720734121042818614983)
          ·
            refine ⟨24034081101181564227922475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16022720734121042818614983 24034081101181564227922475)
            ·
              refine ⟨36051121651772346341883713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24034081101181564227922475 36051121651772346341883713)
              ·
                refine ⟨27038341238829259756412785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36051121651772346341883713 27038341238829259756412785)
                ·
                  refine ⟨20278755929121944817309589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27038341238829259756412785 20278755929121944817309589)
                  ·
                    refine ⟨950566684177591163311387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20278755929121944817309589 950566684177591163311387)
                    ·
                      rfl

theorem cell23_5553666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_5553666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553666 prefixEnd_5553666 := by exact prefixLift 5553666
  have htrace : WordTrace (prefixWord ++ tailWord_5553666) baseStart_5553666 baseEnd_5553666 := by
    simpa [prefixWord, tailWord_5553666, baseEnd_5553666] using wordTrace_append hprefix tailTrace_5553666
  have hstable : (prefixWord ++ tailWord_5553666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553666).length < 2 ^ (prefixWord ++ tailWord_5553666).sum := by decide
  have hdescent : baseEnd_5553666 < baseStart_5553666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553741 : List Nat := [1, 6, 1, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_5553741 : Nat := 118140960795 + 5553741 * 2 ^ 59
def prefixEnd_5553741 : Nat := 4983230072969 + 3 ^ 40 * 5553741 * 2
def baseEnd_5553741 : Nat := 2851738563581860696496317

theorem tailTrace_5553741 : CollatzResearch.WordTrace tailWord_5553741 prefixEnd_5553741 2851738563581860696496317 := by
  unfold tailWord_5553741
  simp only [CollatzResearch.WordTrace]
  refine ⟨202561575372752335293693077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135041050248501556862462051 202561575372752335293693077)
  ·
    refine ⟨9495073845597765716891863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 202561575372752335293693077 9495073845597765716891863)
    ·
      refine ⟨14242610768396648575337795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9495073845597765716891863 14242610768396648575337795)
      ·
        refine ⟨21363916152594972863006693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14242610768396648575337795 21363916152594972863006693)
        ·
          refine ⟨4005734278611557411813755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21363916152594972863006693 4005734278611557411813755)
          ·
            refine ⟨6008601417917336117720633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4005734278611557411813755 6008601417917336117720633)
            ·
              refine ⟨4506451063438002088290475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6008601417917336117720633 4506451063438002088290475)
              ·
                refine ⟨6759676595157003132435713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4506451063438002088290475 6759676595157003132435713)
                ·
                  refine ⟨5069757446367752349326785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6759676595157003132435713 5069757446367752349326785)
                  ·
                    refine ⟨3802318084775814261995089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5069757446367752349326785 3802318084775814261995089)
                    ·
                      refine ⟨2851738563581860696496317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3802318084775814261995089 2851738563581860696496317)
                      ·
                        rfl

theorem cell23_5553741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_5553741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553741 prefixEnd_5553741 := by exact prefixLift 5553741
  have htrace : WordTrace (prefixWord ++ tailWord_5553741) baseStart_5553741 baseEnd_5553741 := by
    simpa [prefixWord, tailWord_5553741, baseEnd_5553741] using wordTrace_append hprefix tailTrace_5553741
  have hstable : (prefixWord ++ tailWord_5553741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553741).length < 2 ^ (prefixWord ++ tailWord_5553741).sum := by decide
  have hdescent : baseEnd_5553741 < baseStart_5553741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553779 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 3]
def baseStart_5553779 : Nat := 118140960795 + 5553779 * 2 ^ 59
def prefixEnd_5553779 : Nat := 4983230072969 + 3 ^ 40 * 5553779 * 2
def baseEnd_5553779 : Nat := 2851758075846731547821141

theorem tailTrace_5553779 : CollatzResearch.WordTrace tailWord_5553779 prefixEnd_5553779 2851758075846731547821141 := by
  unfold tailWord_5553779
  simp only [CollatzResearch.WordTrace]
  refine ⟨202562961346614667783576391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135041974231076445189050927 202562961346614667783576391)
  ·
    refine ⟨303844442019922001675364587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202562961346614667783576391 303844442019922001675364587)
    ·
      refine ⟨455766663029883002513046881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303844442019922001675364587 455766663029883002513046881)
      ·
        refine ⟨341824997272412251884785161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 455766663029883002513046881 341824997272412251884785161)
        ·
          refine ⟨256368747954309188913588871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341824997272412251884785161 256368747954309188913588871)
          ·
            refine ⟨384553121931463783370383307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256368747954309188913588871 384553121931463783370383307)
            ·
              refine ⟨576829682897195675055574961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384553121931463783370383307 576829682897195675055574961)
              ·
                refine ⟨432622262172896756291681221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576829682897195675055574961 432622262172896756291681221)
                ·
                  refine ⟨81116674157418141804690229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432622262172896756291681221 81116674157418141804690229)
                  ·
                    refine ⟨7604688202257950794189709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81116674157418141804690229 7604688202257950794189709)
                    ·
                      refine ⟨2851758075846731547821141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7604688202257950794189709 2851758075846731547821141)
                      ·
                        rfl

theorem cell23_5553779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 3].length) (baseStart_5553779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553779 prefixEnd_5553779 := by exact prefixLift 5553779
  have htrace : WordTrace (prefixWord ++ tailWord_5553779) baseStart_5553779 baseEnd_5553779 := by
    simpa [prefixWord, tailWord_5553779, baseEnd_5553779] using wordTrace_append hprefix tailTrace_5553779
  have hstable : (prefixWord ++ tailWord_5553779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553779).length < 2 ^ (prefixWord ++ tailWord_5553779).sum := by decide
  have hdescent : baseEnd_5553779 < baseStart_5553779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553816 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 3, 5]
def baseStart_5553816 : Nat := 118140960795 + 5553816 * 2 ^ 59
def prefixEnd_5553816 : Nat := 4983230072969 + 3 ^ 40 * 5553816 * 2
def baseEnd_5553816 : Nat := 950592358210315967686157

theorem tailTrace_5553816 : CollatzResearch.WordTrace tailWord_5553816 prefixEnd_5553816 950592358210315967686157 := by
  unfold tailWord_5553816
  simp only [CollatzResearch.WordTrace]
  refine ⟨101282155423740311551336651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135042873898320415401782201 101282155423740311551336651)
  ·
    refine ⟨151923233135610467327004977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101282155423740311551336651 151923233135610467327004977)
    ·
      refine ⟨113942424851707850495253733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151923233135610467327004977 113942424851707850495253733)
      ·
        refine ⟨21364204659695221967860075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113942424851707850495253733 21364204659695221967860075)
        ·
          refine ⟨32046306989542832951790113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21364204659695221967860075 32046306989542832951790113)
          ·
            refine ⟨24034730242157124713842585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32046306989542832951790113 24034730242157124713842585)
            ·
              refine ⟨18026047681617843535381939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24034730242157124713842585 18026047681617843535381939)
              ·
                refine ⟨27039071522426765303072909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18026047681617843535381939 27039071522426765303072909)
                ·
                  refine ⟨10139651820910036988652341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27039071522426765303072909 10139651820910036988652341)
                  ·
                    refine ⟨950592358210315967686157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10139651820910036988652341 950592358210315967686157)
                    ·
                      rfl

theorem cell23_5553816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_5553816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553816 prefixEnd_5553816 := by exact prefixLift 5553816
  have htrace : WordTrace (prefixWord ++ tailWord_5553816) baseStart_5553816 baseEnd_5553816 := by
    simpa [prefixWord, tailWord_5553816, baseEnd_5553816] using wordTrace_append hprefix tailTrace_5553816
  have hstable : (prefixWord ++ tailWord_5553816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553816).length < 2 ^ (prefixWord ++ tailWord_5553816).sum := by decide
  have hdescent : baseEnd_5553816 < baseStart_5553816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553836 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 3, 8, 2]
def baseStart_5553836 : Nat := 118140960795 + 5553836 * 2 ^ 59
def prefixEnd_5553836 : Nat := 4983230072969 + 3 ^ 40 * 5553836 * 2
def baseEnd_5553836 : Nat := 2851787344244037824808379

theorem tailTrace_5553836 : CollatzResearch.WordTrace tailWord_5553836 prefixEnd_5553836 2851787344244037824808379 := by
  unfold tailWord_5553836
  simp only [CollatzResearch.WordTrace]
  refine ⟨101282520153704083259200681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135043360204938777678934241 101282520153704083259200681)
  ·
    refine ⟨75961890115278062444400511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101282520153704083259200681 75961890115278062444400511)
    ·
      refine ⟨113942835172917093666600767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75961890115278062444400511 113942835172917093666600767)
      ·
        refine ⟨170914252759375640499901151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113942835172917093666600767 170914252759375640499901151)
        ·
          refine ⟨256371379139063460749851727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170914252759375640499901151 256371379139063460749851727)
          ·
            refine ⟨384557068708595191124777591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256371379139063460749851727 384557068708595191124777591)
            ·
              refine ⟨576835603062892786687166387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384557068708595191124777591 576835603062892786687166387)
              ·
                refine ⟨865253404594339180030749581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576835603062892786687166387 865253404594339180030749581)
                ·
                  refine ⟨324470026722877192511531093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865253404594339180030749581 324470026722877192511531093)
                  ·
                    refine ⟨3802383125658717099744505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 324470026722877192511531093 3802383125658717099744505)
                    ·
                      refine ⟨2851787344244037824808379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3802383125658717099744505 2851787344244037824808379)
                      ·
                        rfl

theorem cell23_5553836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 8, 2].length) (baseStart_5553836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553836 prefixEnd_5553836 := by exact prefixLift 5553836
  have htrace : WordTrace (prefixWord ++ tailWord_5553836) baseStart_5553836 baseEnd_5553836 := by
    simpa [prefixWord, tailWord_5553836, baseEnd_5553836] using wordTrace_append hprefix tailTrace_5553836
  have hstable : (prefixWord ++ tailWord_5553836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553836).length < 2 ^ (prefixWord ++ tailWord_5553836).sum := by decide
  have hdescent : baseEnd_5553836 < baseStart_5553836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553856 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 5]
def baseStart_5553856 : Nat := 118140960795 + 5553856 * 2 ^ 59
def prefixEnd_5553856 : Nat := 4983230072969 + 3 ^ 40 * 5553856 * 2
def baseEnd_5553856 : Nat := 2851797613857127746558287

theorem tailTrace_5553856 : CollatzResearch.WordTrace tailWord_5553856 prefixEnd_5553856 2851797613857127746558287 := by
  unfold tailWord_5553856
  simp only [CollatzResearch.WordTrace]
  refine ⟨101282884883667854967064711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135043846511557139956086281 101282884883667854967064711)
  ·
    refine ⟨151924327325501782450597067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101282884883667854967064711 151924327325501782450597067)
    ·
      refine ⟨227886490988252673675895601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151924327325501782450597067 227886490988252673675895601)
      ·
        refine ⟨170914868241189505256921701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227886490988252673675895601 170914868241189505256921701)
        ·
          refine ⟨32046537795223032235672819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170914868241189505256921701 32046537795223032235672819)
          ·
            refine ⟨48069806692834548353509229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32046537795223032235672819 48069806692834548353509229)
            ·
              refine ⟨18026177509812955632565961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48069806692834548353509229 18026177509812955632565961)
              ·
                refine ⟨13519633132359716724424471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18026177509812955632565961 13519633132359716724424471)
                ·
                  refine ⟨20279449698539575086636707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13519633132359716724424471 20279449698539575086636707)
                  ·
                    refine ⟨30419174547809362629955061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20279449698539575086636707 30419174547809362629955061)
                    ·
                      refine ⟨2851797613857127746558287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30419174547809362629955061 2851797613857127746558287)
                      ·
                        rfl

theorem cell23_5553856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_5553856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553856 prefixEnd_5553856 := by exact prefixLift 5553856
  have htrace : WordTrace (prefixWord ++ tailWord_5553856) baseStart_5553856 baseEnd_5553856 := by
    simpa [prefixWord, tailWord_5553856, baseEnd_5553856] using wordTrace_append hprefix tailTrace_5553856
  have hstable : (prefixWord ++ tailWord_5553856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553856).length < 2 ^ (prefixWord ++ tailWord_5553856).sum := by decide
  have hdescent : baseEnd_5553856 < baseStart_5553856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553870 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2]
def baseStart_5553870 : Nat := 118140960795 + 5553870 * 2 ^ 59
def prefixEnd_5553870 : Nat := 4983230072969 + 3 ^ 40 * 5553870 * 2
def baseEnd_5553870 : Nat := 2851804802586290691783223

theorem tailTrace_5553870 : CollatzResearch.WordTrace tailWord_5553870 prefixEnd_5553870 2851804802586290691783223 := by
  unfold tailWord_5553870
  simp only [CollatzResearch.WordTrace]
  refine ⟨25320785048660623790642383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135044186926189993550092709 25320785048660623790642383)
  ·
    refine ⟨37981177572990935685963575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25320785048660623790642383 37981177572990935685963575)
    ·
      refine ⟨56971766359486403528945363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37981177572990935685963575 56971766359486403528945363)
      ·
        refine ⟨85457649539229605293418045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56971766359486403528945363 85457649539229605293418045)
        ·
          refine ⟨32046618577211101985031767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85457649539229605293418045 32046618577211101985031767)
          ·
            refine ⟨48069927865816652977547651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32046618577211101985031767 48069927865816652977547651)
            ·
              refine ⟨72104891798724979466321477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48069927865816652977547651 72104891798724979466321477)
              ·
                refine ⟨13519667212260933649935277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72104891798724979466321477 13519667212260933649935277)
                ·
                  refine ⟨5069875204597850118725729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13519667212260933649935277 5069875204597850118725729)
                  ·
                    refine ⟨3802406403448387589044297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5069875204597850118725729 3802406403448387589044297)
                    ·
                      refine ⟨2851804802586290691783223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3802406403448387589044297 2851804802586290691783223)
                      ·
                        rfl

theorem cell23_5553870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_5553870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553870 prefixEnd_5553870 := by exact prefixLift 5553870
  have htrace : WordTrace (prefixWord ++ tailWord_5553870) baseStart_5553870 baseEnd_5553870 := by
    simpa [prefixWord, tailWord_5553870, baseEnd_5553870] using wordTrace_append hprefix tailTrace_5553870
  have hstable : (prefixWord ++ tailWord_5553870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553870).length < 2 ^ (prefixWord ++ tailWord_5553870).sum := by decide
  have hdescent : baseEnd_5553870 < baseStart_5553870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553873 : List Nat := [1, 2, 2, 1, 2, 4, 1, 4, 1, 2, 3]
def baseStart_5553873 : Nat := 118140960795 + 5553873 * 2 ^ 59
def prefixEnd_5553873 : Nat := 4983230072969 + 3 ^ 40 * 5553873 * 2
def baseEnd_5553873 : Nat := 2851806343028254180045709

theorem tailTrace_5553873 : CollatzResearch.WordTrace tailWord_5553873 prefixEnd_5553873 2851806343028254180045709 := by
  unfold tailWord_5553873
  simp only [CollatzResearch.WordTrace]
  refine ⟨202566389808274121837498273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135044259872182747891665515 202566389808274121837498273)
  ·
    refine ⟨151924792356205591378123705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202566389808274121837498273 151924792356205591378123705)
    ·
      refine ⟨113943594267154193533592779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151924792356205591378123705 113943594267154193533592779)
      ·
        refine ⟨170915391400731290300389169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113943594267154193533592779 170915391400731290300389169)
        ·
          refine ⟨128186543550548467725291877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170915391400731290300389169 128186543550548467725291877)
          ·
            refine ⟨24034976915727837698492227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128186543550548467725291877 24034976915727837698492227)
            ·
              refine ⟨36052465373591756547738341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24034976915727837698492227 36052465373591756547738341)
              ·
                refine ⟨6759837257548454352700939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36052465373591756547738341 6759837257548454352700939)
                ·
                  refine ⟨10139755886322681529051409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6759837257548454352700939 10139755886322681529051409)
                  ·
                    refine ⟨7604816914742011146788557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10139755886322681529051409 7604816914742011146788557)
                    ·
                      refine ⟨2851806343028254180045709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7604816914742011146788557 2851806343028254180045709)
                      ·
                        rfl

theorem cell23_5553873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_5553873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553873 prefixEnd_5553873 := by exact prefixLift 5553873
  have htrace : WordTrace (prefixWord ++ tailWord_5553873) baseStart_5553873 baseEnd_5553873 := by
    simpa [prefixWord, tailWord_5553873, baseEnd_5553873] using wordTrace_append hprefix tailTrace_5553873
  have hstable : (prefixWord ++ tailWord_5553873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553873).length < 2 ^ (prefixWord ++ tailWord_5553873).sum := by decide
  have hdescent : baseEnd_5553873 < baseStart_5553873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553903 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 4, 1, 3]
def baseStart_5553903 : Nat := 118140960795 + 5553903 * 2 ^ 59
def prefixEnd_5553903 : Nat := 4983230072969 + 3 ^ 40 * 5553903 * 2
def baseEnd_5553903 : Nat := 2851821747447889062670571

theorem tailTrace_5553903 : CollatzResearch.WordTrace tailWord_5553903 prefixEnd_5553903 2851821747447889062670571 := by
  unfold tailWord_5553903
  simp only [CollatzResearch.WordTrace]
  refine ⟨202567483998165436961090363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135044989332110291307393575 202567483998165436961090363)
  ·
    refine ⟨303851225997248155441635545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202567483998165436961090363 303851225997248155441635545)
    ·
      refine ⟨227888419497936116581226659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303851225997248155441635545 227888419497936116581226659)
      ·
        refine ⟨341832629246904174871839989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227888419497936116581226659 341832629246904174871839989)
        ·
          refine ⟨32046808991897266394234999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 341832629246904174871839989 32046808991897266394234999)
          ·
            refine ⟨48070213487845899591352499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32046808991897266394234999 48070213487845899591352499)
            ·
              refine ⟨72105320231768849387028749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48070213487845899591352499 72105320231768849387028749)
              ·
                refine ⟨27039495086913318520135781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72105320231768849387028749 27039495086913318520135781)
                ·
                  refine ⟨5069905328796247222525459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27039495086913318520135781 5069905328796247222525459)
                  ·
                    refine ⟨7604857993194370833788189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5069905328796247222525459 7604857993194370833788189)
                    ·
                      refine ⟨2851821747447889062670571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7604857993194370833788189 2851821747447889062670571)
                      ·
                        rfl

theorem cell23_5553903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 1, 3].length) (baseStart_5553903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553903 prefixEnd_5553903 := by exact prefixLift 5553903
  have htrace : WordTrace (prefixWord ++ tailWord_5553903) baseStart_5553903 baseEnd_5553903 := by
    simpa [prefixWord, tailWord_5553903, baseEnd_5553903] using wordTrace_append hprefix tailTrace_5553903
  have hstable : (prefixWord ++ tailWord_5553903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553903).length < 2 ^ (prefixWord ++ tailWord_5553903).sum := by decide
  have hdescent : baseEnd_5553903 < baseStart_5553903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553906 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_5553906 : Nat := 118140960795 + 5553906 * 2 ^ 59
def prefixEnd_5553906 : Nat := 4983230072969 + 3 ^ 40 * 5553906 * 2
def baseEnd_5553906 : Nat := 950607762629950850311019

theorem tailTrace_5553906 : CollatzResearch.WordTrace tailWord_5553906 prefixEnd_5553906 950607762629950850311019 := by
  unfold tailWord_5553906
  simp only [CollatzResearch.WordTrace]
  refine ⟨50641898354288642118362393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135045062278103045648966381 50641898354288642118362393)
  ·
    refine ⟨37981423765716481588771795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50641898354288642118362393 37981423765716481588771795)
    ·
      refine ⟨56972135648574722383157693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37981423765716481588771795 56972135648574722383157693)
      ·
        refine ⟨21364550868215520893684135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56972135648574722383157693 21364550868215520893684135)
        ·
          refine ⟨32046826302323281340526203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21364550868215520893684135 32046826302323281340526203)
          ·
            refine ⟨48070239453484922010789305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32046826302323281340526203 48070239453484922010789305)
            ·
              refine ⟨36052679590113691508091979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48070239453484922010789305 36052679590113691508091979)
              ·
                refine ⟨54079019385170537262137969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36052679590113691508091979 54079019385170537262137969)
                ·
                  refine ⟨40559264538877902946603477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54079019385170537262137969 40559264538877902946603477)
                  ·
                    refine ⟨950607762629950850311019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40559264538877902946603477 950607762629950850311019)
                    ·
                      rfl

theorem cell23_5553906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_5553906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553906 prefixEnd_5553906 := by exact prefixLift 5553906
  have htrace : WordTrace (prefixWord ++ tailWord_5553906) baseStart_5553906 baseEnd_5553906 := by
    simpa [prefixWord, tailWord_5553906, baseEnd_5553906] using wordTrace_append hprefix tailTrace_5553906
  have hstable : (prefixWord ++ tailWord_5553906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553906).length < 2 ^ (prefixWord ++ tailWord_5553906).sum := by decide
  have hdescent : baseEnd_5553906 < baseStart_5553906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553930 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 3, 3, 2]
def baseStart_5553930 : Nat := 118140960795 + 5553930 * 2 ^ 59
def prefixEnd_5553930 : Nat := 4983230072969 + 3 ^ 40 * 5553930 * 2
def baseEnd_5553930 : Nat := 2851835611425560457032947

theorem tailTrace_5553930 : CollatzResearch.WordTrace tailWord_5553930 prefixEnd_5553930 2851835611425560457032947 := by
  unfold tailWord_5553930
  simp only [CollatzResearch.WordTrace]
  refine ⟨50642117192266905143080811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135045645846045080381548829 50642117192266905143080811)
  ·
    refine ⟨75963175788400357714621217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50642117192266905143080811 75963175788400357714621217)
    ·
      refine ⟨56972381841300268285965913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75963175788400357714621217 56972381841300268285965913)
      ·
        refine ⟨42729286380975201214474435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56972381841300268285965913 42729286380975201214474435)
        ·
          refine ⟨64093929571462801821711653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42729286380975201214474435 64093929571462801821711653)
          ·
            refine ⟨12017611794649275341570935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64093929571462801821711653 12017611794649275341570935)
            ·
              refine ⟨18026417691973913012356403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12017611794649275341570935 18026417691973913012356403)
              ·
                refine ⟨27039626537960869518534605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18026417691973913012356403 27039626537960869518534605)
                ·
                  refine ⟨10139859951735326069450477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27039626537960869518534605 10139859951735326069450477)
                  ·
                    refine ⟨3802447481900747276043929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10139859951735326069450477 3802447481900747276043929)
                    ·
                      refine ⟨2851835611425560457032947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3802447481900747276043929 2851835611425560457032947)
                      ·
                        rfl

theorem cell23_5553930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_5553930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553930 prefixEnd_5553930 := by exact prefixLift 5553930
  have htrace : WordTrace (prefixWord ++ tailWord_5553930) baseStart_5553930 baseEnd_5553930 := by
    simpa [prefixWord, tailWord_5553930, baseEnd_5553930] using wordTrace_append hprefix tailTrace_5553930
  have hstable : (prefixWord ++ tailWord_5553930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553930).length < 2 ^ (prefixWord ++ tailWord_5553930).sum := by decide
  have hdescent : baseEnd_5553930 < baseStart_5553930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5553983 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 7]
def baseStart_5553983 : Nat := 118140960795 + 5553983 * 2 ^ 59
def prefixEnd_5553983 : Nat := 4983230072969 + 3 ^ 40 * 5553983 * 2
def baseEnd_5553983 : Nat := 316873647322249861074467

theorem tailTrace_5553983 : CollatzResearch.WordTrace tailWord_5553983 prefixEnd_5553983 316873647322249861074467 := by
  unfold tailWord_5553983
  simp only [CollatzResearch.WordTrace]
  refine ⟨202570401837875610624002603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135046934558583740416001735 202570401837875610624002603)
  ·
    refine ⟨303855602756813415936003905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202570401837875610624002603 303855602756813415936003905)
    ·
      refine ⟨227891702067610061952002929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303855602756813415936003905 227891702067610061952002929)
      ·
        refine ⟨170918776550707546464002197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227891702067610061952002929 170918776550707546464002197)
        ·
          refine ⟨8011817650814416240500103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 170918776550707546464002197 8011817650814416240500103)
          ·
            refine ⟨12017726476221624360750155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8011817650814416240500103 12017726476221624360750155)
            ·
              refine ⟨18026589714332436541125233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12017726476221624360750155 18026589714332436541125233)
              ·
                refine ⟨13519942285749327405843925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18026589714332436541125233 13519942285749327405843925)
                ·
                  refine ⟨316873647322249861074467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13519942285749327405843925 316873647322249861074467)
                  ·
                    rfl

theorem cell23_5553983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 7].length) (baseStart_5553983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5553983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5553983 prefixEnd_5553983 := by exact prefixLift 5553983
  have htrace : WordTrace (prefixWord ++ tailWord_5553983) baseStart_5553983 baseEnd_5553983 := by
    simpa [prefixWord, tailWord_5553983, baseEnd_5553983] using wordTrace_append hprefix tailTrace_5553983
  have hstable : (prefixWord ++ tailWord_5553983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5553983).length < 2 ^ (prefixWord ++ tailWord_5553983).sum := by decide
  have hdescent : baseEnd_5553983 < baseStart_5553983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5553983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554053 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 1, 4, 3]
def baseStart_5554053 : Nat := 118140960795 + 5554053 * 2 ^ 59
def prefixEnd_5554053 : Nat := 4983230072969 + 3 ^ 40 * 5554053 * 2
def baseEnd_5554053 : Nat := 2851898769546063475794881

theorem tailTrace_5554053 : CollatzResearch.WordTrace tailWord_5554053 prefixEnd_5554053 2851898769546063475794881 := by
  unfold tailWord_5554053
  simp only [CollatzResearch.WordTrace]
  refine ⟨202572954947622012579050813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135048636631748008386033875 202572954947622012579050813)
  ·
    refine ⟨75964858105358254717144055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202572954947622012579050813 75964858105358254717144055)
    ·
      refine ⟨113947287158037382075716083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75964858105358254717144055 113947287158037382075716083)
      ·
        refine ⟨170920930737056073113574125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113947287158037382075716083 170920930737056073113574125)
        ·
          refine ⟨64095349026396027417590297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170920930737056073113574125 64095349026396027417590297)
          ·
            refine ⟨48071511769797020563192723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64095349026396027417590297 48071511769797020563192723)
            ·
              refine ⟨72107267654695530844789085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48071511769797020563192723 72107267654695530844789085)
              ·
                refine ⟨27040225370510824066795907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72107267654695530844789085 27040225370510824066795907)
                ·
                  refine ⟨40560338055766236100193861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27040225370510824066795907 40560338055766236100193861)
                  ·
                    refine ⟨7605063385456169268786349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40560338055766236100193861 7605063385456169268786349)
                    ·
                      refine ⟨2851898769546063475794881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7605063385456169268786349 2851898769546063475794881)
                      ·
                        rfl

theorem cell23_5554053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_5554053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554053 prefixEnd_5554053 := by exact prefixLift 5554053
  have htrace : WordTrace (prefixWord ++ tailWord_5554053) baseStart_5554053 baseEnd_5554053 := by
    simpa [prefixWord, tailWord_5554053, baseEnd_5554053] using wordTrace_append hprefix tailTrace_5554053
  have hstable : (prefixWord ++ tailWord_5554053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554053).length < 2 ^ (prefixWord ++ tailWord_5554053).sum := by decide
  have hdescent : baseEnd_5554053 < baseStart_5554053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554077 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_5554077 : Nat := 118140960795 + 5554077 * 2 ^ 59
def prefixEnd_5554077 : Nat := 4983230072969 + 3 ^ 40 * 5554077 * 2
def baseEnd_5554077 : Nat := 950637031027257127298257

theorem tailTrace_5554077 : CollatzResearch.WordTrace tailWord_5554077 prefixEnd_5554077 950637031027257127298257 := by
  unfold tailWord_5554077
  simp only [CollatzResearch.WordTrace]
  refine ⟨202573830299535064677924485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135049220199690043118616323 202573830299535064677924485)
  ·
    refine ⟨37982593181162824627110841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202573830299535064677924485 37982593181162824627110841)
    ·
      refine ⟨28486944885872118470333131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37982593181162824627110841 28486944885872118470333131)
      ·
        refine ⟨42730417328808177705499697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28486944885872118470333131 42730417328808177705499697)
        ·
          refine ⟨32047812996606133279124773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42730417328808177705499697 32047812996606133279124773)
          ·
            refine ⟨6008964936863649989835895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32047812996606133279124773 6008964936863649989835895)
            ·
              refine ⟨9013447405295474984753843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6008964936863649989835895 9013447405295474984753843)
              ·
                refine ⟨13520171107943212477130765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9013447405295474984753843 13520171107943212477130765)
                ·
                  refine ⟨5070064165478704678924037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13520171107943212477130765 5070064165478704678924037)
                  ·
                    refine ⟨950637031027257127298257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5070064165478704678924037 950637031027257127298257)
                    ·
                      rfl

theorem cell23_5554077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_5554077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554077 prefixEnd_5554077 := by exact prefixLift 5554077
  have htrace : WordTrace (prefixWord ++ tailWord_5554077) baseStart_5554077 baseEnd_5554077 := by
    simpa [prefixWord, tailWord_5554077, baseEnd_5554077] using wordTrace_append hprefix tailTrace_5554077
  have hstable : (prefixWord ++ tailWord_5554077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554077).length < 2 ^ (prefixWord ++ tailWord_5554077).sum := by decide
  have hdescent : baseEnd_5554077 < baseStart_5554077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554160 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 3]
def baseStart_5554160 : Nat := 118140960795 + 5554160 * 2 ^ 59
def prefixEnd_5554160 : Nat := 4983230072969 + 3 ^ 40 * 5554160 * 2
def baseEnd_5554160 : Nat := 2851953711976094557156889

theorem tailTrace_5554160 : CollatzResearch.WordTrace tailWord_5554160 prefixEnd_5554160 2851953711976094557156889 := by
  unfold tailWord_5554160
  simp only [CollatzResearch.WordTrace]
  refine ⟨101288428779117184926597967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135051238372156246568797289 101288428779117184926597967)
  ·
    refine ⟨151932643168675777389896951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101288428779117184926597967 151932643168675777389896951)
    ·
      refine ⟨227898964753013666084845427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151932643168675777389896951 227898964753013666084845427)
      ·
        refine ⟨341848447129520499127268141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227898964753013666084845427 341848447129520499127268141)
        ·
          refine ⟨128193167673570187172725553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341848447129520499127268141 128193167673570187172725553)
          ·
            refine ⟨96144875755177640379544165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128193167673570187172725553 96144875755177640379544165)
            ·
              refine ⟨18027164204095807571164531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96144875755177640379544165 18027164204095807571164531)
              ·
                refine ⟨27040746306143711356746797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18027164204095807571164531 27040746306143711356746797)
                ·
                  refine ⟨10140279864803891758780049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27040746306143711356746797 10140279864803891758780049)
                  ·
                    refine ⟨7605209898602918819085037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10140279864803891758780049 7605209898602918819085037)
                    ·
                      refine ⟨2851953711976094557156889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7605209898602918819085037 2851953711976094557156889)
                      ·
                        rfl

theorem cell23_5554160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 3].length) (baseStart_5554160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554160 prefixEnd_5554160 := by exact prefixLift 5554160
  have htrace : WordTrace (prefixWord ++ tailWord_5554160) baseStart_5554160 baseEnd_5554160 := by
    simpa [prefixWord, tailWord_5554160, baseEnd_5554160] using wordTrace_append hprefix tailTrace_5554160
  have hstable : (prefixWord ++ tailWord_5554160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554160).length < 2 ^ (prefixWord ++ tailWord_5554160).sum := by decide
  have hdescent : baseEnd_5554160 < baseStart_5554160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554161 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 2, 3, 2]
def baseStart_5554161 : Nat := 118140960795 + 5554161 * 2 ^ 59
def prefixEnd_5554161 : Nat := 4983230072969 + 3 ^ 40 * 5554161 * 2
def baseEnd_5554161 : Nat := 2851954225456749053244385

theorem tailTrace_5554161 : CollatzResearch.WordTrace tailWord_5554161 prefixEnd_5554161 2851954225456749053244385 := by
  unfold tailWord_5554161
  simp only [CollatzResearch.WordTrace]
  refine ⟨202576894031230747023982337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135051262687487164682654891 202576894031230747023982337)
  ·
    refine ⟨151932670523423060267986753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202576894031230747023982337 151932670523423060267986753)
    ·
      refine ⟨113949502892567295200990065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151932670523423060267986753 113949502892567295200990065)
      ·
        refine ⟨85462127169425471400742549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113949502892567295200990065 85462127169425471400742549)
        ·
          refine ⟨4006037211066818971909807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85462127169425471400742549 4006037211066818971909807)
          ·
            refine ⟨6009055816600228457864711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006037211066818971909807 6009055816600228457864711)
            ·
              refine ⟨9013583724900342686797067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6009055816600228457864711 9013583724900342686797067)
              ·
                refine ⟨13520375587350514030195601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9013583724900342686797067 13520375587350514030195601)
                ·
                  refine ⟨10140281690512885522646701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13520375587350514030195601 10140281690512885522646701)
                  ·
                    refine ⟨3802605633942332070992513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10140281690512885522646701 3802605633942332070992513)
                    ·
                      refine ⟨2851954225456749053244385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3802605633942332070992513 2851954225456749053244385)
                      ·
                        rfl

theorem cell23_5554161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_5554161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554161 prefixEnd_5554161 := by exact prefixLift 5554161
  have htrace : WordTrace (prefixWord ++ tailWord_5554161) baseStart_5554161 baseEnd_5554161 := by
    simpa [prefixWord, tailWord_5554161, baseEnd_5554161] using wordTrace_append hprefix tailTrace_5554161
  have hstable : (prefixWord ++ tailWord_5554161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554161).length < 2 ^ (prefixWord ++ tailWord_5554161).sum := by decide
  have hdescent : baseEnd_5554161 < baseStart_5554161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554174 : List Nat := [4, 2, 2, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_5554174 : Nat := 118140960795 + 5554174 * 2 ^ 59
def prefixEnd_5554174 : Nat := 4983230072969 + 3 ^ 40 * 5554174 * 2
def baseEnd_5554174 : Nat := 2851960900705257502381825

theorem tailTrace_5554174 : CollatzResearch.WordTrace tailWord_5554174 prefixEnd_5554174 2851960900705257502381825 := by
  unfold tailWord_5554174
  simp only [CollatzResearch.WordTrace]
  refine ⟨25322171022522956280525697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135051578786789100162803717 25322171022522956280525697)
  ·
    refine ⟨18991628266892217210394273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25322171022522956280525697 18991628266892217210394273)
    ·
      refine ⟨14243721200169162907795705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18991628266892217210394273 14243721200169162907795705)
      ·
        refine ⟨10682790900126872180846779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14243721200169162907795705 10682790900126872180846779)
        ·
          refine ⟨16024186350190308271270169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10682790900126872180846779 16024186350190308271270169)
          ·
            refine ⟨12018139762642731203452627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16024186350190308271270169 12018139762642731203452627)
            ·
              refine ⟨18027209643964096805178941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12018139762642731203452627 18027209643964096805178941)
              ·
                refine ⟨6760203616486536301942103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18027209643964096805178941 6760203616486536301942103)
                ·
                  refine ⟨10140305424729804452913155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6760203616486536301942103 10140305424729804452913155)
                  ·
                    refine ⟨15210458137094706679369733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10140305424729804452913155 15210458137094706679369733)
                    ·
                      refine ⟨2851960900705257502381825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15210458137094706679369733 2851960900705257502381825)
                      ·
                        rfl

theorem cell23_5554174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_5554174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554174 prefixEnd_5554174 := by exact prefixLift 5554174
  have htrace : WordTrace (prefixWord ++ tailWord_5554174) baseStart_5554174 baseEnd_5554174 := by
    simpa [prefixWord, tailWord_5554174, baseEnd_5554174] using wordTrace_append hprefix tailTrace_5554174
  have hstable : (prefixWord ++ tailWord_5554174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554174).length < 2 ^ (prefixWord ++ tailWord_5554174).sum := by decide
  have hdescent : baseEnd_5554174 < baseStart_5554174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554177 : List Nat := [1, 2, 4, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_5554177 : Nat := 118140960795 + 5554177 * 2 ^ 59
def prefixEnd_5554177 : Nat := 4983230072969 + 3 ^ 40 * 5554177 * 2
def baseEnd_5554177 : Nat := 2851962441147220990644311

theorem tailTrace_5554177 : CollatzResearch.WordTrace tailWord_5554177 prefixEnd_5554177 2851962441147220990644311 := by
  unfold tailWord_5554177
  simp only [CollatzResearch.WordTrace]
  refine ⟨202577477599172781756564785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135051651732781854504376523 202577477599172781756564785)
  ·
    refine ⟨151933108199379586317423589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202577477599172781756564785 151933108199379586317423589)
    ·
      refine ⟨28487457787383672434516923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151933108199379586317423589 28487457787383672434516923)
      ·
        refine ⟨42731186681075508651775385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28487457787383672434516923 42731186681075508651775385)
        ·
          refine ⟨32048390010806631488831539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42731186681075508651775385 32048390010806631488831539)
          ·
            refine ⟨48072585016209947233247309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32048390010806631488831539 48072585016209947233247309)
            ·
              refine ⟨18027219381078730212467741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48072585016209947233247309 18027219381078730212467741)
              ·
                refine ⟨6760207267904523829675403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18027219381078730212467741 6760207267904523829675403)
                ·
                  refine ⟨10140310901856785744513105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6760207267904523829675403 10140310901856785744513105)
                  ·
                    refine ⟨7605233176392589308384829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10140310901856785744513105 7605233176392589308384829)
                    ·
                      refine ⟨2851962441147220990644311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7605233176392589308384829 2851962441147220990644311)
                      ·
                        rfl

theorem cell23_5554177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_5554177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554177 prefixEnd_5554177 := by exact prefixLift 5554177
  have htrace : WordTrace (prefixWord ++ tailWord_5554177) baseStart_5554177 baseEnd_5554177 := by
    simpa [prefixWord, tailWord_5554177, baseEnd_5554177] using wordTrace_append hprefix tailTrace_5554177
  have hstable : (prefixWord ++ tailWord_5554177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554177).length < 2 ^ (prefixWord ++ tailWord_5554177).sum := by decide
  have hdescent : baseEnd_5554177 < baseStart_5554177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554223 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 4, 6]
def baseStart_5554223 : Nat := 118140960795 + 5554223 * 2 ^ 59
def prefixEnd_5554223 : Nat := 4983230072969 + 3 ^ 40 * 5554223 * 2
def baseEnd_5554223 : Nat := 950662020419109270223033

theorem tailTrace_5554223 : CollatzResearch.WordTrace tailWord_5554223 prefixEnd_5554223 950662020419109270223033 := by
  unfold tailWord_5554223
  simp only [CollatzResearch.WordTrace]
  refine ⟨202579155357006131612739323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135052770238004087741826215 202579155357006131612739323)
  ·
    refine ⟨303868733035509197419108985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202579155357006131612739323 303868733035509197419108985)
    ·
      refine ⟨227901549776631898064331739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303868733035509197419108985 227901549776631898064331739)
      ·
        refine ⟨341852324664947847096497609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227901549776631898064331739 341852324664947847096497609)
        ·
          refine ⟨256389243498710885322373207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341852324664947847096497609 256389243498710885322373207)
          ·
            refine ⟨384583865248066327983559811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256389243498710885322373207 384583865248066327983559811)
            ·
              refine ⟨576875797872099491975339717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384583865248066327983559811 576875797872099491975339717)
              ·
                refine ⟨108164212101018654745376197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 576875797872099491975339717 108164212101018654745376197)
                ·
                  refine ⟨20280789768940997764758037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108164212101018654745376197 20280789768940997764758037)
                  ·
                    refine ⟨950662020419109270223033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20280789768940997764758037 950662020419109270223033)
                    ·
                      rfl

theorem cell23_5554223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 6].length) (baseStart_5554223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554223 prefixEnd_5554223 := by exact prefixLift 5554223
  have htrace : WordTrace (prefixWord ++ tailWord_5554223) baseStart_5554223 baseEnd_5554223 := by
    simpa [prefixWord, tailWord_5554223, baseEnd_5554223] using wordTrace_append hprefix tailTrace_5554223
  have hstable : (prefixWord ++ tailWord_5554223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554223).length < 2 ^ (prefixWord ++ tailWord_5554223).sum := by decide
  have hdescent : baseEnd_5554223 < baseStart_5554223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554243 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 6]
def baseStart_5554243 : Nat := 118140960795 + 5554243 * 2 ^ 59
def prefixEnd_5554243 : Nat := 4983230072969 + 3 ^ 40 * 5554243 * 2
def baseEnd_5554243 : Nat := 2851996330870417732419007

theorem tailTrace_5554243 : CollatzResearch.WordTrace tailWord_5554243 prefixEnd_5554243 2851996330870417732419007 := by
  unfold tailWord_5554243
  simp only [CollatzResearch.WordTrace]
  refine ⟨202579884816933675028467383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135053256544622450018978255 202579884816933675028467383)
  ·
    refine ⟨303869827225400512542701075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202579884816933675028467383 303869827225400512542701075)
    ·
      refine ⟨455804740838100768814051613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303869827225400512542701075 455804740838100768814051613)
      ·
        refine ⟨170926777814287788305269355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 455804740838100768814051613 170926777814287788305269355)
        ·
          refine ⟨256390166721431682457904033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170926777814287788305269355 256390166721431682457904033)
          ·
            refine ⟨192292625041073761843428025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256390166721431682457904033 192292625041073761843428025)
            ·
              refine ⟨144219468780805321382571019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192292625041073761843428025 144219468780805321382571019)
              ·
                refine ⟨216329203171207982073856529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144219468780805321382571019 216329203171207982073856529)
                ·
                  refine ⟨162246902378405986555392397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216329203171207982073856529 162246902378405986555392397)
                  ·
                    refine ⟨60842588391902244958272149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 162246902378405986555392397 60842588391902244958272149)
                    ·
                      refine ⟨2851996330870417732419007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60842588391902244958272149 2851996330870417732419007)
                      ·
                        rfl

theorem cell23_5554243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_5554243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554243 prefixEnd_5554243 := by exact prefixLift 5554243
  have htrace : WordTrace (prefixWord ++ tailWord_5554243) baseStart_5554243 baseEnd_5554243 := by
    simpa [prefixWord, tailWord_5554243, baseEnd_5554243] using wordTrace_append hprefix tailTrace_5554243
  have hstable : (prefixWord ++ tailWord_5554243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554243).length < 2 ^ (prefixWord ++ tailWord_5554243).sum := by decide
  have hdescent : baseEnd_5554243 < baseStart_5554243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554250 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_5554250 : Nat := 118140960795 + 5554250 * 2 ^ 59
def prefixEnd_5554250 : Nat := 4983230072969 + 3 ^ 40 * 5554250 * 2
def baseEnd_5554250 : Nat := 2851999925234999205031475

theorem tailTrace_5554250 : CollatzResearch.WordTrace tailWord_5554250 prefixEnd_5554250 2851999925234999205031475 := by
  unfold tailWord_5554250
  simp only [CollatzResearch.WordTrace]
  refine ⟨50645035031977078805993051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135053426751938876815981469 50645035031977078805993051)
  ·
    refine ⟨75967552547965618208989577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50645035031977078805993051 75967552547965618208989577)
    ·
      refine ⟨56975664410974213656742183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75967552547965618208989577 56975664410974213656742183)
      ·
        refine ⟨85463496616461320485113275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56975664410974213656742183 85463496616461320485113275)
        ·
          refine ⟨128195244924691980727669913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85463496616461320485113275 128195244924691980727669913)
          ·
            refine ⟨96146433693518985545752435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128195244924691980727669913 96146433693518985545752435)
            ·
              refine ⟨144219650540278478318628653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96146433693518985545752435 144219650540278478318628653)
              ·
                refine ⟨54082368952604429369485745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144219650540278478318628653 54082368952604429369485745)
                ·
                  refine ⟨40561776714453322027114309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54082368952604429369485745 40561776714453322027114309)
                  ·
                    refine ⟨7605333133959997880083933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40561776714453322027114309 7605333133959997880083933)
                    ·
                      refine ⟨2851999925234999205031475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7605333133959997880083933 2851999925234999205031475)
                      ·
                        rfl

theorem cell23_5554250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_5554250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554250 prefixEnd_5554250 := by exact prefixLift 5554250
  have htrace : WordTrace (prefixWord ++ tailWord_5554250) baseStart_5554250 baseEnd_5554250 := by
    simpa [prefixWord, tailWord_5554250, baseEnd_5554250] using wordTrace_append hprefix tailTrace_5554250
  have hstable : (prefixWord ++ tailWord_5554250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554250).length < 2 ^ (prefixWord ++ tailWord_5554250).sum := by decide
  have hdescent : baseEnd_5554250 < baseStart_5554250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554258 : List Nat := [3, 2, 2, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_5554258 : Nat := 118140960795 + 5554258 * 2 ^ 59
def prefixEnd_5554258 : Nat := 4983230072969 + 3 ^ 40 * 5554258 * 2
def baseEnd_5554258 : Nat := 2852004033080235173731439

theorem tailTrace_5554258 : CollatzResearch.WordTrace tailWord_5554258 prefixEnd_5554258 2852004033080235173731439 := by
  unfold tailWord_5554258
  simp only [CollatzResearch.WordTrace]
  refine ⟨50645107977969833147565857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135053621274586221726842285 50645107977969833147565857)
  ·
    refine ⟨37983830983477374860674393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50645107977969833147565857 37983830983477374860674393)
    ·
      refine ⟨28487873237608031145505795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37983830983477374860674393 28487873237608031145505795)
      ·
        refine ⟨42731809856412046718258693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28487873237608031145505795 42731809856412046718258693)
        ·
          refine ⟨8012214348077258759673505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42731809856412046718258693 8012214348077258759673505)
          ·
            refine ⟨6009160761057944069755129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8012214348077258759673505 6009160761057944069755129)
            ·
              refine ⟨4506870570793458052316347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6009160761057944069755129 4506870570793458052316347)
              ·
                refine ⟨6760305856190187078474521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4506870570793458052316347 6760305856190187078474521)
                ·
                  refine ⟨5070229392142640308855891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6760305856190187078474521 5070229392142640308855891)
                  ·
                    refine ⟨7605344088213960463283837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5070229392142640308855891 7605344088213960463283837)
                    ·
                      refine ⟨2852004033080235173731439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7605344088213960463283837 2852004033080235173731439)
                      ·
                        rfl

theorem cell23_5554258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_5554258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554258 prefixEnd_5554258 := by exact prefixLift 5554258
  have htrace : WordTrace (prefixWord ++ tailWord_5554258) baseStart_5554258 baseEnd_5554258 := by
    simpa [prefixWord, tailWord_5554258, baseEnd_5554258] using wordTrace_append hprefix tailTrace_5554258
  have hstable : (prefixWord ++ tailWord_5554258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554258).length < 2 ^ (prefixWord ++ tailWord_5554258).sum := by decide
  have hdescent : baseEnd_5554258 < baseStart_5554258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554260 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_5554260 : Nat := 118140960795 + 5554260 * 2 ^ 59
def prefixEnd_5554260 : Nat := 4983230072969 + 3 ^ 40 * 5554260 * 2
def baseEnd_5554260 : Nat := 2852005060041544165906429

theorem tailTrace_5554260 : CollatzResearch.WordTrace tailWord_5554260 prefixEnd_5554260 2852005060041544165906429 := by
  unfold tailWord_5554260
  simp only [CollatzResearch.WordTrace]
  refine ⟨101290252428936043465918117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135053669905248057954557489 101290252428936043465918117)
  ·
    refine ⟨18991922330425508149859647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101290252428936043465918117 18991922330425508149859647)
    ·
      refine ⟨28487883495638262224789471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18991922330425508149859647 28487883495638262224789471)
      ·
        refine ⟨42731825243457393337184207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28487883495638262224789471 42731825243457393337184207)
        ·
          refine ⟨64097737865186090005776311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42731825243457393337184207 64097737865186090005776311)
          ·
            refine ⟨96146606797779135008664467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64097737865186090005776311 96146606797779135008664467)
            ·
              refine ⟨144219910196668702512996701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96146606797779135008664467 144219910196668702512996701)
              ·
                refine ⟨54082466323750763442373763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144219910196668702512996701 54082466323750763442373763)
                ·
                  refine ⟨81123699485626145163560645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54082466323750763442373763 81123699485626145163560645)
                  ·
                    refine ⟨15210693653554902218167621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81123699485626145163560645 15210693653554902218167621)
                    ·
                      refine ⟨2852005060041544165906429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15210693653554902218167621 2852005060041544165906429)
                      ·
                        rfl

theorem cell23_5554260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_5554260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554260 prefixEnd_5554260 := by exact prefixLift 5554260
  have htrace : WordTrace (prefixWord ++ tailWord_5554260) baseStart_5554260 baseEnd_5554260 := by
    simpa [prefixWord, tailWord_5554260, baseEnd_5554260] using wordTrace_append hprefix tailTrace_5554260
  have hstable : (prefixWord ++ tailWord_5554260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554260).length < 2 ^ (prefixWord ++ tailWord_5554260).sum := by decide
  have hdescent : baseEnd_5554260 < baseStart_5554260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554307 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 2, 5, 2]
def baseStart_5554307 : Nat := 118140960795 + 5554307 * 2 ^ 59
def prefixEnd_5554307 : Nat := 4983230072969 + 3 ^ 40 * 5554307 * 2
def baseEnd_5554307 : Nat := 2852029193632305482018713

theorem tailTrace_5554307 : CollatzResearch.WordTrace tailWord_5554307 prefixEnd_5554307 2852029193632305482018713 := by
  unfold tailWord_5554307
  simp only [CollatzResearch.WordTrace]
  refine ⟨202582219088701813958797175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135054812725801209305864783 202582219088701813958797175)
  ·
    refine ⟨303873328633052720938195763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202582219088701813958797175 303873328633052720938195763)
    ·
      refine ⟨455809992949579081407293645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303873328633052720938195763 455809992949579081407293645)
      ·
        refine ⟨170928747356092155527735117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 455809992949579081407293645 170928747356092155527735117)
        ·
          refine ⟨64098280258534558322900669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170928747356092155527735117 64098280258534558322900669)
          ·
            refine ⟨24036855096950459371087751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64098280258534558322900669 24036855096950459371087751)
            ·
              refine ⟨36055282645425689056631627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24036855096950459371087751 36055282645425689056631627)
              ·
                refine ⟨54082923968138533584947441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36055282645425689056631627 54082923968138533584947441)
                ·
                  refine ⟨40562192976103900188710581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54082923968138533584947441 40562192976103900188710581)
                  ·
                    refine ⟨3802705591509740642691617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40562192976103900188710581 3802705591509740642691617)
                    ·
                      refine ⟨2852029193632305482018713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3802705591509740642691617 2852029193632305482018713)
                      ·
                        rfl

theorem cell23_5554307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 5, 2].length) (baseStart_5554307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554307 prefixEnd_5554307 := by exact prefixLift 5554307
  have htrace : WordTrace (prefixWord ++ tailWord_5554307) baseStart_5554307 baseEnd_5554307 := by
    simpa [prefixWord, tailWord_5554307, baseEnd_5554307] using wordTrace_append hprefix tailTrace_5554307
  have hstable : (prefixWord ++ tailWord_5554307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554307).length < 2 ^ (prefixWord ++ tailWord_5554307).sum := by decide
  have hdescent : baseEnd_5554307 < baseStart_5554307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554320 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 4]
def baseStart_5554320 : Nat := 118140960795 + 5554320 * 2 ^ 59
def prefixEnd_5554320 : Nat := 4983230072969 + 3 ^ 40 * 5554320 * 2
def baseEnd_5554320 : Nat := 2852035868880813931156153

theorem tailTrace_5554320 : CollatzResearch.WordTrace tailWord_5554320 prefixEnd_5554320 2852035868880813931156153 := by
  unfold tailWord_5554320
  simp only [CollatzResearch.WordTrace]
  refine ⟨101291346618827358589510207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135055128825103144786013609 101291346618827358589510207)
  ·
    refine ⟨151937019928241037884265311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101291346618827358589510207 151937019928241037884265311)
    ·
      refine ⟨227905529892361556826397967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151937019928241037884265311 227905529892361556826397967)
      ·
        refine ⟨341858294838542335239596951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227905529892361556826397967 341858294838542335239596951)
        ·
          refine ⟨512787442257813502859395427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341858294838542335239596951 512787442257813502859395427)
          ·
            refine ⟨769181163386720254289093141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512787442257813502859395427 769181163386720254289093141)
            ·
              refine ⟨36055367033752511919801241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 769181163386720254289093141 36055367033752511919801241)
              ·
                refine ⟨27041525275314383939850931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36055367033752511919801241 27041525275314383939850931)
                ·
                  refine ⟨40562287912971575909776397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27041525275314383939850931 40562287912971575909776397)
                  ·
                    refine ⟨15210857967364340966166149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40562287912971575909776397 15210857967364340966166149)
                    ·
                      refine ⟨2852035868880813931156153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15210857967364340966166149 2852035868880813931156153)
                      ·
                        rfl

theorem cell23_5554320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_5554320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554320 prefixEnd_5554320 := by exact prefixLift 5554320
  have htrace : WordTrace (prefixWord ++ tailWord_5554320) baseStart_5554320 baseEnd_5554320 := by
    simpa [prefixWord, tailWord_5554320, baseEnd_5554320] using wordTrace_append hprefix tailTrace_5554320
  have hstable : (prefixWord ++ tailWord_5554320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554320).length < 2 ^ (prefixWord ++ tailWord_5554320).sum := by decide
  have hdescent : baseEnd_5554320 < baseStart_5554320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554334 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_5554334 : Nat := 118140960795 + 5554334 * 2 ^ 59
def prefixEnd_5554334 : Nat := 4983230072969 + 3 ^ 40 * 5554334 * 2
def baseEnd_5554334 : Nat := 950681019203325625460363

theorem tailTrace_5554334 : CollatzResearch.WordTrace tailWord_5554334 prefixEnd_5554334 950681019203325625460363 := by
  unfold tailWord_5554334
  simp only [CollatzResearch.WordTrace]
  refine ⟨25322900482450499696253757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135055469239735998380020037 25322900482450499696253757)
  ·
    refine ⟨9496087680918937386095159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25322900482450499696253757 9496087680918937386095159)
    ·
      refine ⟨14244131521378406079142739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9496087680918937386095159 14244131521378406079142739)
      ·
        refine ⟨21366197282067609118714109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14244131521378406079142739 21366197282067609118714109)
        ·
          refine ⟨8012323980775353419517791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21366197282067609118714109 8012323980775353419517791)
          ·
            refine ⟨12018485971163030129276687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8012323980775353419517791 12018485971163030129276687)
            ·
              refine ⟨18027728956744545193915031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12018485971163030129276687 18027728956744545193915031)
              ·
                refine ⟨27041593435116817790872547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18027728956744545193915031 27041593435116817790872547)
                ·
                  refine ⟨40562390152675226686308821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27041593435116817790872547 40562390152675226686308821)
                  ·
                    refine ⟨950681019203325625460363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40562390152675226686308821 950681019203325625460363)
                    ·
                      rfl

theorem cell23_5554334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_5554334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554334 prefixEnd_5554334 := by exact prefixLift 5554334
  have htrace : WordTrace (prefixWord ++ tailWord_5554334) baseStart_5554334 baseEnd_5554334 := by
    simpa [prefixWord, tailWord_5554334, baseEnd_5554334] using wordTrace_append hprefix tailTrace_5554334
  have hstable : (prefixWord ++ tailWord_5554334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554334).length < 2 ^ (prefixWord ++ tailWord_5554334).sum := by decide
  have hdescent : baseEnd_5554334 < baseStart_5554334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554337 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_5554337 : Nat := 118140960795 + 5554337 * 2 ^ 59
def prefixEnd_5554337 : Nat := 4983230072969 + 3 ^ 40 * 5554337 * 2
def baseEnd_5554337 : Nat := 2852044598051940364643575

theorem tailTrace_5554337 : CollatzResearch.WordTrace tailWord_5554337 prefixEnd_5554337 2852044598051940364643575 := by
  unfold tailWord_5554337
  simp only [CollatzResearch.WordTrace]
  refine ⟨202583313278593129082389265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135055542185728752721592843 202583313278593129082389265)
  ·
    refine ⟨151937484958944846811791949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202583313278593129082389265 151937484958944846811791949)
    ·
      refine ⟨56976556859604317554421981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151937484958944846811791949 56976556859604317554421981)
      ·
        refine ⟨21366208822351619082908243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56976556859604317554421981 21366208822351619082908243)
        ·
          refine ⟨32049313233527428624362365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21366208822351619082908243 32049313233527428624362365)
          ·
            refine ⟨12018492462572785734135887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32049313233527428624362365 12018492462572785734135887)
            ·
              refine ⟨18027738693859178601203831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12018492462572785734135887 18027738693859178601203831)
              ·
                refine ⟨27041608040788767901805747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18027738693859178601203831 27041608040788767901805747)
                ·
                  refine ⟨40562412061183151852708621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27041608040788767901805747 40562412061183151852708621)
                  ·
                    refine ⟨15210904522943681944765733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40562412061183151852708621 15210904522943681944765733)
                    ·
                      refine ⟨2852044598051940364643575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15210904522943681944765733 2852044598051940364643575)
                      ·
                        rfl

theorem cell23_5554337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_5554337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554337 prefixEnd_5554337 := by exact prefixLift 5554337
  have htrace : WordTrace (prefixWord ++ tailWord_5554337) baseStart_5554337 baseEnd_5554337 := by
    simpa [prefixWord, tailWord_5554337, baseEnd_5554337] using wordTrace_append hprefix tailTrace_5554337
  have hstable : (prefixWord ++ tailWord_5554337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554337).length < 2 ^ (prefixWord ++ tailWord_5554337).sum := by decide
  have hdescent : baseEnd_5554337 < baseStart_5554337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554360 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 8]
def baseStart_5554360 : Nat := 118140960795 + 5554360 * 2 ^ 59
def prefixEnd_5554360 : Nat := 4983230072969 + 3 ^ 40 * 5554360 * 2
def baseEnd_5554360 : Nat := 316895156456332641628441

theorem tailTrace_5554360 : CollatzResearch.WordTrace tailWord_5554360 prefixEnd_5554360 316895156456332641628441 := by
  unfold tailWord_5554360
  simp only [CollatzResearch.WordTrace]
  refine ⟨101292076078754902005238267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135056101438339869340317689 101292076078754902005238267)
  ·
    refine ⟨151938114118132353007857401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101292076078754902005238267 151938114118132353007857401)
    ·
      refine ⟨113953585588599264755893051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151938114118132353007857401 113953585588599264755893051)
      ·
        refine ⟨170930378382898897133839577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113953585588599264755893051 170930378382898897133839577)
        ·
          refine ⟨128197783787174172850379683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170930378382898897133839577 128197783787174172850379683)
          ·
            refine ⟨192296675680761259275569525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128197783787174172850379683 192296675680761259275569525)
            ·
              refine ⟨18027813345071368057084643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192296675680761259275569525 18027813345071368057084643)
              ·
                refine ⟨27041720017607052085626965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18027813345071368057084643 27041720017607052085626965)
                ·
                  refine ⟨316895156456332641628441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27041720017607052085626965 316895156456332641628441)
                  ·
                    rfl

theorem cell23_5554360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 8].length) (baseStart_5554360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554360 prefixEnd_5554360 := by exact prefixLift 5554360
  have htrace : WordTrace (prefixWord ++ tailWord_5554360) baseStart_5554360 baseEnd_5554360 := by
    simpa [prefixWord, tailWord_5554360, baseEnd_5554360] using wordTrace_append hprefix tailTrace_5554360
  have hstable : (prefixWord ++ tailWord_5554360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554360).length < 2 ^ (prefixWord ++ tailWord_5554360).sum := by decide
  have hdescent : baseEnd_5554360 < baseStart_5554360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554437 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 6, 4]
def baseStart_5554437 : Nat := 118140960795 + 5554437 * 2 ^ 59
def prefixEnd_5554437 : Nat := 4983230072969 + 3 ^ 40 * 5554437 * 2
def baseEnd_5554437 : Nat := 950698648705796657797705

theorem tailTrace_5554437 : CollatzResearch.WordTrace tailWord_5554437 prefixEnd_5554437 950698648705796657797705 := by
  unfold tailWord_5554437
  simp only [CollatzResearch.WordTrace]
  refine ⟨202586960578230846161029565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135057973718820564107353043 202586960578230846161029565)
  ·
    refine ⟨75970110216836567310386087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202586960578230846161029565 75970110216836567310386087)
    ·
      refine ⟨113955165325254850965579131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75970110216836567310386087 113955165325254850965579131)
      ·
        refine ⟨170932747987882276448368697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113955165325254850965579131 170932747987882276448368697)
        ·
          refine ⟨128199560990911707336276523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170932747987882276448368697 128199560990911707336276523)
          ·
            refine ⟨192299341486367561004414785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128199560990911707336276523 192299341486367561004414785)
            ·
              refine ⟨144224506114775670753311089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192299341486367561004414785 144224506114775670753311089)
              ·
                refine ⟨108168379586081753064983317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144224506114775670753311089 108168379586081753064983317)
                ·
                  refine ⟨5070392793097582174921093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108168379586081753064983317 5070392793097582174921093)
                  ·
                    refine ⟨950698648705796657797705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5070392793097582174921093 950698648705796657797705)
                    ·
                      rfl

theorem cell23_5554437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_5554437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554437 prefixEnd_5554437 := by exact prefixLift 5554437
  have htrace : WordTrace (prefixWord ++ tailWord_5554437) baseStart_5554437 baseEnd_5554437 := by
    simpa [prefixWord, tailWord_5554437, baseEnd_5554437] using wordTrace_append hprefix tailTrace_5554437
  have hstable : (prefixWord ++ tailWord_5554437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554437).length < 2 ^ (prefixWord ++ tailWord_5554437).sum := by decide
  have hdescent : baseEnd_5554437 < baseStart_5554437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554464 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 5]
def baseStart_5554464 : Nat := 118140960795 + 5554464 * 2 ^ 59
def prefixEnd_5554464 : Nat := 4983230072969 + 3 ^ 40 * 5554464 * 2
def baseEnd_5554464 : Nat := 2852109810095061367755491

theorem tailTrace_5554464 : CollatzResearch.WordTrace tailWord_5554464 prefixEnd_5554464 2852109810095061367755491 := by
  unfold tailWord_5554464
  simp only [CollatzResearch.WordTrace]
  refine ⟨101293972674566514886131223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135058630232755353181508297 101293972674566514886131223)
  ·
    refine ⟨151940959011849772329196835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101293972674566514886131223 151940959011849772329196835)
    ·
      refine ⟨227911438517774658493795253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151940959011849772329196835 227911438517774658493795253)
      ·
        refine ⟨21366697361041374233793305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 227911438517774658493795253 21366697361041374233793305)
        ·
          refine ⟨16025023020781030675344979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21366697361041374233793305 16025023020781030675344979)
          ·
            refine ⟨24037534531171546013017469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16025023020781030675344979 24037534531171546013017469)
            ·
              refine ⟨9014075449189329754881551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24037534531171546013017469 9014075449189329754881551)
              ·
                refine ⟨13521113173783994632322327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9014075449189329754881551 13521113173783994632322327)
                ·
                  refine ⟨20281669760675991948483491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13521113173783994632322327 20281669760675991948483491)
                  ·
                    refine ⟨30422504641013987922725237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20281669760675991948483491 30422504641013987922725237)
                    ·
                      refine ⟨2852109810095061367755491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30422504641013987922725237 2852109810095061367755491)
                      ·
                        rfl

theorem cell23_5554464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_5554464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554464 prefixEnd_5554464 := by exact prefixLift 5554464
  have htrace : WordTrace (prefixWord ++ tailWord_5554464) baseStart_5554464 baseEnd_5554464 := by
    simpa [prefixWord, tailWord_5554464, baseEnd_5554464] using wordTrace_append hprefix tailTrace_5554464
  have hstable : (prefixWord ++ tailWord_5554464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554464).length < 2 ^ (prefixWord ++ tailWord_5554464).sum := by decide
  have hdescent : baseEnd_5554464 < baseStart_5554464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554472 : List Nat := [2, 1, 5, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_5554472 : Nat := 118140960795 + 5554472 * 2 ^ 59
def prefixEnd_5554472 : Nat := 4983230072969 + 3 ^ 40 * 5554472 * 2
def baseEnd_5554472 : Nat := 2852113917940297336455455

theorem tailTrace_5554472 : CollatzResearch.WordTrace tailWord_5554472 prefixEnd_5554472 2852113917940297336455455 := by
  unfold tailWord_5554472
  simp only [CollatzResearch.WordTrace]
  refine ⟨101294118566552023569276835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135058824755402698092369113 101294118566552023569276835)
  ·
    refine ⟨151941177849828035353915253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101294118566552023569276835 151941177849828035353915253)
    ·
      refine ⟨14244485423421378314429555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151941177849828035353915253 14244485423421378314429555)
      ·
        refine ⟨21366728135132067471644333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14244485423421378314429555 21366728135132067471644333)
        ·
          refine ⟨8012523050674525301866625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21366728135132067471644333 8012523050674525301866625)
          ·
            refine ⟨6009392288005893976399969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8012523050674525301866625 6009392288005893976399969)
            ·
              refine ⟨4507044216004420482299977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6009392288005893976399969 4507044216004420482299977)
              ·
                refine ⟨3380283162003315361724983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4507044216004420482299977 3380283162003315361724983)
                ·
                  refine ⟨5070424743004973042587475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3380283162003315361724983 5070424743004973042587475)
                  ·
                    refine ⟨7605637114507459563881213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5070424743004973042587475 7605637114507459563881213)
                    ·
                      refine ⟨2852113917940297336455455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7605637114507459563881213 2852113917940297336455455)
                      ·
                        rfl

theorem cell23_5554472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_5554472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554472 prefixEnd_5554472 := by exact prefixLift 5554472
  have htrace : WordTrace (prefixWord ++ tailWord_5554472) baseStart_5554472 baseEnd_5554472 := by
    simpa [prefixWord, tailWord_5554472, baseEnd_5554472] using wordTrace_append hprefix tailTrace_5554472
  have hstable : (prefixWord ++ tailWord_5554472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554472).length < 2 ^ (prefixWord ++ tailWord_5554472).sum := by decide
  have hdescent : baseEnd_5554472 < baseStart_5554472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554484 : List Nat := [2, 5, 1, 1, 1, 2, 3, 8]
def baseStart_5554484 : Nat := 118140960795 + 5554484 * 2 ^ 59
def prefixEnd_5554484 : Nat := 4983230072969 + 3 ^ 40 * 5554484 * 2
def baseEnd_5554484 : Nat := 105634077026227825537237

theorem tailTrace_5554484 : CollatzResearch.WordTrace tailWord_5554484 prefixEnd_5554484 105634077026227825537237 := by
  unfold tailWord_5554484
  simp only [CollatzResearch.WordTrace]
  refine ⟨101294337404530286593995253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135059116539373715458660337 101294337404530286593995253)
  ·
    refine ⟨9496344131674714368187055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101294337404530286593995253 9496344131674714368187055)
    ·
      refine ⟨14244516197512071552280583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9496344131674714368187055 14244516197512071552280583)
      ·
        refine ⟨21366774296268107328420875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14244516197512071552280583 21366774296268107328420875)
        ·
          refine ⟨32050161444402160992631313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21366774296268107328420875 32050161444402160992631313)
          ·
            refine ⟨24037621083301620744473485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32050161444402160992631313 24037621083301620744473485)
            ·
              refine ⟨9014107906238107779177557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24037621083301620744473485 9014107906238107779177557)
              ·
                refine ⟨105634077026227825537237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9014107906238107779177557 105634077026227825537237)
                ·
                  rfl

theorem cell23_5554484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 8].length) (baseStart_5554484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554484 prefixEnd_5554484 := by exact prefixLift 5554484
  have htrace : WordTrace (prefixWord ++ tailWord_5554484) baseStart_5554484 baseEnd_5554484 := by
    simpa [prefixWord, tailWord_5554484, baseEnd_5554484] using wordTrace_append hprefix tailTrace_5554484
  have hstable : (prefixWord ++ tailWord_5554484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554484).length < 2 ^ (prefixWord ++ tailWord_5554484).sum := by decide
  have hdescent : baseEnd_5554484 < baseStart_5554484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554527 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 2, 6]
def baseStart_5554527 : Nat := 118140960795 + 5554527 * 2 ^ 59
def prefixEnd_5554527 : Nat := 4983230072969 + 3 ^ 40 * 5554527 * 2
def baseEnd_5554527 : Nat := 950714053125431540422567

theorem tailTrace_5554527 : CollatzResearch.WordTrace tailWord_5554527 prefixEnd_5554527 950714053125431540422567 := by
  unfold tailWord_5554527
  simp only [CollatzResearch.WordTrace]
  refine ⟨202590243147904791531805835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135060162098603194354537223 202590243147904791531805835)
  ·
    refine ⟨303885364721857187297708753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202590243147904791531805835 303885364721857187297708753)
    ·
      refine ⟨227914023541392890473281565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303885364721857187297708753 227914023541392890473281565)
      ·
        refine ⟨85467758828022333927480587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227914023541392890473281565 85467758828022333927480587)
        ·
          refine ⟨128201638242033500891220881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85467758828022333927480587 128201638242033500891220881)
          ·
            refine ⟨96151228681525125668415661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128201638242033500891220881 96151228681525125668415661)
            ·
              refine ⟨36056710755571922125655873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96151228681525125668415661 36056710755571922125655873)
              ·
                refine ⟨27042533066678941594241905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36056710755571922125655873 27042533066678941594241905)
                ·
                  refine ⟨20281899800009206195681429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27042533066678941594241905 20281899800009206195681429)
                  ·
                    refine ⟨950714053125431540422567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20281899800009206195681429 950714053125431540422567)
                    ·
                      rfl

theorem cell23_5554527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 6].length) (baseStart_5554527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554527 prefixEnd_5554527 := by exact prefixLift 5554527
  have htrace : WordTrace (prefixWord ++ tailWord_5554527) baseStart_5554527 baseEnd_5554527 := by
    simpa [prefixWord, tailWord_5554527, baseEnd_5554527] using wordTrace_append hprefix tailTrace_5554527
  have hstable : (prefixWord ++ tailWord_5554527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554527).length < 2 ^ (prefixWord ++ tailWord_5554527).sum := by decide
  have hdescent : baseEnd_5554527 < baseStart_5554527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554621 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_5554621 : Nat := 118140960795 + 5554621 * 2 ^ 59
def prefixEnd_5554621 : Nat := 4983230072969 + 3 ^ 40 * 5554621 * 2
def baseEnd_5554621 : Nat := 950730142185939084497423

theorem tailTrace_5554621 : CollatzResearch.WordTrace tailWord_5554621 prefixEnd_5554621 950730142185939084497423 := by
  unfold tailWord_5554621
  simp only [CollatzResearch.WordTrace]
  refine ⟨202593671609564245585727717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135062447739709497057151811 202593671609564245585727717)
  ·
    refine ⟨37986313426793296047323947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202593671609564245585727717 37986313426793296047323947)
    ·
      refine ⟨56979470140189944070985921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37986313426793296047323947 56979470140189944070985921)
      ·
        refine ⟨42734602605142458053239441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56979470140189944070985921 42734602605142458053239441)
        ·
          refine ⟨32050951953856843539929581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42734602605142458053239441 32050951953856843539929581)
          ·
            refine ⟨12019106982696316327473593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32050951953856843539929581 12019106982696316327473593)
            ·
              refine ⟨9014330237022237245605195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12019106982696316327473593 9014330237022237245605195)
              ·
                refine ⟨13521495355533355868407793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9014330237022237245605195 13521495355533355868407793)
                ·
                  refine ⟨10141121516650016901305845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13521495355533355868407793 10141121516650016901305845)
                  ·
                    refine ⟨950730142185939084497423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10141121516650016901305845 950730142185939084497423)
                    ·
                      rfl

theorem cell23_5554621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_5554621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554621 prefixEnd_5554621 := by exact prefixLift 5554621
  have htrace : WordTrace (prefixWord ++ tailWord_5554621) baseStart_5554621 baseEnd_5554621 := by
    simpa [prefixWord, tailWord_5554621, baseEnd_5554621] using wordTrace_append hprefix tailTrace_5554621
  have hstable : (prefixWord ++ tailWord_5554621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554621).length < 2 ^ (prefixWord ++ tailWord_5554621).sum := by decide
  have hdescent : baseEnd_5554621 < baseStart_5554621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554642 : List Nat := [3, 2, 2, 4, 1, 2, 2, 2, 5]
def baseStart_5554642 : Nat := 118140960795 + 5554642 * 2 ^ 59
def prefixEnd_5554642 : Nat := 4983230072969 + 3 ^ 40 * 5554642 * 2
def baseEnd_5554642 : Nat := 316911245516840185703297

theorem tailTrace_5554642 : CollatzResearch.WordTrace tailWord_5554642 prefixEnd_5554642 316911245516840185703297 := by
  unfold tailWord_5554642
  simp only [CollatzResearch.WordTrace]
  refine ⟨50648609385622041543060545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135062958361658777448161453 50648609385622041543060545)
  ·
    refine ⟨37986457039216531157295409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50648609385622041543060545 37986457039216531157295409)
    ·
      refine ⟨28489842779412398367971557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37986457039216531157295409 28489842779412398367971557)
      ·
        refine ⟨5341845521139824693994667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28489842779412398367971557 5341845521139824693994667)
        ·
          refine ⟨8012768281709737040992001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5341845521139824693994667 8012768281709737040992001)
          ·
            refine ⟨6009576211282302780744001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8012768281709737040992001 6009576211282302780744001)
            ·
              refine ⟨4507182158461727085558001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6009576211282302780744001 4507182158461727085558001)
              ·
                refine ⟨3380386618846295314168501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4507182158461727085558001 3380386618846295314168501)
                ·
                  refine ⟨316911245516840185703297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3380386618846295314168501 316911245516840185703297)
                  ·
                    rfl

theorem cell23_5554642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_5554642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554642 prefixEnd_5554642 := by exact prefixLift 5554642
  have htrace : WordTrace (prefixWord ++ tailWord_5554642) baseStart_5554642 baseEnd_5554642 := by
    simpa [prefixWord, tailWord_5554642, baseEnd_5554642] using wordTrace_append hprefix tailTrace_5554642
  have hstable : (prefixWord ++ tailWord_5554642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554642).length < 2 ^ (prefixWord ++ tailWord_5554642).sum := by decide
  have hdescent : baseEnd_5554642 < baseStart_5554642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554691 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 5, 1, 3]
def baseStart_5554691 : Nat := 118140960795 + 5554691 * 2 ^ 59
def prefixEnd_5554691 : Nat := 4983230072969 + 3 ^ 40 * 5554691 * 2
def baseEnd_5554691 : Nat := 2852226370203631979616947

theorem tailTrace_5554691 : CollatzResearch.WordTrace tailWord_5554691 prefixEnd_5554691 2852226370203631979616947 := by
  unfold tailWord_5554691
  simp only [CollatzResearch.WordTrace]
  refine ⟨202596224719310647540775927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135064149812873765027183951 202596224719310647540775927)
  ·
    refine ⟨303894337078965971311163891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202596224719310647540775927 303894337078965971311163891)
    ·
      refine ⟨455841505618448956966745837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303894337078965971311163891 455841505618448956966745837)
      ·
        refine ⟨170940564606918358862529689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 455841505618448956966745837 170940564606918358862529689)
        ·
          refine ⟨128205423455188769146897267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170940564606918358862529689 128205423455188769146897267)
          ·
            refine ⟨192308135182783153720345901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128205423455188769146897267 192308135182783153720345901)
            ·
              refine ⟨72115550693543682645129713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192308135182783153720345901 72115550693543682645129713)
              ·
                refine ⟨54086663020157761983847285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72115550693543682645129713 54086663020157761983847285)
                ·
                  refine ⟨5070624658139790185985683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54086663020157761983847285 5070624658139790185985683)
                  ·
                    refine ⟨7605936987209685278978525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5070624658139790185985683 7605936987209685278978525)
                    ·
                      refine ⟨2852226370203631979616947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7605936987209685278978525 2852226370203631979616947)
                      ·
                        rfl

theorem cell23_5554691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_5554691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554691 prefixEnd_5554691 := by exact prefixLift 5554691
  have htrace : WordTrace (prefixWord ++ tailWord_5554691) baseStart_5554691 baseEnd_5554691 := by
    simpa [prefixWord, tailWord_5554691, baseEnd_5554691] using wordTrace_append hprefix tailTrace_5554691
  have hstable : (prefixWord ++ tailWord_5554691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554691).length < 2 ^ (prefixWord ++ tailWord_5554691).sum := by decide
  have hdescent : baseEnd_5554691 < baseStart_5554691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554728 : List Nat := [2, 1, 5, 2, 1, 1, 1, 4, 1, 5]
def baseStart_5554728 : Nat := 118140960795 + 5554728 * 2 ^ 59
def prefixEnd_5554728 : Nat := 4983230072969 + 3 ^ 40 * 5554728 * 2
def baseEnd_5554728 : Nat := 950748456329282778284759

theorem tailTrace_5554728 : CollatzResearch.WordTrace tailWord_5554728 prefixEnd_5554728 950748456329282778284759 := by
  unfold tailWord_5554728
  simp only [CollatzResearch.WordTrace]
  refine ⟨101298787110088301429936419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135065049480117735239915225 101298787110088301429936419)
  ·
    refine ⟨151948180665132452144904629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101298787110088301429936419 151948180665132452144904629)
    ·
      refine ⟨14245141937356167388584809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151948180665132452144904629 14245141937356167388584809)
      ·
        refine ⟨10683856453017125541438607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14245141937356167388584809 10683856453017125541438607)
        ·
          refine ⟨16025784679525688312157911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10683856453017125541438607 16025784679525688312157911)
          ·
            refine ⟨24038677019288532468236867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16025784679525688312157911 24038677019288532468236867)
            ·
              refine ⟨36058015528932798702355301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24038677019288532468236867 36058015528932798702355301)
              ·
                refine ⟨6760877911674899756691619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36058015528932798702355301 6760877911674899756691619)
                ·
                  refine ⟨10141316867512349635037429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6760877911674899756691619 10141316867512349635037429)
                  ·
                    refine ⟨950748456329282778284759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10141316867512349635037429 950748456329282778284759)
                    ·
                      rfl

theorem cell23_5554728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_5554728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554728 prefixEnd_5554728 := by exact prefixLift 5554728
  have htrace : WordTrace (prefixWord ++ tailWord_5554728) baseStart_5554728 baseEnd_5554728 := by
    simpa [prefixWord, tailWord_5554728, baseEnd_5554728] using wordTrace_append hprefix tailTrace_5554728
  have hstable : (prefixWord ++ tailWord_5554728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554728).length < 2 ^ (prefixWord ++ tailWord_5554728).sum := by decide
  have hdescent : baseEnd_5554728 < baseStart_5554728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554741 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 6, 4]
def baseStart_5554741 : Nat := 118140960795 + 5554741 * 2 ^ 59
def prefixEnd_5554741 : Nat := 4983230072969 + 3 ^ 40 * 5554741 * 2
def baseEnd_5554741 : Nat := 950750681412118927997239

theorem tailTrace_5554741 : CollatzResearch.WordTrace tailWord_5554741 prefixEnd_5554741 950750681412118927997239 := by
  unfold tailWord_5554741
  simp only [CollatzResearch.WordTrace]
  refine ⟨202598048369129506080096077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135065365579419670720064051 202598048369129506080096077)
  ·
    refine ⟨75974268138423564780036029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202598048369129506080096077 75974268138423564780036029)
    ·
      refine ⟨28490350551908836792513511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75974268138423564780036029 28490350551908836792513511)
      ·
        refine ⟨42735525827863255188770267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28490350551908836792513511 42735525827863255188770267)
        ·
          refine ⟨64103288741794882783155401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42735525827863255188770267 64103288741794882783155401)
          ·
            refine ⟨48077466556346162087366551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64103288741794882783155401 48077466556346162087366551)
            ·
              refine ⟨72116199834519243131049827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48077466556346162087366551 72116199834519243131049827)
              ·
                refine ⟨108174299751778864696574741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72116199834519243131049827 108174299751778864696574741)
                ·
                  refine ⟨5070670300864634282651941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108174299751778864696574741 5070670300864634282651941)
                  ·
                    refine ⟨950750681412118927997239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5070670300864634282651941 950750681412118927997239)
                    ·
                      rfl

theorem cell23_5554741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_5554741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554741 prefixEnd_5554741 := by exact prefixLift 5554741
  have htrace : WordTrace (prefixWord ++ tailWord_5554741) baseStart_5554741 baseEnd_5554741 := by
    simpa [prefixWord, tailWord_5554741, baseEnd_5554741] using wordTrace_append hprefix tailTrace_5554741
  have hstable : (prefixWord ++ tailWord_5554741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554741).length < 2 ^ (prefixWord ++ tailWord_5554741).sum := by decide
  have hdescent : baseEnd_5554741 < baseStart_5554741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554748 : List Nat := [2, 2, 2, 2, 3, 1, 2, 3, 1, 1, 4]
def baseStart_5554748 : Nat := 118140960795 + 5554748 * 2 ^ 59
def prefixEnd_5554748 : Nat := 4983230072969 + 3 ^ 40 * 5554748 * 2
def baseEnd_5554748 : Nat := 2852255638600938256604185

theorem tailTrace_5554748 : CollatzResearch.WordTrace tailWord_5554748 prefixEnd_5554748 2852255638600938256604185 := by
  unfold tailWord_5554748
  simp only [CollatzResearch.WordTrace]
  refine ⟨101299151840052073137800449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135065535786736097517067265 101299151840052073137800449)
  ·
    refine ⟨75974363880039054853350337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101299151840052073137800449 75974363880039054853350337)
    ·
      refine ⟨56980772910029291140012753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75974363880039054853350337 56980772910029291140012753)
      ·
        refine ⟨42735579682521968355009565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56980772910029291140012753 42735579682521968355009565)
        ·
          refine ⟨16025842380945738133128587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42735579682521968355009565 16025842380945738133128587)
          ·
            refine ⟨24038763571418607199692881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16025842380945738133128587 24038763571418607199692881)
            ·
              refine ⟨18029072678563955399769661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24038763571418607199692881 18029072678563955399769661)
              ·
                refine ⟨6760902254461483274913623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18029072678563955399769661 6760902254461483274913623)
                ·
                  refine ⟨10141353381692224912370435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6760902254461483274913623 10141353381692224912370435)
                  ·
                    refine ⟨15212030072538337368555653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10141353381692224912370435 15212030072538337368555653)
                    ·
                      refine ⟨2852255638600938256604185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15212030072538337368555653 2852255638600938256604185)
                      ·
                        rfl

theorem cell23_5554748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_5554748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554748 prefixEnd_5554748 := by exact prefixLift 5554748
  have htrace : WordTrace (prefixWord ++ tailWord_5554748) baseStart_5554748 baseEnd_5554748 := by
    simpa [prefixWord, tailWord_5554748, baseEnd_5554748] using wordTrace_append hprefix tailTrace_5554748
  have hstable : (prefixWord ++ tailWord_5554748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554748).length < 2 ^ (prefixWord ++ tailWord_5554748).sum := by decide
  have hdescent : baseEnd_5554748 < baseStart_5554748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554751 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 5]
def baseStart_5554751 : Nat := 118140960795 + 5554751 * 2 ^ 59
def prefixEnd_5554751 : Nat := 4983230072969 + 3 ^ 40 * 5554751 * 2
def baseEnd_5554751 : Nat := 2852257179042901744866671

theorem tailTrace_5554751 : CollatzResearch.WordTrace tailWord_5554751 prefixEnd_5554751 2852257179042901744866671 := by
  unfold tailWord_5554751
  simp only [CollatzResearch.WordTrace]
  refine ⟨202598413099093277787960107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135065608732728851858640071 202598413099093277787960107)
  ·
    refine ⟨303897619648639916681940161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202598413099093277787960107 303897619648639916681940161)
    ·
      refine ⟨227923214736479937511455121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303897619648639916681940161 227923214736479937511455121)
      ·
        refine ⟨170942411052359953133591341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227923214736479937511455121 170942411052359953133591341)
        ·
          refine ⟨64103404144634982425096753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170942411052359953133591341 64103404144634982425096753)
          ·
            refine ⟨48077553108476236818822565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64103404144634982425096753 48077553108476236818822565)
            ·
              refine ⟨9014541207839294403529231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48077553108476236818822565 9014541207839294403529231)
              ·
                refine ⟨13521811811758941605293847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9014541207839294403529231 13521811811758941605293847)
                ·
                  refine ⟨20282717717638412407940771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13521811811758941605293847 20282717717638412407940771)
                  ·
                    refine ⟨30424076576457618611911157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20282717717638412407940771 30424076576457618611911157)
                    ·
                      refine ⟨2852257179042901744866671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30424076576457618611911157 2852257179042901744866671)
                      ·
                        rfl

theorem cell23_5554751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_5554751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554751 prefixEnd_5554751 := by exact prefixLift 5554751
  have htrace : WordTrace (prefixWord ++ tailWord_5554751) baseStart_5554751 baseEnd_5554751 := by
    simpa [prefixWord, tailWord_5554751, baseEnd_5554751] using wordTrace_append hprefix tailTrace_5554751
  have hstable : (prefixWord ++ tailWord_5554751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554751).length < 2 ^ (prefixWord ++ tailWord_5554751).sum := by decide
  have hdescent : baseEnd_5554751 < baseStart_5554751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554785 : List Nat := [1, 2, 3, 1, 1, 6, 1, 2, 1, 2, 3]
def baseStart_5554785 : Nat := 118140960795 + 5554785 * 2 ^ 59
def prefixEnd_5554785 : Nat := 4983230072969 + 3 ^ 40 * 5554785 * 2
def baseEnd_5554785 : Nat := 2852274637385154611841515

theorem tailTrace_5554785 : CollatzResearch.WordTrace tailWord_5554785 prefixEnd_5554785 2852274637385154611841515 := by
  unfold tailWord_5554785
  simp only [CollatzResearch.WordTrace]
  refine ⟨202599653180970101594697809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135066435453980067729798539 202599653180970101594697809)
  ·
    refine ⟨151949739885727576196023357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202599653180970101594697809 151949739885727576196023357)
    ·
      refine ⟨56981152457147841073508759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151949739885727576196023357 56981152457147841073508759)
      ·
        refine ⟨85471728685721761610263139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56981152457147841073508759 85471728685721761610263139)
        ·
          refine ⟨128207593028582642415394709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85471728685721761610263139 128207593028582642415394709)
          ·
            refine ⟨6009730923214811363221627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128207593028582642415394709 6009730923214811363221627)
            ·
              refine ⟨9014596384822217044832441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6009730923214811363221627 9014596384822217044832441)
              ·
                refine ⟨6760947288616662783624331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9014596384822217044832441 6760947288616662783624331)
                ·
                  refine ⟨10141420932924994175436497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6760947288616662783624331 10141420932924994175436497)
                  ·
                    refine ⟨7606065699693745631577373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10141420932924994175436497 7606065699693745631577373)
                    ·
                      refine ⟨2852274637385154611841515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7606065699693745631577373 2852274637385154611841515)
                      ·
                        rfl

theorem cell23_5554785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_5554785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554785 prefixEnd_5554785 := by exact prefixLift 5554785
  have htrace : WordTrace (prefixWord ++ tailWord_5554785) baseStart_5554785 baseEnd_5554785 := by
    simpa [prefixWord, tailWord_5554785, baseEnd_5554785] using wordTrace_append hprefix tailTrace_5554785
  have hstable : (prefixWord ++ tailWord_5554785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554785).length < 2 ^ (prefixWord ++ tailWord_5554785).sum := by decide
  have hdescent : baseEnd_5554785 < baseStart_5554785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554798 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_5554798 : Nat := 118140960795 + 5554798 * 2 ^ 59
def prefixEnd_5554798 : Nat := 4983230072969 + 3 ^ 40 * 5554798 * 2
def baseEnd_5554798 : Nat := 2852281312633663060978955

theorem tailTrace_5554798 : CollatzResearch.WordTrace tailWord_5554798 prefixEnd_5554798 2852281312633663060978955 := by
  unfold tailWord_5554798
  simp only [CollatzResearch.WordTrace]
  refine ⟨25325015916240375601865131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135066751553282003209947365 25325015916240375601865131)
  ·
    refine ⟨37987523874360563402797697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25325015916240375601865131 37987523874360563402797697)
    ·
      refine ⟨28490642905770422552098273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37987523874360563402797697 28490642905770422552098273)
      ·
        refine ⟨21367982179327816914073705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28490642905770422552098273 21367982179327816914073705)
        ·
          refine ⟨16025986634495862685555279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21367982179327816914073705 16025986634495862685555279)
          ·
            refine ⟨24038979951743794028332919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16025986634495862685555279 24038979951743794028332919)
            ·
              refine ⟨36058469927615691042499379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24038979951743794028332919 36058469927615691042499379)
              ·
                refine ⟨54087704891423536563749069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36058469927615691042499379 54087704891423536563749069)
                ·
                  refine ⟨20282889334283826211405901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54087704891423536563749069 20282889334283826211405901)
                  ·
                    refine ⟨7606083500356434829277213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20282889334283826211405901 7606083500356434829277213)
                    ·
                      refine ⟨2852281312633663060978955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7606083500356434829277213 2852281312633663060978955)
                      ·
                        rfl

theorem cell23_5554798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_5554798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554798 prefixEnd_5554798 := by exact prefixLift 5554798
  have htrace : WordTrace (prefixWord ++ tailWord_5554798) baseStart_5554798 baseEnd_5554798 := by
    simpa [prefixWord, tailWord_5554798, baseEnd_5554798] using wordTrace_append hprefix tailTrace_5554798
  have hstable : (prefixWord ++ tailWord_5554798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554798).length < 2 ^ (prefixWord ++ tailWord_5554798).sum := by decide
  have hdescent : baseEnd_5554798 < baseStart_5554798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554802 : List Nat := [3, 2, 1, 2, 4, 1, 3, 1, 1, 2, 3]
def baseStart_5554802 : Nat := 118140960795 + 5554802 * 2 ^ 59
def prefixEnd_5554802 : Nat := 4983230072969 + 3 ^ 40 * 5554802 * 2
def baseEnd_5554802 : Nat := 2852283366556281045328937

theorem tailTrace_5554802 : CollatzResearch.WordTrace tailWord_5554802 prefixEnd_5554802 2852283366556281045328937 := by
  unfold tailWord_5554802
  simp only [CollatzResearch.WordTrace]
  refine ⟨50650068305477128374516665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135066848814605675665377773 50650068305477128374516665)
  ·
    refine ⟨37987551229107846280887499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50650068305477128374516665 37987551229107846280887499)
    ·
      refine ⟨56981326843661769421331249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37987551229107846280887499 56981326843661769421331249)
      ·
        refine ⟨42735995132746327065998437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56981326843661769421331249 42735995132746327065998437)
        ·
          refine ⟨8012999087389936324874707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42735995132746327065998437 8012999087389936324874707)
          ·
            refine ⟨12019498631084904487312061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8012999087389936324874707 12019498631084904487312061)
            ·
              refine ⟨4507311986656839182742023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12019498631084904487312061 4507311986656839182742023)
              ·
                refine ⟨6760967979985258774113035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4507311986656839182742023 6760967979985258774113035)
                ·
                  refine ⟨10141451969977888161169553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6760967979985258774113035 10141451969977888161169553)
                  ·
                    refine ⟨7606088977483416120877165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10141451969977888161169553 7606088977483416120877165)
                    ·
                      refine ⟨2852283366556281045328937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7606088977483416120877165 2852283366556281045328937)
                      ·
                        rfl

theorem cell23_5554802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_5554802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554802 prefixEnd_5554802 := by exact prefixLift 5554802
  have htrace : WordTrace (prefixWord ++ tailWord_5554802) baseStart_5554802 baseEnd_5554802 := by
    simpa [prefixWord, tailWord_5554802, baseEnd_5554802] using wordTrace_append hprefix tailTrace_5554802
  have hstable : (prefixWord ++ tailWord_5554802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554802).length < 2 ^ (prefixWord ++ tailWord_5554802).sum := by decide
  have hdescent : baseEnd_5554802 < baseStart_5554802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554821 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_5554821 : Nat := 118140960795 + 5554821 * 2 ^ 59
def prefixEnd_5554821 : Nat := 4983230072969 + 3 ^ 40 * 5554821 * 2
def baseEnd_5554821 : Nat := 2852293122688716470991349

theorem tailTrace_5554821 : CollatzResearch.WordTrace tailWord_5554821 prefixEnd_5554821 2852293122688716470991349 := by
  unfold tailWord_5554821
  simp only [CollatzResearch.WordTrace]
  refine ⟨202600966208839679743008317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135067310805893119828672211 202600966208839679743008317)
  ·
    refine ⟨75975362328314879903628119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202600966208839679743008317 75975362328314879903628119)
    ·
      refine ⟨113963043492472319855442179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75975362328314879903628119 113963043492472319855442179)
      ·
        refine ⟨170944565238708479783163269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113963043492472319855442179 170944565238708479783163269)
        ·
          refine ⟨32052105982257839959343113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170944565238708479783163269 32052105982257839959343113)
          ·
            refine ⟨24039079486693379969507335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32052105982257839959343113 24039079486693379969507335)
            ·
              refine ⟨36058619230040069954261003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24039079486693379969507335 36058619230040069954261003)
              ·
                refine ⟨54087928845060104931391505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36058619230040069954261003 54087928845060104931391505)
                ·
                  refine ⟨40565946633795078698543629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54087928845060104931391505 40565946633795078698543629)
                  ·
                    refine ⟨15212229987673154511953861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40565946633795078698543629 15212229987673154511953861)
                    ·
                      refine ⟨2852293122688716470991349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15212229987673154511953861 2852293122688716470991349)
                      ·
                        rfl

theorem cell23_5554821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_5554821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554821 prefixEnd_5554821 := by exact prefixLift 5554821
  have htrace : WordTrace (prefixWord ++ tailWord_5554821) baseStart_5554821 baseEnd_5554821 := by
    simpa [prefixWord, tailWord_5554821, baseEnd_5554821] using wordTrace_append hprefix tailTrace_5554821
  have hstable : (prefixWord ++ tailWord_5554821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554821).length < 2 ^ (prefixWord ++ tailWord_5554821).sum := by decide
  have hdescent : baseEnd_5554821 < baseStart_5554821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554841 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 2, 4, 3]
def baseStart_5554841 : Nat := 118140960795 + 5554841 * 2 ^ 59
def prefixEnd_5554841 : Nat := 4983230072969 + 3 ^ 40 * 5554841 * 2
def baseEnd_5554841 : Nat := 2852303392301806392741257

theorem tailTrace_5554841 : CollatzResearch.WordTrace tailWord_5554841 prefixEnd_5554841 2852303392301806392741257 := by
  unfold tailWord_5554841
  simp only [CollatzResearch.WordTrace]
  refine ⟨202601695668767223158736377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135067797112511482105824251 202601695668767223158736377)
  ·
    refine ⟨151951271751575417369052283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202601695668767223158736377 151951271751575417369052283)
    ·
      refine ⟨227926907627363126053578425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151951271751575417369052283 227926907627363126053578425)
      ·
        refine ⟨170945180720522344540183819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227926907627363126053578425 170945180720522344540183819)
        ·
          refine ⟨256417771080783516810275729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170945180720522344540183819 256417771080783516810275729)
          ·
            refine ⟨192313328310587637607706797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256417771080783516810275729 192313328310587637607706797)
            ·
              refine ⟨72117498116470364102890049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192313328310587637607706797 72117498116470364102890049)
              ·
                refine ⟨54088123587352773077167537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72117498116470364102890049 54088123587352773077167537)
                ·
                  refine ⟨40566092690514579807875653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54088123587352773077167537 40566092690514579807875653)
                  ·
                    refine ⟨7606142379471483713976685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40566092690514579807875653 7606142379471483713976685)
                    ·
                      refine ⟨2852303392301806392741257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7606142379471483713976685 2852303392301806392741257)
                      ·
                        rfl

theorem cell23_5554841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_5554841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554841 prefixEnd_5554841 := by exact prefixLift 5554841
  have htrace : WordTrace (prefixWord ++ tailWord_5554841) baseStart_5554841 baseEnd_5554841 := by
    simpa [prefixWord, tailWord_5554841, baseEnd_5554841] using wordTrace_append hprefix tailTrace_5554841
  have hstable : (prefixWord ++ tailWord_5554841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554841).length < 2 ^ (prefixWord ++ tailWord_5554841).sum := by decide
  have hdescent : baseEnd_5554841 < baseStart_5554841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554878 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 7]
def baseStart_5554878 : Nat := 118140960795 + 5554878 * 2 ^ 59
def prefixEnd_5554878 : Nat := 4983230072969 + 3 ^ 40 * 5554878 * 2
def baseEnd_5554878 : Nat := 316924710120669194219843

theorem tailTrace_5554878 : CollatzResearch.WordTrace tailWord_5554878 prefixEnd_5554878 316924710120669194219843 := by
  unfold tailWord_5554878
  simp only [CollatzResearch.WordTrace]
  refine ⟨25325380646204147309729161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135068696779755452318555525 25325380646204147309729161)
  ·
    refine ⟨18994035484653110482296871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25325380646204147309729161 18994035484653110482296871)
    ·
      refine ⟨28491053226979665723445307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18994035484653110482296871 28491053226979665723445307)
      ·
        refine ⟨42736579840469498585167961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28491053226979665723445307 42736579840469498585167961)
        ·
          refine ⟨32052434880352123938875971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42736579840469498585167961 32052434880352123938875971)
          ·
            refine ⟨48078652320528185908313957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32052434880352123938875971 48078652320528185908313957)
            ·
              refine ⟨9014747310099034857808867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48078652320528185908313957 9014747310099034857808867)
              ·
                refine ⟨13522120965148552286713301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9014747310099034857808867 13522120965148552286713301)
                ·
                  refine ⟨316924710120669194219843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13522120965148552286713301 316924710120669194219843)
                  ·
                    rfl

theorem cell23_5554878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_5554878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554878 prefixEnd_5554878 := by exact prefixLift 5554878
  have htrace : WordTrace (prefixWord ++ tailWord_5554878) baseStart_5554878 baseEnd_5554878 := by
    simpa [prefixWord, tailWord_5554878, baseEnd_5554878] using wordTrace_append hprefix tailTrace_5554878
  have hstable : (prefixWord ++ tailWord_5554878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554878).length < 2 ^ (prefixWord ++ tailWord_5554878).sum := by decide
  have hdescent : baseEnd_5554878 < baseStart_5554878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554888 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_5554888 : Nat := 118140960795 + 5554888 * 2 ^ 59
def prefixEnd_5554888 : Nat := 4983230072969 + 3 ^ 40 * 5554888 * 2
def baseEnd_5554888 : Nat := 2852327525892567708853541

theorem tailTrace_5554888 : CollatzResearch.WordTrace tailWord_5554888 prefixEnd_5554888 2852327525892567708853541 := by
  unfold tailWord_5554888
  simp only [CollatzResearch.WordTrace]
  refine ⟨101301704949798475092848659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135068939933064633457131545 101301704949798475092848659)
  ·
    refine ⟨151952557424697712639272989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101301704949798475092848659 151952557424697712639272989)
    ·
      refine ⟨56982209034261642239727371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151952557424697712639272989 56982209034261642239727371)
      ·
        refine ⟨85473313551392463359591057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56982209034261642239727371 85473313551392463359591057)
        ·
          refine ⟨64104985163544347519693293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85473313551392463359591057 64104985163544347519693293)
          ·
            refine ⟨24039369436329130319884985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64104985163544347519693293 24039369436329130319884985)
            ·
              refine ⟨18029527077246847739913739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24039369436329130319884985 18029527077246847739913739)
              ·
                refine ⟨27044290615870271609870609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18029527077246847739913739 27044290615870271609870609)
                ·
                  refine ⟨20283217961902703707402957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27044290615870271609870609 20283217961902703707402957)
                  ·
                    refine ⟨7606206735713513890276109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20283217961902703707402957 7606206735713513890276109)
                    ·
                      refine ⟨2852327525892567708853541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7606206735713513890276109 2852327525892567708853541)
                      ·
                        rfl

theorem cell23_5554888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_5554888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554888 prefixEnd_5554888 := by exact prefixLift 5554888
  have htrace : WordTrace (prefixWord ++ tailWord_5554888) baseStart_5554888 baseEnd_5554888 := by
    simpa [prefixWord, tailWord_5554888, baseEnd_5554888] using wordTrace_append hprefix tailTrace_5554888
  have hstable : (prefixWord ++ tailWord_5554888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554888).length < 2 ^ (prefixWord ++ tailWord_5554888).sum := by decide
  have hdescent : baseEnd_5554888 < baseStart_5554888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554928 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 4]
def baseStart_5554928 : Nat := 118140960795 + 5554928 * 2 ^ 59
def prefixEnd_5554928 : Nat := 4983230072969 + 3 ^ 40 * 5554928 * 2
def baseEnd_5554928 : Nat := 2852348065118747552353357

theorem tailTrace_5554928 : CollatzResearch.WordTrace tailWord_5554928 prefixEnd_5554928 2852348065118747552353357 := by
  unfold tailWord_5554928
  simp only [CollatzResearch.WordTrace]
  refine ⟨101302434409726018508576719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135069912546301358011435625 101302434409726018508576719)
  ·
    refine ⟨151953651614589027762865079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101302434409726018508576719 151953651614589027762865079)
    ·
      refine ⟨227930477421883541644297619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151953651614589027762865079 227930477421883541644297619)
      ·
        refine ⟨341895716132825312466446429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227930477421883541644297619 341895716132825312466446429)
        ·
          refine ⟨128210893549809492174917411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341895716132825312466446429 128210893549809492174917411)
          ·
            refine ⟨192316340324714238262376117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128210893549809492174917411 192316340324714238262376117)
            ·
              refine ⟨18029656905441959837097761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192316340324714238262376117 18029656905441959837097761)
              ·
                refine ⟨13522242679081469877823321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18029656905441959837097761 13522242679081469877823321)
                ·
                  refine ⟨10141682009311102408367491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13522242679081469877823321 10141682009311102408367491)
                  ·
                    refine ⟨15212523013966653612551237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10141682009311102408367491 15212523013966653612551237)
                    ·
                      refine ⟨2852348065118747552353357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15212523013966653612551237 2852348065118747552353357)
                      ·
                        rfl

theorem cell23_5554928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_5554928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554928 prefixEnd_5554928 := by exact prefixLift 5554928
  have htrace : WordTrace (prefixWord ++ tailWord_5554928) baseStart_5554928 baseEnd_5554928 := by
    simpa [prefixWord, tailWord_5554928, baseEnd_5554928] using wordTrace_append hprefix tailTrace_5554928
  have hstable : (prefixWord ++ tailWord_5554928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554928).length < 2 ^ (prefixWord ++ tailWord_5554928).sum := by decide
  have hdescent : baseEnd_5554928 < baseStart_5554928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554965 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_5554965 : Nat := 118140960795 + 5554965 * 2 ^ 59
def prefixEnd_5554965 : Nat := 4983230072969 + 3 ^ 40 * 5554965 * 2
def baseEnd_5554965 : Nat := 2852367063902963907590687

theorem tailTrace_5554965 : CollatzResearch.WordTrace tailWord_5554965 prefixEnd_5554965 2852367063902963907590687 := by
  unfold tailWord_5554965
  simp only [CollatzResearch.WordTrace]
  refine ⟨202606218320317992336250349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135070812213545328224166899 202606218320317992336250349)
  ·
    refine ⟨75977331870119247126093881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202606218320317992336250349 75977331870119247126093881)
    ·
      refine ⟨56982998902589435344570411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75977331870119247126093881 56982998902589435344570411)
      ·
        refine ⟨85474498353884153016855617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56982998902589435344570411 85474498353884153016855617)
        ·
          refine ⟨64105873765413114762641713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85474498353884153016855617 64105873765413114762641713)
          ·
            refine ⟨48079405324059836071981285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64105873765413114762641713 48079405324059836071981285)
            ·
              refine ⟨9014888498261219263496491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48079405324059836071981285 9014888498261219263496491)
              ·
                refine ⟨13522332747391828895244737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9014888498261219263496491 13522332747391828895244737)
                ·
                  refine ⟨10141749560543871671433553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13522332747391828895244737 10141749560543871671433553)
                  ·
                    refine ⟨7606312170407903753575165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10141749560543871671433553 7606312170407903753575165)
                    ·
                      refine ⟨2852367063902963907590687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7606312170407903753575165 2852367063902963907590687)
                      ·
                        rfl

theorem cell23_5554965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_5554965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554965 prefixEnd_5554965 := by exact prefixLift 5554965
  have htrace : WordTrace (prefixWord ++ tailWord_5554965) baseStart_5554965 baseEnd_5554965 := by
    simpa [prefixWord, tailWord_5554965, baseEnd_5554965] using wordTrace_append hprefix tailTrace_5554965
  have hstable : (prefixWord ++ tailWord_5554965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554965).length < 2 ^ (prefixWord ++ tailWord_5554965).sum := by decide
  have hdescent : baseEnd_5554965 < baseStart_5554965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5554991 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 7]
def baseStart_5554991 : Nat := 118140960795 + 5554991 * 2 ^ 59
def prefixEnd_5554991 : Nat := 4983230072969 + 3 ^ 40 * 5554991 * 2
def baseEnd_5554991 : Nat := 2852380414399980805865567

theorem tailTrace_5554991 : CollatzResearch.WordTrace tailWord_5554991 prefixEnd_5554991 2852380414399980805865567 := by
  unfold tailWord_5554991
  simp only [CollatzResearch.WordTrace]
  refine ⟨202607166618223798776696827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135071444412149199184464551 202607166618223798776696827)
  ·
    refine ⟨303910749927335698165045241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202607166618223798776696827 303910749927335698165045241)
    ·
      refine ⟨227933062445501773623783931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303910749927335698165045241 227933062445501773623783931)
      ·
        refine ⟨341899593668252660435675897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227933062445501773623783931 341899593668252660435675897)
        ·
          refine ⟨256424695251189495326756923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341899593668252660435675897 256424695251189495326756923)
          ·
            refine ⟨384637042876784242990135385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256424695251189495326756923 384637042876784242990135385)
            ·
              refine ⟨288477782157588182242601539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384637042876784242990135385 288477782157588182242601539)
              ·
                refine ⟨432716673236382273363902309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288477782157588182242601539 432716673236382273363902309)
                ·
                  refine ⟨81134376231821676255731683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432716673236382273363902309 81134376231821676255731683)
                  ·
                    refine ⟨121701564347732514383597525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81134376231821676255731683 121701564347732514383597525)
                    ·
                      refine ⟨2852380414399980805865567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121701564347732514383597525 2852380414399980805865567)
                      ·
                        rfl

theorem cell23_5554991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_5554991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5554991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5554991 prefixEnd_5554991 := by exact prefixLift 5554991
  have htrace : WordTrace (prefixWord ++ tailWord_5554991) baseStart_5554991 baseEnd_5554991 := by
    simpa [prefixWord, tailWord_5554991, baseEnd_5554991] using wordTrace_append hprefix tailTrace_5554991
  have hstable : (prefixWord ++ tailWord_5554991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5554991).length < 2 ^ (prefixWord ++ tailWord_5554991).sum := by decide
  have hdescent : baseEnd_5554991 < baseStart_5554991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5554991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555029 : List Nat := [1, 3, 2, 2, 2, 1, 4, 3, 1, 1, 3]
def baseStart_5555029 : Nat := 118140960795 + 5555029 * 2 ^ 59
def prefixEnd_5555029 : Nat := 4983230072969 + 3 ^ 40 * 5555029 * 2
def baseEnd_5555029 : Nat := 2852399926664851657190393

theorem tailTrace_5555029 : CollatzResearch.WordTrace tailWord_5555029 prefixEnd_5555029 2852399926664851657190393 := by
  unfold tailWord_5555029
  simp only [CollatzResearch.WordTrace]
  refine ⟨202608552592086131266580141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135072368394724087511053427 202608552592086131266580141)
  ·
    refine ⟨75978207222032299224967553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202608552592086131266580141 75978207222032299224967553)
    ·
      refine ⟨56983655416524224418725665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75978207222032299224967553 56983655416524224418725665)
      ·
        refine ⟨42737741562393168314044249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56983655416524224418725665 42737741562393168314044249)
        ·
          refine ⟨32053306171794876235533187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42737741562393168314044249 32053306171794876235533187)
          ·
            refine ⟨48079959257692314353299781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32053306171794876235533187 48079959257692314353299781)
            ·
              refine ⟨9014992360817308941243709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48079959257692314353299781 9014992360817308941243709)
              ·
                refine ⟨3380622135306490852966391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9014992360817308941243709 3380622135306490852966391)
                ·
                  refine ⟨5070933202959736279449587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3380622135306490852966391 5070933202959736279449587)
                  ·
                    refine ⟨7606399804439604419174381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5070933202959736279449587 7606399804439604419174381)
                    ·
                      refine ⟨2852399926664851657190393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7606399804439604419174381 2852399926664851657190393)
                      ·
                        rfl

theorem cell23_5555029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_5555029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555029 prefixEnd_5555029 := by exact prefixLift 5555029
  have htrace : WordTrace (prefixWord ++ tailWord_5555029) baseStart_5555029 baseEnd_5555029 := by
    simpa [prefixWord, tailWord_5555029, baseEnd_5555029] using wordTrace_append hprefix tailTrace_5555029
  have hstable : (prefixWord ++ tailWord_5555029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555029).length < 2 ^ (prefixWord ++ tailWord_5555029).sum := by decide
  have hdescent : baseEnd_5555029 < baseStart_5555029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555062 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_5555062 : Nat := 118140960795 + 5555062 * 2 ^ 59
def prefixEnd_5555062 : Nat := 4983230072969 + 3 ^ 40 * 5555062 * 2
def baseEnd_5555062 : Nat := 950805623842150009359247

theorem tailTrace_5555062 : CollatzResearch.WordTrace tailWord_5555062 prefixEnd_5555062 950805623842150009359247 := by
  unfold tailWord_5555062
  simp only [CollatzResearch.WordTrace]
  refine ⟨12663109762560411118908215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135073170800644385268354293 12663109762560411118908215)
  ·
    refine ⟨18994664643840616678362323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12663109762560411118908215 18994664643840616678362323)
    ·
      refine ⟨28491996965760925017543485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18994664643840616678362323 28491996965760925017543485)
      ·
        refine ⟨10684498862160346881578807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28491996965760925017543485 10684498862160346881578807)
        ·
          refine ⟨16026748293240520322368211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10684498862160346881578807 16026748293240520322368211)
          ·
            refine ⟨24040122439860780483552317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16026748293240520322368211 24040122439860780483552317)
            ·
              refine ⟨9015045914947792681332119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24040122439860780483552317 9015045914947792681332119)
              ·
                refine ⟨13522568872421689021998179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9015045914947792681332119 13522568872421689021998179)
                ·
                  refine ⟨20283853308632533532997269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13522568872421689021998179 20283853308632533532997269)
                  ·
                    refine ⟨950805623842150009359247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20283853308632533532997269 950805623842150009359247)
                    ·
                      rfl

theorem cell23_5555062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_5555062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555062 prefixEnd_5555062 := by exact prefixLift 5555062
  have htrace : WordTrace (prefixWord ++ tailWord_5555062) baseStart_5555062 baseEnd_5555062 := by
    simpa [prefixWord, tailWord_5555062, baseEnd_5555062] using wordTrace_append hprefix tailTrace_5555062
  have hstable : (prefixWord ++ tailWord_5555062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555062).length < 2 ^ (prefixWord ++ tailWord_5555062).sum := by decide
  have hdescent : baseEnd_5555062 < baseStart_5555062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555065 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 1, 2, 4]
def baseStart_5555065 : Nat := 118140960795 + 5555065 * 2 ^ 59
def prefixEnd_5555065 : Nat := 4983230072969 + 3 ^ 40 * 5555065 * 2
def baseEnd_5555065 : Nat := 2852418411968413516340227

theorem tailTrace_5555065 : CollatzResearch.WordTrace tailWord_5555065 prefixEnd_5555065 2852418411968413516340227 := by
  unfold tailWord_5555065
  simp only [CollatzResearch.WordTrace]
  refine ⟨202609865619955709414890649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135073243746637139609927099 202609865619955709414890649)
  ·
    refine ⟨151957399214966782061167987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202609865619955709414890649 151957399214966782061167987)
    ·
      refine ⟨227936098822450173091751981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151957399214966782061167987 227936098822450173091751981)
      ·
        refine ⟨85476037058418814909406993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227936098822450173091751981 85476037058418814909406993)
        ·
          refine ⟨64107027793814111182055245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85476037058418814909406993 64107027793814111182055245)
          ·
            refine ⟨24040135422680291693270717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64107027793814111182055245 24040135422680291693270717)
            ·
              refine ⟨9015050783505109384976519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24040135422680291693270717 9015050783505109384976519)
              ·
                refine ⟨13522576175257664077464779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9015050783505109384976519 13522576175257664077464779)
                ·
                  refine ⟨20283864262886496116197169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13522576175257664077464779 20283864262886496116197169)
                  ·
                    refine ⟨15212898197164872087147877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20283864262886496116197169 15212898197164872087147877)
                    ·
                      refine ⟨2852418411968413516340227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15212898197164872087147877 2852418411968413516340227)
                      ·
                        rfl

theorem cell23_5555065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_5555065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555065 prefixEnd_5555065 := by exact prefixLift 5555065
  have htrace : WordTrace (prefixWord ++ tailWord_5555065) baseStart_5555065 baseEnd_5555065 := by
    simpa [prefixWord, tailWord_5555065, baseEnd_5555065] using wordTrace_append hprefix tailTrace_5555065
  have hstable : (prefixWord ++ tailWord_5555065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555065).length < 2 ^ (prefixWord ++ tailWord_5555065).sum := by decide
  have hdescent : baseEnd_5555065 < baseStart_5555065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555103 : List Nat := [1, 1, 2, 5, 2, 2, 3, 2, 1, 2, 2]
def baseStart_5555103 : Nat := 118140960795 + 5555103 * 2 ^ 59
def prefixEnd_5555103 : Nat := 4983230072969 + 3 ^ 40 * 5555103 * 2
def baseEnd_5555103 : Nat := 2852437924233284367665053

theorem tailTrace_5555103 : CollatzResearch.WordTrace tailWord_5555103 prefixEnd_5555103 2852437924233284367665053 := by
  unfold tailWord_5555103
  simp only [CollatzResearch.WordTrace]
  refine ⟨202611251593818041904773963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135074167729212027936515975 202611251593818041904773963)
  ·
    refine ⟨303916877390727062857160945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202611251593818041904773963 303916877390727062857160945)
    ·
      refine ⟨227937658043045297142870709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303916877390727062857160945 227937658043045297142870709)
      ·
        refine ⟨21369155441535496607144129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 227937658043045297142870709 21369155441535496607144129)
        ·
          refine ⟨16026866581151622455358097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21369155441535496607144129 16026866581151622455358097)
          ·
            refine ⟨12020149935863716841518573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16026866581151622455358097 12020149935863716841518573)
            ·
              refine ⟨4507556225948893815569465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12020149935863716841518573 4507556225948893815569465)
              ·
                refine ⟨3380667169461670361677099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4507556225948893815569465 3380667169461670361677099)
                ·
                  refine ⟨5071000754192505542515649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3380667169461670361677099 5071000754192505542515649)
                  ·
                    refine ⟨3803250565644379156886737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5071000754192505542515649 3803250565644379156886737)
                    ·
                      refine ⟨2852437924233284367665053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3803250565644379156886737 2852437924233284367665053)
                      ·
                        rfl

theorem cell23_5555103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_5555103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555103 prefixEnd_5555103 := by exact prefixLift 5555103
  have htrace : WordTrace (prefixWord ++ tailWord_5555103) baseStart_5555103 baseEnd_5555103 := by
    simpa [prefixWord, tailWord_5555103, baseEnd_5555103] using wordTrace_append hprefix tailTrace_5555103
  have hstable : (prefixWord ++ tailWord_5555103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555103).length < 2 ^ (prefixWord ++ tailWord_5555103).sum := by decide
  have hdescent : baseEnd_5555103 < baseStart_5555103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555129 : List Nat := [1, 2, 1, 4, 2, 2, 3, 2, 1, 3, 2]
def baseStart_5555129 : Nat := 118140960795 + 5555129 * 2 ^ 59
def prefixEnd_5555129 : Nat := 4983230072969 + 3 ^ 40 * 5555129 * 2
def baseEnd_5555129 : Nat := 2852451274730301265939933

theorem tailTrace_5555129 : CollatzResearch.WordTrace tailWord_5555129 prefixEnd_5555129 2852451274730301265939933 := by
  unfold tailWord_5555129
  simp only [CollatzResearch.WordTrace]
  refine ⟨202612199891723848345220441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135074799927815898896813627 202612199891723848345220441)
  ·
    refine ⟨151959149918792886258915331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202612199891723848345220441 151959149918792886258915331)
    ·
      refine ⟨227938724878189329388372997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151959149918792886258915331 227938724878189329388372997)
      ·
        refine ⟨42738510914660499260319937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227938724878189329388372997 42738510914660499260319937)
        ·
          refine ⟨32053883185995374445239953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42738510914660499260319937 32053883185995374445239953)
          ·
            refine ⟨24040412389496530833929965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32053883185995374445239953 24040412389496530833929965)
            ·
              refine ⟨9015154646061199062723737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24040412389496530833929965 9015154646061199062723737)
              ·
                refine ⟨6761365984545899297042803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9015154646061199062723737 6761365984545899297042803)
                ·
                  refine ⟨10142048976818848945564205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6761365984545899297042803 10142048976818848945564205)
                  ·
                    refine ⟨3803268366307068354586577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10142048976818848945564205 3803268366307068354586577)
                    ·
                      refine ⟨2852451274730301265939933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3803268366307068354586577 2852451274730301265939933)
                      ·
                        rfl

theorem cell23_5555129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_5555129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555129 prefixEnd_5555129 := by exact prefixLift 5555129
  have htrace : WordTrace (prefixWord ++ tailWord_5555129) baseStart_5555129 baseEnd_5555129 := by
    simpa [prefixWord, tailWord_5555129, baseEnd_5555129] using wordTrace_append hprefix tailTrace_5555129
  have hstable : (prefixWord ++ tailWord_5555129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555129).length < 2 ^ (prefixWord ++ tailWord_5555129).sum := by decide
  have hdescent : baseEnd_5555129 < baseStart_5555129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555168 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 8]
def baseStart_5555168 : Nat := 118140960795 + 5555168 * 2 ^ 59
def prefixEnd_5555168 : Nat := 4983230072969 + 3 ^ 40 * 5555168 * 2
def baseEnd_5555168 : Nat := 2852471300475826613352253

theorem tailTrace_5555168 : CollatzResearch.WordTrace tailWord_5555168 prefixEnd_5555168 2852471300475826613352253 := by
  unfold tailWord_5555168
  simp only [CollatzResearch.WordTrace]
  refine ⟨101306811169291279002945079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135075748225721705337260105 101306811169291279002945079)
  ·
    refine ⟨151960216753936918504417619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101306811169291279002945079 151960216753936918504417619)
    ·
      refine ⟨227940325130905377756626429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151960216753936918504417619 227940325130905377756626429)
      ·
        refine ⟨85477621924089516658734911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227940325130905377756626429 85477621924089516658734911)
        ·
          refine ⟨128216432886134274988102367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85477621924089516658734911 128216432886134274988102367)
          ·
            refine ⟨192324649329201412482153551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128216432886134274988102367 192324649329201412482153551)
            ·
              refine ⟨288486973993802118723230327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192324649329201412482153551 288486973993802118723230327)
              ·
                refine ⟨432730460990703178084845491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288486973993802118723230327 432730460990703178084845491)
                ·
                  refine ⟨649095691486054767127268237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 432730460990703178084845491 649095691486054767127268237)
                  ·
                    refine ⟨243410884307270537672725589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 649095691486054767127268237 243410884307270537672725589)
                    ·
                      refine ⟨2852471300475826613352253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 243410884307270537672725589 2852471300475826613352253)
                      ·
                        rfl

theorem cell23_5555168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_5555168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555168 prefixEnd_5555168 := by exact prefixLift 5555168
  have htrace : WordTrace (prefixWord ++ tailWord_5555168) baseStart_5555168 baseEnd_5555168 := by
    simpa [prefixWord, tailWord_5555168, baseEnd_5555168] using wordTrace_append hprefix tailTrace_5555168
  have hstable : (prefixWord ++ tailWord_5555168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555168).length < 2 ^ (prefixWord ++ tailWord_5555168).sum := by decide
  have hdescent : baseEnd_5555168 < baseStart_5555168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555182 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 7]
def baseStart_5555182 : Nat := 118140960795 + 5555182 * 2 ^ 59
def prefixEnd_5555182 : Nat := 4983230072969 + 3 ^ 40 * 5555182 * 2
def baseEnd_5555182 : Nat := 316942054356109950953021

theorem tailTrace_5555182 : CollatzResearch.WordTrace tailWord_5555182 prefixEnd_5555182 316942054356109950953021 := by
  unfold tailWord_5555182
  simp only [CollatzResearch.WordTrace]
  refine ⟨25326766620066479799612475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135076088640354558931266533 25326766620066479799612475)
  ·
    refine ⟨37990149930099719699418713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25326766620066479799612475 37990149930099719699418713)
    ·
      refine ⟨28492612447574789774564035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37990149930099719699418713 28492612447574789774564035)
      ·
        refine ⟨42738918671362184661846053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28492612447574789774564035 42738918671362184661846053)
        ·
          refine ⟨8013547250880409624096135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42738918671362184661846053 8013547250880409624096135)
          ·
            refine ⟨12020320876320614436144203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8013547250880409624096135 12020320876320614436144203)
            ·
              refine ⟨18030481314480921654216305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12020320876320614436144203 18030481314480921654216305)
              ·
                refine ⟨13522860985860691240662229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18030481314480921654216305 13522860985860691240662229)
                ·
                  refine ⟨316942054356109950953021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13522860985860691240662229 316942054356109950953021)
                  ·
                    rfl

theorem cell23_5555182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_5555182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555182 prefixEnd_5555182 := by exact prefixLift 5555182
  have htrace : WordTrace (prefixWord ++ tailWord_5555182) baseStart_5555182 baseEnd_5555182 := by
    simpa [prefixWord, tailWord_5555182, baseEnd_5555182] using wordTrace_append hprefix tailTrace_5555182
  have hstable : (prefixWord ++ tailWord_5555182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555182).length < 2 ^ (prefixWord ++ tailWord_5555182).sum := by decide
  have hdescent : baseEnd_5555182 < baseStart_5555182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555319 : List Nat := [1, 1, 3, 1, 1, 4, 5, 1, 1, 5]
def baseStart_5555319 : Nat := 118140960795 + 5555319 * 2 ^ 59
def prefixEnd_5555319 : Nat := 4983230072969 + 3 ^ 40 * 5555319 * 2
def baseEnd_5555319 : Nat := 950849612018218507521353

theorem tailTrace_5555319 : CollatzResearch.WordTrace tailWord_5555319 prefixEnd_5555319 950849612018218507521353 := by
  unfold tailWord_5555319
  simp only [CollatzResearch.WordTrace]
  refine ⟨202619129761035510794637011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135079419840690340529758007 202619129761035510794637011)
  ·
    refine ⟨303928694641553266191955517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202619129761035510794637011 303928694641553266191955517)
    ·
      refine ⟨113973260490582474821983319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303928694641553266191955517 113973260490582474821983319)
      ·
        refine ⟨170959890735873712232974979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113973260490582474821983319 170959890735873712232974979)
        ·
          refine ⟨256439836103810568349462469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170959890735873712232974979 256439836103810568349462469)
          ·
            refine ⟨48082469269464481565524213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256439836103810568349462469 48082469269464481565524213)
            ·
              refine ⟨4507731494012295146767895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48082469269464481565524213 4507731494012295146767895)
              ·
                refine ⟨6761597241018442720151843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4507731494012295146767895 6761597241018442720151843)
                ·
                  refine ⟨10142395861527664080227765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6761597241018442720151843 10142395861527664080227765)
                  ·
                    refine ⟨950849612018218507521353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10142395861527664080227765 950849612018218507521353)
                    ·
                      rfl

theorem cell23_5555319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_5555319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555319 prefixEnd_5555319 := by exact prefixLift 5555319
  have htrace : WordTrace (prefixWord ++ tailWord_5555319) baseStart_5555319 baseEnd_5555319 := by
    simpa [prefixWord, tailWord_5555319, baseEnd_5555319] using wordTrace_append hprefix tailTrace_5555319
  have hstable : (prefixWord ++ tailWord_5555319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555319).length < 2 ^ (prefixWord ++ tailWord_5555319).sum := by decide
  have hdescent : baseEnd_5555319 < baseStart_5555319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555333 : List Nat := [1, 3, 1, 1, 6, 1, 1, 4, 1, 1, 3]
def baseStart_5555333 : Nat := 118140960795 + 5555333 * 2 ^ 59
def prefixEnd_5555333 : Nat := 4983230072969 + 3 ^ 40 * 5555333 * 2
def baseEnd_5555333 : Nat := 2852556024783818467788995

theorem tailTrace_5555333 : CollatzResearch.WordTrace tailWord_5555333 prefixEnd_5555333 2852556024783818467788995 := by
  unfold tailWord_5555333
  simp only [CollatzResearch.WordTrace]
  refine ⟨202619640382984791185646653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135079760255323194123764435 202619640382984791185646653)
  ·
    refine ⟨75982365143619296694617495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202619640382984791185646653 75982365143619296694617495)
    ·
      refine ⟨113973547715428945041926243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75982365143619296694617495 113973547715428945041926243)
      ·
        refine ⟨170960321573143417562889365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113973547715428945041926243 170960321573143417562889365)
        ·
          refine ⟨8013765073741097698260439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 170960321573143417562889365 8013765073741097698260439)
          ·
            refine ⟨12020647610611646547390659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8013765073741097698260439 12020647610611646547390659)
            ·
              refine ⟨18030971415917469821085989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12020647610611646547390659 18030971415917469821085989)
              ·
                refine ⟨3380807140484525591453623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18030971415917469821085989 3380807140484525591453623)
                ·
                  refine ⟨5071210710726788387180435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3380807140484525591453623 5071210710726788387180435)
                  ·
                    refine ⟨7606816066090182580770653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5071210710726788387180435 7606816066090182580770653)
                    ·
                      refine ⟨2852556024783818467788995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7606816066090182580770653 2852556024783818467788995)
                      ·
                        rfl

theorem cell23_5555333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 1, 1, 3].length) (baseStart_5555333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555333 prefixEnd_5555333 := by exact prefixLift 5555333
  have htrace : WordTrace (prefixWord ++ tailWord_5555333) baseStart_5555333 baseEnd_5555333 := by
    simpa [prefixWord, tailWord_5555333, baseEnd_5555333] using wordTrace_append hprefix tailTrace_5555333
  have hstable : (prefixWord ++ tailWord_5555333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555333).length < 2 ^ (prefixWord ++ tailWord_5555333).sum := by decide
  have hdescent : baseEnd_5555333 < baseStart_5555333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555339 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 7, 2, 2]
def baseStart_5555339 : Nat := 118140960795 + 5555339 * 2 ^ 59
def prefixEnd_5555339 : Nat := 4983230072969 + 3 ^ 40 * 5555339 * 2
def baseEnd_5555339 : Nat := 2852559105667745444313967

theorem tailTrace_5555339 : CollatzResearch.WordTrace tailWord_5555339 prefixEnd_5555339 2852559105667745444313967 := by
  unfold tailWord_5555339
  simp only [CollatzResearch.WordTrace]
  refine ⟨202619859220963054210365071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135079906147308702806910047 202619859220963054210365071)
  ·
    refine ⟨303929788831444581315547607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202619859220963054210365071 303929788831444581315547607)
    ·
      refine ⟨455894683247166871973321411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303929788831444581315547607 455894683247166871973321411)
      ·
        refine ⟨683842024870750307959982117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455894683247166871973321411 683842024870750307959982117)
        ·
          refine ⟨128220379663265682742496647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 683842024870750307959982117 128220379663265682742496647)
          ·
            refine ⟨192330569494898524113744971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128220379663265682742496647 192330569494898524113744971)
            ·
              refine ⟨288495854242347786170617457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192330569494898524113744971 288495854242347786170617457)
              ·
                refine ⟨216371890681760839627963093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288495854242347786170617457 216371890681760839627963093)
                ·
                  refine ⟨5071216187853769678780385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 216371890681760839627963093 5071216187853769678780385)
                  ·
                    refine ⟨3803412140890327259085289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5071216187853769678780385 3803412140890327259085289)
                    ·
                      refine ⟨2852559105667745444313967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3803412140890327259085289 2852559105667745444313967)
                      ·
                        rfl

theorem cell23_5555339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 2, 2].length) (baseStart_5555339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555339 prefixEnd_5555339 := by exact prefixLift 5555339
  have htrace : WordTrace (prefixWord ++ tailWord_5555339) baseStart_5555339 baseEnd_5555339 := by
    simpa [prefixWord, tailWord_5555339, baseEnd_5555339] using wordTrace_append hprefix tailTrace_5555339
  have hstable : (prefixWord ++ tailWord_5555339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555339).length < 2 ^ (prefixWord ++ tailWord_5555339).sum := by decide
  have hdescent : baseEnd_5555339 < baseStart_5555339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555356 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_5555356 : Nat := 118140960795 + 5555356 * 2 ^ 59
def prefixEnd_5555356 : Nat := 4983230072969 + 3 ^ 40 * 5555356 * 2
def baseEnd_5555356 : Nat := 2852567834838871877801389

theorem tailTrace_5555356 : CollatzResearch.WordTrace tailWord_5555356 prefixEnd_5555356 2852567834838871877801389 := by
  unfold tailWord_5555356
  simp only [CollatzResearch.WordTrace]
  refine ⟨101310239630950733056866961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135080319507934310742489281 101310239630950733056866961)
  ·
    refine ⟨75982679723213049792650221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101310239630950733056866961 75982679723213049792650221)
    ·
      refine ⟨28493504896204893672243833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75982679723213049792650221 28493504896204893672243833)
      ·
        refine ⟨21370128672153670254182875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28493504896204893672243833 21370128672153670254182875)
        ·
          refine ⟨32055193008230505381274313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21370128672153670254182875 32055193008230505381274313)
          ·
            refine ⟨24041394756172879035955735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32055193008230505381274313 24041394756172879035955735)
            ·
              refine ⟨36062092134259318553933603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24041394756172879035955735 36062092134259318553933603)
              ·
                refine ⟨54093138201388977830900405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36062092134259318553933603 54093138201388977830900405)
                ·
                  refine ⟨5071231706380216671646913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54093138201388977830900405 5071231706380216671646913)
                  ·
                    refine ⟨3803423779785162503735185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5071231706380216671646913 3803423779785162503735185)
                    ·
                      refine ⟨2852567834838871877801389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3803423779785162503735185 2852567834838871877801389)
                      ·
                        rfl

theorem cell23_5555356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_5555356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555356 prefixEnd_5555356 := by exact prefixLift 5555356
  have htrace : WordTrace (prefixWord ++ tailWord_5555356) baseStart_5555356 baseEnd_5555356 := by
    simpa [prefixWord, tailWord_5555356, baseEnd_5555356] using wordTrace_append hprefix tailTrace_5555356
  have hstable : (prefixWord ++ tailWord_5555356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555356).length < 2 ^ (prefixWord ++ tailWord_5555356).sum := by decide
  have hdescent : baseEnd_5555356 < baseStart_5555356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555372 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 3]
def baseStart_5555372 : Nat := 118140960795 + 5555372 * 2 ^ 59
def prefixEnd_5555372 : Nat := 4983230072969 + 3 ^ 40 * 5555372 * 2
def baseEnd_5555372 : Nat := 2852576050529343815201315

theorem tailTrace_5555372 : CollatzResearch.WordTrace tailWord_5555372 prefixEnd_5555372 2852576050529343815201315 := by
  unfold tailWord_5555372
  simp only [CollatzResearch.WordTrace]
  refine ⟨101310531414921750423158185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135080708553229000564210913 101310531414921750423158185)
  ·
    refine ⟨75982898561191312817368639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101310531414921750423158185 75982898561191312817368639)
    ·
      refine ⟨113974347841786969226052959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75982898561191312817368639 113974347841786969226052959)
      ·
        refine ⟨170961521762680453839079439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113974347841786969226052959 170961521762680453839079439)
        ·
          refine ⟨256442282644020680758619159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170961521762680453839079439 256442282644020680758619159)
          ·
            refine ⟨384663423966031021137928739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256442282644020680758619159 384663423966031021137928739)
            ·
              refine ⟨576995135949046531706893109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384663423966031021137928739 576995135949046531706893109)
              ·
                refine ⟨54093293995223112347521229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 576995135949046531706893109 54093293995223112347521229)
                ·
                  refine ⟨20284985248208667130320461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54093293995223112347521229 20284985248208667130320461)
                  ·
                    refine ⟨7606869468078250173870173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20284985248208667130320461 7606869468078250173870173)
                    ·
                      refine ⟨2852576050529343815201315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7606869468078250173870173 2852576050529343815201315)
                      ·
                        rfl

theorem cell23_5555372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_5555372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555372 prefixEnd_5555372 := by exact prefixLift 5555372
  have htrace : WordTrace (prefixWord ++ tailWord_5555372) baseStart_5555372 baseEnd_5555372 := by
    simpa [prefixWord, tailWord_5555372, baseEnd_5555372] using wordTrace_append hprefix tailTrace_5555372
  have hstable : (prefixWord ++ tailWord_5555372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555372).length < 2 ^ (prefixWord ++ tailWord_5555372).sum := by decide
  have hdescent : baseEnd_5555372 < baseStart_5555372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555390 : List Nat := [4, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2]
def baseStart_5555390 : Nat := 118140960795 + 5555390 * 2 ^ 59
def prefixEnd_5555390 : Nat := 4983230072969 + 3 ^ 40 * 5555390 * 2
def baseEnd_5555390 : Nat := 2852585293181124744776233

theorem tailTrace_5555390 : CollatzResearch.WordTrace tailWord_5555390 prefixEnd_5555390 2852585293181124744776233 := by
  unfold tailWord_5555390
  simp only [CollatzResearch.WordTrace]
  refine ⟨25327714917972286240058953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135081146229185526613647749 25327714917972286240058953)
  ·
    refine ⟨18995786188479214680044215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25327714917972286240058953 18995786188479214680044215)
    ·
      refine ⟨28493679282718822020066323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18995786188479214680044215 28493679282718822020066323)
      ·
        refine ⟨42740518924078233030099485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28493679282718822020066323 42740518924078233030099485)
        ·
          refine ⟨16027694596529337386287307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42740518924078233030099485 16027694596529337386287307)
          ·
            refine ⟨24041541894794006079430961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16027694596529337386287307 24041541894794006079430961)
            ·
              refine ⟨18031156421095504559573221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24041541894794006079430961 18031156421095504559573221)
              ·
                refine ⟨3380841828955407104919979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18031156421095504559573221 3380841828955407104919979)
                ·
                  refine ⟨5071262743433110657379969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3380841828955407104919979 5071262743433110657379969)
                  ·
                    refine ⟨3803447057574832993034977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5071262743433110657379969 3803447057574832993034977)
                    ·
                      refine ⟨2852585293181124744776233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3803447057574832993034977 2852585293181124744776233)
                      ·
                        rfl

theorem cell23_5555390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_5555390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555390 prefixEnd_5555390 := by exact prefixLift 5555390
  have htrace : WordTrace (prefixWord ++ tailWord_5555390) baseStart_5555390 baseEnd_5555390 := by
    simpa [prefixWord, tailWord_5555390, baseEnd_5555390] using wordTrace_append hprefix tailTrace_5555390
  have hstable : (prefixWord ++ tailWord_5555390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555390).length < 2 ^ (prefixWord ++ tailWord_5555390).sum := by decide
  have hdescent : baseEnd_5555390 < baseStart_5555390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555399 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 5, 3, 2]
def baseStart_5555399 : Nat := 118140960795 + 5555399 * 2 ^ 59
def prefixEnd_5555399 : Nat := 4983230072969 + 3 ^ 40 * 5555399 * 2
def baseEnd_5555399 : Nat := 2852589914507015209563691

theorem tailTrace_5555399 : CollatzResearch.WordTrace tailWord_5555399 prefixEnd_5555399 2852589914507015209563691 := by
  unfold tailWord_5555399
  simp only [CollatzResearch.WordTrace]
  refine ⟨202622047600745684457549251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135081365067163789638366167 202622047600745684457549251)
  ·
    refine ⟨303933071401118526686323877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202622047600745684457549251 303933071401118526686323877)
    ·
      refine ⟨56987450887709723753685727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303933071401118526686323877 56987450887709723753685727)
      ·
        refine ⟨85481176331564585630528591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56987450887709723753685727 85481176331564585630528591)
        ·
          refine ⟨128221764497346878445792887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85481176331564585630528591 128221764497346878445792887)
          ·
            refine ⟨192332646746020317668689331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128221764497346878445792887 192332646746020317668689331)
            ·
              refine ⟨288498970119030476503033997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192332646746020317668689331 288498970119030476503033997)
              ·
                refine ⟨108187113794636428688637749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288498970119030476503033997 108187113794636428688637749)
                ·
                  refine ⟨10142541918247165189559789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108187113794636428688637749 10142541918247165189559789)
                  ·
                    refine ⟨3803453219342686946084921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10142541918247165189559789 3803453219342686946084921)
                    ·
                      refine ⟨2852589914507015209563691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3803453219342686946084921 2852589914507015209563691)
                      ·
                        rfl

theorem cell23_5555399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_5555399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555399 prefixEnd_5555399 := by exact prefixLift 5555399
  have htrace : WordTrace (prefixWord ++ tailWord_5555399) baseStart_5555399 baseEnd_5555399 := by
    simpa [prefixWord, tailWord_5555399, baseEnd_5555399] using wordTrace_append hprefix tailTrace_5555399
  have hstable : (prefixWord ++ tailWord_5555399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555399).length < 2 ^ (prefixWord ++ tailWord_5555399).sum := by decide
  have hdescent : baseEnd_5555399 < baseStart_5555399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555506 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2]
def baseStart_5555506 : Nat := 118140960795 + 5555506 * 2 ^ 59
def prefixEnd_5555506 : Nat := 4983230072969 + 3 ^ 40 * 5555506 * 2
def baseEnd_5555506 : Nat := 2852644856937046290925699

theorem tailTrace_5555506 : CollatzResearch.WordTrace tailWord_5555506 prefixEnd_5555506 2852644856937046290925699 := by
  unfold tailWord_5555506
  simp only [CollatzResearch.WordTrace]
  refine ⟨50656487552839510432923593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135083966807572027821129581 50656487552839510432923593)
  ·
    refine ⟨37992365664629632824692695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50656487552839510432923593 37992365664629632824692695)
    ·
      refine ⟨56988548496944449237039043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37992365664629632824692695 56988548496944449237039043)
      ·
        refine ⟨85482822745416673855558565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56988548496944449237039043 85482822745416673855558565)
        ·
          refine ⟨16028029264765626347917231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85482822745416673855558565 16028029264765626347917231)
          ·
            refine ⟨24042043897148439521875847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16028029264765626347917231 24042043897148439521875847)
            ·
              refine ⟨36063065845722659282813771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24042043897148439521875847 36063065845722659282813771)
              ·
                refine ⟨54094598768583988924220657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36063065845722659282813771 54094598768583988924220657)
                ·
                  refine ⟨40570949076437991693165493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54094598768583988924220657 40570949076437991693165493)
                  ·
                    refine ⟨3803526475916061721234265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40570949076437991693165493 3803526475916061721234265)
                    ·
                      refine ⟨2852644856937046290925699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3803526475916061721234265 2852644856937046290925699)
                      ·
                        rfl

theorem cell23_5555506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_5555506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555506 prefixEnd_5555506 := by exact prefixLift 5555506
  have htrace : WordTrace (prefixWord ++ tailWord_5555506) baseStart_5555506 baseEnd_5555506 := by
    simpa [prefixWord, tailWord_5555506, baseEnd_5555506] using wordTrace_append hprefix tailTrace_5555506
  have hstable : (prefixWord ++ tailWord_5555506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555506).length < 2 ^ (prefixWord ++ tailWord_5555506).sum := by decide
  have hdescent : baseEnd_5555506 < baseStart_5555506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555509 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_5555509 : Nat := 118140960795 + 5555509 * 2 ^ 59
def prefixEnd_5555509 : Nat := 4983230072969 + 3 ^ 40 * 5555509 * 2
def baseEnd_5555509 : Nat := 2852646397379009779188185

theorem tailTrace_5555509 : CollatzResearch.WordTrace tailWord_5555509 prefixEnd_5555509 2852646397379009779188185 := by
  unfold tailWord_5555509
  simp only [CollatzResearch.WordTrace]
  refine ⟨202626059630347173244053581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135084039753564782162702387 202626059630347173244053581)
  ·
    refine ⟨75984772361380189966520093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202626059630347173244053581 75984772361380189966520093)
    ·
      refine ⟨28494289635517571237445035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75984772361380189966520093 28494289635517571237445035)
      ·
        refine ⟨42741434453276356856167553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28494289635517571237445035 42741434453276356856167553)
        ·
          refine ⟨32056075839957267642125665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42741434453276356856167553 32056075839957267642125665)
          ·
            refine ⟨24042056879967950731594249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32056075839957267642125665 24042056879967950731594249)
            ·
              refine ⟨18031542659975963048695687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24042056879967950731594249 18031542659975963048695687)
              ·
                refine ⟨27047313989963944573043531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18031542659975963048695687 27047313989963944573043531)
                ·
                  refine ⟨40570970984945916859565297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27047313989963944573043531 40570970984945916859565297)
                  ·
                    refine ⟨30428228238709437644673973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40570970984945916859565297 30428228238709437644673973)
                    ·
                      refine ⟨2852646397379009779188185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30428228238709437644673973 2852646397379009779188185)
                      ·
                        rfl

theorem cell23_5555509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_5555509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555509 prefixEnd_5555509 := by exact prefixLift 5555509
  have htrace : WordTrace (prefixWord ++ tailWord_5555509) baseStart_5555509 baseEnd_5555509 := by
    simpa [prefixWord, tailWord_5555509, baseEnd_5555509] using wordTrace_append hprefix tailTrace_5555509
  have hstable : (prefixWord ++ tailWord_5555509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555509).length < 2 ^ (prefixWord ++ tailWord_5555509).sum := by decide
  have hdescent : baseEnd_5555509 < baseStart_5555509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555512 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 2, 8]
def baseStart_5555512 : Nat := 118140960795 + 5555512 * 2 ^ 59
def prefixEnd_5555512 : Nat := 4983230072969 + 3 ^ 40 * 5555512 * 2
def baseEnd_5555512 : Nat := 950882645940324422483557

theorem tailTrace_5555512 : CollatzResearch.WordTrace tailWord_5555512 prefixEnd_5555512 950882645940324422483557 := by
  unfold tailWord_5555512
  simp only [CollatzResearch.WordTrace]
  refine ⟨101313084524668152378206395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135084112699557536504275193 101313084524668152378206395)
  ·
    refine ⟨151969626787002228567309593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101313084524668152378206395 151969626787002228567309593)
    ·
      refine ⟨113977220090251671425482195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151969626787002228567309593 113977220090251671425482195)
      ·
        refine ⟨170965830135377507138223293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113977220090251671425482195 170965830135377507138223293)
        ·
          refine ⟨64112186300766565176833735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170965830135377507138223293 64112186300766565176833735)
          ·
            refine ⟨96168279451149847765250603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64112186300766565176833735 96168279451149847765250603)
            ·
              refine ⟨144252419176724771647875905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96168279451149847765250603 144252419176724771647875905)
              ·
                refine ⟨108189314382543578735906929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144252419176724771647875905 108189314382543578735906929)
                ·
                  refine ⟨81141985786907684051930197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108189314382543578735906929 81141985786907684051930197)
                  ·
                    refine ⟨950882645940324422483557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81141985786907684051930197 950882645940324422483557)
                    ·
                      rfl

theorem cell23_5555512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_5555512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555512 prefixEnd_5555512 := by exact prefixLift 5555512
  have htrace : WordTrace (prefixWord ++ tailWord_5555512) baseStart_5555512 baseEnd_5555512 := by
    simpa [prefixWord, tailWord_5555512, baseEnd_5555512] using wordTrace_append hprefix tailTrace_5555512
  have hstable : (prefixWord ++ tailWord_5555512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555512).length < 2 ^ (prefixWord ++ tailWord_5555512).sum := by decide
  have hdescent : baseEnd_5555512 < baseStart_5555512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555529 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 5, 4]
def baseStart_5555529 : Nat := 118140960795 + 5555529 * 2 ^ 59
def prefixEnd_5555529 : Nat := 4983230072969 + 3 ^ 40 * 5555529 * 2
def baseEnd_5555529 : Nat := 950885555664033233646031

theorem tailTrace_5555529 : CollatzResearch.WordTrace tailWord_5555529 prefixEnd_5555529 950885555664033233646031 := by
  unfold tailWord_5555529
  simp only [CollatzResearch.WordTrace]
  refine ⟨202626789090274716659781641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135084526060183144439854427 202626789090274716659781641)
  ·
    refine ⟨151970091817706037494836231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202626789090274716659781641 151970091817706037494836231)
    ·
      refine ⟨227955137726559056242254347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151970091817706037494836231 227955137726559056242254347)
      ·
        refine ⟨341932706589838584363381521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227955137726559056242254347 341932706589838584363381521)
        ·
          refine ⟨256449529942378938272536141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341932706589838584363381521 256449529942378938272536141)
          ·
            refine ⟨96168573728392101852201053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256449529942378938272536141 96168573728392101852201053)
            ·
              refine ⟨36063215148147038194575395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96168573728392101852201053 36063215148147038194575395)
              ·
                refine ⟨54094822722220557291863093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36063215148147038194575395 54094822722220557291863093)
                ·
                  refine ⟨5071389630208177246112165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54094822722220557291863093 5071389630208177246112165)
                  ·
                    refine ⟨950885555664033233646031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5071389630208177246112165 950885555664033233646031)
                    ·
                      rfl

theorem cell23_5555529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 4].length) (baseStart_5555529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555529 prefixEnd_5555529 := by exact prefixLift 5555529
  have htrace : WordTrace (prefixWord ++ tailWord_5555529) baseStart_5555529 baseEnd_5555529 := by
    simpa [prefixWord, tailWord_5555529, baseEnd_5555529] using wordTrace_append hprefix tailTrace_5555529
  have hstable : (prefixWord ++ tailWord_5555529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555529).length < 2 ^ (prefixWord ++ tailWord_5555529).sum := by decide
  have hdescent : baseEnd_5555529 < baseStart_5555529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555533 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_5555533 : Nat := 118140960795 + 5555533 * 2 ^ 59
def prefixEnd_5555533 : Nat := 4983230072969 + 3 ^ 40 * 5555533 * 2
def baseEnd_5555533 : Nat := 950886240304905895096025

theorem tailTrace_5555533 : CollatzResearch.WordTrace tailWord_5555533 prefixEnd_5555533 950886240304905895096025 := by
  unfold tailWord_5555533
  simp only [CollatzResearch.WordTrace]
  refine ⟨202626934982260225342927253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135084623321506816895284835 202626934982260225342927253)
  ·
    refine ⟨9498137577293448062949715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 202626934982260225342927253 9498137577293448062949715)
    ·
      refine ⟨14247206365940172094424573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9498137577293448062949715 14247206365940172094424573)
      ·
        refine ⟨5342702387227564535409215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14247206365940172094424573 5342702387227564535409215)
        ·
          refine ⟨8014053580841346803113823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5342702387227564535409215 8014053580841346803113823)
          ·
            refine ⟨12021080371262020204670735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8014053580841346803113823 12021080371262020204670735)
            ·
              refine ⟨18031620556893030307006103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12021080371262020204670735 18031620556893030307006103)
              ·
                refine ⟨27047430835339545460509155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18031620556893030307006103 27047430835339545460509155)
                ·
                  refine ⟨40571146253009318190763733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27047430835339545460509155 40571146253009318190763733)
                  ·
                    refine ⟨950886240304905895096025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40571146253009318190763733 950886240304905895096025)
                    ·
                      rfl

theorem cell23_5555533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_5555533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555533 prefixEnd_5555533 := by exact prefixLift 5555533
  have htrace : WordTrace (prefixWord ++ tailWord_5555533) baseStart_5555533 baseEnd_5555533 := by
    simpa [prefixWord, tailWord_5555533, baseEnd_5555533] using wordTrace_append hprefix tailTrace_5555533
  have hstable : (prefixWord ++ tailWord_5555533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555533).length < 2 ^ (prefixWord ++ tailWord_5555533).sum := by decide
  have hdescent : baseEnd_5555533 < baseStart_5555533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555539 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 3]
def baseStart_5555539 : Nat := 118140960795 + 5555539 * 2 ^ 59
def prefixEnd_5555539 : Nat := 4983230072969 + 3 ^ 40 * 5555539 * 2
def baseEnd_5555539 : Nat := 2852661801798644661813047

theorem tailTrace_5555539 : CollatzResearch.WordTrace tailWord_5555539 prefixEnd_5555539 2852661801798644661813047 := by
  unfold tailWord_5555539
  simp only [CollatzResearch.WordTrace]
  refine ⟨202627153820238488367645671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135084769213492325578430447 202627153820238488367645671)
  ·
    refine ⟨303940730730357732551468507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202627153820238488367645671 303940730730357732551468507)
    ·
      refine ⟨455911096095536598827202761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303940730730357732551468507 455911096095536598827202761)
      ·
        refine ⟨341933322071652449120402071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 455911096095536598827202761 341933322071652449120402071)
        ·
          refine ⟨512899983107478673680603107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341933322071652449120402071 512899983107478673680603107)
          ·
            refine ⟨769349974661218010520904661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512899983107478673680603107 769349974661218010520904661)
            ·
              refine ⟨18031640031122297121583703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 769349974661218010520904661 18031640031122297121583703)
              ·
                refine ⟨27047460046683445682375555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18031640031122297121583703 27047460046683445682375555)
                ·
                  refine ⟨40571190070025168523563333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27047460046683445682375555 40571190070025168523563333)
                  ·
                    refine ⟨7607098138129719098168125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40571190070025168523563333 7607098138129719098168125)
                    ·
                      refine ⟨2852661801798644661813047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7607098138129719098168125 2852661801798644661813047)
                      ·
                        rfl

theorem cell23_5555539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 3].length) (baseStart_5555539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555539 prefixEnd_5555539 := by exact prefixLift 5555539
  have htrace : WordTrace (prefixWord ++ tailWord_5555539) baseStart_5555539 baseEnd_5555539 := by
    simpa [prefixWord, tailWord_5555539, baseEnd_5555539] using wordTrace_append hprefix tailTrace_5555539
  have hstable : (prefixWord ++ tailWord_5555539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555539).length < 2 ^ (prefixWord ++ tailWord_5555539).sum := by decide
  have hdescent : baseEnd_5555539 < baseStart_5555539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555589 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 3, 5]
def baseStart_5555589 : Nat := 118140960795 + 5555589 * 2 ^ 59
def prefixEnd_5555589 : Nat := 4983230072969 + 3 ^ 40 * 5555589 * 2
def baseEnd_5555589 : Nat := 950895825277123155395939

theorem tailTrace_5555589 : CollatzResearch.WordTrace tailWord_5555589 prefixEnd_5555589 950895825277123155395939 := by
  unfold tailWord_5555589
  simp only [CollatzResearch.WordTrace]
  refine ⟨202628977470057346906965821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135085984980038231271310547 202628977470057346906965821)
  ·
    refine ⟨75985866551271505090112183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202628977470057346906965821 75985866551271505090112183)
    ·
      refine ⟨113978799826907257635168275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75985866551271505090112183 113978799826907257635168275)
      ·
        refine ⟨170968199740360886452752413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113978799826907257635168275 170968199740360886452752413)
        ·
          refine ⟨64113074902635332419782155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170968199740360886452752413 64113074902635332419782155)
          ·
            refine ⟨96169612353952998629673233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64113074902635332419782155 96169612353952998629673233)
            ·
              refine ⟨72127209265464748972254925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96169612353952998629673233 72127209265464748972254925)
              ·
                refine ⟨27047703474549280864595597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72127209265464748972254925 27047703474549280864595597)
                ·
                  refine ⟨10142888802955980324223349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27047703474549280864595597 10142888802955980324223349)
                  ·
                    refine ⟨950895825277123155395939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10142888802955980324223349 950895825277123155395939)
                    ·
                      rfl

theorem cell23_5555589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_5555589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555589 prefixEnd_5555589 := by exact prefixLift 5555589
  have htrace : WordTrace (prefixWord ++ tailWord_5555589) baseStart_5555589 baseEnd_5555589 := by
    simpa [prefixWord, tailWord_5555589, baseEnd_5555589] using wordTrace_append hprefix tailTrace_5555589
  have hstable : (prefixWord ++ tailWord_5555589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555589).length < 2 ^ (prefixWord ++ tailWord_5555589).sum := by decide
  have hdescent : baseEnd_5555589 < baseStart_5555589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555596 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 1, 5, 2]
def baseStart_5555596 : Nat := 118140960795 + 5555596 * 2 ^ 59
def prefixEnd_5555596 : Nat := 4983230072969 + 3 ^ 40 * 5555596 * 2
def baseEnd_5555596 : Nat := 2852691070195950938800285

theorem tailTrace_5555596 : CollatzResearch.WordTrace tailWord_5555596 prefixEnd_5555596 2852691070195950938800285 := by
  unfold tailWord_5555596
  simp only [CollatzResearch.WordTrace]
  refine ⟨101314616390515993551235321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135086155187354658068313761 101314616390515993551235321)
  ·
    refine ⟨75985962292886995163426491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101314616390515993551235321 75985962292886995163426491)
    ·
      refine ⟨113978943439330492745139737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75985962292886995163426491 113978943439330492745139737)
      ·
        refine ⟨85484207579497869558854803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113978943439330492745139737 85484207579497869558854803)
        ·
          refine ⟨128226311369246804338282205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85484207579497869558854803 128226311369246804338282205)
          ·
            refine ⟨48084866763467551626855827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128226311369246804338282205 48084866763467551626855827)
            ·
              refine ⟨72127300145201327440283741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48084866763467551626855827 72127300145201327440283741)
              ·
                refine ⟨27047737554450497790106403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72127300145201327440283741 27047737554450497790106403)
                ·
                  refine ⟨40571606331675746685159605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27047737554450497790106403 40571606331675746685159605)
                  ·
                    refine ⟨3803588093594601251733713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40571606331675746685159605 3803588093594601251733713)
                    ·
                      refine ⟨2852691070195950938800285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3803588093594601251733713 2852691070195950938800285)
                      ·
                        rfl

theorem cell23_5555596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_5555596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555596 prefixEnd_5555596 := by exact prefixLift 5555596
  have htrace : WordTrace (prefixWord ++ tailWord_5555596) baseStart_5555596 baseEnd_5555596 := by
    simpa [prefixWord, tailWord_5555596, baseEnd_5555596] using wordTrace_append hprefix tailTrace_5555596
  have hstable : (prefixWord ++ tailWord_5555596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555596).length < 2 ^ (prefixWord ++ tailWord_5555596).sum := by decide
  have hdescent : baseEnd_5555596 < baseStart_5555596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555613 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_5555613 : Nat := 118140960795 + 5555613 * 2 ^ 59
def prefixEnd_5555613 : Nat := 4983230072969 + 3 ^ 40 * 5555613 * 2
def baseEnd_5555613 : Nat := 2852699799367077372287707

theorem tailTrace_5555613 : CollatzResearch.WordTrace tailWord_5555613 prefixEnd_5555613 2852699799367077372287707 := by
  unfold tailWord_5555613
  simp only [CollatzResearch.WordTrace]
  refine ⟨202629852821970399005839493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135086568547980266003892995 202629852821970399005839493)
  ·
    refine ⟨37993097404119449813594905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202629852821970399005839493 37993097404119449813594905)
    ·
      refine ⟨28494823053089587360196179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37993097404119449813594905 28494823053089587360196179)
      ·
        refine ⟨42742234579634381040294269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28494823053089587360196179 42742234579634381040294269)
        ·
          refine ⟨16028337967362892890110351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42742234579634381040294269 16028337967362892890110351)
          ·
            refine ⟨24042506951044339335165527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16028337967362892890110351 24042506951044339335165527)
            ·
              refine ⟨36063760426566509002748291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24042506951044339335165527 36063760426566509002748291)
              ·
                refine ⟨54095640639849763504122437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36063760426566509002748291 54095640639849763504122437)
                ·
                  refine ⟨10142932619971830657022957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54095640639849763504122437 10142932619971830657022957)
                  ·
                    refine ⟨3803599732489436496383609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10142932619971830657022957 3803599732489436496383609)
                    ·
                      refine ⟨2852699799367077372287707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3803599732489436496383609 2852699799367077372287707)
                      ·
                        rfl

theorem cell23_5555613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_5555613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555613 prefixEnd_5555613 := by exact prefixLift 5555613
  have htrace : WordTrace (prefixWord ++ tailWord_5555613) baseStart_5555613 baseEnd_5555613 := by
    simpa [prefixWord, tailWord_5555613, baseEnd_5555613] using wordTrace_append hprefix tailTrace_5555613
  have hstable : (prefixWord ++ tailWord_5555613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555613).length < 2 ^ (prefixWord ++ tailWord_5555613).sum := by decide
  have hdescent : baseEnd_5555613 < baseStart_5555613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555614 : List Nat := [4, 3, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_5555614 : Nat := 118140960795 + 5555614 * 2 ^ 59
def prefixEnd_5555614 : Nat := 4983230072969 + 3 ^ 40 * 5555614 * 2
def baseEnd_5555614 : Nat := 950900104282577289458401

theorem tailTrace_5555614 : CollatzResearch.WordTrace tailWord_5555614 prefixEnd_5555614 950900104282577289458401 := by
  unfold tailWord_5555614
  simp only [CollatzResearch.WordTrace]
  refine ⟨25328736161870847022078237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135086592863311184117750597 25328736161870847022078237)
  ·
    refine ⟨9498276060701567633279339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25328736161870847022078237 9498276060701567633279339)
    ·
      refine ⟨14247414091052351449919009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9498276060701567633279339 14247414091052351449919009)
      ·
        refine ⟨10685560568289263587439257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14247414091052351449919009 10685560568289263587439257)
        ·
          refine ⟨8014170426216947690579443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10685560568289263587439257 8014170426216947690579443)
          ·
            refine ⟨12021255639325421535869165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8014170426216947690579443 12021255639325421535869165)
            ·
              refine ⟨4507970864747033075950937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12021255639325421535869165 4507970864747033075950937)
              ·
                refine ⟨3380978148560274806963203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4507970864747033075950937 3380978148560274806963203)
                ·
                  refine ⟨5071467222840412210444805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3380978148560274806963203 5071467222840412210444805)
                  ·
                    refine ⟨950900104282577289458401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5071467222840412210444805 950900104282577289458401)
                    ·
                      rfl

theorem cell23_5555614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_5555614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555614 prefixEnd_5555614 := by exact prefixLift 5555614
  have htrace : WordTrace (prefixWord ++ tailWord_5555614) baseStart_5555614 baseEnd_5555614 := by
    simpa [prefixWord, tailWord_5555614, baseEnd_5555614] using wordTrace_append hprefix tailTrace_5555614
  have hstable : (prefixWord ++ tailWord_5555614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555614).length < 2 ^ (prefixWord ++ tailWord_5555614).sum := by decide
  have hdescent : baseEnd_5555614 < baseStart_5555614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555639 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_5555639 : Nat := 118140960795 + 5555639 * 2 ^ 59
def prefixEnd_5555639 : Nat := 4983230072969 + 3 ^ 40 * 5555639 * 2
def baseEnd_5555639 : Nat := 2852713149864094270562587

theorem tailTrace_5555639 : CollatzResearch.WordTrace tailWord_5555639 prefixEnd_5555639 2852713149864094270562587 := by
  unfold tailWord_5555639
  simp only [CollatzResearch.WordTrace]
  refine ⟨202630801119876205446285971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135087200746584136964190647 202630801119876205446285971)
  ·
    refine ⟨303946201679814308169428957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202630801119876205446285971 303946201679814308169428957)
    ·
      refine ⟨113979825629930365563535859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303946201679814308169428957 113979825629930365563535859)
      ·
        refine ⟨170969738444895548345303789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113979825629930365563535859 170969738444895548345303789)
        ·
          refine ⟨64113651916835830629488921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170969738444895548345303789 64113651916835830629488921)
          ·
            refine ⟨48085238937626872972116691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64113651916835830629488921 48085238937626872972116691)
            ·
              refine ⟨72127858406440309458175037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48085238937626872972116691 72127858406440309458175037)
              ·
                refine ⟨27047946902415116046815639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72127858406440309458175037 27047946902415116046815639)
                ·
                  refine ⟨40571920353622674070223459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27047946902415116046815639 40571920353622674070223459)
                  ·
                    refine ⟨60857880530434011105335189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40571920353622674070223459 60857880530434011105335189)
                    ·
                      refine ⟨2852713149864094270562587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60857880530434011105335189 2852713149864094270562587)
                      ·
                        rfl

theorem cell23_5555639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_5555639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555639 prefixEnd_5555639 := by exact prefixLift 5555639
  have htrace : WordTrace (prefixWord ++ tailWord_5555639) baseStart_5555639 baseEnd_5555639 := by
    simpa [prefixWord, tailWord_5555639, baseEnd_5555639] using wordTrace_append hprefix tailTrace_5555639
  have hstable : (prefixWord ++ tailWord_5555639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555639).length < 2 ^ (prefixWord ++ tailWord_5555639).sum := by decide
  have hdescent : baseEnd_5555639 < baseStart_5555639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555656 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_5555656 : Nat := 118140960795 + 5555656 * 2 ^ 59
def prefixEnd_5555656 : Nat := 4983230072969 + 3 ^ 40 * 5555656 * 2
def baseEnd_5555656 : Nat := 2852721879035220704050009

theorem tailTrace_5555656 : CollatzResearch.WordTrace tailWord_5555656 prefixEnd_5555656 2852721879035220704050009 := by
  unfold tailWord_5555656
  simp only [CollatzResearch.WordTrace]
  refine ⟨101315710580407308674827411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135087614107209744899769881 101315710580407308674827411)
  ·
    refine ⟨151973565870610963012241117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101315710580407308674827411 151973565870610963012241117)
    ·
      refine ⟨56990087201479111129590419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151973565870610963012241117 56990087201479111129590419)
      ·
        refine ⟨85485130802218666694385629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56990087201479111129590419 85485130802218666694385629)
        ·
          refine ⟨32056924050832000010394611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85485130802218666694385629 32056924050832000010394611)
          ·
            refine ⟨48085386076248000015591917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32056924050832000010394611 48085386076248000015591917)
            ·
              refine ⟨18032019778593000005846969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48085386076248000015591917 18032019778593000005846969)
              ·
                refine ⟨13524014833944750004385227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18032019778593000005846969 13524014833944750004385227)
                ·
                  refine ⟨20286022250917125006577841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13524014833944750004385227 20286022250917125006577841)
                  ·
                    refine ⟨15214516688187843754933381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20286022250917125006577841 15214516688187843754933381)
                    ·
                      refine ⟨2852721879035220704050009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15214516688187843754933381 2852721879035220704050009)
                      ·
                        rfl

theorem cell23_5555656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_5555656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555656 prefixEnd_5555656 := by exact prefixLift 5555656
  have htrace : WordTrace (prefixWord ++ tailWord_5555656) baseStart_5555656 baseEnd_5555656 := by
    simpa [prefixWord, tailWord_5555656, baseEnd_5555656] using wordTrace_append hprefix tailTrace_5555656
  have hstable : (prefixWord ++ tailWord_5555656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555656).length < 2 ^ (prefixWord ++ tailWord_5555656).sum := by decide
  have hdescent : baseEnd_5555656 < baseStart_5555656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555660 : List Nat := [2, 2, 1, 4, 2, 2, 3, 1, 1, 1, 4]
def baseStart_5555660 : Nat := 118140960795 + 5555660 * 2 ^ 59
def prefixEnd_5555660 : Nat := 4983230072969 + 3 ^ 40 * 5555660 * 2
def baseEnd_5555660 : Nat := 2852723932957838688399991

theorem tailTrace_5555660 : CollatzResearch.WordTrace tailWord_5555660 prefixEnd_5555660 2852723932957838688399991 := by
  unfold tailWord_5555660
  simp only [CollatzResearch.WordTrace]
  refine ⟨101315783526400063016400217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135087711368533417355200289 101315783526400063016400217)
  ·
    refine ⟨75986837644800047262300163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101315783526400063016400217 75986837644800047262300163)
    ·
      refine ⟨113980256467200070893450245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75986837644800047262300163 113980256467200070893450245)
      ·
        refine ⟨21371298087600013292521921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113980256467200070893450245 21371298087600013292521921)
        ·
          refine ⟨16028473565700009969391441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21371298087600013292521921 16028473565700009969391441)
          ·
            refine ⟨12021355174275007477043581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16028473565700009969391441 12021355174275007477043581)
            ·
              refine ⟨4508008190353127803891343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12021355174275007477043581 4508008190353127803891343)
              ·
                refine ⟨6762012285529691705837015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4508008190353127803891343 6762012285529691705837015)
                ·
                  refine ⟨10143018428294537558755523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6762012285529691705837015 10143018428294537558755523)
                  ·
                    refine ⟨15214527642441806338133285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10143018428294537558755523 15214527642441806338133285)
                    ·
                      refine ⟨2852723932957838688399991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15214527642441806338133285 2852723932957838688399991)
                      ·
                        rfl

theorem cell23_5555660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_5555660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555660 prefixEnd_5555660 := by exact prefixLift 5555660
  have htrace : WordTrace (prefixWord ++ tailWord_5555660) baseStart_5555660 baseEnd_5555660 := by
    simpa [prefixWord, tailWord_5555660, baseEnd_5555660] using wordTrace_append hprefix tailTrace_5555660
  have hstable : (prefixWord ++ tailWord_5555660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555660).length < 2 ^ (prefixWord ++ tailWord_5555660).sum := by decide
  have hdescent : baseEnd_5555660 < baseStart_5555660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555670 : List Nat := [5, 2, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_5555670 : Nat := 118140960795 + 5555670 * 2 ^ 59
def prefixEnd_5555670 : Nat := 4983230072969 + 3 ^ 40 * 5555670 * 2
def baseEnd_5555670 : Nat := 950909689254794549758315

theorem tailTrace_5555670 : CollatzResearch.WordTrace tailWord_5555670 prefixEnd_5555670 950909689254794549758315 := by
  unfold tailWord_5555670
  simp only [CollatzResearch.WordTrace]
  refine ⟨12664495736422743608791529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135087954521842598493776309 12664495736422743608791529)
  ·
    refine ⟨9498371802317057706593647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12664495736422743608791529 9498371802317057706593647)
    ·
      refine ⟨14247557703475586559890471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9498371802317057706593647 14247557703475586559890471)
      ·
        refine ⟨21371336555213379839835707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14247557703475586559890471 21371336555213379839835707)
        ·
          refine ⟨32057004832820069759753561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21371336555213379839835707 32057004832820069759753561)
          ·
            refine ⟨24042753624615052319815171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32057004832820069759753561 24042753624615052319815171)
            ·
              refine ⟨36064130436922578479722757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24042753624615052319815171 36064130436922578479722757)
              ·
                refine ⟨6762024456922983464948017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36064130436922578479722757 6762024456922983464948017)
                ·
                  refine ⟨5071518342692237598711013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6762024456922983464948017 5071518342692237598711013)
                  ·
                    refine ⟨950909689254794549758315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5071518342692237598711013 950909689254794549758315)
                    ·
                      rfl

theorem cell23_5555670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_5555670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555670 prefixEnd_5555670 := by exact prefixLift 5555670
  have htrace : WordTrace (prefixWord ++ tailWord_5555670) baseStart_5555670 baseEnd_5555670 := by
    simpa [prefixWord, tailWord_5555670, baseEnd_5555670] using wordTrace_append hprefix tailTrace_5555670
  have hstable : (prefixWord ++ tailWord_5555670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555670).length < 2 ^ (prefixWord ++ tailWord_5555670).sum := by decide
  have hdescent : baseEnd_5555670 < baseStart_5555670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555679 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 1, 9]
def baseStart_5555679 : Nat := 118140960795 + 5555679 * 2 ^ 59
def prefixEnd_5555679 : Nat := 4983230072969 + 3 ^ 40 * 5555679 * 2
def baseEnd_5555679 : Nat := 950911229696758038020801

theorem tailTrace_5555679 : CollatzResearch.WordTrace tailWord_5555679 prefixEnd_5555679 950911229696758038020801 := by
  unfold tailWord_5555679
  simp only [CollatzResearch.WordTrace]
  refine ⟨202632260039731292277742091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135088173359820861518494727 202632260039731292277742091)
  ·
    refine ⟨303948390059596938416613137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202632260039731292277742091 303948390059596938416613137)
    ·
      refine ⟨227961292544697703812459853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303948390059596938416613137 227961292544697703812459853)
      ·
        refine ⟨85485484704261638929672445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227961292544697703812459853 85485484704261638929672445)
        ·
          refine ⟨32057056764098114598627167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85485484704261638929672445 32057056764098114598627167)
          ·
            refine ⟨48085585146147171897940751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32057056764098114598627167 48085585146147171897940751)
            ·
              refine ⟨72128377719220757846911127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48085585146147171897940751 72128377719220757846911127)
              ·
                refine ⟨108192566578831136770366691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72128377719220757846911127 108192566578831136770366691)
                ·
                  refine ⟨162288849868246705155550037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108192566578831136770366691 162288849868246705155550037)
                  ·
                    refine ⟨950911229696758038020801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 162288849868246705155550037 950911229696758038020801)
                    ·
                      rfl

theorem cell23_5555679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_5555679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555679 prefixEnd_5555679 := by exact prefixLift 5555679
  have htrace : WordTrace (prefixWord ++ tailWord_5555679) baseStart_5555679 baseEnd_5555679 := by
    simpa [prefixWord, tailWord_5555679, baseEnd_5555679] using wordTrace_append hprefix tailTrace_5555679
  have hstable : (prefixWord ++ tailWord_5555679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555679).length < 2 ^ (prefixWord ++ tailWord_5555679).sum := by decide
  have hdescent : baseEnd_5555679 < baseStart_5555679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555714 : List Nat := [3, 4, 1, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_5555714 : Nat := 118140960795 + 5555714 * 2 ^ 59
def prefixEnd_5555714 : Nat := 4983230072969 + 3 ^ 40 * 5555714 * 2
def baseEnd_5555714 : Nat := 2852751660913181477124743

theorem tailTrace_5555714 : CollatzResearch.WordTrace tailWord_5555714 prefixEnd_5555714 2852751660913181477124743 := by
  unfold tailWord_5555714
  simp only [CollatzResearch.WordTrace]
  refine ⟨50658384148651123313816549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135089024396402995503510797 50658384148651123313816549)
  ·
    refine ⟨9498447027872085621340603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50658384148651123313816549 9498447027872085621340603)
    ·
      refine ⟨14247670541808128432010905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9498447027872085621340603 14247670541808128432010905)
      ·
        refine ⟨10685752906356096324008179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14247670541808128432010905 10685752906356096324008179)
        ·
          refine ⟨16028629359534144486012269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10685752906356096324008179 16028629359534144486012269)
          ·
            refine ⟨6010736009825304182254601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16028629359534144486012269 6010736009825304182254601)
            ·
              refine ⟨4508052007368978136690951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6010736009825304182254601 4508052007368978136690951)
              ·
                refine ⟨6762078011053467205036427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4508052007368978136690951 6762078011053467205036427)
                ·
                  refine ⟨10143117016580200807554641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6762078011053467205036427 10143117016580200807554641)
                  ·
                    refine ⟨7607337762435150605665981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10143117016580200807554641 7607337762435150605665981)
                    ·
                      refine ⟨2852751660913181477124743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7607337762435150605665981 2852751660913181477124743)
                      ·
                        rfl

theorem cell23_5555714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_5555714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555714 prefixEnd_5555714 := by exact prefixLift 5555714
  have htrace : WordTrace (prefixWord ++ tailWord_5555714) baseStart_5555714 baseEnd_5555714 := by
    simpa [prefixWord, tailWord_5555714, baseEnd_5555714] using wordTrace_append hprefix tailTrace_5555714
  have hstable : (prefixWord ++ tailWord_5555714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555714).length < 2 ^ (prefixWord ++ tailWord_5555714).sum := by decide
  have hdescent : baseEnd_5555714 < baseStart_5555714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555793 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 2, 5, 2]
def baseStart_5555793 : Nat := 118140960795 + 5555793 * 2 ^ 59
def prefixEnd_5555793 : Nat := 4983230072969 + 3 ^ 40 * 5555793 * 2
def baseEnd_5555793 : Nat := 2852792225884886668036879

theorem tailTrace_5555793 : CollatzResearch.WordTrace tailWord_5555793 prefixEnd_5555793 2852792225884886668036879 := by
  unfold tailWord_5555793
  simp only [CollatzResearch.WordTrace]
  refine ⟨202636417961318289747392033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135090945307545526498261355 202636417961318289747392033)
  ·
    refine ⟨151977313470988717310544025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202636417961318289747392033 151977313470988717310544025)
    ·
      refine ⟨113982985103241537982908019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151977313470988717310544025 113982985103241537982908019)
      ·
        refine ⟨170974477654862306974362029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113982985103241537982908019 170974477654862306974362029)
        ·
          refine ⟨64115429120573365115385761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170974477654862306974362029 64115429120573365115385761)
          ·
            refine ⟨48086571840430023836539321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64115429120573365115385761 48086571840430023836539321)
            ·
              refine ⟨36064928880322517877404491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48086571840430023836539321 36064928880322517877404491)
              ·
                refine ⟨54097393320483776816106737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36064928880322517877404491 54097393320483776816106737)
                ·
                  refine ⟨40573044990362832612080053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54097393320483776816106737 40573044990362832612080053)
                  ·
                    refine ⟨3803722967846515557382505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40573044990362832612080053 3803722967846515557382505)
                    ·
                      refine ⟨2852792225884886668036879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3803722967846515557382505 2852792225884886668036879)
                      ·
                        rfl

theorem cell23_5555793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 5, 2].length) (baseStart_5555793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555793 prefixEnd_5555793 := by exact prefixLift 5555793
  have htrace : WordTrace (prefixWord ++ tailWord_5555793) baseStart_5555793 baseEnd_5555793 := by
    simpa [prefixWord, tailWord_5555793, baseEnd_5555793] using wordTrace_append hprefix tailTrace_5555793
  have hstable : (prefixWord ++ tailWord_5555793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555793).length < 2 ^ (prefixWord ++ tailWord_5555793).sum := by decide
  have hdescent : baseEnd_5555793 < baseStart_5555793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555823 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 4, 4, 2]
def baseStart_5555823 : Nat := 118140960795 + 5555823 * 2 ^ 59
def prefixEnd_5555823 : Nat := 4983230072969 + 3 ^ 40 * 5555823 * 2
def baseEnd_5555823 : Nat := 2852807630304521550661741

theorem tailTrace_5555823 : CollatzResearch.WordTrace tailWord_5555823 prefixEnd_5555823 2852807630304521550661741 := by
  unfold tailWord_5555823
  simp only [CollatzResearch.WordTrace]
  refine ⟨202637512151209604870984123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135091674767473069913989415 202637512151209604870984123)
  ·
    refine ⟨303956268226814407306476185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202637512151209604870984123 303956268226814407306476185)
    ·
      refine ⟨227967201170110805479857139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303956268226814407306476185 227967201170110805479857139)
      ·
        refine ⟨341950801755166208219785709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227967201170110805479857139 341950801755166208219785709)
        ·
          refine ⟨128231550658187328082419641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341950801755166208219785709 128231550658187328082419641)
          ·
            refine ⟨96173662993640496061814731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128231550658187328082419641 96173662993640496061814731)
            ·
              refine ⟨144260494490460744092722097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96173662993640496061814731 144260494490460744092722097)
              ·
                refine ⟨108195370867845558069541573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144260494490460744092722097 108195370867845558069541573)
                ·
                  refine ⟨20286632037721042138039045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108195370867845558069541573 20286632037721042138039045)
                  ·
                    refine ⟨3803743507072695400882321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20286632037721042138039045 3803743507072695400882321)
                    ·
                      refine ⟨2852807630304521550661741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3803743507072695400882321 2852807630304521550661741)
                      ·
                        rfl

theorem cell23_5555823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 4, 2].length) (baseStart_5555823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555823 prefixEnd_5555823 := by exact prefixLift 5555823
  have htrace : WordTrace (prefixWord ++ tailWord_5555823) baseStart_5555823 baseEnd_5555823 := by
    simpa [prefixWord, tailWord_5555823, baseEnd_5555823] using wordTrace_append hprefix tailTrace_5555823
  have hstable : (prefixWord ++ tailWord_5555823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555823).length < 2 ^ (prefixWord ++ tailWord_5555823).sum := by decide
  have hdescent : baseEnd_5555823 < baseStart_5555823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555836 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_5555836 : Nat := 118140960795 + 5555836 * 2 ^ 59
def prefixEnd_5555836 : Nat := 4983230072969 + 3 ^ 40 * 5555836 * 2
def baseEnd_5555836 : Nat := 2852814305553029999799181

theorem tailTrace_5555836 : CollatzResearch.WordTrace tailWord_5555836 prefixEnd_5555836 2852814305553029999799181 := by
  unfold tailWord_5555836
  simp only [CollatzResearch.WordTrace]
  refine ⟨101318993150081254045603681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135091990866775005394138241 101318993150081254045603681)
  ·
    refine ⟨75989244862560940534202761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101318993150081254045603681 75989244862560940534202761)
    ·
      refine ⟨56991933646920705400652071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75989244862560940534202761 56991933646920705400652071)
      ·
        refine ⟨85487900470381058100978107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56991933646920705400652071 85487900470381058100978107)
        ·
          refine ⟨128231850705571587151467161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85487900470381058100978107 128231850705571587151467161)
          ·
            refine ⟨96173888029178690363600371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128231850705571587151467161 96173888029178690363600371)
            ·
              refine ⟨144260832043768035545400557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96173888029178690363600371 144260832043768035545400557)
              ·
                refine ⟨54097812016413013329525209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144260832043768035545400557 54097812016413013329525209)
                ·
                  refine ⟨40573359012309759997143907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54097812016413013329525209 40573359012309759997143907)
                  ·
                    refine ⟨60860038518464639995715861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40573359012309759997143907 60860038518464639995715861)
                    ·
                      refine ⟨2852814305553029999799181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60860038518464639995715861 2852814305553029999799181)
                      ·
                        rfl

theorem cell23_5555836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_5555836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555836 prefixEnd_5555836 := by exact prefixLift 5555836
  have htrace : WordTrace (prefixWord ++ tailWord_5555836) baseStart_5555836 baseEnd_5555836 := by
    simpa [prefixWord, tailWord_5555836, baseEnd_5555836] using wordTrace_append hprefix tailTrace_5555836
  have hstable : (prefixWord ++ tailWord_5555836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555836).length < 2 ^ (prefixWord ++ tailWord_5555836).sum := by decide
  have hdescent : baseEnd_5555836 < baseStart_5555836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555863 : List Nat := [1, 1, 3, 3, 2, 2, 2, 3, 6]
def baseStart_5555863 : Nat := 118140960795 + 5555863 * 2 ^ 59
def prefixEnd_5555863 : Nat := 4983230072969 + 3 ^ 40 * 5555863 * 2
def baseEnd_5555863 : Nat := 316980907725633488240173

theorem tailTrace_5555863 : CollatzResearch.WordTrace tailWord_5555863 prefixEnd_5555863 316980907725633488240173 := by
  unfold tailWord_5555863
  simp only [CollatzResearch.WordTrace]
  refine ⟨202638971071064691702440243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135092647380709794468293495 202638971071064691702440243)
  ·
    refine ⟨303958456606597037553660365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202638971071064691702440243 303958456606597037553660365)
    ·
      refine ⟨113984421227473889082622637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303958456606597037553660365 113984421227473889082622637)
      ·
        refine ⟨42744157960302708405983489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113984421227473889082622637 42744157960302708405983489)
        ·
          refine ⟨32058118470227031304487617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42744157960302708405983489 32058118470227031304487617)
          ·
            refine ⟨24043588852670273478365713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32058118470227031304487617 24043588852670273478365713)
            ·
              refine ⟨18032691639502705108774285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24043588852670273478365713 18032691639502705108774285)
              ·
                refine ⟨6762259364813514415790357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18032691639502705108774285 6762259364813514415790357)
                ·
                  refine ⟨316980907725633488240173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6762259364813514415790357 316980907725633488240173)
                  ·
                    rfl

theorem cell23_5555863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 6].length) (baseStart_5555863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555863 prefixEnd_5555863 := by exact prefixLift 5555863
  have htrace : WordTrace (prefixWord ++ tailWord_5555863) baseStart_5555863 baseEnd_5555863 := by
    simpa [prefixWord, tailWord_5555863, baseEnd_5555863] using wordTrace_append hprefix tailTrace_5555863
  have hstable : (prefixWord ++ tailWord_5555863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555863).length < 2 ^ (prefixWord ++ tailWord_5555863).sum := by decide
  have hdescent : baseEnd_5555863 < baseStart_5555863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555874 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_5555874 : Nat := 118140960795 + 5555874 * 2 ^ 59
def prefixEnd_5555874 : Nat := 4983230072969 + 3 ^ 40 * 5555874 * 2
def baseEnd_5555874 : Nat := 2852833817817900851124007

theorem tailTrace_5555874 : CollatzResearch.WordTrace tailWord_5555874 prefixEnd_5555874 2852833817817900851124007 := by
  unfold tailWord_5555874
  simp only [CollatzResearch.WordTrace]
  refine ⟨50659843068506210145272669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135092914849349893720727117 50659843068506210145272669)
  ·
    refine ⟨18997441150689828804477251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50659843068506210145272669 18997441150689828804477251)
    ·
      refine ⟨28496161726034743206715877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18997441150689828804477251 28496161726034743206715877)
      ·
        refine ⟨5343030323631514351259227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28496161726034743206715877 5343030323631514351259227)
        ·
          refine ⟨8014545485447271526888841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5343030323631514351259227 8014545485447271526888841)
          ·
            refine ⟨6010909114085453645166631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8014545485447271526888841 6010909114085453645166631)
            ·
              refine ⟨9016363671128180467749947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6010909114085453645166631 9016363671128180467749947)
              ·
                refine ⟨13524545506692270701624921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9016363671128180467749947 13524545506692270701624921)
                ·
                  refine ⟨10143409130019203026218691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13524545506692270701624921 10143409130019203026218691)
                  ·
                    refine ⟨15215113695028804539328037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10143409130019203026218691 15215113695028804539328037)
                    ·
                      refine ⟨2852833817817900851124007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15215113695028804539328037 2852833817817900851124007)
                      ·
                        rfl

theorem cell23_5555874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_5555874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555874 prefixEnd_5555874 := by exact prefixLift 5555874
  have htrace : WordTrace (prefixWord ++ tailWord_5555874) baseStart_5555874 baseEnd_5555874 := by
    simpa [prefixWord, tailWord_5555874, baseEnd_5555874] using wordTrace_append hprefix tailTrace_5555874
  have hstable : (prefixWord ++ tailWord_5555874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555874).length < 2 ^ (prefixWord ++ tailWord_5555874).sum := by decide
  have hdescent : baseEnd_5555874 < baseStart_5555874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555930 : List Nat := [3, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4]
def baseStart_5555930 : Nat := 118140960795 + 5555930 * 2 ^ 59
def prefixEnd_5555930 : Nat := 4983230072969 + 3 ^ 40 * 5555930 * 2
def baseEnd_5555930 : Nat := 2852862572734552632023749

theorem tailTrace_5555930 : CollatzResearch.WordTrace tailWord_5555930 prefixEnd_5555930 2852862572734552632023749 := by
  unfold tailWord_5555930
  simp only [CollatzResearch.WordTrace]
  refine ⟨50660353690455490536282311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135094276507881308096752829 50660353690455490536282311)
  ·
    refine ⟨75990530535683235804423467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50660353690455490536282311 75990530535683235804423467)
    ·
      refine ⟨113985795803524853706635201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75990530535683235804423467 113985795803524853706635201)
      ·
        refine ⟨85489346852643640279976401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113985795803524853706635201 85489346852643640279976401)
        ·
          refine ⟨64117010139482730209982301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85489346852643640279976401 64117010139482730209982301)
          ·
            refine ⟨24043878802306023828743363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64117010139482730209982301 24043878802306023828743363)
            ·
              refine ⟨36065818203459035743115045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24043878802306023828743363 36065818203459035743115045)
              ·
                refine ⟨6762340913148569201834071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36065818203459035743115045 6762340913148569201834071)
                ·
                  refine ⟨10143511369722853802751107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6762340913148569201834071 10143511369722853802751107)
                  ·
                    refine ⟨15215267054584280704126661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10143511369722853802751107 15215267054584280704126661)
                    ·
                      refine ⟨2852862572734552632023749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15215267054584280704126661 2852862572734552632023749)
                      ·
                        rfl

theorem cell23_5555930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_5555930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555930 prefixEnd_5555930 := by exact prefixLift 5555930
  have htrace : WordTrace (prefixWord ++ tailWord_5555930) baseStart_5555930 baseEnd_5555930 := by
    simpa [prefixWord, tailWord_5555930, baseEnd_5555930] using wordTrace_append hprefix tailTrace_5555930
  have hstable : (prefixWord ++ tailWord_5555930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555930).length < 2 ^ (prefixWord ++ tailWord_5555930).sum := by decide
  have hdescent : baseEnd_5555930 < baseStart_5555930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555950 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_5555950 : Nat := 118140960795 + 5555950 * 2 ^ 59
def prefixEnd_5555950 : Nat := 4983230072969 + 3 ^ 40 * 5555950 * 2
def baseEnd_5555950 : Nat := 2852872842347642553773657

theorem tailTrace_5555950 : CollatzResearch.WordTrace tailWord_5555950 prefixEnd_5555950 2852872842347642553773657 := by
  unfold tailWord_5555950
  simp only [CollatzResearch.WordTrace]
  refine ⟨25330268027718688195107163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135094762814499670373904869 25330268027718688195107163)
  ·
    refine ⟨37995402041578032292660745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25330268027718688195107163 37995402041578032292660745)
    ·
      refine ⟨28496551531183524219495559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37995402041578032292660745 28496551531183524219495559)
      ·
        refine ⟨42744827296775286329243339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28496551531183524219495559 42744827296775286329243339)
        ·
          refine ⟨64117240945162929493865009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42744827296775286329243339 64117240945162929493865009)
          ·
            refine ⟨48087930708872197120398757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64117240945162929493865009 48087930708872197120398757)
            ·
              refine ⟨9016487007913536960074767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48087930708872197120398757 9016487007913536960074767)
              ·
                refine ⟨13524730511870305440112151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9016487007913536960074767 13524730511870305440112151)
                ·
                  refine ⟨20287095767805458160168227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13524730511870305440112151 20287095767805458160168227)
                  ·
                    refine ⟨30430643651708187240252341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20287095767805458160168227 30430643651708187240252341)
                    ·
                      refine ⟨2852872842347642553773657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30430643651708187240252341 2852872842347642553773657)
                      ·
                        rfl

theorem cell23_5555950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_5555950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555950 prefixEnd_5555950 := by exact prefixLift 5555950
  have htrace : WordTrace (prefixWord ++ tailWord_5555950) baseStart_5555950 baseEnd_5555950 := by
    simpa [prefixWord, tailWord_5555950, baseEnd_5555950] using wordTrace_append hprefix tailTrace_5555950
  have hstable : (prefixWord ++ tailWord_5555950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555950).length < 2 ^ (prefixWord ++ tailWord_5555950).sum := by decide
  have hdescent : baseEnd_5555950 < baseStart_5555950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555953 : List Nat := [1, 2, 2, 2, 2, 5, 9]
def baseStart_5555953 : Nat := 118140960795 + 5555953 * 2 ^ 59
def prefixEnd_5555953 : Nat := 4983230072969 + 3 ^ 40 * 5555953 * 2
def baseEnd_5555953 : Nat := 35220671392464272123903

theorem tailTrace_5555953 : CollatzResearch.WordTrace tailWord_5555953 prefixEnd_5555953 35220671392464272123903 := by
  unfold tailWord_5555953
  simp only [CollatzResearch.WordTrace]
  refine ⟨202642253640738637073216513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135094835760492424715477675 202642253640738637073216513)
  ·
    refine ⟨151981690230553977804912385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202642253640738637073216513 151981690230553977804912385)
    ·
      refine ⟨113986267672915483353684289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151981690230553977804912385 113986267672915483353684289)
      ·
        refine ⟨85489700754686612515263217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113986267672915483353684289 85489700754686612515263217)
        ·
          refine ⟨64117275566014959386447413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85489700754686612515263217 64117275566014959386447413)
          ·
            refine ⟨6010994584313902442479445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64117275566014959386447413 6010994584313902442479445)
            ·
              refine ⟨35220671392464272123903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6010994584313902442479445 35220671392464272123903)
              ·
                rfl

theorem cell23_5555953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 9].length) (baseStart_5555953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555953 prefixEnd_5555953 := by exact prefixLift 5555953
  have htrace : WordTrace (prefixWord ++ tailWord_5555953) baseStart_5555953 baseEnd_5555953 := by
    simpa [prefixWord, tailWord_5555953, baseEnd_5555953] using wordTrace_append hprefix tailTrace_5555953
  have hstable : (prefixWord ++ tailWord_5555953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555953).length < 2 ^ (prefixWord ++ tailWord_5555953).sum := by decide
  have hdescent : baseEnd_5555953 < baseStart_5555953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555963 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 3]
def baseStart_5555963 : Nat := 118140960795 + 5555963 * 2 ^ 59
def prefixEnd_5555963 : Nat := 4983230072969 + 3 ^ 40 * 5555963 * 2
def baseEnd_5555963 : Nat := 2852879517596151002911097

theorem tailTrace_5555963 : CollatzResearch.WordTrace tailWord_5555963 prefixEnd_5555963 2852879517596151002911097 := by
  unfold tailWord_5555963
  simp only [CollatzResearch.WordTrace]
  refine ⟨202642618370702408781080543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135095078913801605854053695 202642618370702408781080543)
  ·
    refine ⟨303963927556053613171620815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202642618370702408781080543 303963927556053613171620815)
    ·
      refine ⟨455945891334080419757431223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303963927556053613171620815 455945891334080419757431223)
      ·
        refine ⟨683918837001120629636146835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455945891334080419757431223 683918837001120629636146835)
        ·
          refine ⟨1025878255501680944454220253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683918837001120629636146835 1025878255501680944454220253)
          ·
            refine ⟨384704345813130354170332595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1025878255501680944454220253 384704345813130354170332595)
            ·
              refine ⟨577056518719695531255498893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384704345813130354170332595 577056518719695531255498893)
              ·
                refine ⟨216396194519885824220812085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 577056518719695531255498893 216396194519885824220812085)
                ·
                  refine ⟨20287143236239296020701133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 216396194519885824220812085 20287143236239296020701133)
                  ·
                    refine ⟨7607678713589736007762925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20287143236239296020701133 7607678713589736007762925)
                    ·
                      refine ⟨2852879517596151002911097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7607678713589736007762925 2852879517596151002911097)
                      ·
                        rfl

theorem cell23_5555963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 3].length) (baseStart_5555963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555963 prefixEnd_5555963 := by exact prefixLift 5555963
  have htrace : WordTrace (prefixWord ++ tailWord_5555963) baseStart_5555963 baseEnd_5555963 := by
    simpa [prefixWord, tailWord_5555963, baseEnd_5555963] using wordTrace_append hprefix tailTrace_5555963
  have hstable : (prefixWord ++ tailWord_5555963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555963).length < 2 ^ (prefixWord ++ tailWord_5555963).sum := by decide
  have hdescent : baseEnd_5555963 < baseStart_5555963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555970 : List Nat := [3, 4, 1, 1, 1, 1, 4, 8]
def baseStart_5555970 : Nat := 118140960795 + 5555970 * 2 ^ 59
def prefixEnd_5555970 : Nat := 4983230072969 + 3 ^ 40 * 5555970 * 2
def baseEnd_5555970 : Nat := 105662337480027128723095

theorem tailTrace_5555970 : CollatzResearch.WordTrace tailWord_5555970 prefixEnd_5555970 105662337480027128723095 := by
  unfold tailWord_5555970
  simp only [CollatzResearch.WordTrace]
  refine ⟨50660718420419262244146341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135095249121118032651056909 50660718420419262244146341)
  ·
    refine ⟨9498884703828611670777439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50660718420419262244146341 9498884703828611670777439)
    ·
      refine ⟨14248327055742917506166159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9498884703828611670777439 14248327055742917506166159)
      ·
        refine ⟨21372490583614376259249239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14248327055742917506166159 21372490583614376259249239)
        ·
          refine ⟨32058735875421564388873859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21372490583614376259249239 32058735875421564388873859)
          ·
            refine ⟨48088103813132346583310789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32058735875421564388873859 48088103813132346583310789)
            ·
              refine ⟨9016519464962314984370773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48088103813132346583310789 9016519464962314984370773)
              ·
                refine ⟨105662337480027128723095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9016519464962314984370773 105662337480027128723095)
                ·
                  rfl

theorem cell23_5555970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 8].length) (baseStart_5555970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555970 prefixEnd_5555970 := by exact prefixLift 5555970
  have htrace : WordTrace (prefixWord ++ tailWord_5555970) baseStart_5555970 baseEnd_5555970 := by
    simpa [prefixWord, tailWord_5555970, baseEnd_5555970] using wordTrace_append hprefix tailTrace_5555970
  have hstable : (prefixWord ++ tailWord_5555970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555970).length < 2 ^ (prefixWord ++ tailWord_5555970).sum := by decide
  have hdescent : baseEnd_5555970 < baseStart_5555970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5555998 : List Nat := [4, 3, 2, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_5555998 : Nat := 118140960795 + 5555998 * 2 ^ 59
def prefixEnd_5555998 : Nat := 4983230072969 + 3 ^ 40 * 5555998 * 2
def baseEnd_5555998 : Nat := 2852897489419058365973437

theorem tailTrace_5555998 : CollatzResearch.WordTrace tailWord_5555998 prefixEnd_5555998 2852897489419058365973437 := by
  unfold tailWord_5555998
  simp only [CollatzResearch.WordTrace]
  refine ⟨25330486865696951219825581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135095929950383739839069765 25330486865696951219825581)
  ·
    refine ⟨9498932574636356707434593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25330486865696951219825581 9498932574636356707434593)
    ·
      refine ⟨7124199430977267530575945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9498932574636356707434593 7124199430977267530575945)
      ·
        refine ⟨5343149573232950647931959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7124199430977267530575945 5343149573232950647931959)
        ·
          refine ⟨8014724359849425971897939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5343149573232950647931959 8014724359849425971897939)
          ·
            refine ⟨12022086539774138957846909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8014724359849425971897939 12022086539774138957846909)
            ·
              refine ⟨4508282452415302109192591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12022086539774138957846909 4508282452415302109192591)
              ·
                refine ⟨6762423678622953163788887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4508282452415302109192591 6762423678622953163788887)
                ·
                  refine ⟨10143635517934429745683331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6762423678622953163788887 10143635517934429745683331)
                  ·
                    refine ⟨15215453276901644618524997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10143635517934429745683331 15215453276901644618524997)
                    ·
                      refine ⟨2852897489419058365973437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15215453276901644618524997 2852897489419058365973437)
                      ·
                        rfl

theorem cell23_5555998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_5555998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5555998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5555998 prefixEnd_5555998 := by exact prefixLift 5555998
  have htrace : WordTrace (prefixWord ++ tailWord_5555998) baseStart_5555998 baseEnd_5555998 := by
    simpa [prefixWord, tailWord_5555998, baseEnd_5555998] using wordTrace_append hprefix tailTrace_5555998
  have hstable : (prefixWord ++ tailWord_5555998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5555998).length < 2 ^ (prefixWord ++ tailWord_5555998).sum := by decide
  have hdescent : baseEnd_5555998 < baseStart_5555998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5555998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556023 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_5556023 : Nat := 118140960795 + 5556023 * 2 ^ 59
def prefixEnd_5556023 : Nat := 4983230072969 + 3 ^ 40 * 5556023 * 2
def baseEnd_5556023 : Nat := 2852910326435420768160821

theorem tailTrace_5556023 : CollatzResearch.WordTrace tailWord_5556023 prefixEnd_5556023 2852910326435420768160821 := by
  unfold tailWord_5556023
  simp only [CollatzResearch.WordTrace]
  refine ⟨202644806750485039028264723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135096537833656692685509815 202644806750485039028264723)
  ·
    refine ⟨303967210125727558542397085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202644806750485039028264723 303967210125727558542397085)
    ·
      refine ⟨113987703797147834453398907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303967210125727558542397085 113987703797147834453398907)
      ·
        refine ⟨170981555695721751680098361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113987703797147834453398907 170981555695721751680098361)
        ·
          refine ⟨128236166771791313760073771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170981555695721751680098361 128236166771791313760073771)
          ·
            refine ⟨192354250157686970640110657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128236166771791313760073771 192354250157686970640110657)
            ·
              refine ⟨144265687618265227980082993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192354250157686970640110657 144265687618265227980082993)
              ·
                refine ⟨108199265713698920985062245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144265687618265227980082993 108199265713698920985062245)
                ·
                  refine ⟨20287362321318547684699171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108199265713698920985062245 20287362321318547684699171)
                  ·
                    refine ⟨30431043481977821527048757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20287362321318547684699171 30431043481977821527048757)
                    ·
                      refine ⟨2852910326435420768160821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30431043481977821527048757 2852910326435420768160821)
                      ·
                        rfl

theorem cell23_5556023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_5556023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556023 prefixEnd_5556023 := by exact prefixLift 5556023
  have htrace : WordTrace (prefixWord ++ tailWord_5556023) baseStart_5556023 baseEnd_5556023 := by
    simpa [prefixWord, tailWord_5556023, baseEnd_5556023] using wordTrace_append hprefix tailTrace_5556023
  have hstable : (prefixWord ++ tailWord_5556023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556023).length < 2 ^ (prefixWord ++ tailWord_5556023).sum := by decide
  have hdescent : baseEnd_5556023 < baseStart_5556023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556030 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_5556030 : Nat := 118140960795 + 5556030 * 2 ^ 59
def prefixEnd_5556030 : Nat := 4983230072969 + 3 ^ 40 * 5556030 * 2
def baseEnd_5556030 : Nat := 950971306933334080257763

theorem tailTrace_5556030 : CollatzResearch.WordTrace tailWord_5556030 prefixEnd_5556030 950971306933334080257763 := by
  unfold tailWord_5556030
  simp only [CollatzResearch.WordTrace]
  refine ⟨25330632757682459902971193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135096708040973119482513029 25330632757682459902971193)
  ·
    refine ⟨18997974568261844927228395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25330632757682459902971193 18997974568261844927228395)
    ·
      refine ⟨28496961852392767390842593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18997974568261844927228395 28496961852392767390842593)
      ·
        refine ⟨21372721389294575543131945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28496961852392767390842593 21372721389294575543131945)
        ·
          refine ⟨16029541041970931657348959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21372721389294575543131945 16029541041970931657348959)
          ·
            refine ⟨24044311562956397486023439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16029541041970931657348959 24044311562956397486023439)
            ·
              refine ⟨36066467344434596229035159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24044311562956397486023439 36066467344434596229035159)
              ·
                refine ⟨54099701016651894343552739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36066467344434596229035159 54099701016651894343552739)
                ·
                  refine ⟨81149551524977841515329109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54099701016651894343552739 81149551524977841515329109)
                  ·
                    refine ⟨950971306933334080257763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81149551524977841515329109 950971306933334080257763)
                    ·
                      rfl

theorem cell23_5556030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_5556030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556030 prefixEnd_5556030 := by exact prefixLift 5556030
  have htrace : WordTrace (prefixWord ++ tailWord_5556030) baseStart_5556030 baseEnd_5556030 := by
    simpa [prefixWord, tailWord_5556030, baseEnd_5556030] using wordTrace_append hprefix tailTrace_5556030
  have hstable : (prefixWord ++ tailWord_5556030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556030).length < 2 ^ (prefixWord ++ tailWord_5556030).sum := by decide
  have hdescent : baseEnd_5556030 < baseStart_5556030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556037 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 1, 4, 2]
def baseStart_5556037 : Nat := 118140960795 + 5556037 * 2 ^ 59
def prefixEnd_5556037 : Nat := 4983230072969 + 3 ^ 40 * 5556037 * 2
def baseEnd_5556037 : Nat := 2852917515164583713385757

theorem tailTrace_5556037 : CollatzResearch.WordTrace tailWord_5556037 prefixEnd_5556037 2852917515164583713385757 := by
  unfold tailWord_5556037
  simp only [CollatzResearch.WordTrace]
  refine ⟨202645317372434319419274365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135096878248289546279516243 202645317372434319419274365)
  ·
    refine ⟨75991994014662869782227887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202645317372434319419274365 75991994014662869782227887)
    ·
      refine ⟨113987991021994304673341831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75991994014662869782227887 113987991021994304673341831)
      ·
        refine ⟨170981986532991457010012747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113987991021994304673341831 170981986532991457010012747)
        ·
          refine ⟨256472979799487185515019121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170981986532991457010012747 256472979799487185515019121)
          ·
            refine ⟨192354734849615389136264341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256472979799487185515019121 192354734849615389136264341)
            ·
              refine ⟨9016628196075721365762391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 192354734849615389136264341 9016628196075721365762391)
              ·
                refine ⟨13524942294113582048643587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9016628196075721365762391 13524942294113582048643587)
                ·
                  refine ⟨20287413441170373072965381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13524942294113582048643587 20287413441170373072965381)
                  ·
                    refine ⟨3803890020219444951181009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20287413441170373072965381 3803890020219444951181009)
                    ·
                      refine ⟨2852917515164583713385757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3803890020219444951181009 2852917515164583713385757)
                      ·
                        rfl

theorem cell23_5556037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 4, 2].length) (baseStart_5556037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556037 prefixEnd_5556037 := by exact prefixLift 5556037
  have htrace : WordTrace (prefixWord ++ tailWord_5556037) baseStart_5556037 baseEnd_5556037 := by
    simpa [prefixWord, tailWord_5556037, baseEnd_5556037] using wordTrace_append hprefix tailTrace_5556037
  have hstable : (prefixWord ++ tailWord_5556037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556037).length < 2 ^ (prefixWord ++ tailWord_5556037).sum := by decide
  have hdescent : baseEnd_5556037 < baseStart_5556037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556077 : List Nat := [1, 5, 1, 1, 1, 1, 4, 4, 5]
def baseStart_5556077 : Nat := 118140960795 + 5556077 * 2 ^ 59
def prefixEnd_5556077 : Nat := 4983230072969 + 3 ^ 40 * 5556077 * 2
def baseEnd_5556077 : Nat := 316993117154529284098397

theorem tailTrace_5556077 : CollatzResearch.WordTrace tailWord_5556077 prefixEnd_5556077 316993117154529284098397 := by
  unfold tailWord_5556077
  simp only [CollatzResearch.WordTrace]
  refine ⟨202646776292289406250730485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135097850861526270833820323 202646776292289406250730485)
  ·
    refine ⟨18998135277402131836005983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 202646776292289406250730485 18998135277402131836005983)
    ·
      refine ⟨28497202916103197754008975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18998135277402131836005983 28497202916103197754008975)
      ·
        refine ⟨42745804374154796631013463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28497202916103197754008975 42745804374154796631013463)
        ·
          refine ⟨64118706561232194946520195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42745804374154796631013463 64118706561232194946520195)
          ·
            refine ⟨96178059841848292419780293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64118706561232194946520195 96178059841848292419780293)
            ·
              refine ⟨18033386220346554828708805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96178059841848292419780293 18033386220346554828708805)
              ·
                refine ⟨3381259916314979030382901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18033386220346554828708805 3381259916314979030382901)
                ·
                  refine ⟨316993117154529284098397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3381259916314979030382901 316993117154529284098397)
                  ·
                    rfl

theorem cell23_5556077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_5556077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556077 prefixEnd_5556077 := by exact prefixLift 5556077
  have htrace : WordTrace (prefixWord ++ tailWord_5556077) baseStart_5556077 baseEnd_5556077 := by
    simpa [prefixWord, tailWord_5556077, baseEnd_5556077] using wordTrace_append hprefix tailTrace_5556077
  have hstable : (prefixWord ++ tailWord_5556077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556077).length < 2 ^ (prefixWord ++ tailWord_5556077).sum := by decide
  have hdescent : baseEnd_5556077 < baseStart_5556077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556083 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 7]
def baseStart_5556083 : Nat := 118140960795 + 5556083 * 2 ^ 59
def prefixEnd_5556083 : Nat := 4983230072969 + 3 ^ 40 * 5556083 * 2
def baseEnd_5556083 : Nat := 2852941135274690533410545

theorem tailTrace_5556083 : CollatzResearch.WordTrace tailWord_5556083 prefixEnd_5556083 2852941135274690533410545 := by
  unfold tailWord_5556083
  simp only [CollatzResearch.WordTrace]
  refine ⟨202646995130267669275448903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135097996753511779516965935 202646995130267669275448903)
  ·
    refine ⟨303970492695401503913173355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202646995130267669275448903 303970492695401503913173355)
    ·
      refine ⟨455955739043102255869760033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303970492695401503913173355 455955739043102255869760033)
      ·
        refine ⟨341966804282326691902320025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 455955739043102255869760033 341966804282326691902320025)
        ·
          refine ⟨256475103211745018926740019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341966804282326691902320025 256475103211745018926740019)
          ·
            refine ⟨384712654817617528390110029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256475103211745018926740019 384712654817617528390110029)
            ·
              refine ⟨144267245556606573146291261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 384712654817617528390110029 144267245556606573146291261)
              ·
                refine ⟨54100217083727464929859223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144267245556606573146291261 54100217083727464929859223)
                ·
                  refine ⟨81150325625591197394788835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54100217083727464929859223 81150325625591197394788835)
                  ·
                    refine ⟨121725488438386796092183253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81150325625591197394788835 121725488438386796092183253)
                    ·
                      refine ⟨2852941135274690533410545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121725488438386796092183253 2852941135274690533410545)
                      ·
                        rfl

theorem cell23_5556083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_5556083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556083 prefixEnd_5556083 := by exact prefixLift 5556083
  have htrace : WordTrace (prefixWord ++ tailWord_5556083) baseStart_5556083 baseEnd_5556083 := by
    simpa [prefixWord, tailWord_5556083, baseEnd_5556083] using wordTrace_append hprefix tailTrace_5556083
  have hstable : (prefixWord ++ tailWord_5556083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556083).length < 2 ^ (prefixWord ++ tailWord_5556083).sum := by decide
  have hdescent : baseEnd_5556083 < baseStart_5556083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556177 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 7, 1, 3]
def baseStart_5556177 : Nat := 118140960795 + 5556177 * 2 ^ 59
def prefixEnd_5556177 : Nat := 4983230072969 + 3 ^ 40 * 5556177 * 2
def baseEnd_5556177 : Nat := 2852989402456213165635113

theorem tailTrace_5556177 : CollatzResearch.WordTrace tailWord_5556177 prefixEnd_5556177 2852989402456213165635113 := by
  unfold tailWord_5556177
  simp only [CollatzResearch.WordTrace]
  refine ⟨202650423591927123329370785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135100282394618082219580523 202650423591927123329370785)
  ·
    refine ⟨151987817693945342497028089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202650423591927123329370785 151987817693945342497028089)
    ·
      refine ⟨113990863270459006872771067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151987817693945342497028089 113990863270459006872771067)
      ·
        refine ⟨170986294905688510309156601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113990863270459006872771067 170986294905688510309156601)
        ·
          refine ⟨128239721179266382731867451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170986294905688510309156601 128239721179266382731867451)
          ·
            refine ⟨192359581768899574097801177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128239721179266382731867451 192359581768899574097801177)
            ·
              refine ⟨144269686326674680573350883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192359581768899574097801177 144269686326674680573350883)
              ·
                refine ⟨216404529490012020860026325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144269686326674680573350883 216404529490012020860026325)
                ·
                  refine ⟨5071981159922156738906867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 216404529490012020860026325 5071981159922156738906867)
                  ·
                    refine ⟨7607971739883235108360301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5071981159922156738906867 7607971739883235108360301)
                    ·
                      refine ⟨2852989402456213165635113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7607971739883235108360301 2852989402456213165635113)
                      ·
                        rfl

theorem cell23_5556177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_5556177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556177 prefixEnd_5556177 := by exact prefixLift 5556177
  have htrace : WordTrace (prefixWord ++ tailWord_5556177) baseStart_5556177 baseEnd_5556177 := by
    simpa [prefixWord, tailWord_5556177, baseEnd_5556177] using wordTrace_append hprefix tailTrace_5556177
  have hstable : (prefixWord ++ tailWord_5556177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556177).length < 2 ^ (prefixWord ++ tailWord_5556177).sum := by decide
  have hdescent : baseEnd_5556177 < baseStart_5556177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556217 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 3, 1, 4]
def baseStart_5556217 : Nat := 118140960795 + 5556217 * 2 ^ 59
def prefixEnd_5556217 : Nat := 4983230072969 + 3 ^ 40 * 5556217 * 2
def baseEnd_5556217 : Nat := 2853009941682393009134929

theorem tailTrace_5556217 : CollatzResearch.WordTrace tailWord_5556217 prefixEnd_5556217 2853009941682393009134929 := by
  unfold tailWord_5556217
  simp only [CollatzResearch.WordTrace]
  refine ⟨202651882511782210160826905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135101255007854806773884603 202651882511782210160826905)
  ·
    refine ⟨151988911883836657620620179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202651882511782210160826905 151988911883836657620620179)
    ·
      refine ⟨227983367825754986430930269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151988911883836657620620179 227983367825754986430930269)
      ·
        refine ⟨85493762934658119911598851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227983367825754986430930269 85493762934658119911598851)
        ·
          refine ⟨128240644401987179867398277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85493762934658119911598851 128240644401987179867398277)
          ·
            refine ⟨24045120825372596225137177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128240644401987179867398277 24045120825372596225137177)
            ·
              refine ⟨18033840619029447168852883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24045120825372596225137177 18033840619029447168852883)
              ·
                refine ⟨27050760928544170753279325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18033840619029447168852883 27050760928544170753279325)
                ·
                  refine ⟨10144035348204064032479747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27050760928544170753279325 10144035348204064032479747)
                  ·
                    refine ⟨15216053022306096048719621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10144035348204064032479747 15216053022306096048719621)
                    ·
                      refine ⟨2853009941682393009134929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15216053022306096048719621 2853009941682393009134929)
                      ·
                        rfl

theorem cell23_5556217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_5556217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556217 prefixEnd_5556217 := by exact prefixLift 5556217
  have htrace : WordTrace (prefixWord ++ tailWord_5556217) baseStart_5556217 baseEnd_5556217 := by
    simpa [prefixWord, tailWord_5556217, baseEnd_5556217] using wordTrace_append hprefix tailTrace_5556217
  have hstable : (prefixWord ++ tailWord_5556217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556217).length < 2 ^ (prefixWord ++ tailWord_5556217).sum := by decide
  have hdescent : baseEnd_5556217 < baseStart_5556217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556231 : List Nat := [1, 1, 4, 3, 1, 4, 2, 1, 1, 5]
def baseStart_5556231 : Nat := 118140960795 + 5556231 * 2 ^ 59
def prefixEnd_5556231 : Nat := 4983230072969 + 3 ^ 40 * 5556231 * 2
def baseEnd_5556231 : Nat := 951005710137185318119955

theorem tailTrace_5556231 : CollatzResearch.WordTrace tailWord_5556231 prefixEnd_5556231 951005710137185318119955 := by
  unfold tailWord_5556231
  simp only [CollatzResearch.WordTrace]
  refine ⟨202652393133731490551836547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135101595422487660367891031 202652393133731490551836547)
  ·
    refine ⟨303978589700597235827754821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202652393133731490551836547 303978589700597235827754821)
    ·
      refine ⟨56995985568861981717704029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303978589700597235827754821 56995985568861981717704029)
      ·
        refine ⟨21373494588323243144139011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56995985568861981717704029 21373494588323243144139011)
        ·
          refine ⟨32060241882484864716208517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21373494588323243144139011 32060241882484864716208517)
          ·
            refine ⟨6011295352965912134289097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32060241882484864716208517 6011295352965912134289097)
            ·
              refine ⟨4508471514724434100716823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6011295352965912134289097 4508471514724434100716823)
              ·
                refine ⟨6762707272086651151075235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4508471514724434100716823 6762707272086651151075235)
                ·
                  refine ⟨10144060908129976726612853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6762707272086651151075235 10144060908129976726612853)
                  ·
                    refine ⟨951005710137185318119955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10144060908129976726612853 951005710137185318119955)
                    ·
                      rfl

theorem cell23_5556231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_5556231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556231 prefixEnd_5556231 := by exact prefixLift 5556231
  have htrace : WordTrace (prefixWord ++ tailWord_5556231) baseStart_5556231 baseEnd_5556231 := by
    simpa [prefixWord, tailWord_5556231, baseEnd_5556231] using wordTrace_append hprefix tailTrace_5556231
  have hstable : (prefixWord ++ tailWord_5556231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556231).length < 2 ^ (prefixWord ++ tailWord_5556231).sum := by decide
  have hdescent : baseEnd_5556231 < baseStart_5556231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556261 : List Nat := [1, 3, 1, 2, 2, 4, 3, 1, 2, 4]
def baseStart_5556261 : Nat := 118140960795 + 5556261 * 2 ^ 59
def prefixEnd_5556261 : Nat := 4983230072969 + 3 ^ 40 * 5556261 * 2
def baseEnd_5556261 : Nat := 951010844943730278994909

theorem tailTrace_5556261 : CollatzResearch.WordTrace tailWord_5556261 prefixEnd_5556261 951010844943730278994909 := by
  unfold tailWord_5556261
  simp only [CollatzResearch.WordTrace]
  refine ⟨202653487323622805675428637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135102324882415203783619091 202653487323622805675428637)
  ·
    refine ⟨75995057746358552128285739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202653487323622805675428637 75995057746358552128285739)
    ·
      refine ⟨113992586619537828192428609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75995057746358552128285739 113992586619537828192428609)
      ·
        refine ⟨85494439964653371144321457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113992586619537828192428609 85494439964653371144321457)
        ·
          refine ⟨64120829973490028358241093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85494439964653371144321457 64120829973490028358241093)
          ·
            refine ⟨12022655620029380317170205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64120829973490028358241093 12022655620029380317170205)
            ·
              refine ⟨4508495857511017618938827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12022655620029380317170205 4508495857511017618938827)
              ·
                refine ⟨6762743786266526428408241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4508495857511017618938827 6762743786266526428408241)
                ·
                  refine ⟨5072057839699894821306181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6762743786266526428408241 5072057839699894821306181)
                  ·
                    refine ⟨951010844943730278994909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5072057839699894821306181 951010844943730278994909)
                    ·
                      rfl

theorem cell23_5556261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_5556261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556261 prefixEnd_5556261 := by exact prefixLift 5556261
  have htrace : WordTrace (prefixWord ++ tailWord_5556261) baseStart_5556261 baseEnd_5556261 := by
    simpa [prefixWord, tailWord_5556261, baseEnd_5556261] using wordTrace_append hprefix tailTrace_5556261
  have hstable : (prefixWord ++ tailWord_5556261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556261).length < 2 ^ (prefixWord ++ tailWord_5556261).sum := by decide
  have hdescent : baseEnd_5556261 < baseStart_5556261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556267 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 3]
def baseStart_5556267 : Nat := 118140960795 + 5556267 * 2 ^ 59
def prefixEnd_5556267 : Nat := 4983230072969 + 3 ^ 40 * 5556267 * 2
def baseEnd_5556267 : Nat := 2853035615715117813509699

theorem tailTrace_5556267 : CollatzResearch.WordTrace tailWord_5556267 prefixEnd_5556267 2853035615715117813509699 := by
  unfold tailWord_5556267
  simp only [CollatzResearch.WordTrace]
  refine ⟨202653706161601068700147055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135102470774400712466764703 202653706161601068700147055)
  ·
    refine ⟨303980559242401603050220583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202653706161601068700147055 303980559242401603050220583)
    ·
      refine ⟨455970838863602404575330875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303980559242401603050220583 455970838863602404575330875)
      ·
        refine ⟨683956258295403606862996313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455970838863602404575330875 683956258295403606862996313)
        ·
          refine ⟨512967193721552705147247235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683956258295403606862996313 512967193721552705147247235)
          ·
            refine ⟨769450790582329057720870853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512967193721552705147247235 769450790582329057720870853)
            ·
              refine ⟨144272023234186698322663285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 769450790582329057720870853 144272023234186698322663285)
              ·
                refine ⟨13525502178205002967749683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144272023234186698322663285 13525502178205002967749683)
                ·
                  refine ⟨20288253267307504451624525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13525502178205002967749683 20288253267307504451624525)
                  ·
                    refine ⟨7608094975240314169359197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20288253267307504451624525 7608094975240314169359197)
                    ·
                      refine ⟨2853035615715117813509699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7608094975240314169359197 2853035615715117813509699)
                      ·
                        rfl

theorem cell23_5556267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 3].length) (baseStart_5556267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556267 prefixEnd_5556267 := by exact prefixLift 5556267
  have htrace : WordTrace (prefixWord ++ tailWord_5556267) baseStart_5556267 baseEnd_5556267 := by
    simpa [prefixWord, tailWord_5556267, baseEnd_5556267] using wordTrace_append hprefix tailTrace_5556267
  have hstable : (prefixWord ++ tailWord_5556267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556267).length < 2 ^ (prefixWord ++ tailWord_5556267).sum := by decide
  have hdescent : baseEnd_5556267 < baseStart_5556267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556274 : List Nat := [3, 2, 1, 1, 2, 5, 2, 7]
def baseStart_5556274 : Nat := 118140960795 + 5556274 * 2 ^ 59
def prefixEnd_5556274 : Nat := 4983230072969 + 3 ^ 40 * 5556274 * 2
def baseEnd_5556274 : Nat := 105668118891840714300821

theorem tailTrace_5556274 : CollatzResearch.WordTrace tailWord_5556274 prefixEnd_5556274 105668118891840714300821 := by
  unfold tailWord_5556274
  simp only [CollatzResearch.WordTrace]
  refine ⟨50663490368143927223912969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135102640981717139263767917 50663490368143927223912969)
  ·
    refine ⟨37997617776107945417934727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50663490368143927223912969 37997617776107945417934727)
    ·
      refine ⟨56996426664161918126902091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37997617776107945417934727 56996426664161918126902091)
      ·
        refine ⟨85494639996242877190353137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56996426664161918126902091 85494639996242877190353137)
        ·
          refine ⟨64120979997182157892764853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85494639996242877190353137 64120979997182157892764853)
          ·
            refine ⟨6011341874735827302446705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64120979997182157892764853 6011341874735827302446705)
            ·
              refine ⟨4508506406051870476835029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6011341874735827302446705 4508506406051870476835029)
              ·
                refine ⟨105668118891840714300821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4508506406051870476835029 105668118891840714300821)
                ·
                  rfl

theorem cell23_5556274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 7].length) (baseStart_5556274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556274 prefixEnd_5556274 := by exact prefixLift 5556274
  have htrace : WordTrace (prefixWord ++ tailWord_5556274) baseStart_5556274 baseEnd_5556274 := by
    simpa [prefixWord, tailWord_5556274, baseEnd_5556274] using wordTrace_append hprefix tailTrace_5556274
  have hstable : (prefixWord ++ tailWord_5556274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556274).length < 2 ^ (prefixWord ++ tailWord_5556274).sum := by decide
  have hdescent : baseEnd_5556274 < baseStart_5556274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556284 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 6, 1, 3]
def baseStart_5556284 : Nat := 118140960795 + 5556284 * 2 ^ 59
def prefixEnd_5556284 : Nat := 4983230072969 + 3 ^ 40 * 5556284 * 2
def baseEnd_5556284 : Nat := 2853044344886244246997121

theorem tailTrace_5556284 : CollatzResearch.WordTrace tailWord_5556284 prefixEnd_5556284 2853044344886244246997121 := by
  unfold tailWord_5556284
  simp only [CollatzResearch.WordTrace]
  refine ⟨101327163101269740301757953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135102884135026320402343937 101327163101269740301757953)
  ·
    refine ⟨75995372325952305226318465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101327163101269740301757953 75995372325952305226318465)
    ·
      refine ⟨56996529244464228919738849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75995372325952305226318465 56996529244464228919738849)
      ·
        refine ⟨42747396933348171689804137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56996529244464228919738849 42747396933348171689804137)
        ·
          refine ⟨32060547700011128767353103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42747396933348171689804137 32060547700011128767353103)
          ·
            refine ⟨48090821550016693151029655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32060547700011128767353103 48090821550016693151029655)
            ·
              refine ⟨72136232325025039726544483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48090821550016693151029655 72136232325025039726544483)
              ·
                refine ⟨108204348487537559589816725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72136232325025039726544483 108204348487537559589816725)
                ·
                  refine ⟨5072078835353323105772659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108204348487537559589816725 5072078835353323105772659)
                  ·
                    refine ⟨7608118253029984658658989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5072078835353323105772659 7608118253029984658658989)
                    ·
                      refine ⟨2853044344886244246997121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7608118253029984658658989 2853044344886244246997121)
                      ·
                        rfl

theorem cell23_5556284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_5556284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556284 prefixEnd_5556284 := by exact prefixLift 5556284
  have htrace : WordTrace (prefixWord ++ tailWord_5556284) baseStart_5556284 baseEnd_5556284 := by
    simpa [prefixWord, tailWord_5556284, baseEnd_5556284] using wordTrace_append hprefix tailTrace_5556284
  have hstable : (prefixWord ++ tailWord_5556284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556284).length < 2 ^ (prefixWord ++ tailWord_5556284).sum := by decide
  have hdescent : baseEnd_5556284 < baseStart_5556284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556301 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_5556301 : Nat := 118140960795 + 5556301 * 2 ^ 59
def prefixEnd_5556301 : Nat := 4983230072969 + 3 ^ 40 * 5556301 * 2
def baseEnd_5556301 : Nat := 2853053074057370680484543

theorem tailTrace_5556301 : CollatzResearch.WordTrace tailWord_5556301 prefixEnd_5556301 2853053074057370680484543 := by
  unfold tailWord_5556301
  simp only [CollatzResearch.WordTrace]
  refine ⟨202654946243477892506884757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135103297495651928337923171 202654946243477892506884757)
  ·
    refine ⟨9499450605163026211260223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 202654946243477892506884757 9499450605163026211260223)
    ·
      refine ⟨14249175907744539316890335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9499450605163026211260223 14249175907744539316890335)
      ·
        refine ⟨21373763861616808975335503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14249175907744539316890335 21373763861616808975335503)
        ·
          refine ⟨32060645792425213463003255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21373763861616808975335503 32060645792425213463003255)
          ·
            refine ⟨48090968688637820194504883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32060645792425213463003255 48090968688637820194504883)
            ·
              refine ⟨72136453032956730291757325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48090968688637820194504883 72136453032956730291757325)
              ·
                refine ⟨27051169887358773859408997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72136453032956730291757325 27051169887358773859408997)
                ·
                  refine ⟨5072094353879770098639187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27051169887358773859408997 5072094353879770098639187)
                  ·
                    refine ⟨7608141530819655147958781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5072094353879770098639187 7608141530819655147958781)
                    ·
                      refine ⟨2853053074057370680484543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7608141530819655147958781 2853053074057370680484543)
                      ·
                        rfl

theorem cell23_5556301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_5556301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556301 prefixEnd_5556301 := by exact prefixLift 5556301
  have htrace : WordTrace (prefixWord ++ tailWord_5556301) baseStart_5556301 baseEnd_5556301 := by
    simpa [prefixWord, tailWord_5556301, baseEnd_5556301] using wordTrace_append hprefix tailTrace_5556301
  have hstable : (prefixWord ++ tailWord_5556301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556301).length < 2 ^ (prefixWord ++ tailWord_5556301).sum := by decide
  have hdescent : baseEnd_5556301 < baseStart_5556301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556327 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_5556327 : Nat := 118140960795 + 5556327 * 2 ^ 59
def prefixEnd_5556327 : Nat := 4983230072969 + 3 ^ 40 * 5556327 * 2
def baseEnd_5556327 : Nat := 2853066424554387578759423

theorem tailTrace_5556327 : CollatzResearch.WordTrace tailWord_5556327 prefixEnd_5556327 2853066424554387578759423 := by
  unfold tailWord_5556327
  simp only [CollatzResearch.WordTrace]
  refine ⟨202655894541383698947331235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135103929694255799298220823 202655894541383698947331235)
  ·
    refine ⟨303983841812075548420996853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202655894541383698947331235 303983841812075548420996853)
    ·
      refine ⟨28498485169882082664468455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 303983841812075548420996853 28498485169882082664468455)
      ·
        refine ⟨42747727754823123996702683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28498485169882082664468455 42747727754823123996702683)
        ·
          refine ⟨64121591632234685995054025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42747727754823123996702683 64121591632234685995054025)
          ·
            refine ⟨48091193724176014496290519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64121591632234685995054025 48091193724176014496290519)
            ·
              refine ⟨72136790586264021744435779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48091193724176014496290519 72136790586264021744435779)
              ·
                refine ⟨108205185879396032616653669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72136790586264021744435779 108205185879396032616653669)
                ·
                  refine ⟨20288472352386756115622563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108205185879396032616653669 20288472352386756115622563)
                  ·
                    refine ⟨30432708528580134173433845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20288472352386756115622563 30432708528580134173433845)
                    ·
                      refine ⟨2853066424554387578759423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30432708528580134173433845 2853066424554387578759423)
                      ·
                        rfl

theorem cell23_5556327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_5556327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556327 prefixEnd_5556327 := by exact prefixLift 5556327
  have htrace : WordTrace (prefixWord ++ tailWord_5556327) baseStart_5556327 baseEnd_5556327 := by
    simpa [prefixWord, tailWord_5556327, baseEnd_5556327] using wordTrace_append hprefix tailTrace_5556327
  have hstable : (prefixWord ++ tailWord_5556327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556327).length < 2 ^ (prefixWord ++ tailWord_5556327).sum := by decide
  have hdescent : baseEnd_5556327 < baseStart_5556327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556377 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 4, 5]
def baseStart_5556377 : Nat := 118140960795 + 5556377 * 2 ^ 59
def prefixEnd_5556377 : Nat := 4983230072969 + 3 ^ 40 * 5556377 * 2
def baseEnd_5556377 : Nat := 951030699529037461044731

theorem tailTrace_5556377 : CollatzResearch.WordTrace tailWord_5556377 prefixEnd_5556377 951030699529037461044731 := by
  unfold tailWord_5556377
  simp only [CollatzResearch.WordTrace]
  refine ⟨202657718191202557486651385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135105145460801704991100923 202657718191202557486651385)
  ·
    refine ⟨151993288643401918114988539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202657718191202557486651385 151993288643401918114988539)
    ·
      refine ⟨227989932965102877172482809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151993288643401918114988539 227989932965102877172482809)
      ·
        refine ⟨170992449723827157879362107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227989932965102877172482809 170992449723827157879362107)
        ·
          refine ⟨256488674585740736819043161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170992449723827157879362107 256488674585740736819043161)
          ·
            refine ⟨192366505939305552614282371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256488674585740736819043161 192366505939305552614282371)
            ·
              refine ⟨288549758908958328921423557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192366505939305552614282371 288549758908958328921423557)
              ·
                refine ⟨54103079795429686672766917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 288549758908958328921423557 54103079795429686672766917)
                ·
                  refine ⟨10144327461643066251143797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54103079795429686672766917 10144327461643066251143797)
                  ·
                    refine ⟨951030699529037461044731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10144327461643066251143797 951030699529037461044731)
                    ·
                      rfl

theorem cell23_5556377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 5].length) (baseStart_5556377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556377 prefixEnd_5556377 := by exact prefixLift 5556377
  have htrace : WordTrace (prefixWord ++ tailWord_5556377) baseStart_5556377 baseEnd_5556377 := by
    simpa [prefixWord, tailWord_5556377, baseEnd_5556377] using wordTrace_append hprefix tailTrace_5556377
  have hstable : (prefixWord ++ tailWord_5556377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556377).length < 2 ^ (prefixWord ++ tailWord_5556377).sum := by decide
  have hdescent : baseEnd_5556377 < baseStart_5556377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556427 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 6]
def baseStart_5556427 : Nat := 118140960795 + 5556427 * 2 ^ 59
def prefixEnd_5556427 : Nat := 4983230072969 + 3 ^ 40 * 5556427 * 2
def baseEnd_5556427 : Nat := 2853117772619837187508963

theorem tailTrace_5556427 : CollatzResearch.WordTrace tailWord_5556427 prefixEnd_5556427 2853117772619837187508963 := by
  unfold tailWord_5556427
  simp only [CollatzResearch.WordTrace]
  refine ⟨202659541841021416025971535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135106361227347610683981023 202659541841021416025971535)
  ·
    refine ⟨303989312761532124038957303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202659541841021416025971535 303989312761532124038957303)
    ·
      refine ⟨455983969142298186058435955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303989312761532124038957303 455983969142298186058435955)
      ·
        refine ⟨683975953713447279087653933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455983969142298186058435955 683975953713447279087653933)
        ·
          refine ⟨256490982642542729657870225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 683975953713447279087653933 256490982642542729657870225)
          ·
            refine ⟨192368236981907047243402669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256490982642542729657870225 192368236981907047243402669)
            ·
              refine ⟨72138088868215142716276001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192368236981907047243402669 72138088868215142716276001)
              ·
                refine ⟨54103566651161357037207001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72138088868215142716276001 54103566651161357037207001)
                ·
                  refine ⟨40577674988371017777905251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54103566651161357037207001 40577674988371017777905251)
                  ·
                    refine ⟨60866512482556526666857877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40577674988371017777905251 60866512482556526666857877)
                    ·
                      refine ⟨2853117772619837187508963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60866512482556526666857877 2853117772619837187508963)
                      ·
                        rfl

theorem cell23_5556427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 6].length) (baseStart_5556427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556427 prefixEnd_5556427 := by exact prefixLift 5556427
  have htrace : WordTrace (prefixWord ++ tailWord_5556427) baseStart_5556427 baseEnd_5556427 := by
    simpa [prefixWord, tailWord_5556427, baseEnd_5556427] using wordTrace_append hprefix tailTrace_5556427
  have hstable : (prefixWord ++ tailWord_5556427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556427).length < 2 ^ (prefixWord ++ tailWord_5556427).sum := by decide
  have hdescent : baseEnd_5556427 < baseStart_5556427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556457 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 6]
def baseStart_5556457 : Nat := 118140960795 + 5556457 * 2 ^ 59
def prefixEnd_5556457 : Nat := 4983230072969 + 3 ^ 40 * 5556457 * 2
def baseEnd_5556457 : Nat := 2853133177039472070133825

theorem tailTrace_5556457 : CollatzResearch.WordTrace tailWord_5556457 prefixEnd_5556457 2853133177039472070133825 := by
  unfold tailWord_5556457
  simp only [CollatzResearch.WordTrace]
  refine ⟨202660636030912731149563625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135107090687275154099709083 202660636030912731149563625)
  ·
    refine ⟨151995477023184548362172719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202660636030912731149563625 151995477023184548362172719)
    ·
      refine ⟨227993215534776822543259079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151995477023184548362172719 227993215534776822543259079)
      ·
        refine ⟨341989823302165233814888619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227993215534776822543259079 341989823302165233814888619)
        ·
          refine ⟨512984734953247850722332929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341989823302165233814888619 512984734953247850722332929)
          ·
            refine ⟨384738551214935888041749697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512984734953247850722332929 384738551214935888041749697)
            ·
              refine ⟨288553913411201916031312273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384738551214935888041749697 288553913411201916031312273)
              ·
                refine ⟨216415435058401437023484205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288553913411201916031312273 216415435058401437023484205)
                ·
                  refine ⟨81155788146900538883806577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216415435058401437023484205 81155788146900538883806577)
                  ·
                    refine ⟨60866841110175404162854933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81155788146900538883806577 60866841110175404162854933)
                    ·
                      refine ⟨2853133177039472070133825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60866841110175404162854933 2853133177039472070133825)
                      ·
                        rfl

theorem cell23_5556457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_5556457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556457 prefixEnd_5556457 := by exact prefixLift 5556457
  have htrace : WordTrace (prefixWord ++ tailWord_5556457) baseStart_5556457 baseEnd_5556457 := by
    simpa [prefixWord, tailWord_5556457, baseEnd_5556457] using wordTrace_append hprefix tailTrace_5556457
  have hstable : (prefixWord ++ tailWord_5556457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556457).length < 2 ^ (prefixWord ++ tailWord_5556457).sum := by decide
  have hdescent : baseEnd_5556457 < baseStart_5556457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556488 : List Nat := [2, 1, 3, 2, 3, 3, 2, 1, 6]
def baseStart_5556488 : Nat := 118140960795 + 5556488 * 2 ^ 59
def prefixEnd_5556488 : Nat := 4983230072969 + 3 ^ 40 * 5556488 * 2
def baseEnd_5556488 : Nat := 317016566104417938760687

theorem tailTrace_5556488 : CollatzResearch.WordTrace tailWord_5556488 prefixEnd_5556488 317016566104417938760687 := by
  unfold tailWord_5556488
  simp only [CollatzResearch.WordTrace]
  refine ⟨101330883346900211721971059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135107844462533615629294745 101330883346900211721971059)
  ·
    refine ⟨151996325020350317582956589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101330883346900211721971059 151996325020350317582956589)
    ·
      refine ⟨56998621882631369093608721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151996325020350317582956589 56998621882631369093608721)
      ·
        refine ⟨42748966411973526820206541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56998621882631369093608721 42748966411973526820206541)
        ·
          refine ⟨16030862404490072557577453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42748966411973526820206541 16030862404490072557577453)
          ·
            refine ⟨6011573401683777209091545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16030862404490072557577453 6011573401683777209091545)
            ·
              refine ⟨4508680051262832906818659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6011573401683777209091545 4508680051262832906818659)
              ·
                refine ⟨6763020076894249360227989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4508680051262832906818659 6763020076894249360227989)
                ·
                  refine ⟨317016566104417938760687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6763020076894249360227989 317016566104417938760687)
                  ·
                    rfl

theorem cell23_5556488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 6].length) (baseStart_5556488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556488 prefixEnd_5556488 := by exact prefixLift 5556488
  have htrace : WordTrace (prefixWord ++ tailWord_5556488) baseStart_5556488 baseEnd_5556488 := by
    simpa [prefixWord, tailWord_5556488, baseEnd_5556488] using wordTrace_append hprefix tailTrace_5556488
  have hstable : (prefixWord ++ tailWord_5556488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556488).length < 2 ^ (prefixWord ++ tailWord_5556488).sum := by decide
  have hdescent : baseEnd_5556488 < baseStart_5556488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556491 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 4, 3, 2]
def baseStart_5556491 : Nat := 118140960795 + 5556491 * 2 ^ 59
def prefixEnd_5556491 : Nat := 4983230072969 + 3 ^ 40 * 5556491 * 2
def baseEnd_5556491 : Nat := 2853150635381724937108669

theorem tailTrace_5556491 : CollatzResearch.WordTrace tailWord_5556491 prefixEnd_5556491 2853150635381724937108669 := by
  unfold tailWord_5556491
  simp only [CollatzResearch.WordTrace]
  refine ⟨202661876112789554956301327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135107917408526369970867551 202661876112789554956301327)
  ·
    refine ⟨303992814169184332434451991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202661876112789554956301327 303992814169184332434451991)
    ·
      refine ⟨455989221253776498651677987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303992814169184332434451991 455989221253776498651677987)
      ·
        refine ⟨683983831880664747977516981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455989221253776498651677987 683983831880664747977516981)
        ·
          refine ⟨64123484238812320122892217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 683983831880664747977516981 64123484238812320122892217)
          ·
            refine ⟨48092613179109240092169163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64123484238812320122892217 48092613179109240092169163)
            ·
              refine ⟨72138919768663860138253745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48092613179109240092169163 72138919768663860138253745)
              ·
                refine ⟨54104189826497895103690309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72138919768663860138253745 54104189826497895103690309)
                ·
                  refine ⟨10144535592468355331941933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54104189826497895103690309 10144535592468355331941933)
                  ·
                    refine ⟨3804200847175633249478225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10144535592468355331941933 3804200847175633249478225)
                    ·
                      refine ⟨2853150635381724937108669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3804200847175633249478225 2853150635381724937108669)
                      ·
                        rfl

theorem cell23_5556491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 3, 2].length) (baseStart_5556491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556491 prefixEnd_5556491 := by exact prefixLift 5556491
  have htrace : WordTrace (prefixWord ++ tailWord_5556491) baseStart_5556491 baseEnd_5556491 := by
    simpa [prefixWord, tailWord_5556491, baseEnd_5556491] using wordTrace_append hprefix tailTrace_5556491
  have hstable : (prefixWord ++ tailWord_5556491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556491).length < 2 ^ (prefixWord ++ tailWord_5556491).sum := by decide
  have hdescent : baseEnd_5556491 < baseStart_5556491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556501 : List Nat := [1, 3, 2, 1, 2, 1, 5, 2, 1, 5]
def baseStart_5556501 : Nat := 118140960795 + 5556501 * 2 ^ 59
def prefixEnd_5556501 : Nat := 4983230072969 + 3 ^ 40 * 5556501 * 2
def baseEnd_5556501 : Nat := 951051923396089965994541

theorem tailTrace_5556501 : CollatzResearch.WordTrace tailWord_5556501 prefixEnd_5556501 951051923396089965994541 := by
  unfold tailWord_5556501
  simp only [CollatzResearch.WordTrace]
  refine ⟨202662240842753326664165357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135108160561835551109443571 202662240842753326664165357)
  ·
    refine ⟨75998340316032497499062009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202662240842753326664165357 75998340316032497499062009)
    ·
      refine ⟨56998755237024373124296507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75998340316032497499062009 56998755237024373124296507)
      ·
        refine ⟨85498132855536559686444761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56998755237024373124296507 85498132855536559686444761)
        ·
          refine ⟨64123599641652419764833571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85498132855536559686444761 64123599641652419764833571)
          ·
            refine ⟨96185399462478629647250357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64123599641652419764833571 96185399462478629647250357)
            ·
              refine ⟨9017381199607371529429721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96185399462478629647250357 9017381199607371529429721)
              ·
                refine ⟨6763035899705528647072291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9017381199607371529429721 6763035899705528647072291)
                ·
                  refine ⟨10144553849558292970608437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6763035899705528647072291 10144553849558292970608437)
                  ·
                    refine ⟨951051923396089965994541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10144553849558292970608437 951051923396089965994541)
                    ·
                      rfl

theorem cell23_5556501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_5556501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556501 prefixEnd_5556501 := by exact prefixLift 5556501
  have htrace : WordTrace (prefixWord ++ tailWord_5556501) baseStart_5556501 baseEnd_5556501 := by
    simpa [prefixWord, tailWord_5556501, baseEnd_5556501] using wordTrace_append hprefix tailTrace_5556501
  have hstable : (prefixWord ++ tailWord_5556501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556501).length < 2 ^ (prefixWord ++ tailWord_5556501).sum := by decide
  have hdescent : baseEnd_5556501 < baseStart_5556501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556526 : List Nat := [4, 1, 3, 3, 2, 1, 2, 2, 1, 4]
def baseStart_5556526 : Nat := 118140960795 + 5556526 * 2 ^ 59
def prefixEnd_5556526 : Nat := 4983230072969 + 3 ^ 40 * 5556526 * 2
def baseEnd_5556526 : Nat := 951056202401544100057003

theorem tailTrace_5556526 : CollatzResearch.WordTrace tailWord_5556526 prefixEnd_5556526 951056202401544100057003 := by
  unfold tailWord_5556526
  simp only [CollatzResearch.WordTrace]
  refine ⟨25332894083457844491728179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135108768445108503955883621 25332894083457844491728179)
  ·
    refine ⟨37999341125186766737592269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25332894083457844491728179 37999341125186766737592269)
    ·
      refine ⟨14249752921945037526597101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37999341125186766737592269 14249752921945037526597101)
      ·
        refine ⟨5343657345729389072473913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14249752921945037526597101 5343657345729389072473913)
        ·
          refine ⟨4007743009297041804355435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5343657345729389072473913 4007743009297041804355435)
          ·
            refine ⟨6011614513945562706533153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4007743009297041804355435 6011614513945562706533153)
            ·
              refine ⟨4508710885459172029899865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6011614513945562706533153 4508710885459172029899865)
              ·
                refine ⟨3381533164094379022424899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4508710885459172029899865 3381533164094379022424899)
                ·
                  refine ⟨5072299746141568533637349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3381533164094379022424899 5072299746141568533637349)
                  ·
                    refine ⟨951056202401544100057003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5072299746141568533637349 951056202401544100057003)
                    ·
                      rfl

theorem cell23_5556526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_5556526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556526 prefixEnd_5556526 := by exact prefixLift 5556526
  have htrace : WordTrace (prefixWord ++ tailWord_5556526) baseStart_5556526 baseEnd_5556526 := by
    simpa [prefixWord, tailWord_5556526, baseEnd_5556526] using wordTrace_append hprefix tailTrace_5556526
  have hstable : (prefixWord ++ tailWord_5556526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556526).length < 2 ^ (prefixWord ++ tailWord_5556526).sum := by decide
  have hdescent : baseEnd_5556526 < baseStart_5556526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556532 : List Nat := [2, 5, 1, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_5556532 : Nat := 118140960795 + 5556532 * 2 ^ 59
def prefixEnd_5556532 : Nat := 4983230072969 + 3 ^ 40 * 5556532 * 2
def baseEnd_5556532 : Nat := 2853171688088559276695981

theorem tailTrace_5556532 : CollatzResearch.WordTrace tailWord_5556532 prefixEnd_5556532 2853171688088559276695981 := by
  unfold tailWord_5556532
  simp only [CollatzResearch.WordTrace]
  refine ⟨101331685752820509479271925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135108914337094012639029233 101331685752820509479271925)
  ·
    refine ⟨9499845539326922763681743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101331685752820509479271925 9499845539326922763681743)
    ·
      refine ⟨14249768308990384145522615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9499845539326922763681743 14249768308990384145522615)
      ·
        refine ⟨21374652463485576218283923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14249768308990384145522615 21374652463485576218283923)
        ·
          refine ⟨32061978695228364327425885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21374652463485576218283923 32061978695228364327425885)
          ·
            refine ⟨12023242010710636622784707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32061978695228364327425885 12023242010710636622784707)
            ·
              refine ⟨18034863016065954934177061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12023242010710636622784707 18034863016065954934177061)
              ·
                refine ⟨3381536815512366550158199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18034863016065954934177061 3381536815512366550158199)
                ·
                  refine ⟨5072305223268549825237299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3381536815512366550158199 5072305223268549825237299)
                  ·
                    refine ⟨7608457834902824737855949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5072305223268549825237299 7608457834902824737855949)
                    ·
                      refine ⟨2853171688088559276695981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7608457834902824737855949 2853171688088559276695981)
                      ·
                        rfl

theorem cell23_5556532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_5556532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556532 prefixEnd_5556532 := by exact prefixLift 5556532
  have htrace : WordTrace (prefixWord ++ tailWord_5556532) baseStart_5556532 baseEnd_5556532 := by
    simpa [prefixWord, tailWord_5556532, baseEnd_5556532] using wordTrace_append hprefix tailTrace_5556532
  have hstable : (prefixWord ++ tailWord_5556532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556532).length < 2 ^ (prefixWord ++ tailWord_5556532).sum := by decide
  have hdescent : baseEnd_5556532 < baseStart_5556532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556551 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_5556551 : Nat := 118140960795 + 5556551 * 2 ^ 59
def prefixEnd_5556551 : Nat := 4983230072969 + 3 ^ 40 * 5556551 * 2
def baseEnd_5556551 : Nat := 2853181444220994702358393

theorem tailTrace_5556551 : CollatzResearch.WordTrace tailWord_5556551 prefixEnd_5556551 2853181444220994702358393 := by
  unfold tailWord_5556551
  simp only [CollatzResearch.WordTrace]
  refine ⟨202664064492572185203485507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135109376328381456802323671 202664064492572185203485507)
  ·
    refine ⟨303996096738858277805228261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202664064492572185203485507 303996096738858277805228261)
    ·
      refine ⟨56999268138535927088480299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303996096738858277805228261 56999268138535927088480299)
      ·
        refine ⟨85498902207803890632720449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56999268138535927088480299 85498902207803890632720449)
        ·
          refine ⟨64124176655852917974540337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85498902207803890632720449 64124176655852917974540337)
          ·
            refine ⟨48093132491889688480905253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64124176655852917974540337 48093132491889688480905253)
            ·
              refine ⟨9017462342229316590169735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48093132491889688480905253 9017462342229316590169735)
              ·
                refine ⟨13526193513343974885254603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9017462342229316590169735 13526193513343974885254603)
                ·
                  refine ⟨20289290270015962327881905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13526193513343974885254603 20289290270015962327881905)
                  ·
                    refine ⟨15216967702511971745911429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20289290270015962327881905 15216967702511971745911429)
                    ·
                      refine ⟨2853181444220994702358393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15216967702511971745911429 2853181444220994702358393)
                      ·
                        rfl

theorem cell23_5556551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_5556551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556551 prefixEnd_5556551 := by exact prefixLift 5556551
  have htrace : WordTrace (prefixWord ++ tailWord_5556551) baseStart_5556551 baseEnd_5556551 := by
    simpa [prefixWord, tailWord_5556551, baseEnd_5556551] using wordTrace_append hprefix tailTrace_5556551
  have hstable : (prefixWord ++ tailWord_5556551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556551).length < 2 ^ (prefixWord ++ tailWord_5556551).sum := by decide
  have hdescent : baseEnd_5556551 < baseStart_5556551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556561 : List Nat := [1, 2, 2, 1, 4, 3, 3, 7]
def baseStart_5556561 : Nat := 118140960795 + 5556561 * 2 ^ 59
def prefixEnd_5556561 : Nat := 4983230072969 + 3 ^ 40 * 5556561 * 2
def baseEnd_5556561 : Nat := 105673577001019987527161

theorem tailTrace_5556561 : CollatzResearch.WordTrace tailWord_5556561 prefixEnd_5556561 105673577001019987527161 := by
  unfold tailWord_5556561
  simp only [CollatzResearch.WordTrace]
  refine ⟨202664429222535956911349537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135109619481690637940899691 202664429222535956911349537)
  ·
    refine ⟨151998321916901967683512153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202664429222535956911349537 151998321916901967683512153)
    ·
      refine ⟨113998741437676475762634115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151998321916901967683512153 113998741437676475762634115)
      ·
        refine ⟨170998112156514713643951173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113998741437676475762634115 170998112156514713643951173)
        ·
          refine ⟨32062146029346508808240845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170998112156514713643951173 32062146029346508808240845)
          ·
            refine ⟨12023304761004940803090317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32062146029346508808240845 12023304761004940803090317)
            ·
              refine ⟨4508739285376852801158869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12023304761004940803090317 4508739285376852801158869)
              ·
                refine ⟨105673577001019987527161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4508739285376852801158869 105673577001019987527161)
                ·
                  rfl

theorem cell23_5556561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 7].length) (baseStart_5556561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556561 prefixEnd_5556561 := by exact prefixLift 5556561
  have htrace : WordTrace (prefixWord ++ tailWord_5556561) baseStart_5556561 baseEnd_5556561 := by
    simpa [prefixWord, tailWord_5556561, baseEnd_5556561] using wordTrace_append hprefix tailTrace_5556561
  have hstable : (prefixWord ++ tailWord_5556561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556561).length < 2 ^ (prefixWord ++ tailWord_5556561).sum := by decide
  have hdescent : baseEnd_5556561 < baseStart_5556561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556604 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 1, 8]
def baseStart_5556604 : Nat := 118140960795 + 5556604 * 2 ^ 59
def prefixEnd_5556604 : Nat := 4983230072969 + 3 ^ 40 * 5556604 * 2
def baseEnd_5556604 : Nat := 951069552898560998331883

theorem tailTrace_5556604 : CollatzResearch.WordTrace tailWord_5556604 prefixEnd_5556604 951069552898560998331883 := by
  unfold tailWord_5556604
  simp only [CollatzResearch.WordTrace]
  refine ⟨101332998780690087627582433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135110665040920116836776577 101332998780690087627582433)
  ·
    refine ⟨75999749085517565720686825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101332998780690087627582433 75999749085517565720686825)
    ·
      refine ⟨56999811814138174290515119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75999749085517565720686825 56999811814138174290515119)
      ·
        refine ⟨85499717721207261435772679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56999811814138174290515119 85499717721207261435772679)
        ·
          refine ⟨128249576581810892153659019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85499717721207261435772679 128249576581810892153659019)
          ·
            refine ⟨192374364872716338230488529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128249576581810892153659019 192374364872716338230488529)
            ·
              refine ⟨144280773654537253672866397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192374364872716338230488529 144280773654537253672866397)
              ·
                refine ⟨54105290120451470127324899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144280773654537253672866397 54105290120451470127324899)
                ·
                  refine ⟨81157935180677205190987349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54105290120451470127324899 81157935180677205190987349)
                  ·
                    refine ⟨951069552898560998331883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81157935180677205190987349 951069552898560998331883)
                    ·
                      rfl

theorem cell23_5556604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_5556604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556604 prefixEnd_5556604 := by exact prefixLift 5556604
  have htrace : WordTrace (prefixWord ++ tailWord_5556604) baseStart_5556604 baseEnd_5556604 := by
    simpa [prefixWord, tailWord_5556604, baseEnd_5556604] using wordTrace_append hprefix tailTrace_5556604
  have hstable : (prefixWord ++ tailWord_5556604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556604).length < 2 ^ (prefixWord ++ tailWord_5556604).sum := by decide
  have hdescent : baseEnd_5556604 < baseStart_5556604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556615 : List Nat := [1, 1, 4, 2, 2, 1, 4, 2, 1, 3, 2]
def baseStart_5556615 : Nat := 118140960795 + 5556615 * 2 ^ 59
def prefixEnd_5556615 : Nat := 4983230072969 + 3 ^ 40 * 5556615 * 2
def baseEnd_5556615 : Nat := 2853214306982882451958099

theorem tailTrace_5556615 : CollatzResearch.WordTrace tailWord_5556615 prefixEnd_5556615 2853214306982882451958099 := by
  unfold tailWord_5556615
  simp only [CollatzResearch.WordTrace]
  refine ⟨202666398764340324133815299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135110932509560216089210199 202666398764340324133815299)
  ·
    refine ⟨303999598146510486200722949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202666398764340324133815299 303999598146510486200722949)
    ·
      refine ⟨56999924652470716162635553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 303999598146510486200722949 56999924652470716162635553)
      ·
        refine ⟨42749943489353037121976665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56999924652470716162635553 42749943489353037121976665)
        ·
          refine ⟨32062457617014777841482499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42749943489353037121976665 32062457617014777841482499)
          ·
            refine ⟨48093686425522166762223749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32062457617014777841482499 48093686425522166762223749)
            ·
              refine ⟨9017566204785406267916953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48093686425522166762223749 9017566204785406267916953)
              ·
                refine ⟨6763174653589054700937715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9017566204785406267916953 6763174653589054700937715)
                ·
                  refine ⟨10144761980383582051406573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6763174653589054700937715 10144761980383582051406573)
                  ·
                    refine ⟨3804285742643843269277465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10144761980383582051406573 3804285742643843269277465)
                    ·
                      refine ⟨2853214306982882451958099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3804285742643843269277465 2853214306982882451958099)
                      ·
                        rfl

theorem cell23_5556615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_5556615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556615 prefixEnd_5556615 := by exact prefixLift 5556615
  have htrace : WordTrace (prefixWord ++ tailWord_5556615) baseStart_5556615 baseEnd_5556615 := by
    simpa [prefixWord, tailWord_5556615, baseEnd_5556615] using wordTrace_append hprefix tailTrace_5556615
  have hstable : (prefixWord ++ tailWord_5556615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556615).length < 2 ^ (prefixWord ++ tailWord_5556615).sum := by decide
  have hdescent : baseEnd_5556615 < baseStart_5556615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556645 : List Nat := [1, 3, 1, 2, 1, 1, 4, 4, 2, 2, 2]
def baseStart_5556645 : Nat := 118140960795 + 5556645 * 2 ^ 59
def prefixEnd_5556645 : Nat := 4983230072969 + 3 ^ 40 * 5556645 * 2
def baseEnd_5556645 : Nat := 2853229711402517334582961

theorem tailTrace_5556645 : CollatzResearch.WordTrace tailWord_5556645 prefixEnd_5556645 2853229711402517334582961 := by
  unfold tailWord_5556645
  simp only [CollatzResearch.WordTrace]
  refine ⟨202667492954231639257407389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135111661969487759504938259 202667492954231639257407389)
  ·
    refine ⟨76000309857836864721527771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202667492954231639257407389 76000309857836864721527771)
    ·
      refine ⟨114000464786755297082291657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76000309857836864721527771 114000464786755297082291657)
      ·
        refine ⟨85500348590066472811718743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114000464786755297082291657 85500348590066472811718743)
        ·
          refine ⟨128250522885099709217578115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85500348590066472811718743 128250522885099709217578115)
          ·
            refine ⟨192375784327649563826367173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128250522885099709217578115 192375784327649563826367173)
            ·
              refine ⟨36070459561434293217443845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192375784327649563826367173 36070459561434293217443845)
              ·
                refine ⟨6763211167768929978270721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36070459561434293217443845 6763211167768929978270721)
                ·
                  refine ⟨5072408375826697483703041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6763211167768929978270721 5072408375826697483703041)
                  ·
                    refine ⟨3804306281870023112777281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5072408375826697483703041 3804306281870023112777281)
                    ·
                      refine ⟨2853229711402517334582961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3804306281870023112777281 2853229711402517334582961)
                      ·
                        rfl

theorem cell23_5556645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_5556645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556645 prefixEnd_5556645 := by exact prefixLift 5556645
  have htrace : WordTrace (prefixWord ++ tailWord_5556645) baseStart_5556645 baseEnd_5556645 := by
    simpa [prefixWord, tailWord_5556645, baseEnd_5556645] using wordTrace_append hprefix tailTrace_5556645
  have hstable : (prefixWord ++ tailWord_5556645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556645).length < 2 ^ (prefixWord ++ tailWord_5556645).sum := by decide
  have hdescent : baseEnd_5556645 < baseStart_5556645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556681 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 2, 5]
def baseStart_5556681 : Nat := 118140960795 + 5556681 * 2 ^ 59
def prefixEnd_5556681 : Nat := 4983230072969 + 3 ^ 40 * 5556681 * 2
def baseEnd_5556681 : Nat := 951082732235359731244265

theorem tailTrace_5556681 : CollatzResearch.WordTrace tailWord_5556681 prefixEnd_5556681 951082732235359731244265 := by
  unfold tailWord_5556681
  simp only [CollatzResearch.WordTrace]
  refine ⟨202668805982101217405717897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135112537321400811603811931 202668805982101217405717897)
  ·
    refine ⟨152001604486575913054288423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202668805982101217405717897 152001604486575913054288423)
    ·
      refine ⟨228002406729863869581432635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152001604486575913054288423 228002406729863869581432635)
      ·
        refine ⟨342003610094795804372148953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228002406729863869581432635 342003610094795804372148953)
        ·
          refine ⟨256502707571096853279111715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342003610094795804372148953 256502707571096853279111715)
          ·
            refine ⟨384754061356645279918667573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256502707571096853279111715 384754061356645279918667573)
            ·
              refine ⟨36070693252185494992375085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 384754061356645279918667573 36070693252185494992375085)
              ·
                refine ⟨13526509969569560622140657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36070693252185494992375085 13526509969569560622140657)
                ·
                  refine ⟨10144882477177170466605493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13526509969569560622140657 10144882477177170466605493)
                  ·
                    refine ⟨951082732235359731244265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10144882477177170466605493 951082732235359731244265)
                    ·
                      rfl

theorem cell23_5556681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 5].length) (baseStart_5556681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556681 prefixEnd_5556681 := by exact prefixLift 5556681
  have htrace : WordTrace (prefixWord ++ tailWord_5556681) baseStart_5556681 baseEnd_5556681 := by
    simpa [prefixWord, tailWord_5556681, baseEnd_5556681] using wordTrace_append hprefix tailTrace_5556681
  have hstable : (prefixWord ++ tailWord_5556681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556681).length < 2 ^ (prefixWord ++ tailWord_5556681).sum := by decide
  have hdescent : baseEnd_5556681 < baseStart_5556681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556728 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 3, 4]
def baseStart_5556728 : Nat := 118140960795 + 5556728 * 2 ^ 59
def prefixEnd_5556728 : Nat := 4983230072969 + 3 ^ 40 * 5556728 * 2
def baseEnd_5556728 : Nat := 951090776765613503281693

theorem tailTrace_5556728 : CollatzResearch.WordTrace tailWord_5556728 prefixEnd_5556728 951090776765613503281693 := by
  unfold tailWord_5556728
  simp only [CollatzResearch.WordTrace]
  refine ⟨101335260106465472216339419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135113680141953962955119225 101335260106465472216339419)
  ·
    refine ⟨152002890159698208324509129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101335260106465472216339419 152002890159698208324509129)
    ·
      refine ⟨114002167619773656243381847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152002890159698208324509129 114002167619773656243381847)
      ·
        refine ⟨171003251429660484365072771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114002167619773656243381847 171003251429660484365072771)
        ·
          refine ⟨256504877144490726547609157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171003251429660484365072771 256504877144490726547609157)
          ·
            refine ⟨48094664464592011227676717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256504877144490726547609157 48094664464592011227676717)
            ·
              refine ⟨18035499174222004210378769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48094664464592011227676717 18035499174222004210378769)
              ·
                refine ⟨13526624380666503157784077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18035499174222004210378769 13526624380666503157784077)
                ·
                  refine ⟨5072484142749938684169029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13526624380666503157784077 5072484142749938684169029)
                  ·
                    refine ⟨951090776765613503281693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5072484142749938684169029 951090776765613503281693)
                    ·
                      rfl

theorem cell23_5556728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_5556728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556728 prefixEnd_5556728 := by exact prefixLift 5556728
  have htrace : WordTrace (prefixWord ++ tailWord_5556728) baseStart_5556728 baseEnd_5556728 := by
    simpa [prefixWord, tailWord_5556728, baseEnd_5556728] using wordTrace_append hprefix tailTrace_5556728
  have hstable : (prefixWord ++ tailWord_5556728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556728).length < 2 ^ (prefixWord ++ tailWord_5556728).sum := by decide
  have hdescent : baseEnd_5556728 < baseStart_5556728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556785 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 3, 1, 3]
def baseStart_5556785 : Nat := 118140960795 + 5556785 * 2 ^ 59
def prefixEnd_5556785 : Nat := 4983230072969 + 3 ^ 40 * 5556785 * 2
def baseEnd_5556785 : Nat := 2853301598694146786832317

theorem tailTrace_5556785 : CollatzResearch.WordTrace tailWord_5556785 prefixEnd_5556785 2853301598694146786832317 := by
  unfold tailWord_5556785
  simp only [CollatzResearch.WordTrace]
  refine ⟨202672599173724443167503809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135115066115816295445002539 202672599173724443167503809)
  ·
    refine ⟨152004449380293332375627857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202672599173724443167503809 152004449380293332375627857)
    ·
      refine ⟨114003337035219999281720893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152004449380293332375627857 114003337035219999281720893)
      ·
        refine ⟨42751251388207499730645335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114003337035219999281720893 42751251388207499730645335)
        ·
          refine ⟨64126877082311249595968003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42751251388207499730645335 64126877082311249595968003)
          ·
            refine ⟨96190315623466874393952005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64126877082311249595968003 96190315623466874393952005)
            ·
              refine ⟨18035684179400038948866001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96190315623466874393952005 18035684179400038948866001)
              ·
                refine ⟨13526763134550029211649501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18035684179400038948866001 13526763134550029211649501)
                ·
                  refine ⟨5072536175456260954368563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13526763134550029211649501 5072536175456260954368563)
                  ·
                    refine ⟨7608804263184391431552845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5072536175456260954368563 7608804263184391431552845)
                    ·
                      refine ⟨2853301598694146786832317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7608804263184391431552845 2853301598694146786832317)
                      ·
                        rfl

theorem cell23_5556785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_5556785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556785 prefixEnd_5556785 := by exact prefixLift 5556785
  have htrace : WordTrace (prefixWord ++ tailWord_5556785) baseStart_5556785 baseEnd_5556785 := by
    simpa [prefixWord, tailWord_5556785, baseEnd_5556785] using wordTrace_append hprefix tailTrace_5556785
  have hstable : (prefixWord ++ tailWord_5556785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556785).length < 2 ^ (prefixWord ++ tailWord_5556785).sum := by decide
  have hdescent : baseEnd_5556785 < baseStart_5556785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556835 : List Nat := [1, 1, 1, 5, 1, 2, 3, 3, 2, 4]
def baseStart_5556835 : Nat := 118140960795 + 5556835 * 2 ^ 59
def prefixEnd_5556835 : Nat := 4983230072969 + 3 ^ 40 * 5556835 * 2
def baseEnd_5556835 : Nat := 951109090908957197069029

theorem tailTrace_5556835 : CollatzResearch.WordTrace tailWord_5556835 prefixEnd_5556835 951109090908957197069029 := by
  unfold tailWord_5556835
  simp only [CollatzResearch.WordTrace]
  refine ⟨202674422823543301706823959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135116281882362201137882639 202674422823543301706823959)
  ·
    refine ⟨304011634235314952560235939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202674422823543301706823959 304011634235314952560235939)
    ·
      refine ⟨456017451352972428840353909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304011634235314952560235939 456017451352972428840353909)
      ·
        refine ⟨42751636064341165203783179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 456017451352972428840353909 42751636064341165203783179)
        ·
          refine ⟨64127454096511747805674769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42751636064341165203783179 64127454096511747805674769)
          ·
            refine ⟨48095590572383810854256077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64127454096511747805674769 48095590572383810854256077)
            ·
              refine ⟨18035846464643929070346029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48095590572383810854256077 18035846464643929070346029)
              ·
                refine ⟨6763442424241473401379761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18035846464643929070346029 6763442424241473401379761)
                ·
                  refine ⟨5072581818181105051034821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6763442424241473401379761 5072581818181105051034821)
                  ·
                    refine ⟨951109090908957197069029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5072581818181105051034821 951109090908957197069029)
                    ·
                      rfl

theorem cell23_5556835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 4].length) (baseStart_5556835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556835 prefixEnd_5556835 := by exact prefixLift 5556835
  have htrace : WordTrace (prefixWord ++ tailWord_5556835) baseStart_5556835 baseEnd_5556835 := by
    simpa [prefixWord, tailWord_5556835, baseEnd_5556835] using wordTrace_append hprefix tailTrace_5556835
  have hstable : (prefixWord ++ tailWord_5556835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556835).length < 2 ^ (prefixWord ++ tailWord_5556835).sum := by decide
  have hdescent : baseEnd_5556835 < baseStart_5556835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556842 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_5556842 : Nat := 118140960795 + 5556842 * 2 ^ 59
def prefixEnd_5556842 : Nat := 4983230072969 + 3 ^ 40 * 5556842 * 2
def baseEnd_5556842 : Nat := 2853330867091453063819555

theorem tailTrace_5556842 : CollatzResearch.WordTrace tailWord_5556842 prefixEnd_5556842 2853330867091453063819555 := by
  unfold tailWord_5556842
  simp only [CollatzResearch.WordTrace]
  refine ⟨50668669533629485475582195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135116452089678627934885853 50668669533629485475582195)
  ·
    refine ⟨76003004300444228213373293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50668669533629485475582195 76003004300444228213373293)
    ·
      refine ⟨28501126612666585580014985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76003004300444228213373293 28501126612666585580014985)
      ·
        refine ⟨21375844959499939185011239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28501126612666585580014985 21375844959499939185011239)
        ·
          refine ⟨32063767439249908777516859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21375844959499939185011239 32063767439249908777516859)
          ·
            refine ⟨48095651158874863166275289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32063767439249908777516859 48095651158874863166275289)
            ·
              refine ⟨36071738369156147374706467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48095651158874863166275289 36071738369156147374706467)
              ·
                refine ⟨54107607553734221062059701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36071738369156147374706467 54107607553734221062059701)
                ·
                  refine ⟨5072588208162583224568097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54107607553734221062059701 5072588208162583224568097)
                  ·
                    refine ⟨3804441156121937418426073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5072588208162583224568097 3804441156121937418426073)
                    ·
                      refine ⟨2853330867091453063819555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3804441156121937418426073 2853330867091453063819555)
                      ·
                        rfl

theorem cell23_5556842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_5556842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556842 prefixEnd_5556842 := by exact prefixLift 5556842
  have htrace : WordTrace (prefixWord ++ tailWord_5556842) baseStart_5556842 baseEnd_5556842 := by
    simpa [prefixWord, tailWord_5556842, baseEnd_5556842] using wordTrace_append hprefix tailTrace_5556842
  have hstable : (prefixWord ++ tailWord_5556842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556842).length < 2 ^ (prefixWord ++ tailWord_5556842).sum := by decide
  have hdescent : baseEnd_5556842 < baseStart_5556842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556878 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_5556878 : Nat := 118140960795 + 5556878 * 2 ^ 59
def prefixEnd_5556878 : Nat := 4983230072969 + 3 ^ 40 * 5556878 * 2
def baseEnd_5556878 : Nat := 951116450798338307656463

theorem tailTrace_5556878 : CollatzResearch.WordTrace tailWord_5556878 prefixEnd_5556878 951116450798338307656463 := by
  unfold tailWord_5556878
  simp only [CollatzResearch.WordTrace]
  refine ⟨25334498895298440006329911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135117327441591680033759525 25334498895298440006329911)
  ·
    refine ⟨38001748342947660009494867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25334498895298440006329911 38001748342947660009494867)
    ·
      refine ⟨57002622514421490014242301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38001748342947660009494867 57002622514421490014242301)
      ·
        refine ⟨21375983442908058755340863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57002622514421490014242301 21375983442908058755340863)
        ·
          refine ⟨32063975164362088133011295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21375983442908058755340863 32063975164362088133011295)
          ·
            refine ⟨48095962746543132199516943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32063975164362088133011295 48095962746543132199516943)
            ·
              refine ⟨72143944119814698299275415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48095962746543132199516943 72143944119814698299275415)
              ·
                refine ⟨108215916179722047448913123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72143944119814698299275415 108215916179722047448913123)
                ·
                  refine ⟨162323874269583071173369685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108215916179722047448913123 162323874269583071173369685)
                  ·
                    refine ⟨951116450798338307656463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 162323874269583071173369685 951116450798338307656463)
                    ·
                      rfl

theorem cell23_5556878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_5556878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556878 prefixEnd_5556878 := by exact prefixLift 5556878
  have htrace : WordTrace (prefixWord ++ tailWord_5556878) baseStart_5556878 baseEnd_5556878 := by
    simpa [prefixWord, tailWord_5556878, baseEnd_5556878] using wordTrace_append hprefix tailTrace_5556878
  have hstable : (prefixWord ++ tailWord_5556878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556878).length < 2 ^ (prefixWord ++ tailWord_5556878).sum := by decide
  have hdescent : baseEnd_5556878 < baseStart_5556878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556892 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_5556892 : Nat := 118140960795 + 5556892 * 2 ^ 59
def prefixEnd_5556892 : Nat := 4983230072969 + 3 ^ 40 * 5556892 * 2
def baseEnd_5556892 : Nat := 2853356541124177868194325

theorem tailTrace_5556892 : CollatzResearch.WordTrace tailWord_5556892 prefixEnd_5556892 2853356541124177868194325 := by
  unfold tailWord_5556892
  simp only [CollatzResearch.WordTrace]
  refine ⟨101338250892168400220824465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135117667856224533627765953 101338250892168400220824465)
  ·
    refine ⟨76003688169126300165618349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101338250892168400220824465 76003688169126300165618349)
    ·
      refine ⟨28501383063422362562106881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76003688169126300165618349 28501383063422362562106881)
      ·
        refine ⟨21376037297566771921580161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28501383063422362562106881 21376037297566771921580161)
        ·
          refine ⟨16032027973175078941185121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21376037297566771921580161 16032027973175078941185121)
          ·
            refine ⟨12024020979881309205888841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16032027973175078941185121 12024020979881309205888841)
            ·
              refine ⟨9018015734910981904416631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12024020979881309205888841 9018015734910981904416631)
              ·
                refine ⟨13527023602366472856624947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9018015734910981904416631 13527023602366472856624947)
                ·
                  refine ⟨20290535403549709284937421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13527023602366472856624947 20290535403549709284937421)
                  ·
                    refine ⟨7608950776331140981851533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20290535403549709284937421 7608950776331140981851533)
                    ·
                      refine ⟨2853356541124177868194325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7608950776331140981851533 2853356541124177868194325)
                      ·
                        rfl

theorem cell23_5556892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_5556892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556892 prefixEnd_5556892 := by exact prefixLift 5556892
  have htrace : WordTrace (prefixWord ++ tailWord_5556892) baseStart_5556892 baseEnd_5556892 := by
    simpa [prefixWord, tailWord_5556892, baseEnd_5556892] using wordTrace_append hprefix tailTrace_5556892
  have hstable : (prefixWord ++ tailWord_5556892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556892).length < 2 ^ (prefixWord ++ tailWord_5556892).sum := by decide
  have hdescent : baseEnd_5556892 < baseStart_5556892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556913 : List Nat := [1, 2, 2, 6, 2, 1, 2, 1, 1, 2, 3]
def baseStart_5556913 : Nat := 118140960795 + 5556913 * 2 ^ 59
def prefixEnd_5556913 : Nat := 4983230072969 + 3 ^ 40 * 5556913 * 2
def baseEnd_5556913 : Nat := 2853367324217922286031729

theorem tailTrace_5556913 : CollatzResearch.WordTrace tailWord_5556913 prefixEnd_5556913 2853367324217922286031729 := by
  unfold tailWord_5556913
  simp only [CollatzResearch.WordTrace]
  refine ⟨202677267717260721028163393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135118178478173814018775595 202677267717260721028163393)
  ·
    refine ⟨152007950787945540771122545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202677267717260721028163393 152007950787945540771122545)
    ·
      refine ⟨114005963090959155578341909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152007950787945540771122545 114005963090959155578341909)
      ·
        refine ⟨5344029519888710417734777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 114005963090959155578341909 5344029519888710417734777)
        ·
          refine ⟨4008022139916532813301083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5344029519888710417734777 4008022139916532813301083)
          ·
            refine ⟨6012033209874799219951625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4008022139916532813301083 6012033209874799219951625)
            ·
              refine ⟨4509024907406099414963719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6012033209874799219951625 4509024907406099414963719)
              ·
                refine ⟨6763537361109149122445579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4509024907406099414963719 6763537361109149122445579)
                ·
                  refine ⟨10145306041663723683668369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6763537361109149122445579 10145306041663723683668369)
                  ·
                    refine ⟨7608979531247792762751277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10145306041663723683668369 7608979531247792762751277)
                    ·
                      refine ⟨2853367324217922286031729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7608979531247792762751277 2853367324217922286031729)
                      ·
                        rfl

theorem cell23_5556913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_5556913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556913 prefixEnd_5556913 := by exact prefixLift 5556913
  have htrace : WordTrace (prefixWord ++ tailWord_5556913) baseStart_5556913 baseEnd_5556913 := by
    simpa [prefixWord, tailWord_5556913, baseEnd_5556913] using wordTrace_append hprefix tailTrace_5556913
  have hstable : (prefixWord ++ tailWord_5556913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556913).length < 2 ^ (prefixWord ++ tailWord_5556913).sum := by decide
  have hdescent : baseEnd_5556913 < baseStart_5556913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5556919 : List Nat := [1, 1, 3, 1, 6, 1, 1, 3, 1, 3, 2]
def baseStart_5556919 : Nat := 118140960795 + 5556919 * 2 ^ 59
def prefixEnd_5556919 : Nat := 4983230072969 + 3 ^ 40 * 5556919 * 2
def baseEnd_5556919 : Nat := 2853370405101849262556701

theorem tailTrace_5556919 : CollatzResearch.WordTrace tailWord_5556919 prefixEnd_5556919 2853370405101849262556701 := by
  unfold tailWord_5556919
  simp only [CollatzResearch.WordTrace]
  refine ⟨202677486555238984052881811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135118324370159322701921207 202677486555238984052881811)
  ·
    refine ⟨304016229832858476079322717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202677486555238984052881811 304016229832858476079322717)
    ·
      refine ⟨114006086187321928529746019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304016229832858476079322717 114006086187321928529746019)
      ·
        refine ⟨171009129280982892794619029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114006086187321928529746019 171009129280982892794619029)
        ·
          refine ⟨8016052935046073099747767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 171009129280982892794619029 8016052935046073099747767)
          ·
            refine ⟨12024079402569109649621651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8016052935046073099747767 12024079402569109649621651)
            ·
              refine ⟨18036119103853664474432477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12024079402569109649621651 18036119103853664474432477)
              ·
                refine ⟨6763544663945124177912179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18036119103853664474432477 6763544663945124177912179)
                ·
                  refine ⟨10145316995917686266868269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6763544663945124177912179 10145316995917686266868269)
                  ·
                    refine ⟨3804493873469132350075601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10145316995917686266868269 3804493873469132350075601)
                    ·
                      refine ⟨2853370405101849262556701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3804493873469132350075601 2853370405101849262556701)
                      ·
                        rfl

theorem cell23_5556919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 3, 2].length) (baseStart_5556919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5556919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5556919 prefixEnd_5556919 := by exact prefixLift 5556919
  have htrace : WordTrace (prefixWord ++ tailWord_5556919) baseStart_5556919 baseEnd_5556919 := by
    simpa [prefixWord, tailWord_5556919, baseEnd_5556919] using wordTrace_append hprefix tailTrace_5556919
  have hstable : (prefixWord ++ tailWord_5556919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5556919).length < 2 ^ (prefixWord ++ tailWord_5556919).sum := by decide
  have hdescent : baseEnd_5556919 < baseStart_5556919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5556919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557042 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_5557042 : Nat := 118140960795 + 5557042 * 2 ^ 59
def prefixEnd_5557042 : Nat := 4983230072969 + 3 ^ 40 * 5557042 * 2
def baseEnd_5557042 : Nat := 2853433563222352281318635

theorem tailTrace_5557042 : CollatzResearch.WordTrace tailWord_5557042 prefixEnd_5557042 2853433563222352281318635 := by
  unfold tailWord_5557042
  simp only [CollatzResearch.WordTrace]
  refine ⟨50670493183448344014902345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135121315155862250706406253 50670493183448344014902345)
  ·
    refine ⟨38002869887586258011176759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50670493183448344014902345 38002869887586258011176759)
    ·
      refine ⟨57004304831379387016765139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38002869887586258011176759 57004304831379387016765139)
      ·
        refine ⟨85506457247069080525147709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57004304831379387016765139 85506457247069080525147709)
        ·
          refine ⟨32064921467650905196930391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85506457247069080525147709 32064921467650905196930391)
          ·
            refine ⟨48097382201476357795395587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32064921467650905196930391 48097382201476357795395587)
            ·
              refine ⟨72146073302214536693093381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48097382201476357795395587 72146073302214536693093381)
              ·
                refine ⟨13527388744165225629955009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72146073302214536693093381 13527388744165225629955009)
                ·
                  refine ⟨10145541558123919222466257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13527388744165225629955009 10145541558123919222466257)
                  ·
                    refine ⟨7609156168592939416849693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10145541558123919222466257 7609156168592939416849693)
                    ·
                      refine ⟨2853433563222352281318635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7609156168592939416849693 2853433563222352281318635)
                      ·
                        rfl

theorem cell23_5557042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_5557042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557042 prefixEnd_5557042 := by exact prefixLift 5557042
  have htrace : WordTrace (prefixWord ++ tailWord_5557042) baseStart_5557042 baseEnd_5557042 := by
    simpa [prefixWord, tailWord_5557042, baseEnd_5557042] using wordTrace_append hprefix tailTrace_5557042
  have hstable : (prefixWord ++ tailWord_5557042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557042).length < 2 ^ (prefixWord ++ tailWord_5557042).sum := by decide
  have hdescent : baseEnd_5557042 < baseStart_5557042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557072 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 5, 1, 3]
def baseStart_5557072 : Nat := 118140960795 + 5557072 * 2 ^ 59
def prefixEnd_5557072 : Nat := 4983230072969 + 3 ^ 40 * 5557072 * 2
def baseEnd_5557072 : Nat := 2853448967641987163943497

theorem tailTrace_5557072 : CollatzResearch.WordTrace tailWord_5557072 prefixEnd_5557072 2853448967641987163943497 := by
  unfold tailWord_5557072
  simp only [CollatzResearch.WordTrace]
  refine ⟨101341533461842345591600735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135122044615789794122134313 101341533461842345591600735)
  ·
    refine ⟨152012300192763518387401103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101341533461842345591600735 152012300192763518387401103)
    ·
      refine ⟨228018450289145277581101655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152012300192763518387401103 228018450289145277581101655)
      ·
        refine ⟨342027675433717916371652483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228018450289145277581101655 342027675433717916371652483)
        ·
          refine ⟨513041513150576874557478725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342027675433717916371652483 513041513150576874557478725)
          ·
            refine ⟨96195283715733163979527261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 513041513150576874557478725 96195283715733163979527261)
            ·
              refine ⟨36073231393399936492322723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96195283715733163979527261 36073231393399936492322723)
              ·
                refine ⟨54109847090099904738484085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36073231393399936492322723 54109847090099904738484085)
                ·
                  refine ⟨5072798164696866069232883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54109847090099904738484085 5072798164696866069232883)
                  ·
                    refine ⟨7609197247045299103849325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5072798164696866069232883 7609197247045299103849325)
                    ·
                      refine ⟨2853448967641987163943497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7609197247045299103849325 2853448967641987163943497)
                      ·
                        rfl

theorem cell23_5557072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 5, 1, 3].length) (baseStart_5557072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557072 prefixEnd_5557072 := by exact prefixLift 5557072
  have htrace : WordTrace (prefixWord ++ tailWord_5557072) baseStart_5557072 baseEnd_5557072 := by
    simpa [prefixWord, tailWord_5557072, baseEnd_5557072] using wordTrace_append hprefix tailTrace_5557072
  have hstable : (prefixWord ++ tailWord_5557072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557072).length < 2 ^ (prefixWord ++ tailWord_5557072).sum := by decide
  have hdescent : baseEnd_5557072 < baseStart_5557072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557076 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_5557076 : Nat := 118140960795 + 5557076 * 2 ^ 59
def prefixEnd_5557076 : Nat := 4983230072969 + 3 ^ 40 * 5557076 * 2
def baseEnd_5557076 : Nat := 2853451021564605148293479

theorem tailTrace_5557076 : CollatzResearch.WordTrace tailWord_5557076 prefixEnd_5557076 2853451021564605148293479 := by
  unfold tailWord_5557076
  simp only [CollatzResearch.WordTrace]
  refine ⟨101341606407835099933173541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135122141877113466577564721 101341606407835099933173541)
  ·
    refine ⟨19001551201469081237470039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101341606407835099933173541 19001551201469081237470039)
    ·
      refine ⟨28502326802203621856205059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19001551201469081237470039 28502326802203621856205059)
      ·
        refine ⟨42753490203305432784307589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28502326802203621856205059 42753490203305432784307589)
        ·
          refine ⟨8016279413119768647057673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42753490203305432784307589 8016279413119768647057673)
          ·
            refine ⟨6012209559839826485293255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8016279413119768647057673 6012209559839826485293255)
            ·
              refine ⟨9018314339759739727939883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6012209559839826485293255 9018314339759739727939883)
              ·
                refine ⟨13527471509639609591909825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9018314339759739727939883 13527471509639609591909825)
                ·
                  refine ⟨10145603632229707193932369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13527471509639609591909825 10145603632229707193932369)
                  ·
                    refine ⟨7609202724172280395449277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10145603632229707193932369 7609202724172280395449277)
                    ·
                      refine ⟨2853451021564605148293479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7609202724172280395449277 2853451021564605148293479)
                      ·
                        rfl

theorem cell23_5557076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_5557076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557076 prefixEnd_5557076 := by exact prefixLift 5557076
  have htrace : WordTrace (prefixWord ++ tailWord_5557076) baseStart_5557076 baseEnd_5557076 := by
    simpa [prefixWord, tailWord_5557076, baseEnd_5557076] using wordTrace_append hprefix tailTrace_5557076
  have hstable : (prefixWord ++ tailWord_5557076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557076).length < 2 ^ (prefixWord ++ tailWord_5557076).sum := by decide
  have hdescent : baseEnd_5557076 < baseStart_5557076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557106 : List Nat := [3, 2, 1, 2, 1, 1, 4, 4, 1, 1, 3]
def baseStart_5557106 : Nat := 118140960795 + 5557106 * 2 ^ 59
def prefixEnd_5557106 : Nat := 4983230072969 + 3 ^ 40 * 5557106 * 2
def baseEnd_5557106 : Nat := 2853466425984240030918341

theorem tailTrace_5557106 : CollatzResearch.WordTrace tailWord_5557106 prefixEnd_5557106 2853466425984240030918341 := by
  unfold tailWord_5557106
  simp only [CollatzResearch.WordTrace]
  refine ⟨50671076751390378747484793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135122871337041009993292781 50671076751390378747484793)
  ·
    refine ⟨38003307563542784060613595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50671076751390378747484793 38003307563542784060613595)
    ·
      refine ⟨57004961345314176090920393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38003307563542784060613595 57004961345314176090920393)
      ·
        refine ⟨42753721008985632068190295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57004961345314176090920393 42753721008985632068190295)
        ·
          refine ⟨64130581513478448102285443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42753721008985632068190295 64130581513478448102285443)
          ·
            refine ⟨96195872270217672153428165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64130581513478448102285443 96195872270217672153428165)
            ·
              refine ⟨18036726050665813528767781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96195872270217672153428165 18036726050665813528767781)
              ·
                refine ⟨3381886134499840036643959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18036726050665813528767781 3381886134499840036643959)
                ·
                  refine ⟨5072829201749760054965939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3381886134499840036643959 5072829201749760054965939)
                  ·
                    refine ⟨7609243802624640082448909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5072829201749760054965939 7609243802624640082448909)
                    ·
                      refine ⟨2853466425984240030918341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7609243802624640082448909 2853466425984240030918341)
                      ·
                        rfl

theorem cell23_5557106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_5557106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557106 prefixEnd_5557106 := by exact prefixLift 5557106
  have htrace : WordTrace (prefixWord ++ tailWord_5557106) baseStart_5557106 baseEnd_5557106 := by
    simpa [prefixWord, tailWord_5557106, baseEnd_5557106] using wordTrace_append hprefix tailTrace_5557106
  have hstable : (prefixWord ++ tailWord_5557106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557106).length < 2 ^ (prefixWord ++ tailWord_5557106).sum := by decide
  have hdescent : baseEnd_5557106 < baseStart_5557106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557115 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 5]
def baseStart_5557115 : Nat := 118140960795 + 5557115 * 2 ^ 59
def prefixEnd_5557115 : Nat := 4983230072969 + 3 ^ 40 * 5557115 * 2
def baseEnd_5557115 : Nat := 2853471047310130495705799

theorem tailTrace_5557115 : CollatzResearch.WordTrace tailWord_5557115 prefixEnd_5557115 2853471047310130495705799 := by
  unfold tailWord_5557115
  simp only [CollatzResearch.WordTrace]
  refine ⟨202684635262528909527016799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135123090175019273018011199 202684635262528909527016799)
  ·
    refine ⟨304026952893793364290525199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202684635262528909527016799 304026952893793364290525199)
    ·
      refine ⟨456040429340690046435787799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304026952893793364290525199 456040429340690046435787799)
      ·
        refine ⟨684060644011035069653681699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456040429340690046435787799 684060644011035069653681699)
        ·
          refine ⟨1026090966016552604480522549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684060644011035069653681699 1026090966016552604480522549)
          ·
            refine ⟨96196028064051806670048989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1026090966016552604480522549 96196028064051806670048989)
            ·
              refine ⟨36073510524019427501268371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96196028064051806670048989 36073510524019427501268371)
              ·
                refine ⟨54110265786029141251902557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36073510524019427501268371 54110265786029141251902557)
                ·
                  refine ⟨20291349669760927969463459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54110265786029141251902557 20291349669760927969463459)
                  ·
                    refine ⟨30437024504641391954195189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20291349669760927969463459 30437024504641391954195189)
                    ·
                      refine ⟨2853471047310130495705799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30437024504641391954195189 2853471047310130495705799)
                      ·
                        rfl

theorem cell23_5557115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 5].length) (baseStart_5557115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557115 prefixEnd_5557115 := by exact prefixLift 5557115
  have htrace : WordTrace (prefixWord ++ tailWord_5557115) baseStart_5557115 baseEnd_5557115 := by
    simpa [prefixWord, tailWord_5557115, baseEnd_5557115] using wordTrace_append hprefix tailTrace_5557115
  have hstable : (prefixWord ++ tailWord_5557115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557115).length < 2 ^ (prefixWord ++ tailWord_5557115).sum := by decide
  have hdescent : baseEnd_5557115 < baseStart_5557115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557129 : List Nat := [1, 2, 1, 1, 5, 3, 2, 2, 1, 1, 4]
def baseStart_5557129 : Nat := 118140960795 + 5557129 * 2 ^ 59
def prefixEnd_5557129 : Nat := 4983230072969 + 3 ^ 40 * 5557129 * 2
def baseEnd_5557129 : Nat := 2853478236039293440930735

theorem tailTrace_5557129 : CollatzResearch.WordTrace tailWord_5557129 prefixEnd_5557129 2853478236039293440930735 := by
  unfold tailWord_5557129
  simp only [CollatzResearch.WordTrace]
  refine ⟨202685145884478189918026441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135123430589652126612017627 202685145884478189918026441)
  ·
    refine ⟨152013859413358642438519831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202685145884478189918026441 152013859413358642438519831)
    ·
      refine ⟨228020789120037963657779747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152013859413358642438519831 228020789120037963657779747)
      ·
        refine ⟨342031183680056945486669621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228020789120037963657779747 342031183680056945486669621)
        ·
          refine ⟨32065423470005338639375277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 342031183680056945486669621 32065423470005338639375277)
          ·
            refine ⟨12024533801252001989765729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32065423470005338639375277 12024533801252001989765729)
            ·
              refine ⟨9018400350939001492324297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12024533801252001989765729 9018400350939001492324297)
              ·
                refine ⟨6763800263204251119243223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9018400350939001492324297 6763800263204251119243223)
                ·
                  refine ⟨10145700394806376678864835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6763800263204251119243223 10145700394806376678864835)
                  ·
                    refine ⟨15218550592209565018297253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10145700394806376678864835 15218550592209565018297253)
                    ·
                      refine ⟨2853478236039293440930735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15218550592209565018297253 2853478236039293440930735)
                      ·
                        rfl

theorem cell23_5557129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 1, 4].length) (baseStart_5557129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557129 prefixEnd_5557129 := by exact prefixLift 5557129
  have htrace : WordTrace (prefixWord ++ tailWord_5557129) baseStart_5557129 baseEnd_5557129 := by
    simpa [prefixWord, tailWord_5557129, baseEnd_5557129] using wordTrace_append hprefix tailTrace_5557129
  have hstable : (prefixWord ++ tailWord_5557129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557129).length < 2 ^ (prefixWord ++ tailWord_5557129).sum := by decide
  have hdescent : baseEnd_5557129 < baseStart_5557129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557132 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 3, 2, 3]
def baseStart_5557132 : Nat := 118140960795 + 5557132 * 2 ^ 59
def prefixEnd_5557132 : Nat := 4983230072969 + 3 ^ 40 * 5557132 * 2
def baseEnd_5557132 : Nat := 2853479776481256929193221

theorem tailTrace_5557132 : CollatzResearch.WordTrace tailWord_5557132 prefixEnd_5557132 2853479776481256929193221 := by
  unfold tailWord_5557132
  simp only [CollatzResearch.WordTrace]
  refine ⟨101342627651733660715192825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135123503535644880953590433 101342627651733660715192825)
  ·
    refine ⟨76006970738800245536394619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101342627651733660715192825 76006970738800245536394619)
    ·
      refine ⟨114010456108200368304591929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76006970738800245536394619 114010456108200368304591929)
      ·
        refine ⟨85507842081150276228443947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114010456108200368304591929 85507842081150276228443947)
        ·
          refine ⟨128261763121725414342665921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85507842081150276228443947 128261763121725414342665921)
          ·
            refine ⟨96196322341294060756999441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128261763121725414342665921 96196322341294060756999441)
            ·
              refine ⟨72147241755970545567749581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96196322341294060756999441 72147241755970545567749581)
              ·
                refine ⟨27055215658488954587906093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72147241755970545567749581 27055215658488954587906093)
                ·
                  refine ⟨10145705871933357970464785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27055215658488954587906093 10145705871933357970464785)
                  ·
                    refine ⟨7609279403950018477848589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10145705871933357970464785 7609279403950018477848589)
                    ·
                      refine ⟨2853479776481256929193221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7609279403950018477848589 2853479776481256929193221)
                      ·
                        rfl

theorem cell23_5557132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_5557132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557132 prefixEnd_5557132 := by exact prefixLift 5557132
  have htrace : WordTrace (prefixWord ++ tailWord_5557132) baseStart_5557132 baseEnd_5557132 := by
    simpa [prefixWord, tailWord_5557132, baseEnd_5557132] using wordTrace_append hprefix tailTrace_5557132
  have hstable : (prefixWord ++ tailWord_5557132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557132).length < 2 ^ (prefixWord ++ tailWord_5557132).sum := by decide
  have hdescent : baseEnd_5557132 < baseStart_5557132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557149 : List Nat := [1, 4, 2, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_5557149 : Nat := 118140960795 + 5557149 * 2 ^ 59
def prefixEnd_5557149 : Nat := 4983230072969 + 3 ^ 40 * 5557149 * 2
def baseEnd_5557149 : Nat := 2853488505652383362680643

theorem tailTrace_5557149 : CollatzResearch.WordTrace tailWord_5557149 prefixEnd_5557149 2853488505652383362680643 := by
  unfold tailWord_5557149
  simp only [CollatzResearch.WordTrace]
  refine ⟨202685875344405733333754501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135123916896270488889169667 202685875344405733333754501)
  ·
    refine ⟨38003601627076075000078969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202685875344405733333754501 38003601627076075000078969)
    ·
      refine ⟨28502701220307056250059227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38003601627076075000078969 28502701220307056250059227)
      ·
        refine ⟨42754051830460584375088841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28502701220307056250059227 42754051830460584375088841)
        ·
          refine ⟨32065538872845438281316631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42754051830460584375088841 32065538872845438281316631)
          ·
            refine ⟨48098308309268157421974947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32065538872845438281316631 48098308309268157421974947)
            ·
              refine ⟨72147462463902236132962421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48098308309268157421974947 72147462463902236132962421)
              ·
                refine ⟨6763824605990834637465227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72147462463902236132962421 6763824605990834637465227)
                ·
                  refine ⟨10145736908986251956197841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6763824605990834637465227 10145736908986251956197841)
                  ·
                    refine ⟨7609302681739688967148381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10145736908986251956197841 7609302681739688967148381)
                    ·
                      refine ⟨2853488505652383362680643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7609302681739688967148381 2853488505652383362680643)
                      ·
                        rfl

theorem cell23_5557149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_5557149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557149 prefixEnd_5557149 := by exact prefixLift 5557149
  have htrace : WordTrace (prefixWord ++ tailWord_5557149) baseStart_5557149 baseEnd_5557149 := by
    simpa [prefixWord, tailWord_5557149, baseEnd_5557149] using wordTrace_append hprefix tailTrace_5557149
  have hstable : (prefixWord ++ tailWord_5557149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557149).length < 2 ^ (prefixWord ++ tailWord_5557149).sum := by decide
  have hdescent : baseEnd_5557149 < baseStart_5557149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557190 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_5557190 : Nat := 118140960795 + 5557190 * 2 ^ 59
def prefixEnd_5557190 : Nat := 4983230072969 + 3 ^ 40 * 5557190 * 2
def baseEnd_5557190 : Nat := 951169852786405900755985

theorem tailTrace_5557190 : CollatzResearch.WordTrace tailWord_5557190 prefixEnd_5557190 951169852786405900755985 := by
  unfold tailWord_5557190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6333980335539287416749907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135124913824838131557331349 6333980335539287416749907)
  ·
    refine ⟨9500970503308931125124861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6333980335539287416749907 9500970503308931125124861)
    ·
      refine ⟨3562863938740849171921823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9500970503308931125124861 3562863938740849171921823)
      ·
        refine ⟨5344295908111273757882735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3562863938740849171921823 5344295908111273757882735)
        ·
          refine ⟨8016443862166910636824103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5344295908111273757882735 8016443862166910636824103)
          ·
            refine ⟨12024665793250365955236155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8016443862166910636824103 12024665793250365955236155)
            ·
              refine ⟨18036998689875548932854233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12024665793250365955236155 18036998689875548932854233)
              ·
                refine ⟨13527749017406661699640675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18036998689875548932854233 13527749017406661699640675)
                ·
                  refine ⟨20291623526109992549461013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13527749017406661699640675 20291623526109992549461013)
                  ·
                    refine ⟨951169852786405900755985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20291623526109992549461013 951169852786405900755985)
                    ·
                      rfl

theorem cell23_5557190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_5557190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557190 prefixEnd_5557190 := by exact prefixLift 5557190
  have htrace : WordTrace (prefixWord ++ tailWord_5557190) baseStart_5557190 baseEnd_5557190 := by
    simpa [prefixWord, tailWord_5557190, baseEnd_5557190] using wordTrace_append hprefix tailTrace_5557190
  have hstable : (prefixWord ++ tailWord_5557190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557190).length < 2 ^ (prefixWord ++ tailWord_5557190).sum := by decide
  have hdescent : baseEnd_5557190 < baseStart_5557190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557197 : List Nat := [1, 6, 3, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_5557197 : Nat := 118140960795 + 5557197 * 2 ^ 59
def prefixEnd_5557197 : Nat := 4983230072969 + 3 ^ 40 * 5557197 * 2
def baseEnd_5557197 : Nat := 2853513152723799174880423

theorem tailTrace_5557197 : CollatzResearch.WordTrace tailWord_5557197 prefixEnd_5557197 2853513152723799174880423 := by
  unfold tailWord_5557197
  simp only [CollatzResearch.WordTrace]
  refine ⟨202687626048231837531501845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135125084032154558354334563 202687626048231837531501845)
  ·
    refine ⟨9500982471010867384289149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 202687626048231837531501845 9500982471010867384289149)
    ·
      refine ⟨3562868426629075269108431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9500982471010867384289149 3562868426629075269108431)
      ·
        refine ⟨5344302639943612903662647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3562868426629075269108431 5344302639943612903662647)
        ·
          refine ⟨8016453959915419355493971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5344302639943612903662647 8016453959915419355493971)
          ·
            refine ⟨12024680939873129033240957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8016453959915419355493971 12024680939873129033240957)
            ·
              refine ⟨4509255352452423387465359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12024680939873129033240957 4509255352452423387465359)
              ·
                refine ⟨6763883028678635081198039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4509255352452423387465359 6763883028678635081198039)
                ·
                  refine ⟨10145824543017952621797059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6763883028678635081198039 10145824543017952621797059)
                  ·
                    refine ⟨15218736814526928932695589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10145824543017952621797059 15218736814526928932695589)
                    ·
                      refine ⟨2853513152723799174880423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15218736814526928932695589 2853513152723799174880423)
                      ·
                        rfl

theorem cell23_5557197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_5557197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557197 prefixEnd_5557197 := by exact prefixLift 5557197
  have htrace : WordTrace (prefixWord ++ tailWord_5557197) baseStart_5557197 baseEnd_5557197 := by
    simpa [prefixWord, tailWord_5557197, baseEnd_5557197] using wordTrace_append hprefix tailTrace_5557197
  have hstable : (prefixWord ++ tailWord_5557197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557197).length < 2 ^ (prefixWord ++ tailWord_5557197).sum := by decide
  have hdescent : baseEnd_5557197 < baseStart_5557197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557213 : List Nat := [1, 4, 3, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_5557213 : Nat := 118140960795 + 5557213 * 2 ^ 59
def prefixEnd_5557213 : Nat := 4983230072969 + 3 ^ 40 * 5557213 * 2
def baseEnd_5557213 : Nat := 2853521368414271112280349

theorem tailTrace_5557213 : CollatzResearch.WordTrace tailWord_5557213 prefixEnd_5557213 2853521368414271112280349 := by
  unfold tailWord_5557213
  simp only [CollatzResearch.WordTrace]
  refine ⟨202688209616173872264084293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135125473077449248176056195 202688209616173872264084293)
  ·
    refine ⟨38004039303032601049515805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202688209616173872264084293 38004039303032601049515805)
    ·
      refine ⟨14251514738637225393568427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38004039303032601049515805 14251514738637225393568427)
      ·
        refine ⟨21377272107955838090352641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14251514738637225393568427 21377272107955838090352641)
        ·
          refine ⟨16032954080966878567764481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21377272107955838090352641 16032954080966878567764481)
          ·
            refine ⟨12024715560725158925823361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16032954080966878567764481 12024715560725158925823361)
            ·
              refine ⟨9018536670543869194367521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12024715560725158925823361 9018536670543869194367521)
              ·
                refine ⟨6763902502907901895775641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9018536670543869194367521 6763902502907901895775641)
                ·
                  refine ⟨5072926877180926421831731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6763902502907901895775641 5072926877180926421831731)
                  ·
                    refine ⟨7609390315771389632747597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5072926877180926421831731 7609390315771389632747597)
                    ·
                      refine ⟨2853521368414271112280349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7609390315771389632747597 2853521368414271112280349)
                      ·
                        rfl

theorem cell23_5557213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_5557213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557213 prefixEnd_5557213 := by exact prefixLift 5557213
  have htrace : WordTrace (prefixWord ++ tailWord_5557213) baseStart_5557213 baseEnd_5557213 := by
    simpa [prefixWord, tailWord_5557213, baseEnd_5557213] using wordTrace_append hprefix tailTrace_5557213
  have hstable : (prefixWord ++ tailWord_5557213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557213).length < 2 ^ (prefixWord ++ tailWord_5557213).sum := by decide
  have hdescent : baseEnd_5557213 < baseStart_5557213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557219 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 3, 4, 2]
def baseStart_5557219 : Nat := 118140960795 + 5557219 * 2 ^ 59
def prefixEnd_5557219 : Nat := 4983230072969 + 3 ^ 40 * 5557219 * 2
def baseEnd_5557219 : Nat := 2853524449298198088805321

theorem tailTrace_5557219 : CollatzResearch.WordTrace tailWord_5557219 prefixEnd_5557219 2853524449298198088805321 := by
  unfold tailWord_5557219
  simp only [CollatzResearch.WordTrace]
  refine ⟨202688428454152135288802711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135125618969434756859201807 202688428454152135288802711)
  ·
    refine ⟨304032642681228202933204067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202688428454152135288802711 304032642681228202933204067)
    ·
      refine ⟨456048964021842304399806101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304032642681228202933204067 456048964021842304399806101)
      ·
        refine ⟨21377295188523858018740911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 456048964021842304399806101 21377295188523858018740911)
        ·
          refine ⟨32065942782785787028111367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21377295188523858018740911 32065942782785787028111367)
          ·
            refine ⟨48098914174178680542167051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32065942782785787028111367 48098914174178680542167051)
            ·
              refine ⟨72148371261268020813250577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48098914174178680542167051 72148371261268020813250577)
              ·
                refine ⟨54111278445951015609937933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72148371261268020813250577 54111278445951015609937933)
                ·
                  refine ⟨20291729417231630853726725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54111278445951015609937933 20291729417231630853726725)
                  ·
                    refine ⟨3804699265730930785073761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20291729417231630853726725 3804699265730930785073761)
                    ·
                      refine ⟨2853524449298198088805321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3804699265730930785073761 2853524449298198088805321)
                      ·
                        rfl

theorem cell23_5557219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_5557219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557219 prefixEnd_5557219 := by exact prefixLift 5557219
  have htrace : WordTrace (prefixWord ++ tailWord_5557219) baseStart_5557219 baseEnd_5557219 := by
    simpa [prefixWord, tailWord_5557219, baseEnd_5557219] using wordTrace_append hprefix tailTrace_5557219
  have hstable : (prefixWord ++ tailWord_5557219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557219).length < 2 ^ (prefixWord ++ tailWord_5557219).sum := by decide
  have hdescent : baseEnd_5557219 < baseStart_5557219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557225 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 13]
def baseStart_5557225 : Nat := 118140960795 + 5557225 * 2 ^ 59
def prefixEnd_5557225 : Nat := 4983230072969 + 3 ^ 40 * 5557225 * 2
def baseEnd_5557225 : Nat := 317058614464680562814477

theorem tailTrace_5557225 : CollatzResearch.WordTrace tailWord_5557225 prefixEnd_5557225 317058614464680562814477 := by
  unfold tailWord_5557225
  simp only [CollatzResearch.WordTrace]
  refine ⟨202688647292130398313521129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135125764861420265542347419 202688647292130398313521129)
  ·
    refine ⟨152016485469097798735140847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202688647292130398313521129 152016485469097798735140847)
    ·
      refine ⟨228024728203646698102711271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152016485469097798735140847 228024728203646698102711271)
      ·
        refine ⟨342037092305470047154066907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228024728203646698102711271 342037092305470047154066907)
        ·
          refine ⟨513055638458205070731100361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342037092305470047154066907 513055638458205070731100361)
          ·
            refine ⟨384791728843653803048325271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 513055638458205070731100361 384791728843653803048325271)
            ·
              refine ⟨577187593265480704572487907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384791728843653803048325271 577187593265480704572487907)
              ·
                refine ⟨865781389898221056858731861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577187593265480704572487907 865781389898221056858731861)
                ·
                  refine ⟨317058614464680562814477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 865781389898221056858731861 317058614464680562814477)
                  ·
                    rfl

theorem cell23_5557225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 13].length) (baseStart_5557225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557225 prefixEnd_5557225 := by exact prefixLift 5557225
  have htrace : WordTrace (prefixWord ++ tailWord_5557225) baseStart_5557225 baseEnd_5557225 := by
    simpa [prefixWord, tailWord_5557225, baseEnd_5557225] using wordTrace_append hprefix tailTrace_5557225
  have hstable : (prefixWord ++ tailWord_5557225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557225).length < 2 ^ (prefixWord ++ tailWord_5557225).sum := by decide
  have hdescent : baseEnd_5557225 < baseStart_5557225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557259 : List Nat := [1, 1, 1, 1, 6, 2, 1, 5, 5]
def baseStart_5557259 : Nat := 118140960795 + 5557259 * 2 ^ 59
def prefixEnd_5557259 : Nat := 4983230072969 + 3 ^ 40 * 5557259 * 2
def baseEnd_5557259 : Nat := 317060554280486436922793

theorem tailTrace_5557259 : CollatzResearch.WordTrace tailWord_5557259 prefixEnd_5557259 317060554280486436922793 := by
  unfold tailWord_5557259
  simp only [CollatzResearch.WordTrace]
  refine ⟨202689887374007222120258831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135126591582671481413505887 202689887374007222120258831)
  ·
    refine ⟨304034831061010833180388247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202689887374007222120258831 304034831061010833180388247)
    ·
      refine ⟨456052246591516249770582371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304034831061010833180388247 456052246591516249770582371)
      ·
        refine ⟨684078369887274374655873557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456052246591516249770582371 684078369887274374655873557)
        ·
          refine ⟨32066173588465986311994073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 684078369887274374655873557 32066173588465986311994073)
          ·
            refine ⟨24049630191349489733995555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32066173588465986311994073 24049630191349489733995555)
            ·
              refine ⟨36074445287024234600993333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24049630191349489733995555 36074445287024234600993333)
              ·
                refine ⟨3381979245658521993843125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36074445287024234600993333 3381979245658521993843125)
                ·
                  refine ⟨317060554280486436922793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3381979245658521993843125 317060554280486436922793)
                  ·
                    rfl

theorem cell23_5557259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 5, 5].length) (baseStart_5557259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557259 prefixEnd_5557259 := by exact prefixLift 5557259
  have htrace : WordTrace (prefixWord ++ tailWord_5557259) baseStart_5557259 baseEnd_5557259 := by
    simpa [prefixWord, tailWord_5557259, baseEnd_5557259] using wordTrace_append hprefix tailTrace_5557259
  have hstable : (prefixWord ++ tailWord_5557259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557259).length < 2 ^ (prefixWord ++ tailWord_5557259).sum := by decide
  have hdescent : baseEnd_5557259 < baseStart_5557259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557269 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_5557269 : Nat := 118140960795 + 5557269 * 2 ^ 59
def prefixEnd_5557269 : Nat := 4983230072969 + 3 ^ 40 * 5557269 * 2
def baseEnd_5557269 : Nat := 2853550123330922893180091

theorem tailTrace_5557269 : CollatzResearch.WordTrace tailWord_5557269 prefixEnd_5557269 2853550123330922893180091 := by
  unfold tailWord_5557269
  simp only [CollatzResearch.WordTrace]
  refine ⟨202690252103970993828122861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135126834735980662552081907 202690252103970993828122861)
  ·
    refine ⟨76008844538989122685546073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202690252103970993828122861 76008844538989122685546073)
    ·
      refine ⟨57006633404241842014159555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76008844538989122685546073 57006633404241842014159555)
      ·
        refine ⟨85509950106362763021239333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57006633404241842014159555 85509950106362763021239333)
        ·
          refine ⟨16033115644943018066482375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85509950106362763021239333 16033115644943018066482375)
          ·
            refine ⟨24049673467414527099723563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16033115644943018066482375 24049673467414527099723563)
            ·
              refine ⟨36074510201121790649585345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24049673467414527099723563 36074510201121790649585345)
              ·
                refine ⟨27055882650841342987189009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36074510201121790649585345 27055882650841342987189009)
                ·
                  refine ⟨20291911988131007240391757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27055882650841342987189009 20291911988131007240391757)
                  ·
                    refine ⟨7609466995549127715146909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20291911988131007240391757 7609466995549127715146909)
                    ·
                      refine ⟨2853550123330922893180091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7609466995549127715146909 2853550123330922893180091)
                      ·
                        rfl

theorem cell23_5557269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_5557269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557269 prefixEnd_5557269 := by exact prefixLift 5557269
  have htrace : WordTrace (prefixWord ++ tailWord_5557269) baseStart_5557269 baseEnd_5557269 := by
    simpa [prefixWord, tailWord_5557269, baseEnd_5557269] using wordTrace_append hprefix tailTrace_5557269
  have hstable : (prefixWord ++ tailWord_5557269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557269).length < 2 ^ (prefixWord ++ tailWord_5557269).sum := by decide
  have hdescent : baseEnd_5557269 < baseStart_5557269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557287 : List Nat := [1, 1, 7, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_5557287 : Nat := 118140960795 + 5557287 * 2 ^ 59
def prefixEnd_5557287 : Nat := 4983230072969 + 3 ^ 40 * 5557287 * 2
def baseEnd_5557287 : Nat := 2853559365982703822755009

theorem tailTrace_5557287 : CollatzResearch.WordTrace tailWord_5557287 prefixEnd_5557287 2853559365982703822755009 := by
  unfold tailWord_5557287
  simp only [CollatzResearch.WordTrace]
  refine ⟨202690908617905782902278115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135127272411937188601518743 202690908617905782902278115)
  ·
    refine ⟨304036362926858674353417173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202690908617905782902278115 304036362926858674353417173)
    ·
      refine ⟨7125852256098250180158215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 304036362926858674353417173 7125852256098250180158215)
      ·
        refine ⟨10688778384147375270237323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7125852256098250180158215 10688778384147375270237323)
        ·
          refine ⟨16033167576221062905355985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10688778384147375270237323 16033167576221062905355985)
          ·
            refine ⟨12024875682165797179016989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16033167576221062905355985 12024875682165797179016989)
            ·
              refine ⟨4509328380812173942131371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12024875682165797179016989 4509328380812173942131371)
              ·
                refine ⟨6763992571218260913197057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4509328380812173942131371 6763992571218260913197057)
                ·
                  refine ⟨5072994428413695684897793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6763992571218260913197057 5072994428413695684897793)
                  ·
                    refine ⟨3804745821310271763673345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5072994428413695684897793 3804745821310271763673345)
                    ·
                      refine ⟨2853559365982703822755009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3804745821310271763673345 2853559365982703822755009)
                      ·
                        rfl

theorem cell23_5557287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_5557287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557287 prefixEnd_5557287 := by exact prefixLift 5557287
  have htrace : WordTrace (prefixWord ++ tailWord_5557287) baseStart_5557287 baseEnd_5557287 := by
    simpa [prefixWord, tailWord_5557287, baseEnd_5557287] using wordTrace_append hprefix tailTrace_5557287
  have hstable : (prefixWord ++ tailWord_5557287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557287).length < 2 ^ (prefixWord ++ tailWord_5557287).sum := by decide
  have hdescent : baseEnd_5557287 < baseStart_5557287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557292 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_5557292 : Nat := 118140960795 + 5557292 * 2 ^ 59
def prefixEnd_5557292 : Nat := 4983230072969 + 3 ^ 40 * 5557292 * 2
def baseEnd_5557292 : Nat := 2853561933385976303192485

theorem tailTrace_5557292 : CollatzResearch.WordTrace tailWord_5557292 prefixEnd_5557292 2853561933385976303192485 := by
  unfold tailWord_5557292
  simp only [CollatzResearch.WordTrace]
  refine ⟨101345545491443834378105065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135127393988591779170806753 101345545491443834378105065)
  ·
    refine ⟨76009159118582875783578799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101345545491443834378105065 76009159118582875783578799)
    ·
      refine ⟨114013738677874313675368199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76009159118582875783578799 114013738677874313675368199)
      ·
        refine ⟨171020608016811470513052299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114013738677874313675368199 171020608016811470513052299)
        ·
          refine ⟨256530912025217205769578449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171020608016811470513052299 256530912025217205769578449)
          ·
            refine ⟨192398184018912904327183837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256530912025217205769578449 192398184018912904327183837)
            ·
              refine ⟨72149319007092339122693939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192398184018912904327183837 72149319007092339122693939)
              ·
                refine ⟨108223978510638508684040909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72149319007092339122693939 108223978510638508684040909)
                ·
                  refine ⟨40583991941489440756515341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108223978510638508684040909 40583991941489440756515341)
                  ·
                    refine ⟨15218996978058540283693253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40583991941489440756515341 15218996978058540283693253)
                    ·
                      refine ⟨2853561933385976303192485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15218996978058540283693253 2853561933385976303192485)
                      ·
                        rfl

theorem cell23_5557292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_5557292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557292 prefixEnd_5557292 := by exact prefixLift 5557292
  have htrace : WordTrace (prefixWord ++ tailWord_5557292) baseStart_5557292 baseEnd_5557292 := by
    simpa [prefixWord, tailWord_5557292, baseEnd_5557292] using wordTrace_append hprefix tailTrace_5557292
  have hstable : (prefixWord ++ tailWord_5557292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557292).length < 2 ^ (prefixWord ++ tailWord_5557292).sum := by decide
  have hdescent : baseEnd_5557292 < baseStart_5557292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557309 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_5557309 : Nat := 118140960795 + 5557309 * 2 ^ 59
def prefixEnd_5557309 : Nat := 4983230072969 + 3 ^ 40 * 5557309 * 2
def baseEnd_5557309 : Nat := 2853570662557102736679907

theorem tailTrace_5557309 : CollatzResearch.WordTrace tailWord_5557309 prefixEnd_5557309 2853570662557102736679907 := by
  unfold tailWord_5557309
  simp only [CollatzResearch.WordTrace]
  refine ⟨202691711023826080659578981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135127807349217387106385987 202691711023826080659578981)
  ·
    refine ⟨38004695816967390123671059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202691711023826080659578981 38004695816967390123671059)
    ·
      refine ⟨57007043725451085185506589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38004695816967390123671059 57007043725451085185506589)
      ·
        refine ⟨21377641397044156944564971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57007043725451085185506589 21377641397044156944564971)
        ·
          refine ⟨32066462095566235416847457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21377641397044156944564971 32066462095566235416847457)
          ·
            refine ⟨24049846571674676562635593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32066462095566235416847457 24049846571674676562635593)
            ·
              refine ⟨18037384928756007421976695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24049846571674676562635593 18037384928756007421976695)
              ·
                refine ⟨27056077393134011132965043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18037384928756007421976695 27056077393134011132965043)
                ·
                  refine ⟨40584116089701016699447565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27056077393134011132965043 40584116089701016699447565)
                  ·
                    refine ⟨15219043533637881262292837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40584116089701016699447565 15219043533637881262292837)
                    ·
                      refine ⟨2853570662557102736679907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15219043533637881262292837 2853570662557102736679907)
                      ·
                        rfl

theorem cell23_5557309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_5557309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557309 prefixEnd_5557309 := by exact prefixLift 5557309
  have htrace : WordTrace (prefixWord ++ tailWord_5557309) baseStart_5557309 baseEnd_5557309 := by
    simpa [prefixWord, tailWord_5557309, baseEnd_5557309] using wordTrace_append hprefix tailTrace_5557309
  have hstable : (prefixWord ++ tailWord_5557309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557309).length < 2 ^ (prefixWord ++ tailWord_5557309).sum := by decide
  have hdescent : baseEnd_5557309 < baseStart_5557309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557322 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_5557322 : Nat := 118140960795 + 5557322 * 2 ^ 59
def prefixEnd_5557322 : Nat := 4983230072969 + 3 ^ 40 * 5557322 * 2
def baseEnd_5557322 : Nat := 2853577337805611185817347

theorem tailTrace_5557322 : CollatzResearch.WordTrace tailWord_5557322 prefixEnd_5557322 2853577337805611185817347 := by
  unfold tailWord_5557322
  simp only [CollatzResearch.WordTrace]
  refine ⟨50673046293194745969950555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135128123448519322586534813 50673046293194745969950555)
  ·
    refine ⟨76009569439792118954925833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50673046293194745969950555 76009569439792118954925833)
    ·
      refine ⟨57007177079844089216194375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76009569439792118954925833 57007177079844089216194375)
      ·
        refine ⟨85510765619766133824291563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57007177079844089216194375 85510765619766133824291563)
        ·
          refine ⟨128266148429649200736437345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85510765619766133824291563 128266148429649200736437345)
          ·
            refine ⟨96199611322236900552328009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128266148429649200736437345 96199611322236900552328009)
            ·
              refine ⟨72149708491677675414246007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96199611322236900552328009 72149708491677675414246007)
              ·
                refine ⟨108224562737516513121369011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72149708491677675414246007 108224562737516513121369011)
                ·
                  refine ⟨162336844106274769682053517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108224562737516513121369011 162336844106274769682053517)
                  ·
                    refine ⟨60876316539853038630770069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 162336844106274769682053517 60876316539853038630770069)
                    ·
                      refine ⟨2853577337805611185817347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60876316539853038630770069 2853577337805611185817347)
                      ·
                        rfl

theorem cell23_5557322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_5557322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557322 prefixEnd_5557322 := by exact prefixLift 5557322
  have htrace : WordTrace (prefixWord ++ tailWord_5557322) baseStart_5557322 baseEnd_5557322 := by
    simpa [prefixWord, tailWord_5557322, baseEnd_5557322] using wordTrace_append hprefix tailTrace_5557322
  have hstable : (prefixWord ++ tailWord_5557322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557322).length < 2 ^ (prefixWord ++ tailWord_5557322).sum := by decide
  have hdescent : baseEnd_5557322 < baseStart_5557322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557329 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 4, 2, 3]
def baseStart_5557329 : Nat := 118140960795 + 5557329 * 2 ^ 59
def prefixEnd_5557329 : Nat := 4983230072969 + 3 ^ 40 * 5557329 * 2
def baseEnd_5557329 : Nat := 2853580932170192658429815

theorem tailTrace_5557329 : CollatzResearch.WordTrace tailWord_5557329 prefixEnd_5557329 2853580932170192658429815 := by
  unfold tailWord_5557329
  simp only [CollatzResearch.WordTrace]
  refine ⟨202692440483753624075307041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135128293655835749383538027 202692440483753624075307041)
  ·
    refine ⟨152019330362815218056480281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202692440483753624075307041 152019330362815218056480281)
    ·
      refine ⟨114014497772111413542360211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152019330362815218056480281 114014497772111413542360211)
      ·
        refine ⟨171021746658167120313540317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114014497772111413542360211 171021746658167120313540317)
        ·
          refine ⟨64133154996812670117577619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171021746658167120313540317 64133154996812670117577619)
          ·
            refine ⟨96199732495219005176366429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64133154996812670117577619 96199732495219005176366429)
            ·
              refine ⟨36074899685707126941137411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96199732495219005176366429 36074899685707126941137411)
              ·
                refine ⟨54112349528560690411706117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36074899685707126941137411 54112349528560690411706117)
                ·
                  refine ⟨10146065536605129452194897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54112349528560690411706117 10146065536605129452194897)
                  ·
                    refine ⟨7609549152453847089146173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10146065536605129452194897 7609549152453847089146173)
                    ·
                      refine ⟨2853580932170192658429815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7609549152453847089146173 2853580932170192658429815)
                      ·
                        rfl

theorem cell23_5557329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_5557329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557329 prefixEnd_5557329 := by exact prefixLift 5557329
  have htrace : WordTrace (prefixWord ++ tailWord_5557329) baseStart_5557329 baseEnd_5557329 := by
    simpa [prefixWord, tailWord_5557329, baseEnd_5557329] using wordTrace_append hprefix tailTrace_5557329
  have hstable : (prefixWord ++ tailWord_5557329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557329).length < 2 ^ (prefixWord ++ tailWord_5557329).sum := by decide
  have hdescent : baseEnd_5557329 < baseStart_5557329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557349 : List Nat := [1, 3, 1, 3, 2, 1, 3, 3, 6]
def baseStart_5557349 : Nat := 118140960795 + 5557349 * 2 ^ 59
def prefixEnd_5557349 : Nat := 4983230072969 + 3 ^ 40 * 5557349 * 2
def baseEnd_5557349 : Nat := 317065689087031397797747

theorem tailTrace_5557349 : CollatzResearch.WordTrace tailWord_5557349 prefixEnd_5557349 317065689087031397797747 := by
  unfold tailWord_5557349
  simp only [CollatzResearch.WordTrace]
  refine ⟨202693169943681167491035101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135128779962454111660690067 202693169943681167491035101)
  ·
    refine ⟨76009938728880437809138163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202693169943681167491035101 76009938728880437809138163)
    ·
      refine ⟨114014908093320656713707245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76009938728880437809138163 114014908093320656713707245)
      ·
        refine ⟨42755590534995246267640217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114014908093320656713707245 42755590534995246267640217)
        ·
          refine ⟨32066692901246434700730163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42755590534995246267640217 32066692901246434700730163)
          ·
            refine ⟨48100039351869652051095245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32066692901246434700730163 48100039351869652051095245)
            ·
              refine ⟨18037514756951119519160717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48100039351869652051095245 18037514756951119519160717)
              ·
                refine ⟨6764068033856669819685269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18037514756951119519160717 6764068033856669819685269)
                ·
                  refine ⟨317065689087031397797747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6764068033856669819685269 317065689087031397797747)
                  ·
                    rfl

theorem cell23_5557349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 6].length) (baseStart_5557349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557349 prefixEnd_5557349 := by exact prefixLift 5557349
  have htrace : WordTrace (prefixWord ++ tailWord_5557349) baseStart_5557349 baseEnd_5557349 := by
    simpa [prefixWord, tailWord_5557349, baseEnd_5557349] using wordTrace_append hprefix tailTrace_5557349
  have hstable : (prefixWord ++ tailWord_5557349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557349).length < 2 ^ (prefixWord ++ tailWord_5557349).sum := by decide
  have hdescent : baseEnd_5557349 < baseStart_5557349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557410 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_5557410 : Nat := 118140960795 + 5557410 * 2 ^ 59
def prefixEnd_5557410 : Nat := 4983230072969 + 3 ^ 40 * 5557410 * 2
def baseEnd_5557410 : Nat := 2853622524103206841516943

theorem tailTrace_5557410 : CollatzResearch.WordTrace tailWord_5557410 prefixEnd_5557410 2853622524103206841516943 := by
  unfold tailWord_5557410
  simp only [CollatzResearch.WordTrace]
  refine ⟨50673848699115043727251421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135130263197640116606003789 50673848699115043727251421)
  ·
    refine ⟨19002693262168141397719283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50673848699115043727251421 19002693262168141397719283)
    ·
      refine ⟨28504039893252212096578925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19002693262168141397719283 28504039893252212096578925)
      ·
        refine ⟨10689014959969579536217097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28504039893252212096578925 10689014959969579536217097)
        ·
          refine ⟨8016761219977184652162823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10689014959969579536217097 8016761219977184652162823)
          ·
            refine ⟨12025141829965776978244235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8016761219977184652162823 12025141829965776978244235)
            ·
              refine ⟨18037712744948665467366353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12025141829965776978244235 18037712744948665467366353)
              ·
                refine ⟨13528284558711499100524765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18037712744948665467366353 13528284558711499100524765)
                ·
                  refine ⟨5073106709516812162696787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13528284558711499100524765 5073106709516812162696787)
                  ·
                    refine ⟨7609660064275218244045181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5073106709516812162696787 7609660064275218244045181)
                    ·
                      refine ⟨2853622524103206841516943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7609660064275218244045181 2853622524103206841516943)
                      ·
                        rfl

theorem cell23_5557410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_5557410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557410 prefixEnd_5557410 := by exact prefixLift 5557410
  have htrace : WordTrace (prefixWord ++ tailWord_5557410) baseStart_5557410 baseEnd_5557410 := by
    simpa [prefixWord, tailWord_5557410, baseEnd_5557410] using wordTrace_append hprefix tailTrace_5557410
  have hstable : (prefixWord ++ tailWord_5557410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557410).length < 2 ^ (prefixWord ++ tailWord_5557410).sum := by decide
  have hdescent : baseEnd_5557410 < baseStart_5557410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557433 : List Nat := [1, 2, 1, 4, 1, 3, 4, 1, 1, 1, 4]
def baseStart_5557433 : Nat := 118140960795 + 5557433 * 2 ^ 59
def prefixEnd_5557433 : Nat := 4983230072969 + 3 ^ 40 * 5557433 * 2
def baseEnd_5557433 : Nat := 2853634334158260251529337

theorem tailTrace_5557433 : CollatzResearch.WordTrace tailWord_5557433 prefixEnd_5557433 2853634334158260251529337 := by
  unfold tailWord_5557433
  simp only [CollatzResearch.WordTrace]
  refine ⟨202696233675376849837092953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135130822450251233224728635 202696233675376849837092953)
  ·
    refine ⟨152022175256532637377819715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202696233675376849837092953 152022175256532637377819715)
    ·
      refine ⟨228033262884798956066729573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152022175256532637377819715 228033262884798956066729573)
      ·
        refine ⟨42756236790899804262511795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228033262884798956066729573 42756236790899804262511795)
        ·
          refine ⟨64134355186349706393767693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42756236790899804262511795 64134355186349706393767693)
          ·
            refine ⟨24050383194881139897662885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64134355186349706393767693 24050383194881139897662885)
            ·
              refine ⟨4509446849040213730811791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24050383194881139897662885 4509446849040213730811791)
              ·
                refine ⟨6764170273560320596217687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4509446849040213730811791 6764170273560320596217687)
                ·
                  refine ⟨10146255410340480894326531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6764170273560320596217687 10146255410340480894326531)
                  ·
                    refine ⟨15219383115510721341489797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10146255410340480894326531 15219383115510721341489797)
                    ·
                      refine ⟨2853634334158260251529337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15219383115510721341489797 2853634334158260251529337)
                      ·
                        rfl

theorem cell23_5557433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_5557433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557433 prefixEnd_5557433 := by exact prefixLift 5557433
  have htrace : WordTrace (prefixWord ++ tailWord_5557433) baseStart_5557433 baseEnd_5557433 := by
    simpa [prefixWord, tailWord_5557433, baseEnd_5557433] using wordTrace_append hprefix tailTrace_5557433
  have hstable : (prefixWord ++ tailWord_5557433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557433).length < 2 ^ (prefixWord ++ tailWord_5557433).sum := by decide
  have hdescent : baseEnd_5557433 < baseStart_5557433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557450 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 3, 2, 2]
def baseStart_5557450 : Nat := 118140960795 + 5557450 * 2 ^ 59
def prefixEnd_5557450 : Nat := 4983230072969 + 3 ^ 40 * 5557450 * 2
def baseEnd_5557450 : Nat := 2853643063329386685016759

theorem tailTrace_5557450 : CollatzResearch.WordTrace tailWord_5557450 prefixEnd_5557450 2853643063329386685016759 := by
  unfold tailWord_5557450
  simp only [CollatzResearch.WordTrace]
  refine ⟨50674213429078815435115451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135131235810876841160307869 50674213429078815435115451)
  ·
    refine ⟨76011320143618223152673177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50674213429078815435115451 76011320143618223152673177)
    ·
      refine ⟨57008490107713667364504883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76011320143618223152673177 57008490107713667364504883)
      ·
        refine ⟨85512735161570501046757325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57008490107713667364504883 85512735161570501046757325)
        ·
          refine ⟨32067275685588937892533997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85512735161570501046757325 32067275685588937892533997)
          ·
            refine ⟨12025228382095851709700249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32067275685588937892533997 12025228382095851709700249)
            ·
              refine ⟨9018921286571888782275187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12025228382095851709700249 9018921286571888782275187)
              ·
                refine ⟨13528381929857833173412781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9018921286571888782275187 13528381929857833173412781)
                ·
                  refine ⟨5073143223696687440029793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13528381929857833173412781 5073143223696687440029793)
                  ·
                    refine ⟨3804857417772515580022345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5073143223696687440029793 3804857417772515580022345)
                    ·
                      refine ⟨2853643063329386685016759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3804857417772515580022345 2853643063329386685016759)
                      ·
                        rfl

theorem cell23_5557450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_5557450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557450 prefixEnd_5557450 := by exact prefixLift 5557450
  have htrace : WordTrace (prefixWord ++ tailWord_5557450) baseStart_5557450 baseEnd_5557450 := by
    simpa [prefixWord, tailWord_5557450, baseEnd_5557450] using wordTrace_append hprefix tailTrace_5557450
  have hstable : (prefixWord ++ tailWord_5557450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557450).length < 2 ^ (prefixWord ++ tailWord_5557450).sum := by decide
  have hdescent : baseEnd_5557450 < baseStart_5557450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557460 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_5557460 : Nat := 118140960795 + 5557460 * 2 ^ 59
def prefixEnd_5557460 : Nat := 4983230072969 + 3 ^ 40 * 5557460 * 2
def baseEnd_5557460 : Nat := 951216066045310548630571

theorem tailTrace_5557460 : CollatzResearch.WordTrace tailWord_5557460 prefixEnd_5557460 951216066045310548630571 := by
  unfold tailWord_5557460
  simp only [CollatzResearch.WordTrace]
  refine ⟨101348609223139516724162917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135131478964186022298883889 101348609223139516724162917)
  ·
    refine ⟨19002864229338659385780547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101348609223139516724162917 19002864229338659385780547)
    ·
      refine ⟨28504296344007989078670821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19002864229338659385780547 28504296344007989078670821)
      ·
        refine ⟨5344555564501497952250779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28504296344007989078670821 5344555564501497952250779)
        ·
          refine ⟨8016833346752246928376169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5344555564501497952250779 8016833346752246928376169)
          ·
            refine ⟨6012625010064185196282127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8016833346752246928376169 6012625010064185196282127)
            ·
              refine ⟨9018937515096277794423191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6012625010064185196282127 9018937515096277794423191)
              ·
                refine ⟨13528406272644416691634787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9018937515096277794423191 13528406272644416691634787)
                ·
                  refine ⟨20292609408966625037452181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13528406272644416691634787 20292609408966625037452181)
                  ·
                    refine ⟨951216066045310548630571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20292609408966625037452181 951216066045310548630571)
                    ·
                      rfl

theorem cell23_5557460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_5557460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557460 prefixEnd_5557460 := by exact prefixLift 5557460
  have htrace : WordTrace (prefixWord ++ tailWord_5557460) baseStart_5557460 baseEnd_5557460 := by
    simpa [prefixWord, tailWord_5557460, baseEnd_5557460] using wordTrace_append hprefix tailTrace_5557460
  have hstable : (prefixWord ++ tailWord_5557460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557460).length < 2 ^ (prefixWord ++ tailWord_5557460).sum := by decide
  have hdescent : baseEnd_5557460 < baseStart_5557460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557489 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_5557489 : Nat := 118140960795 + 5557489 * 2 ^ 59
def prefixEnd_5557489 : Nat := 4983230072969 + 3 ^ 40 * 5557489 * 2
def baseEnd_5557489 : Nat := 2853663089074912032429079

theorem tailTrace_5557489 : CollatzResearch.WordTrace tailWord_5557489 prefixEnd_5557489 2853663089074912032429079 := by
  unfold tailWord_5557489
  simp only [CollatzResearch.WordTrace]
  refine ⟨202698276163173971401131521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135132184108782647600754347 202698276163173971401131521)
  ·
    refine ⟨152023707122380478550848641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202698276163173971401131521 152023707122380478550848641)
    ·
      refine ⟨114017780341785358913136481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152023707122380478550848641 114017780341785358913136481)
      ·
        refine ⟨85513335256339019184852361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114017780341785358913136481 85513335256339019184852361)
        ·
          refine ⟨64135001442254264388639271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85513335256339019184852361 64135001442254264388639271)
          ·
            refine ⟨96202502163381396582958907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64135001442254264388639271 96202502163381396582958907)
            ·
              refine ⟨144303753245072094874438361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96202502163381396582958907 144303753245072094874438361)
              ·
                refine ⟨108227814933804071155828771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144303753245072094874438361 108227814933804071155828771)
                ·
                  refine ⟨162341722400706106733743157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108227814933804071155828771 162341722400706106733743157)
                  ·
                    refine ⟨15219536475066197506288421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 162341722400706106733743157 15219536475066197506288421)
                    ·
                      refine ⟨2853663089074912032429079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15219536475066197506288421 2853663089074912032429079)
                      ·
                        rfl

theorem cell23_5557489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_5557489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557489 prefixEnd_5557489 := by exact prefixLift 5557489
  have htrace : WordTrace (prefixWord ++ tailWord_5557489) baseStart_5557489 baseEnd_5557489 := by
    simpa [prefixWord, tailWord_5557489, baseEnd_5557489] using wordTrace_append hprefix tailTrace_5557489
  have hstable : (prefixWord ++ tailWord_5557489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557489).length < 2 ^ (prefixWord ++ tailWord_5557489).sum := by decide
  have hdescent : baseEnd_5557489 < baseStart_5557489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557509 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_5557509 : Nat := 118140960795 + 5557509 * 2 ^ 59
def prefixEnd_5557509 : Nat := 4983230072969 + 3 ^ 40 * 5557509 * 2
def baseEnd_5557509 : Nat := 2853673358688001954178987

theorem tailTrace_5557509 : CollatzResearch.WordTrace tailWord_5557509 prefixEnd_5557509 2853673358688001954178987 := by
  unfold tailWord_5557509
  simp only [CollatzResearch.WordTrace]
  refine ⟨202699005623101514816859581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135132670415401009877906387 202699005623101514816859581)
  ·
    refine ⟨76012127108663068056322343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202699005623101514816859581 76012127108663068056322343)
    ·
      refine ⟨114018190662994602084483515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76012127108663068056322343 114018190662994602084483515)
      ·
        refine ⟨171027285994491903126725273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114018190662994602084483515 171027285994491903126725273)
        ·
          refine ⟨128270464495868927345043955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171027285994491903126725273 128270464495868927345043955)
          ·
            refine ⟨192405696743803391017565933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128270464495868927345043955 192405696743803391017565933)
            ·
              refine ⟨72152136278926271631587225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192405696743803391017565933 72152136278926271631587225)
              ·
                refine ⟨54114102209194703723690419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72152136278926271631587225 54114102209194703723690419)
                ·
                  refine ⟨81171153313792055585535629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54114102209194703723690419 81171153313792055585535629)
                  ·
                    refine ⟨30439182492672020844575861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81171153313792055585535629 30439182492672020844575861)
                    ·
                      refine ⟨2853673358688001954178987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30439182492672020844575861 2853673358688001954178987)
                      ·
                        rfl

theorem cell23_5557509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_5557509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557509 prefixEnd_5557509 := by exact prefixLift 5557509
  have htrace : WordTrace (prefixWord ++ tailWord_5557509) baseStart_5557509 baseEnd_5557509 := by
    simpa [prefixWord, tailWord_5557509, baseEnd_5557509] using wordTrace_append hprefix tailTrace_5557509
  have hstable : (prefixWord ++ tailWord_5557509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557509).length < 2 ^ (prefixWord ++ tailWord_5557509).sum := by decide
  have hdescent : baseEnd_5557509 < baseStart_5557509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557557 : List Nat := [1, 3, 3, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_5557557 : Nat := 118140960795 + 5557557 * 2 ^ 59
def prefixEnd_5557557 : Nat := 4983230072969 + 3 ^ 40 * 5557557 * 2
def baseEnd_5557557 : Nat := 2853698005759417766378767

theorem tailTrace_5557557 : CollatzResearch.WordTrace tailWord_5557557 prefixEnd_5557557 2853698005759417766378767 := by
  unfold tailWord_5557557
  simp only [CollatzResearch.WordTrace]
  refine ⟨202700756326927619014606925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135133837551285079343071283 202700756326927619014606925)
  ·
    refine ⟨76012783622597857130477597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202700756326927619014606925 76012783622597857130477597)
    ·
      refine ⟨28504793858474196423929099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76012783622597857130477597 28504793858474196423929099)
      ·
        refine ⟨42757190787711294635893649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28504793858474196423929099 42757190787711294635893649)
        ·
          refine ⟨32067893090783470976920237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42757190787711294635893649 32067893090783470976920237)
          ·
            refine ⟨12025459909043801616345089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32067893090783470976920237 12025459909043801616345089)
            ·
              refine ⟨9019094931782851212258817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12025459909043801616345089 9019094931782851212258817)
              ·
                refine ⟨6764321198837138409194113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9019094931782851212258817 6764321198837138409194113)
                ·
                  refine ⟨5073240899127853806895585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6764321198837138409194113 5073240899127853806895585)
                  ·
                    refine ⟨3804930674345890355171689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5073240899127853806895585 3804930674345890355171689)
                    ·
                      refine ⟨2853698005759417766378767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3804930674345890355171689 2853698005759417766378767)
                      ·
                        rfl

theorem cell23_5557557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_5557557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557557 prefixEnd_5557557 := by exact prefixLift 5557557
  have htrace : WordTrace (prefixWord ++ tailWord_5557557) baseStart_5557557 baseEnd_5557557 := by
    simpa [prefixWord, tailWord_5557557, baseEnd_5557557] using wordTrace_append hprefix tailTrace_5557557
  have hstable : (prefixWord ++ tailWord_5557557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557557).length < 2 ^ (prefixWord ++ tailWord_5557557).sum := by decide
  have hdescent : baseEnd_5557557 < baseStart_5557557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557559 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 5, 7]
def baseStart_5557559 : Nat := 118140960795 + 5557559 * 2 ^ 59
def prefixEnd_5557559 : Nat := 4983230072969 + 3 ^ 40 * 5557559 * 2
def baseEnd_5557559 : Nat := 951233010906908919517919

theorem tailTrace_5557559 : CollatzResearch.WordTrace tailWord_5557559 prefixEnd_5557559 951233010906908919517919 := by
  unfold tailWord_5557559
  simp only [CollatzResearch.WordTrace]
  refine ⟨202700829272920373356179731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135133886181946915570786487 202700829272920373356179731)
  ·
    refine ⟨304051243909380560034269597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202700829272920373356179731 304051243909380560034269597)
    ·
      refine ⟨114019216466017710012851099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304051243909380560034269597 114019216466017710012851099)
      ·
        refine ⟨171028824699026565019276649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114019216466017710012851099 171028824699026565019276649)
        ·
          refine ⟨128271618524269923764457487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171028824699026565019276649 128271618524269923764457487)
          ·
            refine ⟨192407427786404885646686231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128271618524269923764457487 192407427786404885646686231)
            ·
              refine ⟨288611141679607328470029347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192407427786404885646686231 288611141679607328470029347)
              ·
                refine ⟨432916712519410992705044021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288611141679607328470029347 432916712519410992705044021)
                ·
                  refine ⟨40585941798694780566097877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 432916712519410992705044021 40585941798694780566097877)
                  ·
                    refine ⟨951233010906908919517919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40585941798694780566097877 951233010906908919517919)
                    ·
                      rfl

theorem cell23_5557559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_5557559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557559 prefixEnd_5557559 := by exact prefixLift 5557559
  have htrace : WordTrace (prefixWord ++ tailWord_5557559) baseStart_5557559 baseEnd_5557559 := by
    simpa [prefixWord, tailWord_5557559, baseEnd_5557559] using wordTrace_append hprefix tailTrace_5557559
  have hstable : (prefixWord ++ tailWord_5557559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557559).length < 2 ^ (prefixWord ++ tailWord_5557559).sum := by decide
  have hdescent : baseEnd_5557559 < baseStart_5557559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557623 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 3, 4]
def baseStart_5557623 : Nat := 118140960795 + 5557623 * 2 ^ 59
def prefixEnd_5557623 : Nat := 4983230072969 + 3 ^ 40 * 5557623 * 2
def baseEnd_5557623 : Nat := 951243965160871502717821

theorem tailTrace_5557623 : CollatzResearch.WordTrace tailWord_5557623 prefixEnd_5557623 951243965160871502717821 := by
  unfold tailWord_5557623
  simp only [CollatzResearch.WordTrace]
  refine ⟨202703163544688512286509523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135135442363125674857673015 202703163544688512286509523)
  ·
    refine ⟨304054745317032768429764285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202703163544688512286509523 304054745317032768429764285)
    ·
      refine ⟨114020529493887288161161607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304054745317032768429764285 114020529493887288161161607)
      ·
        refine ⟨171030794240830932241742411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114020529493887288161161607 171030794240830932241742411)
        ·
          refine ⟨256546191361246398362613617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171030794240830932241742411 256546191361246398362613617)
          ·
            refine ⟨192409643520934798771960213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256546191361246398362613617 192409643520934798771960213)
            ·
              refine ⟨9019202040043818692435635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 192409643520934798771960213 9019202040043818692435635)
              ·
                refine ⟨13528803060065728038653453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9019202040043818692435635 13528803060065728038653453)
                ·
                  refine ⟨5073301147524648014495045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13528803060065728038653453 5073301147524648014495045)
                  ·
                    refine ⟨951243965160871502717821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5073301147524648014495045 951243965160871502717821)
                    ·
                      rfl

theorem cell23_5557623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_5557623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557623 prefixEnd_5557623 := by exact prefixLift 5557623
  have htrace : WordTrace (prefixWord ++ tailWord_5557623) baseStart_5557623 baseEnd_5557623 := by
    simpa [prefixWord, tailWord_5557623, baseEnd_5557623] using wordTrace_append hprefix tailTrace_5557623
  have hstable : (prefixWord ++ tailWord_5557623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557623).length < 2 ^ (prefixWord ++ tailWord_5557623).sum := by decide
  have hdescent : baseEnd_5557623 < baseStart_5557623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557657 : List Nat := [1, 2, 1, 2, 1, 7, 1, 3, 1, 4]
def baseStart_5557657 : Nat := 118140960795 + 5557657 * 2 ^ 59
def prefixEnd_5557657 : Nat := 4983230072969 + 3 ^ 40 * 5557657 * 2
def baseEnd_5557657 : Nat := 951249784608289125042769

theorem tailTrace_5557657 : CollatzResearch.WordTrace tailWord_5557657 prefixEnd_5557657 951249784608289125042769 := by
  unfold tailWord_5557657
  simp only [CollatzResearch.WordTrace]
  refine ⟨202704403626565336093247225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135136269084376890728831483 202704403626565336093247225)
  ·
    refine ⟨152028302719924002069935419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202704403626565336093247225 152028302719924002069935419)
    ·
      refine ⟨228042454079886003104903129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152028302719924002069935419 228042454079886003104903129)
      ·
        refine ⟨171031840559914502328677347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228042454079886003104903129 171031840559914502328677347)
        ·
          refine ⟨256547760839871753493016021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171031840559914502328677347 256547760839871753493016021)
          ·
            refine ⟨6012838144684494222492563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 256547760839871753493016021 6012838144684494222492563)
            ·
              refine ⟨9019257217026741333738845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6012838144684494222492563 9019257217026741333738845)
              ·
                refine ⟨3382221456385028000152067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9019257217026741333738845 3382221456385028000152067)
                ·
                  refine ⟨5073332184577542000228101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3382221456385028000152067 5073332184577542000228101)
                  ·
                    refine ⟨951249784608289125042769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5073332184577542000228101 951249784608289125042769)
                    ·
                      rfl

theorem cell23_5557657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 1, 4].length) (baseStart_5557657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557657 prefixEnd_5557657 := by exact prefixLift 5557657
  have htrace : WordTrace (prefixWord ++ tailWord_5557657) baseStart_5557657 baseEnd_5557657 := by
    simpa [prefixWord, tailWord_5557657, baseEnd_5557657] using wordTrace_append hprefix tailTrace_5557657
  have hstable : (prefixWord ++ tailWord_5557657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557657).length < 2 ^ (prefixWord ++ tailWord_5557657).sum := by decide
  have hdescent : baseEnd_5557657 < baseStart_5557657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557700 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_5557700 : Nat := 118140960795 + 5557700 * 2 ^ 59
def prefixEnd_5557700 : Nat := 4983230072969 + 3 ^ 40 * 5557700 * 2
def baseEnd_5557700 : Nat := 951257144497670235630203

theorem tailTrace_5557700 : CollatzResearch.WordTrace tailWord_5557700 prefixEnd_5557700 951257144497670235630203 := by
  unfold tailWord_5557700
  simp only [CollatzResearch.WordTrace]
  refine ⟨101352985982704777218531277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135137314643606369624708369 101352985982704777218531277)
  ·
    refine ⟨38007369743514291456949229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101352985982704777218531277 38007369743514291456949229)
    ·
      refine ⟨14252763653817859296355961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38007369743514291456949229 14252763653817859296355961)
      ·
        refine ⟨10689572740363394472266971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14252763653817859296355961 10689572740363394472266971)
        ·
          refine ⟨16034359110545091708400457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10689572740363394472266971 16034359110545091708400457)
          ·
            refine ⟨12025769332908818781300343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16034359110545091708400457 12025769332908818781300343)
            ·
              refine ⟨18038653999363228171950515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12025769332908818781300343 18038653999363228171950515)
              ·
                refine ⟨27057980999044842257925773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18038653999363228171950515 27057980999044842257925773)
                ·
                  refine ⟨10146742874641815846722165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27057980999044842257925773 10146742874641815846722165)
                  ·
                    refine ⟨951257144497670235630203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10146742874641815846722165 951257144497670235630203)
                    ·
                      rfl

theorem cell23_5557700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_5557700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557700 prefixEnd_5557700 := by exact prefixLift 5557700
  have htrace : WordTrace (prefixWord ++ tailWord_5557700) baseStart_5557700 baseEnd_5557700 := by
    simpa [prefixWord, tailWord_5557700, baseEnd_5557700] using wordTrace_append hprefix tailTrace_5557700
  have hstable : (prefixWord ++ tailWord_5557700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557700).length < 2 ^ (prefixWord ++ tailWord_5557700).sum := by decide
  have hdescent : baseEnd_5557700 < baseStart_5557700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557703 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_5557703 : Nat := 118140960795 + 5557703 * 2 ^ 59
def prefixEnd_5557703 : Nat := 4983230072969 + 3 ^ 40 * 5557703 * 2
def baseEnd_5557703 : Nat := 2853772973934974195153095

theorem tailTrace_5557703 : CollatzResearch.WordTrace tailWord_5557703 prefixEnd_5557703 2853772973934974195153095 := by
  unfold tailWord_5557703
  simp only [CollatzResearch.WordTrace]
  refine ⟨202706081384398685949421763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135137387589599123966281175 202706081384398685949421763)
  ·
    refine ⟨304059122076598028924132645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202706081384398685949421763 304059122076598028924132645)
    ·
      refine ⟨57011085389362130423274871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 304059122076598028924132645 57011085389362130423274871)
      ·
        refine ⟨85516628084043195634912307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57011085389362130423274871 85516628084043195634912307)
        ·
          refine ⟨128274942126064793452368461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85516628084043195634912307 128274942126064793452368461)
          ·
            refine ⟨48103103297274297544638173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128274942126064793452368461 48103103297274297544638173)
            ·
              refine ⟨18038663736477861579239315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48103103297274297544638173 18038663736477861579239315)
              ·
                refine ⟨27057995604716792368858973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18038663736477861579239315 27057995604716792368858973)
                ·
                  refine ⟨10146748351768797138322115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27057995604716792368858973 10146748351768797138322115)
                  ·
                    refine ⟨15220122527653195707483173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10146748351768797138322115 15220122527653195707483173)
                    ·
                      refine ⟨2853772973934974195153095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15220122527653195707483173 2853772973934974195153095)
                      ·
                        rfl

theorem cell23_5557703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_5557703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557703 prefixEnd_5557703 := by exact prefixLift 5557703
  have htrace : WordTrace (prefixWord ++ tailWord_5557703) baseStart_5557703 baseEnd_5557703 := by
    simpa [prefixWord, tailWord_5557703, baseEnd_5557703] using wordTrace_append hprefix tailTrace_5557703
  have hstable : (prefixWord ++ tailWord_5557703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557703).length < 2 ^ (prefixWord ++ tailWord_5557703).sum := by decide
  have hdescent : baseEnd_5557703 < baseStart_5557703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557731 : List Nat := [1, 1, 1, 6, 2, 3, 2, 2, 1, 1, 3]
def baseStart_5557731 : Nat := 118140960795 + 5557731 * 2 ^ 59
def prefixEnd_5557731 : Nat := 4983230072969 + 3 ^ 40 * 5557731 * 2
def baseEnd_5557731 : Nat := 2853787351393300085602967

theorem tailTrace_5557731 : CollatzResearch.WordTrace tailWord_5557731 prefixEnd_5557731 2853787351393300085602967 := by
  unfold tailWord_5557731
  simp only [CollatzResearch.WordTrace]
  refine ⟨202707102628297246731441047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135138068418864831154294031 202707102628297246731441047)
  ·
    refine ⟨304060653942445870097161571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202707102628297246731441047 304060653942445870097161571)
    ·
      refine ⟨456090980913668805145742357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304060653942445870097161571 456090980913668805145742357)
      ·
        refine ⟨21379264730328225241206673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 456090980913668805145742357 21379264730328225241206673)
        ·
          refine ⟨16034448547746168930905005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21379264730328225241206673 16034448547746168930905005)
          ·
            refine ⟨6012918205404813349089377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16034448547746168930905005 6012918205404813349089377)
            ·
              refine ⟨4509688654053610011817033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6012918205404813349089377 4509688654053610011817033)
              ·
                refine ⟨3382266490540207508862775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4509688654053610011817033 3382266490540207508862775)
                ·
                  refine ⟨5073399735810311263294163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3382266490540207508862775 5073399735810311263294163)
                  ·
                    refine ⟨7610099603715466894941245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5073399735810311263294163 7610099603715466894941245)
                    ·
                      refine ⟨2853787351393300085602967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7610099603715466894941245 2853787351393300085602967)
                      ·
                        rfl

theorem cell23_5557731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_5557731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557731 prefixEnd_5557731 := by exact prefixLift 5557731
  have htrace : WordTrace (prefixWord ++ tailWord_5557731) baseStart_5557731 baseEnd_5557731 := by
    simpa [prefixWord, tailWord_5557731, baseEnd_5557731] using wordTrace_append hprefix tailTrace_5557731
  have hstable : (prefixWord ++ tailWord_5557731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557731).length < 2 ^ (prefixWord ++ tailWord_5557731).sum := by decide
  have hdescent : baseEnd_5557731 < baseStart_5557731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557750 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_5557750 : Nat := 118140960795 + 5557750 * 2 ^ 59
def prefixEnd_5557750 : Nat := 4983230072969 + 3 ^ 40 * 5557750 * 2
def baseEnd_5557750 : Nat := 2853797107525735511265379

theorem tailTrace_5557750 : CollatzResearch.WordTrace tailWord_5557750 prefixEnd_5557750 2853797107525735511265379 := by
  unfold tailWord_5557750
  simp only [CollatzResearch.WordTrace]
  refine ⟨12669237225951775811023919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135138530410152275317588469 12669237225951775811023919)
  ·
    refine ⟨19003855838927663716535879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12669237225951775811023919 19003855838927663716535879)
    ·
      refine ⟨28505783758391495574803819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19003855838927663716535879 28505783758391495574803819)
      ·
        refine ⟨42758675637587243362205729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28505783758391495574803819 42758675637587243362205729)
        ·
          refine ⟨32069006728190432521654297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42758675637587243362205729 32069006728190432521654297)
          ·
            refine ⟨24051755046142824391240723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32069006728190432521654297 24051755046142824391240723)
            ·
              refine ⟨36077632569214236586861085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24051755046142824391240723 36077632569214236586861085)
              ·
                refine ⟨13529112213455338720072907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36077632569214236586861085 13529112213455338720072907)
                ·
                  refine ⟨20293668320183008080109361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13529112213455338720072907 20293668320183008080109361)
                  ·
                    refine ⟨15220251240137256060082021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20293668320183008080109361 15220251240137256060082021)
                    ·
                      refine ⟨2853797107525735511265379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15220251240137256060082021 2853797107525735511265379)
                      ·
                        rfl

theorem cell23_5557750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_5557750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557750 prefixEnd_5557750 := by exact prefixLift 5557750
  have htrace : WordTrace (prefixWord ++ tailWord_5557750) baseStart_5557750 baseEnd_5557750 := by
    simpa [prefixWord, tailWord_5557750, baseEnd_5557750] using wordTrace_append hprefix tailTrace_5557750
  have hstable : (prefixWord ++ tailWord_5557750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557750).length < 2 ^ (prefixWord ++ tailWord_5557750).sum := by decide
  have hdescent : baseEnd_5557750 < baseStart_5557750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557758 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5557758 : Nat := 118140960795 + 5557758 * 2 ^ 59
def prefixEnd_5557758 : Nat := 4983230072969 + 3 ^ 40 * 5557758 * 2
def baseEnd_5557758 : Nat := 2853801215370971479965343

theorem tailTrace_5557758 : CollatzResearch.WordTrace tailWord_5557758 prefixEnd_5557758 2853801215370971479965343 := by
  unfold tailWord_5557758
  simp only [CollatzResearch.WordTrace]
  refine ⟨25338510924899928792834241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135138724932799620228449285 25338510924899928792834241)
  ·
    refine ⟨19003883193674946594625681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25338510924899928792834241 19003883193674946594625681)
    ·
      refine ⟨14252912395256209945969261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19003883193674946594625681 14252912395256209945969261)
      ·
        refine ⟨5344842148221078729738473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14252912395256209945969261 5344842148221078729738473)
        ·
          refine ⟨4008631611165809047303855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5344842148221078729738473 4008631611165809047303855)
          ·
            refine ⟨6012947416748713570955783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4008631611165809047303855 6012947416748713570955783)
            ·
              refine ⟨9019421125123070356433675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6012947416748713570955783 9019421125123070356433675)
              ·
                refine ⟨13529131687684605534650513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9019421125123070356433675 13529131687684605534650513)
                ·
                  refine ⟨10146848765763454150987885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13529131687684605534650513 10146848765763454150987885)
                  ·
                    refine ⟨3805068287161295306620457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10146848765763454150987885 3805068287161295306620457)
                    ·
                      refine ⟨2853801215370971479965343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3805068287161295306620457 2853801215370971479965343)
                      ·
                        rfl

theorem cell23_5557758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5557758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557758 prefixEnd_5557758 := by exact prefixLift 5557758
  have htrace : WordTrace (prefixWord ++ tailWord_5557758) baseStart_5557758 baseEnd_5557758 := by
    simpa [prefixWord, tailWord_5557758, baseEnd_5557758] using wordTrace_append hprefix tailTrace_5557758
  have hstable : (prefixWord ++ tailWord_5557758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557758).length < 2 ^ (prefixWord ++ tailWord_5557758).sum := by decide
  have hdescent : baseEnd_5557758 < baseStart_5557758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557770 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_5557770 : Nat := 118140960795 + 5557770 * 2 ^ 59
def prefixEnd_5557770 : Nat := 4983230072969 + 3 ^ 40 * 5557770 * 2
def baseEnd_5557770 : Nat := 2853807377138825433015287

theorem tailTrace_5557770 : CollatzResearch.WordTrace tailWord_5557770 prefixEnd_5557770 2853807377138825433015287 := by
  unfold tailWord_5557770
  simp only [CollatzResearch.WordTrace]
  refine ⟨50677131268788989098027691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135139016716770637594740509 50677131268788989098027691)
  ·
    refine ⟨76015696903183483647041537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50677131268788989098027691 76015696903183483647041537)
    ·
      refine ⟨57011772677387612735281153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76015696903183483647041537 57011772677387612735281153)
      ·
        refine ⟨42758829508040709551460865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57011772677387612735281153 42758829508040709551460865)
        ·
          refine ⟨32069122131030532163595649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42758829508040709551460865 32069122131030532163595649)
          ·
            refine ⟨24051841598272899122696737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32069122131030532163595649 24051841598272899122696737)
            ·
              refine ⟨18038881198704674342022553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24051841598272899122696737 18038881198704674342022553)
              ·
                refine ⟨13529160899028505756516915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18038881198704674342022553 13529160899028505756516915)
                ·
                  refine ⟨20293741348542758634775373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13529160899028505756516915 20293741348542758634775373)
                  ·
                    refine ⟨7610153005703534488040765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20293741348542758634775373 7610153005703534488040765)
                    ·
                      refine ⟨2853807377138825433015287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7610153005703534488040765 2853807377138825433015287)
                      ·
                        rfl

theorem cell23_5557770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_5557770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557770 prefixEnd_5557770 := by exact prefixLift 5557770
  have htrace : WordTrace (prefixWord ++ tailWord_5557770) baseStart_5557770 baseEnd_5557770 := by
    simpa [prefixWord, tailWord_5557770, baseEnd_5557770] using wordTrace_append hprefix tailTrace_5557770
  have hstable : (prefixWord ++ tailWord_5557770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557770).length < 2 ^ (prefixWord ++ tailWord_5557770).sum := by decide
  have hdescent : baseEnd_5557770 < baseStart_5557770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557771 : List Nat := [1, 1, 1, 1, 8, 1, 2, 3, 1, 2, 2]
def baseStart_5557771 : Nat := 118140960795 + 5557771 * 2 ^ 59
def prefixEnd_5557771 : Nat := 4983230072969 + 3 ^ 40 * 5557771 * 2
def baseEnd_5557771 : Nat := 2853807890619479929102783

theorem tailTrace_5557771 : CollatzResearch.WordTrace tailWord_5557771 prefixEnd_5557771 2853807890619479929102783 := by
  unfold tailWord_5557771
  simp only [CollatzResearch.WordTrace]
  refine ⟨202708561548152333562897167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135139041032101555708598111 202708561548152333562897167)
  ·
    refine ⟨304062842322228500344345751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202708561548152333562897167 304062842322228500344345751)
    ·
      refine ⟨456094263483342750516518627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304062842322228500344345751 456094263483342750516518627)
      ·
        refine ⟨684141395225014125774777941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456094263483342750516518627 684141395225014125774777941)
        ·
          refine ⟨8017281975293134286423179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 684141395225014125774777941 8017281975293134286423179)
          ·
            refine ⟨12025922962939701429634769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8017281975293134286423179 12025922962939701429634769)
            ·
              refine ⟨9019442222204776072226077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12025922962939701429634769 9019442222204776072226077)
              ·
                refine ⟨3382290833326791027084779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9019442222204776072226077 3382290833326791027084779)
                ·
                  refine ⟨5073436249990186540627169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3382290833326791027084779 5073436249990186540627169)
                  ·
                    refine ⟨3805077187492639905470377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5073436249990186540627169 3805077187492639905470377)
                    ·
                      refine ⟨2853807890619479929102783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3805077187492639905470377 2853807890619479929102783)
                      ·
                        rfl

theorem cell23_5557771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 1, 2, 2].length) (baseStart_5557771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557771 prefixEnd_5557771 := by exact prefixLift 5557771
  have htrace : WordTrace (prefixWord ++ tailWord_5557771) baseStart_5557771 baseEnd_5557771 := by
    simpa [prefixWord, tailWord_5557771, baseEnd_5557771] using wordTrace_append hprefix tailTrace_5557771
  have hstable : (prefixWord ++ tailWord_5557771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557771).length < 2 ^ (prefixWord ++ tailWord_5557771).sum := by decide
  have hdescent : baseEnd_5557771 < baseStart_5557771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557843 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 3]
def baseStart_5557843 : Nat := 118140960795 + 5557843 * 2 ^ 59
def prefixEnd_5557843 : Nat := 4983230072969 + 3 ^ 40 * 5557843 * 2
def baseEnd_5557843 : Nat := 2853844861226603647402451

theorem tailTrace_5557843 : CollatzResearch.WordTrace tailWord_5557843 prefixEnd_5557843 2853844861226603647402451 := by
  unfold tailWord_5557843
  simp only [CollatzResearch.WordTrace]
  refine ⟨202711187603891489859518183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135140791735927659906345455 202711187603891489859518183)
  ·
    refine ⟨304066781405837234789277275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202711187603891489859518183 304066781405837234789277275)
    ·
      refine ⟨456100172108755852183915913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304066781405837234789277275 456100172108755852183915913)
      ·
        refine ⟨342075129081566889137936935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456100172108755852183915913 342075129081566889137936935)
        ·
          refine ⟨513112693622350333706905403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342075129081566889137936935 513112693622350333706905403)
          ·
            refine ⟨769669040433525500560358105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513112693622350333706905403 769669040433525500560358105)
            ·
              refine ⟨577251780325144125420268579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769669040433525500560358105 577251780325144125420268579)
              ·
                refine ⟨865877670487716188130402869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577251780325144125420268579 865877670487716188130402869)
                ·
                  refine ⟨81176031608223392637225269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 865877670487716188130402869 81176031608223392637225269)
                  ·
                    refine ⟨7610252963270943059739869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81176031608223392637225269 7610252963270943059739869)
                    ·
                      refine ⟨2853844861226603647402451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7610252963270943059739869 2853844861226603647402451)
                      ·
                        rfl

theorem cell23_5557843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 3].length) (baseStart_5557843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557843 prefixEnd_5557843 := by exact prefixLift 5557843
  have htrace : WordTrace (prefixWord ++ tailWord_5557843) baseStart_5557843 baseEnd_5557843 := by
    simpa [prefixWord, tailWord_5557843, baseEnd_5557843] using wordTrace_append hprefix tailTrace_5557843
  have hstable : (prefixWord ++ tailWord_5557843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557843).length < 2 ^ (prefixWord ++ tailWord_5557843).sum := by decide
  have hdescent : baseEnd_5557843 < baseStart_5557843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557844 : List Nat := [2, 4, 1, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_5557844 : Nat := 118140960795 + 5557844 * 2 ^ 59
def prefixEnd_5557844 : Nat := 4983230072969 + 3 ^ 40 * 5557844 * 2
def baseEnd_5557844 : Nat := 2853845374707258143489947

theorem tailTrace_5557844 : CollatzResearch.WordTrace tailWord_5557844 prefixEnd_5557844 2853845374707258143489947 := by
  unfold tailWord_5557844
  simp only [CollatzResearch.WordTrace]
  refine ⟨101355612038443933515152293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135140816051258578020203057 101355612038443933515152293)
  ·
    refine ⟨19004177257208237534091055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101355612038443933515152293 19004177257208237534091055)
    ·
      refine ⟨28506265885812356301136583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19004177257208237534091055 28506265885812356301136583)
      ·
        refine ⟨42759398828718534451704875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28506265885812356301136583 42759398828718534451704875)
        ·
          refine ⟨64139098243077801677557313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42759398828718534451704875 64139098243077801677557313)
          ·
            refine ⟨48104323682308351258167985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64139098243077801677557313 48104323682308351258167985)
            ·
              refine ⟨36078242761731263443625989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48104323682308351258167985 36078242761731263443625989)
              ·
                refine ⟨6764670517824611895679873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36078242761731263443625989 6764670517824611895679873)
                ·
                  refine ⟨5073502888368458921759905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6764670517824611895679873 5073502888368458921759905)
                  ·
                    refine ⟨3805127166276344191319929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5073502888368458921759905 3805127166276344191319929)
                    ·
                      refine ⟨2853845374707258143489947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3805127166276344191319929 2853845374707258143489947)
                      ·
                        rfl

theorem cell23_5557844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_5557844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557844 prefixEnd_5557844 := by exact prefixLift 5557844
  have htrace : WordTrace (prefixWord ++ tailWord_5557844) baseStart_5557844 baseEnd_5557844 := by
    simpa [prefixWord, tailWord_5557844, baseEnd_5557844] using wordTrace_append hprefix tailTrace_5557844
  have hstable : (prefixWord ++ tailWord_5557844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557844).length < 2 ^ (prefixWord ++ tailWord_5557844).sum := by decide
  have hdescent : baseEnd_5557844 < baseStart_5557844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557850 : List Nat := [3, 1, 1, 2, 1, 1, 1, 8, 5]
def baseStart_5557850 : Nat := 118140960795 + 5557850 * 2 ^ 59
def prefixEnd_5557850 : Nat := 4983230072969 + 3 ^ 40 * 5557850 * 2
def baseEnd_5557850 : Nat := 317094272843465013334991

theorem tailTrace_5557850 : CollatzResearch.WordTrace tailWord_5557850 prefixEnd_5557850 317094272843465013334991 := by
  unfold tailWord_5557850
  simp only [CollatzResearch.WordTrace]
  refine ⟨50677860728716532513755751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135140961943244086703348669 50677860728716532513755751)
  ·
    refine ⟨76016791093074798770633627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50677860728716532513755751 76016791093074798770633627)
    ·
      refine ⟨114025186639612198155950441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76016791093074798770633627 114025186639612198155950441)
      ·
        refine ⟨85518889979709148616962831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114025186639612198155950441 85518889979709148616962831)
        ·
          refine ⟨128278334969563722925444247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85518889979709148616962831 128278334969563722925444247)
          ·
            refine ⟨192417502454345584388166371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128278334969563722925444247 192417502454345584388166371)
            ·
              refine ⟨288626253681518376582249557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192417502454345584388166371 288626253681518376582249557)
              ·
                refine ⟨3382338910330293475573237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 288626253681518376582249557 3382338910330293475573237)
                ·
                  refine ⟨317094272843465013334991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3382338910330293475573237 317094272843465013334991)
                  ·
                    rfl

theorem cell23_5557850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 5].length) (baseStart_5557850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557850 prefixEnd_5557850 := by exact prefixLift 5557850
  have htrace : WordTrace (prefixWord ++ tailWord_5557850) baseStart_5557850 baseEnd_5557850 := by
    simpa [prefixWord, tailWord_5557850, baseEnd_5557850] using wordTrace_append hprefix tailTrace_5557850
  have hstable : (prefixWord ++ tailWord_5557850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557850).length < 2 ^ (prefixWord ++ tailWord_5557850).sum := by decide
  have hdescent : baseEnd_5557850 < baseStart_5557850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557861 : List Nat := [1, 3, 1, 3, 3, 1, 4, 1, 2, 2, 2]
def baseStart_5557861 : Nat := 118140960795 + 5557861 * 2 ^ 59
def prefixEnd_5557861 : Nat := 4983230072969 + 3 ^ 40 * 5557861 * 2
def baseEnd_5557861 : Nat := 2853854103878384576977369

theorem tailTrace_5557861 : CollatzResearch.WordTrace tailWord_5557861 prefixEnd_5557861 2853854103878384576977369 := by
  unfold tailWord_5557861
  simp only [CollatzResearch.WordTrace]
  refine ⟨202711844117826278933673437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135141229411884185955782291 202711844117826278933673437)
  ·
    refine ⟨76016941544184854600127539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 202711844117826278933673437 76016941544184854600127539)
    ·
      refine ⟨114025412316277281900191309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76016941544184854600127539 114025412316277281900191309)
      ·
        refine ⟨42759529618603980712571741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114025412316277281900191309 42759529618603980712571741)
        ·
          refine ⟨16034823606976492767214403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42759529618603980712571741 16034823606976492767214403)
          ·
            refine ⟨24052235410464739150821605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16034823606976492767214403 24052235410464739150821605)
            ·
              refine ⟨4509794139462138590779051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24052235410464739150821605 4509794139462138590779051)
              ·
                refine ⟨6764691209193207886168577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4509794139462138590779051 6764691209193207886168577)
                ·
                  refine ⟨5073518406894905914626433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6764691209193207886168577 5073518406894905914626433)
                  ·
                    refine ⟨3805138805171179435969825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5073518406894905914626433 3805138805171179435969825)
                    ·
                      refine ⟨2853854103878384576977369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3805138805171179435969825 2853854103878384576977369)
                      ·
                        rfl

theorem cell23_5557861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_5557861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557861 prefixEnd_5557861 := by exact prefixLift 5557861
  have htrace : WordTrace (prefixWord ++ tailWord_5557861) baseStart_5557861 baseEnd_5557861 := by
    simpa [prefixWord, tailWord_5557861, baseEnd_5557861] using wordTrace_append hprefix tailTrace_5557861
  have hstable : (prefixWord ++ tailWord_5557861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557861).length < 2 ^ (prefixWord ++ tailWord_5557861).sum := by decide
  have hdescent : baseEnd_5557861 < baseStart_5557861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557863 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 3, 7]
def baseStart_5557863 : Nat := 118140960795 + 5557863 * 2 ^ 59
def prefixEnd_5557863 : Nat := 4983230072969 + 3 ^ 40 * 5557863 * 2
def baseEnd_5557863 : Nat := 951285043613231189717453

theorem tailTrace_5557863 : CollatzResearch.WordTrace tailWord_5557863 prefixEnd_5557863 951285043613231189717453 := by
  unfold tailWord_5557863
  simp only [CollatzResearch.WordTrace]
  refine ⟨202711917063819033275246243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135141278042546022183497495 202711917063819033275246243)
  ·
    refine ⟨304067875595728549912869365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202711917063819033275246243 304067875595728549912869365)
    ·
      refine ⟨28506363337099551554331503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 304067875595728549912869365 28506363337099551554331503)
      ·
        refine ⟨42759545005649327331497255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28506363337099551554331503 42759545005649327331497255)
        ·
          refine ⟨64139317508473990997245883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42759545005649327331497255 64139317508473990997245883)
          ·
            refine ⟨96208976262710986495868825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64139317508473990997245883 96208976262710986495868825)
            ·
              refine ⟨72156732197033239871901619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96208976262710986495868825 72156732197033239871901619)
              ·
                refine ⟨108235098295549859807852429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72156732197033239871901619 108235098295549859807852429)
                ·
                  refine ⟨40588161860831197427944661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108235098295549859807852429 40588161860831197427944661)
                  ·
                    refine ⟨951285043613231189717453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40588161860831197427944661 951285043613231189717453)
                    ·
                      rfl

theorem cell23_5557863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_5557863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557863 prefixEnd_5557863 := by exact prefixLift 5557863
  have htrace : WordTrace (prefixWord ++ tailWord_5557863) baseStart_5557863 baseEnd_5557863 := by
    simpa [prefixWord, tailWord_5557863, baseEnd_5557863] using wordTrace_append hprefix tailTrace_5557863
  have hstable : (prefixWord ++ tailWord_5557863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557863).length < 2 ^ (prefixWord ++ tailWord_5557863).sum := by decide
  have hdescent : baseEnd_5557863 < baseStart_5557863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557900 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 2, 1, 4]
def baseStart_5557900 : Nat := 118140960795 + 5557900 * 2 ^ 59
def prefixEnd_5557900 : Nat := 4983230072969 + 3 ^ 40 * 5557900 * 2
def baseEnd_5557900 : Nat := 2853874129623909924389689

theorem tailTrace_5557900 : CollatzResearch.WordTrace tailWord_5557900 prefixEnd_5557900 2853874129623909924389689 := by
  unfold tailWord_5557900
  simp only [CollatzResearch.WordTrace]
  refine ⟨101356633282342494297171577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135142177709789992396228769 101356633282342494297171577)
  ·
    refine ⟨76017474961756870722878683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101356633282342494297171577 76017474961756870722878683)
    ·
      refine ⟨114026212442635306084318025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76017474961756870722878683 114026212442635306084318025)
      ·
        refine ⟨85519659331976479563238519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114026212442635306084318025 85519659331976479563238519)
        ·
          refine ⟨128279488997964719344857779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85519659331976479563238519 128279488997964719344857779)
          ·
            refine ⟨192419233496947079017286669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128279488997964719344857779 192419233496947079017286669)
            ·
              refine ⟨72157212561355154631482501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192419233496947079017286669 72157212561355154631482501)
              ·
                refine ⟨13529477355254091493402969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72157212561355154631482501 13529477355254091493402969)
                ·
                  refine ⟨10147108016440568620052227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13529477355254091493402969 10147108016440568620052227)
                  ·
                    refine ⟨15220662024660852930078341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10147108016440568620052227 15220662024660852930078341)
                    ·
                      refine ⟨2853874129623909924389689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15220662024660852930078341 2853874129623909924389689)
                      ·
                        rfl

theorem cell23_5557900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_5557900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557900 prefixEnd_5557900 := by exact prefixLift 5557900
  have htrace : WordTrace (prefixWord ++ tailWord_5557900) baseStart_5557900 baseEnd_5557900 := by
    simpa [prefixWord, tailWord_5557900, baseEnd_5557900] using wordTrace_append hprefix tailTrace_5557900
  have hstable : (prefixWord ++ tailWord_5557900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557900).length < 2 ^ (prefixWord ++ tailWord_5557900).sum := by decide
  have hdescent : baseEnd_5557900 < baseStart_5557900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557913 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 6]
def baseStart_5557913 : Nat := 118140960795 + 5557913 * 2 ^ 59
def prefixEnd_5557913 : Nat := 4983230072969 + 3 ^ 40 * 5557913 * 2
def baseEnd_5557913 : Nat := 2853880804872418373527129

theorem tailTrace_5557913 : CollatzResearch.WordTrace tailWord_5557913 prefixEnd_5557913 2853880804872418373527129 := by
  unfold tailWord_5557913
  simp only [CollatzResearch.WordTrace]
  refine ⟨202713740713637891814566393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135142493809091927876377595 202713740713637891814566393)
  ·
    refine ⟨152035305535228418860924795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202713740713637891814566393 152035305535228418860924795)
    ·
      refine ⟨228052958302842628291387193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152035305535228418860924795 228052958302842628291387193)
      ·
        refine ⟨171039718727131971218540395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228052958302842628291387193 171039718727131971218540395)
        ·
          refine ⟨256559578090697956827810593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171039718727131971218540395 256559578090697956827810593)
          ·
            refine ⟨192419683568023467620857945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256559578090697956827810593 192419683568023467620857945)
            ·
              refine ⟨144314762676017600715643459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192419683568023467620857945 144314762676017600715643459)
              ·
                refine ⟨216472144014026401073465189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144314762676017600715643459 216472144014026401073465189)
                ·
                  refine ⟨40588527002629950201274723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 216472144014026401073465189 40588527002629950201274723)
                  ·
                    refine ⟨60882790503944925301912085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40588527002629950201274723 60882790503944925301912085)
                    ·
                      refine ⟨2853880804872418373527129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60882790503944925301912085 2853880804872418373527129)
                      ·
                        rfl

theorem cell23_5557913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_5557913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557913 prefixEnd_5557913 := by exact prefixLift 5557913
  have htrace : WordTrace (prefixWord ++ tailWord_5557913) baseStart_5557913 baseEnd_5557913 := by
    simpa [prefixWord, tailWord_5557913, baseEnd_5557913] using wordTrace_append hprefix tailTrace_5557913
  have hstable : (prefixWord ++ tailWord_5557913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557913).length < 2 ^ (prefixWord ++ tailWord_5557913).sum := by decide
  have hdescent : baseEnd_5557913 < baseStart_5557913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557934 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_5557934 : Nat := 118140960795 + 5557934 * 2 ^ 59
def prefixEnd_5557934 : Nat := 4983230072969 + 3 ^ 40 * 5557934 * 2
def baseEnd_5557934 : Nat := 2853891587966162791364533

theorem tailTrace_5557934 : CollatzResearch.WordTrace tailWord_5557934 prefixEnd_5557934 2853891587966162791364533 := by
  unfold tailWord_5557934
  simp only [CollatzResearch.WordTrace]
  refine ⟨25339313330820226550135107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135143004431041208267387237 25339313330820226550135107)
  ·
    refine ⟨38008969996230339825202661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25339313330820226550135107 38008969996230339825202661)
    ·
      refine ⟨7126681874293188717225499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38008969996230339825202661 7126681874293188717225499)
      ·
        refine ⟨10690022811439783075838249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7126681874293188717225499 10690022811439783075838249)
        ·
          refine ⟨8017517108579837306878687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10690022811439783075838249 8017517108579837306878687)
          ·
            refine ⟨12026275662869755960318031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8017517108579837306878687 12026275662869755960318031)
            ·
              refine ⟨18039413494304633940477047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12026275662869755960318031 18039413494304633940477047)
              ·
                refine ⟨27059120241456950910715571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18039413494304633940477047 27059120241456950910715571)
                ·
                  refine ⟨40588680362185426366073357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27059120241456950910715571 40588680362185426366073357)
                  ·
                    refine ⟨15220755135819534887277509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40588680362185426366073357 15220755135819534887277509)
                    ·
                      refine ⟨2853891587966162791364533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15220755135819534887277509 2853891587966162791364533)
                      ·
                        rfl

theorem cell23_5557934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_5557934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557934 prefixEnd_5557934 := by exact prefixLift 5557934
  have htrace : WordTrace (prefixWord ++ tailWord_5557934) baseStart_5557934 baseEnd_5557934 := by
    simpa [prefixWord, tailWord_5557934, baseEnd_5557934] using wordTrace_append hprefix tailTrace_5557934
  have hstable : (prefixWord ++ tailWord_5557934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557934).length < 2 ^ (prefixWord ++ tailWord_5557934).sum := by decide
  have hdescent : baseEnd_5557934 < baseStart_5557934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5557977 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 1, 5, 2]
def baseStart_5557977 : Nat := 118140960795 + 5557977 * 2 ^ 59
def prefixEnd_5557977 : Nat := 4983230072969 + 3 ^ 40 * 5557977 * 2
def baseEnd_5557977 : Nat := 2853913667634306123126835

theorem tailTrace_5557977 : CollatzResearch.WordTrace tailWord_5557977 prefixEnd_5557977 2853913667634306123126835 := by
  unfold tailWord_5557977
  simp only [CollatzResearch.WordTrace]
  refine ⟨202716074985406030744896185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135144049990270687163264123 202716074985406030744896185)
  ·
    refine ⟨152037056239054523058672139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202716074985406030744896185 152037056239054523058672139)
    ·
      refine ⟨228055584358581784588008209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152037056239054523058672139 228055584358581784588008209)
      ·
        refine ⟨171041688268936338441006157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228055584358581784588008209 171041688268936338441006157)
        ·
          refine ⟨64140633100851126915377309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171041688268936338441006157 64140633100851126915377309)
          ·
            refine ⟨24052737412819172593266491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64140633100851126915377309 24052737412819172593266491)
            ·
              refine ⟨36079106119228758889899737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24052737412819172593266491 36079106119228758889899737)
              ·
                refine ⟨27059329589421569167424803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36079106119228758889899737 27059329589421569167424803)
                ·
                  refine ⟨40588994384132353751137205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27059329589421569167424803 40588994384132353751137205)
                  ·
                    refine ⟨3805218223512408164169113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40588994384132353751137205 3805218223512408164169113)
                    ·
                      refine ⟨2853913667634306123126835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3805218223512408164169113 2853913667634306123126835)
                      ·
                        rfl

theorem cell23_5557977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 5, 2].length) (baseStart_5557977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5557977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5557977 prefixEnd_5557977 := by exact prefixLift 5557977
  have htrace : WordTrace (prefixWord ++ tailWord_5557977) baseStart_5557977 baseEnd_5557977 := by
    simpa [prefixWord, tailWord_5557977, baseEnd_5557977] using wordTrace_append hprefix tailTrace_5557977
  have hstable : (prefixWord ++ tailWord_5557977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5557977).length < 2 ^ (prefixWord ++ tailWord_5557977).sum := by decide
  have hdescent : baseEnd_5557977 < baseStart_5557977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5557977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558001 : List Nat := [1, 2, 2, 2, 2, 3, 3, 3, 1, 1, 3]
def baseStart_5558001 : Nat := 118140960795 + 5558001 * 2 ^ 59
def prefixEnd_5558001 : Nat := 4983230072969 + 3 ^ 40 * 5558001 * 2
def baseEnd_5558001 : Nat := 2853925991170014029226725

theorem tailTrace_5558001 : CollatzResearch.WordTrace tailWord_5558001 prefixEnd_5558001 2853925991170014029226725 := by
  unfold tailWord_5558001
  simp only [CollatzResearch.WordTrace]
  refine ⟨202716950337319082843769857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135144633558212721895846571 202716950337319082843769857)
  ·
    refine ⟨152037712752989312132827393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202716950337319082843769857 152037712752989312132827393)
    ·
      refine ⟨114028284564741984099620545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152037712752989312132827393 114028284564741984099620545)
      ·
        refine ⟨85521213423556488074715409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114028284564741984099620545 85521213423556488074715409)
        ·
          refine ⟨64140910067667366056036557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85521213423556488074715409 64140910067667366056036557)
          ·
            refine ⟨24052841275375262271013709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64140910067667366056036557 24052841275375262271013709)
            ·
              refine ⟨9019815478265723351630141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24052841275375262271013709 9019815478265723351630141)
              ·
                refine ⟨3382430804349646256861303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9019815478265723351630141 3382430804349646256861303)
                ·
                  refine ⟨5073646206524469385291955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3382430804349646256861303 5073646206524469385291955)
                  ·
                    refine ⟨7610469309786704077937933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5073646206524469385291955 7610469309786704077937933)
                    ·
                      refine ⟨2853925991170014029226725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7610469309786704077937933 2853925991170014029226725)
                      ·
                        rfl

theorem cell23_5558001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_5558001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558001 prefixEnd_5558001 := by exact prefixLift 5558001
  have htrace : WordTrace (prefixWord ++ tailWord_5558001) baseStart_5558001 baseEnd_5558001 := by
    simpa [prefixWord, tailWord_5558001, baseEnd_5558001] using wordTrace_append hprefix tailTrace_5558001
  have hstable : (prefixWord ++ tailWord_5558001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558001).length < 2 ^ (prefixWord ++ tailWord_5558001).sum := by decide
  have hdescent : baseEnd_5558001 < baseStart_5558001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558007 : List Nat := [1, 1, 3, 1, 1, 1, 6, 3, 1, 1, 4]
def baseStart_5558007 : Nat := 118140960795 + 5558007 * 2 ^ 59
def prefixEnd_5558007 : Nat := 4983230072969 + 3 ^ 40 * 5558007 * 2
def baseEnd_5558007 : Nat := 2853929072053941005751697

theorem tailTrace_5558007 : CollatzResearch.WordTrace tailWord_5558007 prefixEnd_5558007 2853929072053941005751697 := by
  unfold tailWord_5558007
  simp only [CollatzResearch.WordTrace]
  refine ⟨202717169175297345868488275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135144779450198230578992183 202717169175297345868488275)
  ·
    refine ⟨304075753762946018802732413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202717169175297345868488275 304075753762946018802732413)
    ·
      refine ⟨114028407661104757051024655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304075753762946018802732413 114028407661104757051024655)
      ·
        refine ⟨171042611491657135576536983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114028407661104757051024655 171042611491657135576536983)
        ·
          refine ⟨256563917237485703364805475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171042611491657135576536983 256563917237485703364805475)
          ·
            refine ⟨384845875856228555047208213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256563917237485703364805475 384845875856228555047208213)
            ·
              refine ⟨18039650430760713517837885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 384845875856228555047208213 18039650430760713517837885)
              ·
                refine ⟨6764868911535267569189207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18039650430760713517837885 6764868911535267569189207)
                ·
                  refine ⟨10147303367302901353783811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6764868911535267569189207 10147303367302901353783811)
                  ·
                    refine ⟨15220955050954352030675717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10147303367302901353783811 15220955050954352030675717)
                    ·
                      refine ⟨2853929072053941005751697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15220955050954352030675717 2853929072053941005751697)
                      ·
                        rfl

theorem cell23_5558007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_5558007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558007 prefixEnd_5558007 := by exact prefixLift 5558007
  have htrace : WordTrace (prefixWord ++ tailWord_5558007) baseStart_5558007 baseEnd_5558007 := by
    simpa [prefixWord, tailWord_5558007, baseEnd_5558007] using wordTrace_append hprefix tailTrace_5558007
  have hstable : (prefixWord ++ tailWord_5558007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558007).length < 2 ^ (prefixWord ++ tailWord_5558007).sum := by decide
  have hdescent : baseEnd_5558007 < baseStart_5558007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558017 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 4, 4]
def baseStart_5558017 : Nat := 118140960795 + 5558017 * 2 ^ 59
def prefixEnd_5558017 : Nat := 4983230072969 + 3 ^ 40 * 5558017 * 2
def baseEnd_5558017 : Nat := 951311402286828655542217

theorem tailTrace_5558017 : CollatzResearch.WordTrace tailWord_5558017 prefixEnd_5558017 951311402286828655542217 := by
  unfold tailWord_5558017
  simp only [CollatzResearch.WordTrace]
  refine ⟨202717533905261117576352305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135145022603507411717568203 202717533905261117576352305)
  ·
    refine ⟨152038150428945838182264229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202717533905261117576352305 152038150428945838182264229)
    ·
      refine ⟨28507153205427344659174543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152038150428945838182264229 28507153205427344659174543)
      ·
        refine ⟨42760729808141016988761815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28507153205427344659174543 42760729808141016988761815)
        ·
          refine ⟨64141094712211525483142723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42760729808141016988761815 64141094712211525483142723)
          ·
            refine ⟨96211642068317288224714085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64141094712211525483142723 96211642068317288224714085)
            ·
              refine ⟨18039682887809491542133891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96211642068317288224714085 18039682887809491542133891)
              ·
                refine ⟨27059524331714237313200837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18039682887809491542133891 27059524331714237313200837)
                ·
                  refine ⟨5073660812196419496225157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27059524331714237313200837 5073660812196419496225157)
                  ·
                    refine ⟨951311402286828655542217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5073660812196419496225157 951311402286828655542217)
                    ·
                      rfl

theorem cell23_5558017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_5558017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558017 prefixEnd_5558017 := by exact prefixLift 5558017
  have htrace : WordTrace (prefixWord ++ tailWord_5558017) baseStart_5558017 baseEnd_5558017 := by
    simpa [prefixWord, tailWord_5558017, baseEnd_5558017] using wordTrace_append hprefix tailTrace_5558017
  have hstable : (prefixWord ++ tailWord_5558017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558017).length < 2 ^ (prefixWord ++ tailWord_5558017).sum := by decide
  have hdescent : baseEnd_5558017 < baseStart_5558017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558030 : List Nat := [4, 1, 1, 2, 1, 1, 3, 10]
def baseStart_5558030 : Nat := 118140960795 + 5558030 * 2 ^ 59
def prefixEnd_5558030 : Nat := 4983230072969 + 3 ^ 40 * 5558030 * 2
def baseEnd_5558030 : Nat := 105701514152184978361633

theorem tailTrace_5558030 : CollatzResearch.WordTrace tailWord_5558030 prefixEnd_5558030 105701514152184978361633 := by
  unfold tailWord_5558030
  simp only [CollatzResearch.WordTrace]
  refine ⟨25339751006776752599571943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135145338702809347197717029 25339751006776752599571943)
  ·
    refine ⟨38009626510165128899357915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25339751006776752599571943 38009626510165128899357915)
    ·
      refine ⟨57014439765247693349036873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38009626510165128899357915 57014439765247693349036873)
      ·
        refine ⟨42760829823935770011777655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57014439765247693349036873 42760829823935770011777655)
        ·
          refine ⟨64141244735903655017666483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42760829823935770011777655 64141244735903655017666483)
          ·
            refine ⟨96211867103855482526499725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64141244735903655017666483 96211867103855482526499725)
            ·
              refine ⟨36079450163945805947437397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96211867103855482526499725 36079450163945805947437397)
              ·
                refine ⟨105701514152184978361633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36079450163945805947437397 105701514152184978361633)
                ·
                  rfl

theorem cell23_5558030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_5558030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558030 prefixEnd_5558030 := by exact prefixLift 5558030
  have htrace : WordTrace (prefixWord ++ tailWord_5558030) baseStart_5558030 baseEnd_5558030 := by
    simpa [prefixWord, tailWord_5558030, baseEnd_5558030] using wordTrace_append hprefix tailTrace_5558030
  have hstable : (prefixWord ++ tailWord_5558030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558030).length < 2 ^ (prefixWord ++ tailWord_5558030).sum := by decide
  have hdescent : baseEnd_5558030 < baseStart_5558030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558077 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_5558077 : Nat := 118140960795 + 5558077 * 2 ^ 59
def prefixEnd_5558077 : Nat := 4983230072969 + 3 ^ 40 * 5558077 * 2
def baseEnd_5558077 : Nat := 951321671899918577292125

theorem tailTrace_5558077 : CollatzResearch.WordTrace tailWord_5558077 prefixEnd_5558077 951321671899918577292125 := by
  unfold tailWord_5558077
  simp only [CollatzResearch.WordTrace]
  refine ⟨202719722285043747823536485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135146481523362498549024323 202719722285043747823536485)
  ·
    refine ⟨38009947928445702716913091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 202719722285043747823536485 38009947928445702716913091)
    ·
      refine ⟨57014921892668554075369637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38009947928445702716913091 57014921892668554075369637)
      ·
        refine ⟨10690297854875353889131807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57014921892668554075369637 10690297854875353889131807)
        ·
          refine ⟨16035446782313030833697711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10690297854875353889131807 16035446782313030833697711)
          ·
            refine ⟨24053170173469546250546567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16035446782313030833697711 24053170173469546250546567)
            ·
              refine ⟨36079755260204319375819851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24053170173469546250546567 36079755260204319375819851)
              ·
                refine ⟨54119632890306479063729777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36079755260204319375819851 54119632890306479063729777)
                ·
                  refine ⟨40589724667729859297797333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54119632890306479063729777 40589724667729859297797333)
                  ·
                    refine ⟨951321671899918577292125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40589724667729859297797333 951321671899918577292125)
                    ·
                      rfl

theorem cell23_5558077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_5558077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558077 prefixEnd_5558077 := by exact prefixLift 5558077
  have htrace : WordTrace (prefixWord ++ tailWord_5558077) baseStart_5558077 baseEnd_5558077 := by
    simpa [prefixWord, tailWord_5558077, baseEnd_5558077] using wordTrace_append hprefix tailTrace_5558077
  have hstable : (prefixWord ++ tailWord_5558077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558077).length < 2 ^ (prefixWord ++ tailWord_5558077).sum := by decide
  have hdescent : baseEnd_5558077 < baseStart_5558077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558137 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 7]
def baseStart_5558137 : Nat := 118140960795 + 5558137 * 2 ^ 59
def prefixEnd_5558137 : Nat := 4983230072969 + 3 ^ 40 * 5558137 * 2
def baseEnd_5558137 : Nat := 317110647171002833014011

theorem tailTrace_5558137 : CollatzResearch.WordTrace tailWord_5558137 prefixEnd_5558137 317110647171002833014011 := by
  unfold tailWord_5558137
  simp only [CollatzResearch.WordTrace]
  refine ⟨202721910664826378070720665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135147940443217585380480443 202721910664826378070720665)
  ·
    refine ⟨152041432998619783553040499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202721910664826378070720665 152041432998619783553040499)
    ·
      refine ⟨228062149497929675329560749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152041432998619783553040499 228062149497929675329560749)
      ·
        refine ⟨85523306061723628248585281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228062149497929675329560749 85523306061723628248585281)
        ·
          refine ⟨64142479546292721186438961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85523306061723628248585281 64142479546292721186438961)
          ·
            refine ⟨48106859659719540889829221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64142479546292721186438961 48106859659719540889829221)
            ·
              refine ⟨9020036186197413916842979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48106859659719540889829221 9020036186197413916842979)
              ·
                refine ⟨13530054279296120875264469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9020036186197413916842979 13530054279296120875264469)
                ·
                  refine ⟨317110647171002833014011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13530054279296120875264469 317110647171002833014011)
                  ·
                    rfl

theorem cell23_5558137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 7].length) (baseStart_5558137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558137 prefixEnd_5558137 := by exact prefixLift 5558137
  have htrace : WordTrace (prefixWord ++ tailWord_5558137) baseStart_5558137 baseEnd_5558137 := by
    simpa [prefixWord, tailWord_5558137, baseEnd_5558137] using wordTrace_append hprefix tailTrace_5558137
  have hstable : (prefixWord ++ tailWord_5558137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558137).length < 2 ^ (prefixWord ++ tailWord_5558137).sum := by decide
  have hdescent : baseEnd_5558137 < baseStart_5558137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558167 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 1, 7]
def baseStart_5558167 : Nat := 118140960795 + 5558167 * 2 ^ 59
def prefixEnd_5558167 : Nat := 4983230072969 + 3 ^ 40 * 5558167 * 2
def baseEnd_5558167 : Nat := 951337076319553459916987

theorem tailTrace_5558167 : CollatzResearch.WordTrace tailWord_5558167 prefixEnd_5558167 951337076319553459916987 := by
  unfold tailWord_5558167
  simp only [CollatzResearch.WordTrace]
  refine ⟨202723004854717693194312755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135148669903145128796208503 202723004854717693194312755)
  ·
    refine ⟨304084507282076539791469133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202723004854717693194312755 304084507282076539791469133)
    ·
      refine ⟨114031690230778702421800925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304084507282076539791469133 114031690230778702421800925)
      ·
        refine ⟨42761883836542013408175347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114031690230778702421800925 42761883836542013408175347)
        ·
          refine ⟨64142825754813020112263021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42761883836542013408175347 64142825754813020112263021)
          ·
            refine ⟨24053559658054882542098633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64142825754813020112263021 24053559658054882542098633)
            ·
              refine ⟨18040169743541161906573975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24053559658054882542098633 18040169743541161906573975)
              ·
                refine ⟨27060254615311742859860963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18040169743541161906573975 27060254615311742859860963)
                ·
                  refine ⟨40590381922967614289791445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27060254615311742859860963 40590381922967614289791445)
                  ·
                    refine ⟨951337076319553459916987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40590381922967614289791445 951337076319553459916987)
                    ·
                      rfl

theorem cell23_5558167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_5558167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558167 prefixEnd_5558167 := by exact prefixLift 5558167
  have htrace : WordTrace (prefixWord ++ tailWord_5558167) baseStart_5558167 baseEnd_5558167 := by
    simpa [prefixWord, tailWord_5558167, baseEnd_5558167] using wordTrace_append hprefix tailTrace_5558167
  have hstable : (prefixWord ++ tailWord_5558167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558167).length < 2 ^ (prefixWord ++ tailWord_5558167).sum := by decide
  have hdescent : baseEnd_5558167 < baseStart_5558167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558224 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 3]
def baseStart_5558224 : Nat := 118140960795 + 5558224 * 2 ^ 59
def prefixEnd_5558224 : Nat := 4983230072969 + 3 ^ 40 * 5558224 * 2
def baseEnd_5558224 : Nat := 2854040497355966656738199

theorem tailTrace_5558224 : CollatzResearch.WordTrace tailWord_5558224 prefixEnd_5558224 2854040497355966656738199 := by
  unfold tailWord_5558224
  simp only [CollatzResearch.WordTrace]
  refine ⟨101362541907755595964568863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135150055877007461286091817 101362541907755595964568863)
  ·
    refine ⟨152043812861633393946853295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101362541907755595964568863 152043812861633393946853295)
    ·
      refine ⟨228065719292450090920279943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152043812861633393946853295 228065719292450090920279943)
      ·
        refine ⟨342098578938675136380419915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228065719292450090920279943 342098578938675136380419915)
        ·
          refine ⟨513147868408012704570629873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342098578938675136380419915 513147868408012704570629873)
          ·
            refine ⟨384860901306009528427972405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 513147868408012704570629873 384860901306009528427972405)
            ·
              refine ⟨36080709497438393290122413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 384860901306009528427972405 36080709497438393290122413)
              ·
                refine ⟨13530266061539397483795905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36080709497438393290122413 13530266061539397483795905)
                ·
                  refine ⟨10147699546154548112846929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13530266061539397483795905 10147699546154548112846929)
                  ·
                    refine ⟨7610774659615911084635197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10147699546154548112846929 7610774659615911084635197)
                    ·
                      refine ⟨2854040497355966656738199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7610774659615911084635197 2854040497355966656738199)
                      ·
                        rfl

theorem cell23_5558224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 3].length) (baseStart_5558224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558224 prefixEnd_5558224 := by exact prefixLift 5558224
  have htrace : WordTrace (prefixWord ++ tailWord_5558224) baseStart_5558224 baseEnd_5558224 := by
    simpa [prefixWord, tailWord_5558224, baseEnd_5558224] using wordTrace_append hprefix tailTrace_5558224
  have hstable : (prefixWord ++ tailWord_5558224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558224).length < 2 ^ (prefixWord ++ tailWord_5558224).sum := by decide
  have hdescent : baseEnd_5558224 < baseStart_5558224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558231 : List Nat := [1, 1, 3, 2, 1, 1, 4, 5, 1, 4]
def baseStart_5558231 : Nat := 118140960795 + 5558231 * 2 ^ 59
def prefixEnd_5558231 : Nat := 4983230072969 + 3 ^ 40 * 5558231 * 2
def baseEnd_5558231 : Nat := 951348030573516043116889

theorem tailTrace_5558231 : CollatzResearch.WordTrace tailWord_5558231 prefixEnd_5558231 951348030573516043116889 := by
  unfold tailWord_5558231
  simp only [CollatzResearch.WordTrace]
  refine ⟨202725339126485832124642547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135150226084323888083095031 202725339126485832124642547)
  ·
    refine ⟨304088008689728748186963821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202725339126485832124642547 304088008689728748186963821)
    ·
      refine ⟨114033003258648280570111433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 304088008689728748186963821 114033003258648280570111433)
      ·
        refine ⟨85524752443986210427583575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114033003258648280570111433 85524752443986210427583575)
        ·
          refine ⟨128287128665979315641375363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85524752443986210427583575 128287128665979315641375363)
          ·
            refine ⟨192430692998968973462063045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128287128665979315641375363 192430692998968973462063045)
            ·
              refine ⟨36080754937306682524136821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192430692998968973462063045 36080754937306682524136821)
              ·
                refine ⟨3382570775372501486637827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36080754937306682524136821 3382570775372501486637827)
                ·
                  refine ⟨5073856163058752229956741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3382570775372501486637827 5073856163058752229956741)
                  ·
                    refine ⟨951348030573516043116889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5073856163058752229956741 951348030573516043116889)
                    ·
                      rfl

theorem cell23_5558231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_5558231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558231 prefixEnd_5558231 := by exact prefixLift 5558231
  have htrace : WordTrace (prefixWord ++ tailWord_5558231) baseStart_5558231 baseEnd_5558231 := by
    simpa [prefixWord, tailWord_5558231, baseEnd_5558231] using wordTrace_append hprefix tailTrace_5558231
  have hstable : (prefixWord ++ tailWord_5558231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558231).length < 2 ^ (prefixWord ++ tailWord_5558231).sum := by decide
  have hdescent : baseEnd_5558231 < baseStart_5558231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558244 : List Nat := [2, 3, 1, 1, 1, 1, 6, 2, 6]
def baseStart_5558244 : Nat := 118140960795 + 5558244 * 2 ^ 59
def prefixEnd_5558244 : Nat := 4983230072969 + 3 ^ 40 * 5558244 * 2
def baseEnd_5558244 : Nat := 317116751885450730943123

theorem tailTrace_5558244 : CollatzResearch.WordTrace tailWord_5558244 prefixEnd_5558244 317116751885450730943123 := by
  unfold tailWord_5558244
  simp only [CollatzResearch.WordTrace]
  refine ⟨101362906637719367672432893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135150542183625823563243857 101362906637719367672432893)
  ·
    refine ⟨38011089989144762877162335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101362906637719367672432893 38011089989144762877162335)
    ·
      refine ⟨57016634983717144315743503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38011089989144762877162335 57016634983717144315743503)
      ·
        refine ⟨85524952475575716473615255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57016634983717144315743503 85524952475575716473615255)
        ·
          refine ⟨128287428713363574710422883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85524952475575716473615255 128287428713363574710422883)
          ·
            refine ⟨192431143070045362065634325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128287428713363574710422883 192431143070045362065634325)
            ·
              refine ⟨9020209831408376346826609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 192431143070045362065634325 9020209831408376346826609)
              ·
                refine ⟨6765157373556282260119957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9020209831408376346826609 6765157373556282260119957)
                ·
                  refine ⟨317116751885450730943123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6765157373556282260119957 317116751885450730943123)
                  ·
                    rfl

theorem cell23_5558244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_5558244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558244 prefixEnd_5558244 := by exact prefixLift 5558244
  have htrace : WordTrace (prefixWord ++ tailWord_5558244) baseStart_5558244 baseEnd_5558244 := by
    simpa [prefixWord, tailWord_5558244, baseEnd_5558244] using wordTrace_append hprefix tailTrace_5558244
  have hstable : (prefixWord ++ tailWord_5558244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558244).length < 2 ^ (prefixWord ++ tailWord_5558244).sum := by decide
  have hdescent : baseEnd_5558244 < baseStart_5558244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558291 : List Nat := [1, 1, 1, 2, 1, 4, 6, 1, 1, 5]
def baseStart_5558291 : Nat := 118140960795 + 5558291 * 2 ^ 59
def prefixEnd_5558291 : Nat := 4983230072969 + 3 ^ 40 * 5558291 * 2
def baseEnd_5558291 : Nat := 951358300186605964866797

theorem tailTrace_5558291 : CollatzResearch.WordTrace tailWord_5558291 prefixEnd_5558291 951358300186605964866797 := by
  unfold tailWord_5558291
  simp only [CollatzResearch.WordTrace]
  refine ⟨202727527506268462371826727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135151685004178974914551151 202727527506268462371826727)
  ·
    refine ⟨304091291259402693557740091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202727527506268462371826727 304091291259402693557740091)
    ·
      refine ⟨456136936889104040336610137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304091291259402693557740091 456136936889104040336610137)
      ·
        refine ⟨342102702666828030252457603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456136936889104040336610137 342102702666828030252457603)
        ·
          refine ⟨513154054000242045378686405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342102702666828030252457603 513154054000242045378686405)
          ·
            refine ⟨96216385125045383508503701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 513154054000242045378686405 96216385125045383508503701)
            ·
              refine ⟨4510143052736502351961111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96216385125045383508503701 4510143052736502351961111)
              ·
                refine ⟨6765214579104753527941667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510143052736502351961111 6765214579104753527941667)
                ·
                  refine ⟨10147821868657130291912501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6765214579104753527941667 10147821868657130291912501)
                  ·
                    refine ⟨951358300186605964866797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10147821868657130291912501 951358300186605964866797)
                    ·
                      rfl

theorem cell23_5558291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 1, 5].length) (baseStart_5558291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558291 prefixEnd_5558291 := by exact prefixLift 5558291
  have htrace : WordTrace (prefixWord ++ tailWord_5558291) baseStart_5558291 baseEnd_5558291 := by
    simpa [prefixWord, tailWord_5558291, baseEnd_5558291] using wordTrace_append hprefix tailTrace_5558291
  have hstable : (prefixWord ++ tailWord_5558291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558291).length < 2 ^ (prefixWord ++ tailWord_5558291).sum := by decide
  have hdescent : baseEnd_5558291 < baseStart_5558291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5558321 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 1, 6]
def baseStart_5558321 : Nat := 118140960795 + 5558321 * 2 ^ 59
def prefixEnd_5558321 : Nat := 4983230072969 + 3 ^ 40 * 5558321 * 2
def baseEnd_5558321 : Nat := 951363434993150925741751

theorem tailTrace_5558321 : CollatzResearch.WordTrace tailWord_5558321 prefixEnd_5558321 951363434993150925741751 := by
  unfold tailWord_5558321
  simp only [CollatzResearch.WordTrace]
  refine ⟨202728621696159777495418817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135152414464106518330279211 202728621696159777495418817)
  ·
    refine ⟨152046466272119833121564113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202728621696159777495418817 152046466272119833121564113)
    ·
      refine ⟨114034849704089874841173085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152046466272119833121564113 114034849704089874841173085)
      ·
        refine ⟨42763068639033703065439907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114034849704089874841173085 42763068639033703065439907)
        ·
          refine ⟨64144602958550554598159861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42763068639033703065439907 64144602958550554598159861)
          ·
            refine ⟨6013556527364114493577487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64144602958550554598159861 6013556527364114493577487)
            ·
              refine ⟨9020334791046171740366231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6013556527364114493577487 9020334791046171740366231)
              ·
                refine ⟨13530502186569257610549347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9020334791046171740366231 13530502186569257610549347)
                ·
                  refine ⟨20295753279853886415824021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13530502186569257610549347 20295753279853886415824021)
                  ·
                    refine ⟨951363434993150925741751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20295753279853886415824021 951363434993150925741751)
                    ·
                      rfl

theorem cell23_5558321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_5558321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5558321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5558321 prefixEnd_5558321 := by exact prefixLift 5558321
  have htrace : WordTrace (prefixWord ++ tailWord_5558321) baseStart_5558321 baseEnd_5558321 := by
    simpa [prefixWord, tailWord_5558321, baseEnd_5558321] using wordTrace_append hprefix tailTrace_5558321
  have hstable : (prefixWord ++ tailWord_5558321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5558321).length < 2 ^ (prefixWord ++ tailWord_5558321).sum := by decide
  have hdescent : baseEnd_5558321 < baseStart_5558321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5558321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
